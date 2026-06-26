import DeepWiki.SymbolicIntegration.ComputableTowerRischDE
import DeepWiki.SymbolicIntegration.ComputableRischDETowerCorrectG

/-! # The self-validating tower integrator's `D(∫f) = f` BRIDGE at the carrier `α = QFunNZG ℚ`
The generic tower engine certifies every integral with the cleared antiderivative check `checkIdentityG`
(`ComputableTowerIntegrate`): a Boolean self-check that clears `D(g) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) − f` of
denominators and tests it `= 0` (`cisZeroG`). This file gives the **field ⇔ engine bridge** through that
guard: when `checkIdentityG f result = true`, the field-level identity `D(∫f) = f` holds over the tower
fraction field `RatFunc (CFieldSpec.K α)`.

The bridge is the per-instance certificate the guard supplies — it does **not** need the full integrator
field identity `cIntegrateG_field_identity` (the whole §5 Hermite/canonical-split chain). The guard
`checkIdentityG` *never calls the gcd*: it only folds the residue terms `cᵢ·D(vᵢ)/vᵢ` and clears
denominators, so the whole field ⇒ Boolean clearing bridge is **carrier-agnostic** — built once,
generically, over `{α} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]`, with
the field algebra map `amG α` (`ComputableTowerField`) and the fraction-field derivation
`extendDeriv (implicitDeriv (toPolyG Dt))` (`ComputableFractionFieldDeriv`). The deliverable is the
specialization at the generic level-1 carrier `α = QFunNZG ℚ = Frac(ℚ[x])`, where `CFieldSpec.K (QFunNZG ℚ)
= RatFunc ℚ` and the engine runs the recursive tower instances — `cgcdFF`-free, exactly the chunk-1 pattern
of `ComputableSplitFactorTowerCorrectG` / `ComputableRischDETowerCorrectG`.

The deliverable:

* **`logResidueSumG`** — the generic residue sum `∑_{(c,v)} amG(C(toK c))·(Δv)/v` (the symbolic derivative
  of the generic logarithmic part `∑ c·log v`), and the fold reading `checkIdentityG_fold_eq`.
* **`field_identity_of_checkIdentityG`** — the field ⟸ engine bridge: the engine's boolean self-check being
  `true` implies the field identity `D(∫f) = f` (no regime / residue-set / degree hypothesis).
* **`towerFractionFieldDerivG`** — the generic fraction-field derivation `extendDeriv (implicitDeriv (toPolyG
  Dt))` over `RatFunc (CFieldSpec.K α)`, with the quotient rule `towerFractionFieldDerivG_div`.
* **★ `cIntegrateGChecked` / `cIntegrateGChecked_correct`** — the self-validating integrator (guarding
  `cIntegrateGFull`'s output by `checkIdentityG`) and its UNCONDITIONAL correctness at `α = QFunNZG ℚ`:
  `cIntegrateGChecked f = some res ⟹ D(res) = f` over `RatFunc ℚ`, for ALL inputs and ALL regimes — the
  `checkIdentityG` guard alone supplies correctness. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### The generic field algebra map and fraction-field derivation

The field-level identity lives over `RatFunc (CFieldSpec.K α)`. The polynomial-into-rational embedding is
the generic `amG α = algebraMap (CFieldSpec.K α)[X] (RatFunc (CFieldSpec.K α))` (`ComputableTowerField`),
and the derivation is `extendDeriv (implicitDeriv (toPolyG Dt))` — the fraction-field extension of the
monomial derivation by the quotient rule. We package the derivation as `towerFractionFieldDerivG` and give
it the quotient-rule reading on fractions of polynomial images. -/

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- **The generic tower fraction-field derivation** `towerFractionFieldDerivG Dt = extendDeriv (implicitDeriv
(toPolyG Dt))` on `RatFunc (CFieldSpec.K α)`, extending the base monomial derivation `implicitDeriv (toPolyG
Dt)` on `(CFieldSpec.K α)[X]` by the quotient rule. The carrier-generic mirror of `towerFractionFieldDeriv`
(which was pinned at `α = QFunNZ`). -/
noncomputable def towerFractionFieldDerivG (Dt : CPolyG α) :
    Derivation ℤ (RatFunc (CFieldSpec.K α)) (RatFunc (CFieldSpec.K α)) :=
  extendDeriv (Differential.implicitDeriv (toPolyG Dt))

/-- **Quotient-rule reading of `D(gnum/gden)` over the generic tower field**: with `g = amG(gnum)/amG(gden)`,
`towerFractionFieldDerivG Dt g = (amG(Δ gnum)·amG(gden) − amG(gnum)·amG(Δ gden)) / (amG(gden))²`, where
`Δ = implicitDeriv (toPolyG Dt)`. The quotient rule for the keystone derivation on a fraction of polynomial
images — the carrier-generic mirror of `towerFractionFieldDeriv_div`. -/
theorem towerFractionFieldDerivG_div (Dt : CPolyG α) (gnum gden : (CFieldSpec.K α)[X]) :
    towerFractionFieldDerivG Dt (amG α gnum / amG α gden)
      = (amG α (Differential.implicitDeriv (toPolyG Dt) gnum) * amG α gden
          - amG α gnum * amG α (Differential.implicitDeriv (toPolyG Dt) gden))
        / (amG α gden) ^ 2 := by
  rw [towerFractionFieldDerivG, ← RatFunc.mk_eq_div, extendDeriv_mk, RatFunc.mk_eq_div, map_sub,
    map_mul, map_mul, map_pow]

/-! ### The generic logarithmic-part residue sum (over `α`-valued coefficients)

The generic checker `checkIdentityG` folds the logarithmic part `∑ᵢ cᵢ·log(vᵢ)` (coefficients `cᵢ : α`)
into its symbolic derivative `∑ᵢ cᵢ·(Δvᵢ)/vᵢ` (the log-derivative `D(log v) = (Δv)/v`), accumulated as a
single fraction `(Lnum, Lden)` over `∏ᵢ vᵢ`. We give it as a genuine field element `logResidueSumG` over
`RatFunc (CFieldSpec.K α)`, with the residue coefficient `c : α` embedded as the constant `amG(C(toK c))`. -/

/-- **The generic logarithmic-part residue sum** `logResidueSumG Dt logs = ∑_{(c,v)∈logs}
amG(C(toK c))·(Δv)/v` over the tower fraction field `RatFunc (CFieldSpec.K α)`, with `Δ = implicitDeriv
(toPolyG Dt)` (so `Δv = toPolyG (cmonomialDeriv Dt v)`). The symbolic derivative of the generic logarithmic
part `∑ᵢ cᵢ·log(vᵢ)` (`cᵢ : α`) — exactly the residue sum `checkIdentityG` clears against `f`. The
carrier-generic mirror of `logResidueSum`/`logResidueSumG`. -/
noncomputable def logResidueSumG (Dt : CPolyG α) (logs : List (α × CPolyG α)) :
    RatFunc (CFieldSpec.K α) :=
  (logs.map (fun cv =>
    amG α (Polynomial.C (CFieldSpec.toK cv.1))
      * (amG α (toPolyG (cmonomialDeriv Dt cv.2)) / amG α (toPolyG cv.2)))).sum

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `logResidueSumG` of the empty list is `0`. -/
@[simp] theorem logResidueSumG_nil (Dt : CPolyG α) : logResidueSumG Dt ([] : List (α × CPolyG α)) = 0 :=
  rfl

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `logResidueSumG` peels the head: `logResidueSumG Dt ((c,v) :: rest) = amG(C(toK c))·(Δv)/v
+ logResidueSumG Dt rest`. -/
theorem logResidueSumG_cons (Dt : CPolyG α) (cv : α × CPolyG α) (rest : List (α × CPolyG α)) :
    logResidueSumG Dt (cv :: rest)
      = amG α (Polynomial.C (CFieldSpec.toK cv.1))
          * (amG α (toPolyG (cmonomialDeriv Dt cv.2)) / amG α (toPolyG cv.2))
        + logResidueSumG Dt rest := by
  simp only [logResidueSumG, List.map_cons, List.sum_cons]

/-! ### The `checkIdentityG` fold computes the residue sum

`checkIdentityG`'s `foldl` accumulates `∑ cᵢ·(Δvᵢ)/vᵢ` as one fraction `(Lnum, Lden)` over `∏ᵢ vᵢ`,
starting at `([0], [1])` and combining `acc.1/acc.2 + (c·Δv)/v = (acc.1·v + c·Δv·acc.2)/(acc.2·v)`.
Reading through `amG α`, the running fraction is the seed plus the partial `logResidueSumG`; with all `vᵢ`
nonzero the seed contributes `0`. The carrier-generic mirror of `checkIdentity_fold_eq`. -/

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The `checkIdentityG` fold computes the residue sum** (field reading): folding from a seed
`(snum, sden)` (`sden ≠ 0`) over a generic log list whose every argument `v` is nonzero, the running
fraction `amG(Lnum)/amG(Lden)` equals the seed fraction plus `logResidueSumG`, and the running denominator
`Lden = sden·∏ᵢ vᵢ` stays nonzero. By induction on the list — the carrier-generic mirror of
`checkIdentityG_fold_eq`. -/
theorem checkIdentityG_fold_eq (Dt : CPolyG α) :
    ∀ (logs : List (α × CPolyG α)) (snum sden : CPolyG α),
      toPolyG sden ≠ 0 →
      (∀ cv ∈ logs, toPolyG cv.2 ≠ 0) →
      let res := logs.foldl
        (fun (acc : CPolyG α × CPolyG α) (cv : α × CPolyG α) =>
          let c := cv.1
          let v := cv.2
          let Dv := cmonomialDeriv Dt v
          let termNum := cscaleG c Dv
          (caddG (cmulG acc.1 v) (cmulG termNum acc.2), cmulG acc.2 v))
        (snum, sden)
      toPolyG res.2 ≠ 0 ∧
        amG α (toPolyG res.1) / amG α (toPolyG res.2)
          = amG α (toPolyG snum) / amG α (toPolyG sden) + logResidueSumG Dt logs := by
  intro logs
  induction logs with
  | nil =>
    intro snum sden hsden _
    refine ⟨hsden, ?_⟩
    simp only [logResidueSumG_nil, add_zero, List.foldl_nil]
  | cons cv rest ih =>
    intro snum sden hsden hv
    -- the head argument `v` is nonzero
    have hvne : toPolyG cv.2 ≠ 0 := hv cv List.mem_cons_self
    -- one fold step: new accumulator
    set newnum := caddG (cmulG snum cv.2) (cmulG (cscaleG cv.1 (cmonomialDeriv Dt cv.2)) sden)
      with hnewnum
    set newden := cmulG sden cv.2 with hnewden
    have hnewden_ne : toPolyG newden ≠ 0 := by
      rw [hnewden, toPolyG_cmulG]; exact mul_ne_zero hsden hvne
    -- the IH applied to the rest with the new seed
    have hrest : ∀ cv' ∈ rest, toPolyG cv'.2 ≠ 0 := fun cv' hcv' => hv cv' (List.mem_cons_of_mem _ hcv')
    obtain ⟨hden, heq⟩ := ih newnum newden hnewden_ne hrest
    refine ⟨?_, ?_⟩
    · -- the running denominator after the head step is `(newnum, newden)`
      simp only [List.foldl_cons]
      exact hden
    simp only [List.foldl_cons]
    rw [heq, logResidueSumG_cons]
    -- the field algebra: `snum/sden + C(c)·(Δv)/v = newnum/newden`
    have hAsden : amG α (toPolyG sden) ≠ 0 := amG_toPolyG_ne_zero hsden
    have hAv : amG α (toPolyG cv.2) ≠ 0 := amG_toPolyG_ne_zero hvne
    have hstep : amG α (toPolyG newnum) / amG α (toPolyG newden)
        = amG α (toPolyG snum) / amG α (toPolyG sden)
          + amG α (Polynomial.C (CFieldSpec.toK cv.1))
              * (amG α (toPolyG (cmonomialDeriv Dt cv.2)) / amG α (toPolyG cv.2)) := by
      rw [hnewnum, hnewden, toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cscaleG,
        toPolyG_cmulG, map_add, map_mul, map_mul, map_mul]
      field_simp
      simp only [map_mul]
      ring
    rw [hstep]; ring

end DeepWiki.SymbolicIntegration
