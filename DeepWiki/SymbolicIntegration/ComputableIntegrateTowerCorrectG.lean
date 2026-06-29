import DeepWiki.SymbolicIntegration.ComputableTowerRischDE
import DeepWiki.SymbolicIntegration.ComputableRischDETowerCorrectG

/-! # The `checkIdentityG` ⟹ field-identity BRIDGE at the carrier `α = QFunNZG ℚ`
The generic tower engine certifies every integral with the cleared antiderivative check `checkIdentityG`
(`ComputableTowerIntegrate`): a Boolean self-check that clears `D(g) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) − f` of
denominators and tests it `= 0` (`cisZeroG`). This file gives the **field ⇔ engine bridge** through that
guard: when `checkIdentityG f result = true`, the field-level identity `D(∫f) = f` holds over the tower
fraction field `RatFunc (CFieldSpec.K α)`.

The bridge is the per-instance certificate the guard supplies — it does **not** need the full integrator
field identity `cIntegrateG_field_identity` (the whole §5 Hermite/canonical-split chain). The guard
`checkIdentityG` *never calls the gcd*: it only folds the residue terms `cᵢ·D(vᵢ)/vᵢ` and clears
denominators, so the whole field ⇒ Boolean clearing bridge is **carrier-agnostic** — built once,
generically, over `{α} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]`, with the field algebra
map `amG α` (`ComputableTowerField`) and the fraction-field derivation
`extendDeriv (implicitDeriv (toPolyG Dt))` (`ComputableFractionFieldDeriv`). It specializes at the generic
level-1 carrier `α = QFunNZG ℚ = Frac(ℚ[x])`, where `CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ` and the engine
runs the recursive tower instances — `cgcdFF`-free, exactly the chunk-1 pattern of
`ComputableSplitFactorTowerCorrectG` / `ComputableRischDETowerCorrectG`.

The deliverable:

* **`logResidueSumG`** — the generic residue sum `∑_{(c,v)} amG(C(toK c))·(Δv)/v` (the symbolic derivative
  of the generic logarithmic part `∑ c·log v`), and the fold reading `checkIdentityG_fold_eq`.
* **`field_identity_of_checkIdentityG`** — the field ⟸ engine bridge: the engine's boolean self-check being
  `true` implies the field identity `D(∫f) = f` (no regime / residue-set / degree hypothesis).
* **`towerFractionFieldDerivG`** — the generic fraction-field derivation `extendDeriv (implicitDeriv (toPolyG
  Dt))` over `RatFunc (CFieldSpec.K α)`, with the quotient rule `towerFractionFieldDerivG_div`.

The bridge is what the a-priori one-shots (`cIntegrateGFull_primitive_oneShot`,
`field_identity_of_cIntegrateGFull_of_checkIdentityG`) consume to turn an engine self-check into the field
identity `D(∫f) = f` — see `ComputableOneShotSoundness` / `ComputableNormalPartSoundness`. -/

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
Dt)` on `(CFieldSpec.K α)[X]` by the quotient rule. The carrier-generic fraction-field derivation over any
computable tower `[CField α] [CFieldSpec α]`. -/
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

/-! ### The `checkIdentityG` ⟹ field-identity bridge

`checkIdentityG Dt res anum aden = true` is (via `cisZeroG_iff`) the cleared polynomial identity
`(GP·LD + LN·GD²)·AD = AN·(GD²·LD)` over `(CFieldSpec.K α)[X]`, where `GP = toPolyG gprimeNum`,
`(LN, LD) = fold-result`, etc. Dividing through the nonzero `GD²·LD·AD` and reading
`D(gnum/gden) = GP/GD²` (quotient rule) and `LN/LD = logResidueSumG` (the fold bridge), this is exactly the
field identity `D(gnum/gden) + logResidueSumG = anum/aden`. The carrier-generic mirror of
`field_identity_of_checkIdentity`; the gcd never enters. -/

/-- **`checkIdentityG = true ⟹ field identity`** (the engine ⟹ field bridge, the carrier-generic mirror of
`field_identity_of_checkIdentity`): if the generic cleared antiderivative check
`checkIdentityG Dt res anum aden = true` holds, with the denominators `gden = res.rational.2`, `aden`
nonzero and every log argument `vᵢ` nonzero, then the field-level antiderivative identity
`towerFractionFieldDerivG Dt (amG gnum / amG gden) + logResidueSumG Dt res.logs = amG anum / amG aden`
holds over `RatFunc (CFieldSpec.K α)`. Runs the forward clearing backwards: `cisZeroG_iff` turns the check
into the cleared polynomial identity, the injective `amG` lifts it, and dividing by the nonzero `GD²·LD·AD`
with `GP/GD² = D(g)` and `LN/LD = logResidueSumG` recovers the field identity. The generic engine's
`D(∫f) = f`, in field form, gated only on `checkIdentityG = true`. -/
theorem field_identity_of_checkIdentityG (Dt : CPolyG α) (res : IntegralResultG α)
    (anum aden : CPolyG α)
    (hgden : toPolyG res.rational.2 ≠ 0) (haden : toPolyG aden ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0)
    (hcheck : CPolyG.checkIdentityG Dt res anum aden = true) :
    towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPolyG anum) / amG α (toPolyG aden) := by
  -- names matching `checkIdentityG`
  set gnum := res.rational.1 with hgnum
  set gden := res.rational.2 with hgdenE
  set gprimeNum := csubG (cmulG (cmonomialDeriv Dt gnum) gden) (cmulG gnum (cmonomialDeriv Dt gden))
    with hgp
  set gden2 := cmulG gden gden with hgden2
  -- the fold result `(Lnum, Lden)`
  set folded := res.logs.foldl
    (fun (acc : CPolyG α × CPolyG α) (cv : α × CPolyG α) =>
      let c := cv.1
      let v := cv.2
      let Dv := cmonomialDeriv Dt v
      let termNum := cscaleG c Dv
      (caddG (cmulG acc.1 v) (cmulG termNum acc.2), cmulG acc.2 v))
    ([CField.zero], [CField.one]) with hfolded
  -- the fold computes `logResidueSumG` over the field, with nonzero `Lden`
  have hseedden : toPolyG ([CField.one] : CPolyG α) ≠ 0 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero]; exact one_ne_zero
  obtain ⟨hLden_ne, hLfield⟩ := checkIdentityG_fold_eq Dt res.logs [CField.zero] [CField.one]
    hseedden hlogs
  rw [← hfolded] at hLden_ne hLfield
  -- the seed fraction `0/1 = 0`
  have hseed0 : amG α (toPolyG ([CField.zero] : CPolyG α))
      / amG α (toPolyG ([CField.one] : CPolyG α)) = 0 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_zero, map_zero, mul_zero, add_zero, map_zero,
      zero_div]
  rw [hseed0, zero_add] at hLfield
  -- abbreviations over the field
  set GP := amG α (toPolyG gprimeNum) with hGP
  set LN := amG α (toPolyG folded.1) with hLN
  set LD := amG α (toPolyG folded.2) with hLD
  set AN := amG α (toPolyG anum) with hAN
  set AD := amG α (toPolyG aden) with hAD
  set GD := amG α (toPolyG gden) with hGD
  -- nonzero readings
  have hGDne : GD ≠ 0 := by rw [hGD]; exact amG_toPolyG_ne_zero hgden
  have hLDne : LD ≠ 0 := by rw [hLD]; exact amG_toPolyG_ne_zero hLden_ne
  have hADne : AD ≠ 0 := by rw [hAD]; exact amG_toPolyG_ne_zero haden
  -- `D(gnum/gden) = GP/GD²` (quotient rule); `logResidueSumG = LN/LD` (fold bridge)
  have hquot : towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden))
      = GP / GD ^ 2 := by
    rw [towerFractionFieldDerivG_div, hGP, hgp, toPolyG_csubG, toPolyG_cmulG, toPolyG_cmulG,
      toPolyG_cmonomialDeriv, toPolyG_cmonomialDeriv, map_sub, map_mul, map_mul, hGD]
  have hLfield' : logResidueSumG Dt res.logs = LN / LD := by rw [← hLfield, hLN, hLD]
  -- ── the converse direction: extract the cleared polynomial identity from `checkIdentityG = true` ──
  rw [CPolyG.checkIdentityG] at hcheck
  simp only [← hgnum, ← hgdenE, ← hgp, ← hgden2, ← hfolded] at hcheck
  rw [cisZeroG_iff, toPolyG_csubG, sub_eq_zero, toPolyG_cmulG, toPolyG_cmulG, toPolyG_caddG,
    toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG] at hcheck
  -- lift the cleared polynomial equation into the tower fraction field (amG injective)
  rw [← (RatFunc.algebraMap_injective (CFieldSpec.K α)).eq_iff] at hcheck
  simp only [map_mul, map_add, hgden2, toPolyG_cmulG] at hcheck
  -- now `hcheck` is the cleared field equation `(GP·LD + LN·GD²)·AD = AN·(GD²·LD)` (over the field)
  rw [← hGP, ← hLN, ← hLD, ← hAN, ← hAD, ← hGD] at hcheck
  -- divide through the nonzero `GD²·LD·AD` to land the field fraction identity `GP/GD² + LN/LD = AN/AD`
  have hfield : GP / GD ^ 2 + LN / LD = AN / AD := by
    rw [div_add_div _ _ (pow_ne_zero 2 hGDne) hLDne,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hGDne) hLDne) hADne]
    ring_nf
    ring_nf at hcheck
    linear_combination hcheck
  -- assemble: rewrite the field readings back into the goal
  rw [hquot, hLfield', hfield]

/-! ### Axiom audit (the bridge rests only on the standard kernel axioms) -/

#print axioms logResidueSumG
#print axioms checkIdentityG_fold_eq
#print axioms field_identity_of_checkIdentityG

end DeepWiki.SymbolicIntegration
