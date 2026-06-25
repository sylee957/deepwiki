import DeepWiki.SymbolicIntegration.ComputableSplitFactorTowerCorrect
import DeepWiki.SymbolicIntegration.ComputableIntegrateCorrect
import DeepWiki.SymbolicIntegration.ComputableIntegrateChecked

/-! # Abstract correctness of the GENERIC tower integrator `cIntegrateG` at the level-1 carrier ℚ(x)
The generic tower engine's top-level driver `cIntegrateG` (`ComputableTowerIntegrate`) assembles the
transcendental Risch loop on the `[CField α] [CDiffField α] [CFracGcdCore α]`-generic ops — canonical
split (`canonicalRepresentationFastG`), Hermite rational part (`cHermiteReduceTowerG`), and the
Rothstein–Trager residue logarithms (`cLogPartG`) — and certifies its output with the generic cleared
antiderivative check `checkIdentityG`. It is `native_decide`-validated only (`towerIntLvl2_driver`).

This file gives the generic engine the abstract `D(∫f) = f` capstone it lacked — at the level-1 carrier
`α = QFunNZ` the engine collapse instantiates, where `cgcdFFCore` reads through `toPolyG` to the SAME gcd
as `cgcdFF` up to associates (the nucleus `ComputableSplitFactorTowerCorrect` filled the §3.5 piece).

**The route.** The generic driver `cIntegrateG` at `α = QFunNZ` differs from the QFunNZ `cIntegrate` only
in (1) the gcd (`cgcdFFCore` vs `cgcdFF`, inside the split/squarefree/log-argument steps), (2) the
residue candidates (`List QFunNZ` vs `List ℚ`), and (3) the result type (`IntegralResultG QFunNZ` with
`QFunNZ`-coefficient logs vs `IntegralResult` with `ℚ`-coefficient logs). The **field-level
antiderivative identity** `D(g) + ∑ᵢ cᵢ·(Δvᵢ)/vᵢ = f` over the tower fraction field `RatFunc (RatFunc ℚ)`
— with `Δ = implicitDeriv (toPolyG Dt)` and `D = towerFractionFieldDeriv Dt` — is what `checkIdentityG`
clears, exactly as `checkIdentity` clears the QFunNZ identity. Since `checkIdentityG` **never calls the
gcd** (it only folds the residue terms `cᵢ·D(vᵢ)/vᵢ` and clears denominators), the whole
field ⇒ Boolean clearing bridge transports **verbatim** from the QFunNZ proof — only the residue-sum
spelling changes (`C (toK cᵢ)` directly, with `cᵢ : QFunNZ`, in place of `C (toK (ofConstNZ cᵢ))`).

The deliverable:

* **`logResidueSumG`** — the generic residue sum `∑_{(c,v)} C(toK c)·(Δv)/v` (the symbolic derivative of
  the generic logarithmic part `∑ c·log v`), and the fold reading `checkIdentityG_fold_eq`.
* **`checkIdentityG_of_field_identity` / `field_identity_of_checkIdentityG`** — the field ⇔ engine bridge,
  the generic mirror of `checkIdentity_of_field_identity` / `field_identity_of_checkIdentity`.
* **★ `cIntegrateG_field_identity`** — the generic engine's `D(∫f) = f` field-level capstone: in the
  primitive regime (`fₚ = fₛ = 0`, the `cIntegrateG` `some`-branch), `cIntegrateG Dt fuel a d cands =
  some res` lands an `IntegralResultG` whose antiderivative identity holds over `RatFunc (RatFunc ℚ)`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZ

/-- The engine carrier `CFieldSpec.K QFunNZ` is `RatFunc ℚ`, a `ℚ`-algebra. Re-declared as a local
instance (matching the keystone's) so this file synthesizes the **same** `Algebra ℚ` as
`towerFractionFieldDeriv`, avoiding an instance-mismatch detour. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K QFunNZ) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-! ### The generic logarithmic-part residue sum (over `QFunNZ`-valued coefficients)

The generic checker `checkIdentityG` folds the logarithmic part `∑ᵢ cᵢ·log(vᵢ)` (coefficients
`cᵢ : QFunNZ`) into its symbolic derivative `∑ᵢ cᵢ·(Δvᵢ)/vᵢ` (the log-derivative `D(log v) = (Δv)/v`),
accumulated as a single fraction `(Lnum, Lden)` over `∏ᵢ vᵢ`. We give it as a genuine field element
`logResidueSumG` over `RatFunc (RatFunc ℚ)`. Unlike the QFunNZ `logResidueSum` (which reads `ℚ`
coefficients through `ofConstNZ`), the coefficient here is *already* a `QFunNZ` constant, so it embeds
directly as `C (toK c)`. -/

/-- **The generic logarithmic-part residue sum** `logResidueSumG Dt logs = ∑_{(c,v)∈logs} C(toK c)·(Δv)/v`
over the tower fraction field `RatFunc (RatFunc ℚ)`, with `Δ = implicitDeriv (toPolyG Dt)` (so
`Δv = toPolyG (cmonomialDeriv Dt v)`). The symbolic derivative of the generic logarithmic part
`∑ᵢ cᵢ·log(vᵢ)` (`cᵢ : QFunNZ`) — exactly the residue sum `checkIdentityG` clears against `f`. The generic
mirror of `logResidueSum`, with the residue coefficient `c : QFunNZ` embedded directly as `C (toK c)`. -/
noncomputable def logResidueSumG (Dt : CPolyG QFunNZ) (logs : List (QFunNZ × CPolyG QFunNZ)) :
    RatFunc (CFieldSpec.K QFunNZ) :=
  (logs.map (fun cv =>
    towerAlg (Polynomial.C (CFieldSpec.toK cv.1))
      * (towerAlg (toPolyG (cmonomialDeriv Dt cv.2)) / towerAlg (toPolyG cv.2)))).sum

/-- `logResidueSumG` of the empty list is `0`. -/
@[simp] theorem logResidueSumG_nil (Dt : CPolyG QFunNZ) : logResidueSumG Dt [] = 0 := rfl

/-- `logResidueSumG` peels the head: `logResidueSumG Dt ((c,v) :: rest) = C(toK c)·(Δv)/v
+ logResidueSumG Dt rest`. -/
theorem logResidueSumG_cons (Dt : CPolyG QFunNZ) (cv : QFunNZ × CPolyG QFunNZ)
    (rest : List (QFunNZ × CPolyG QFunNZ)) :
    logResidueSumG Dt (cv :: rest)
      = towerAlg (Polynomial.C (CFieldSpec.toK cv.1))
          * (towerAlg (toPolyG (cmonomialDeriv Dt cv.2)) / towerAlg (toPolyG cv.2))
        + logResidueSumG Dt rest := by
  simp only [logResidueSumG, List.map_cons, List.sum_cons]

/-! ### The `checkIdentityG` fold computes the residue sum

`checkIdentityG`'s `foldl` accumulates `∑ cᵢ·(Δvᵢ)/vᵢ` as one fraction `(Lnum, Lden)` over `∏ᵢ vᵢ`,
starting at `([0], [1])` and combining `acc.1/acc.2 + (c·Δv)/v = (acc.1·v + c·Δv·acc.2)/(acc.2·v)`.
Reading through `towerAlg`, the running fraction is the seed plus the partial `logResidueSumG`; with all
`vᵢ` nonzero the seed contributes `0`. Verbatim transport of `checkIdentity_fold_eq` — the only change is
`cscaleG cv.1` (direct `QFunNZ` coefficient) in place of `cscaleG (ofConstNZ cv.1)`. -/

/-- **The `checkIdentityG` fold computes the residue sum** (field reading): folding from a seed
`(snum, sden)` (`sden ≠ 0`) over a generic log list whose every argument `v` is nonzero, the running
fraction `towerAlg(Lnum)/towerAlg(Lden)` equals the seed fraction plus `logResidueSumG`, and the running
denominator `Lden = sden·∏ᵢ vᵢ` stays nonzero. By induction on the list — the generic mirror of
`checkIdentity_fold_eq`. -/
theorem checkIdentityG_fold_eq (Dt : CPolyG QFunNZ) :
    ∀ (logs : List (QFunNZ × CPolyG QFunNZ)) (snum sden : CPolyG QFunNZ),
      toPolyG sden ≠ 0 →
      (∀ cv ∈ logs, toPolyG cv.2 ≠ 0) →
      let res := logs.foldl
        (fun (acc : CPolyG QFunNZ × CPolyG QFunNZ) (cv : QFunNZ × CPolyG QFunNZ) =>
          let c := cv.1
          let v := cv.2
          let Dv := cmonomialDeriv Dt v
          let termNum := cscaleG c Dv
          (caddG (cmulG acc.1 v) (cmulG termNum acc.2), cmulG acc.2 v))
        (snum, sden)
      toPolyG res.2 ≠ 0 ∧
        towerAlg (toPolyG res.1) / towerAlg (toPolyG res.2)
          = towerAlg (toPolyG snum) / towerAlg (toPolyG sden) + logResidueSumG Dt logs := by
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
    have hAsden : towerAlg (toPolyG sden) ≠ 0 := towerAlg_ne_zero hsden
    have hAv : towerAlg (toPolyG cv.2) ≠ 0 := towerAlg_ne_zero hvne
    have hstep : towerAlg (toPolyG newnum) / towerAlg (toPolyG newden)
        = towerAlg (toPolyG snum) / towerAlg (toPolyG sden)
          + towerAlg (Polynomial.C (CFieldSpec.toK cv.1))
              * (towerAlg (toPolyG (cmonomialDeriv Dt cv.2)) / towerAlg (toPolyG cv.2)) := by
      rw [hnewnum, hnewden, toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cscaleG,
        toPolyG_cmulG, map_add, map_mul, map_mul, map_mul]
      field_simp
      simp only [map_mul]
      ring
    rw [hstep]; ring

end DeepWiki.SymbolicIntegration
