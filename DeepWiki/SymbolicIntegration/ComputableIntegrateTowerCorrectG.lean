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

end DeepWiki.SymbolicIntegration
