import DeepWiki.SymbolicIntegration.Core.Differential.FractionFieldDeriv
import DeepWiki.SymbolicIntegration.Computable.Tower.Field

/-! # Tower fraction-field derivations

Specializations of the generic `extendDeriv` API to computable tower carriers.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ### Specialization to the tower fraction field `RatFunc (RatFunc ℚ)`

Specializing `extendDeriv` to the base derivation `implicitDeriv (toPolyG Dt)` on `(RatFunc ℚ)[X]`
yields the tower fraction-field derivation on `RatFunc (RatFunc ℚ)`.
-/

open scoped Differential
open CPolyG

/-- The engine carrier `CFieldSpec.K (QFunNZG ℚ)` is `RatFunc ℚ`, a `ℚ`-algebra (needed for the
`ℚ`-route bundle). -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- The engine carrier `CFieldSpec.K (QFunNZG ℚ)` is `RatFunc ℚ`, a `Differential` ring under `d/dx`. -/
noncomputable local instance : Differential (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (Differential (RatFunc ℚ))

/-- The tower fraction-field derivation on `RatFunc (RatFunc ℚ)` for `Dt`:
`extendDeriv (implicitDeriv (toPolyG Dt))`. -/
noncomputable def towerFractionFieldDeriv (Dt : CPolyG (QFunNZG ℚ)) :
    Derivation ℤ (RatFunc (CFieldSpec.K (QFunNZG ℚ))) (RatFunc (CFieldSpec.K (QFunNZG ℚ))) :=
  extendDeriv (Differential.implicitDeriv (toPolyG Dt))

/-- The tower derivation extends the monomial derivation on `algebraMap (RatFunc ℚ)[X]` images. -/
theorem towerFractionFieldDeriv_algebraMap (Dt : CPolyG (QFunNZG ℚ)) (p : (CFieldSpec.K (QFunNZG ℚ))[X]) :
    towerFractionFieldDeriv Dt (algebraMap _ (RatFunc (CFieldSpec.K (QFunNZG ℚ))) p)
      = algebraMap _ (RatFunc (CFieldSpec.K (QFunNZG ℚ))) (Differential.implicitDeriv (toPolyG Dt) p) :=
  extendDeriv_algebraMap _ p

/-- Quotient rule for the tower derivation: `(mk p q) ↦ (Δp·q − p·Δq)/q²`, `Δ = implicitDeriv (toPolyG Dt)`. -/
theorem towerFractionFieldDeriv_mk (Dt : CPolyG (QFunNZG ℚ)) (p q : (CFieldSpec.K (QFunNZG ℚ))[X]) :
    towerFractionFieldDeriv Dt (RatFunc.mk p q)
      = RatFunc.mk (Differential.implicitDeriv (toPolyG Dt) p * q
          - p * Differential.implicitDeriv (toPolyG Dt) q) (q ^ 2) :=
  extendDeriv_mk _ p q

/-- The log-derivative of `g` under the tower derivation is `(Δg)/g`, `Δ = implicitDeriv (toPolyG Dt)`. -/
theorem towerFractionFieldDeriv_logDeriv (Dt : CPolyG (QFunNZG ℚ)) (g : (CFieldSpec.K (QFunNZG ℚ))[X]) :
    towerFractionFieldDeriv Dt (algebraMap _ (RatFunc (CFieldSpec.K (QFunNZG ℚ))) g)
        / algebraMap _ (RatFunc (CFieldSpec.K (QFunNZG ℚ))) g
      = RatFunc.mk (Differential.implicitDeriv (toPolyG Dt) g) g :=
  extendDeriv_logDeriv_mk _ g

/-- `RatFunc (RatFunc ℚ)` as a `Differential` ring under the tower derivation for `Dt`. -/
@[reducible]
noncomputable def towerFractionFieldDifferential (Dt : CPolyG (QFunNZG ℚ)) :
    Differential (RatFunc (CFieldSpec.K (QFunNZG ℚ))) :=
  fractionFieldDifferential (Differential.implicitDeriv (toPolyG Dt))

/-! ## Restatement examples -/

example (Dt : CPolyG (QFunNZG ℚ)) (p : (CFieldSpec.K (QFunNZG ℚ))[X]) :
    towerFractionFieldDeriv Dt (algebraMap _ (RatFunc (CFieldSpec.K (QFunNZG ℚ))) p)
      = algebraMap _ (RatFunc (CFieldSpec.K (QFunNZG ℚ))) (Differential.implicitDeriv (toPolyG Dt) p) :=
  towerFractionFieldDeriv_algebraMap Dt p


end DeepWiki.SymbolicIntegration
