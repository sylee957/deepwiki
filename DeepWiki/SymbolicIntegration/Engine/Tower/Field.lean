import DeepWiki.ComputableAlgebra.FractionField
import DeepWiki.SymbolicIntegration.Engine.ConcreteCoherence
import DeepWiki.SymbolicIntegration.Engine.FuelFreeResultant

/-! # Fraction-field tower examples: concrete-`Compute` coherence and level-2 `native_decide`
The generic fraction field `QFunNZ` lives in `ComputableAlgebra.FractionField`; this file exercises it:
the `α = ℚ` coherence with the concrete `Compute.*` engine, and the `Lvl2 = QFunNZ (QFunNZ ℚ)` tower
computing end to end (`cmul`/`cgcdWf`/`cresultantWf`) under `native_decide`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### Tower level 1: `QFunNZ ℚ ≅ ℚ(x)` and its coherence with the concrete `Compute.*` engine -/

/-- The underlying pair type of `QFun ℚ` is the concrete `Compute.QFun` (both `List ℚ × List ℚ`). -/
example : QFun ℚ = Compute.QFun := rfl

/-- Generic-to-concrete coherence at `α = ℚ`: `toPoly (α := ℚ) = toPoly` pointwise. -/
example (d : CPoly ℚ) : CPoly.toPoly d = Compute.toPoly d :=
  congrFun CPoly.toPolyG_eq_toPoly d

/-! ### The tower computes at level 2 (`ℚ(x)(t₁)[t₂]`) (`native_decide`) -/

/-- Tower level 2: `Lvl2 = QFunNZ (QFunNZ ℚ)`, the field ℚ(x)(t₁); `CPoly Lvl2 = ℚ(x)(t₁)[t₂]`. -/
abbrev Lvl2 : Type := QFunNZ (QFunNZ ℚ)

/-- `1 + 1 ≠ 0` in `Lvl2 = ℚ(x)(t₁)`: the level-2 scalar `add`/`isZero` reduce. -/
example : CField.isZero (CField.add (CField.one : Lvl2) CField.one) = false := by native_decide

/-- `0 = 0` at level 2: the level-2 scalar zero test reduces. -/
example : CField.isZero (CField.zero : Lvl2) = true := by native_decide

/-- `1 ≠ 0` at level 2. -/
example : CField.isZero (CField.one : Lvl2) = false := by native_decide

/-- `(1 + t₂)·(1 + t₂)` over `CPoly Lvl2` is a length-3 normalized list: `cmul` reduces at level 2. -/
example :
    (CPoly.cnorm (CPoly.cmul [(CField.one : Lvl2), CField.one] [CField.one, CField.one])
      : List Lvl2).length = 3 := by native_decide

/-- The product is nonzero over `CPoly Lvl2`: `cisZero` reduces at level 2. -/
example :
    CPoly.cisZero (CPoly.cmul [(CField.one : Lvl2), CField.one] [CField.one, CField.one])
      = false := by native_decide

/-- `gcd(t₂, t₂) = t₂` is nonzero over `CPoly Lvl2`: `cgcdWf` reduces end to end at level 2. -/
example :
    CPoly.cisZero (CPoly.cgcdWf [(CField.zero : Lvl2), CField.one]
      [(CField.zero : Lvl2), CField.one]).1 = false := by native_decide

/-- `res(t₂, 1 + t₂) = 1` over `CPoly Lvl2`: `cresultantWf` reduces end to end at level 2. -/
example :
    CField.isZero
      (CPoly.cresultantWf [(CField.zero : Lvl2), CField.one] [CField.one, CField.one]) = false := by
  native_decide

/-- `1 + (t₁)⁻¹ ≠ 0` at level 2: the `add`/`isZero` engine reduces on a non-trivial `Lvl2` fraction. -/
example :
    CField.isZero
      (CField.add (CField.one : Lvl2)
        (CField.inv ⟨([(CField.zero : QFunNZ ℚ), CField.one], [CField.one]),
          QFunNZ.cisZeroG_one_singleton⟩))
      = false := by native_decide

