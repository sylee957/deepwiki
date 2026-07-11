import DeepWiki.ComputableAlgebra.PolyEngine

/-! # Representation-independent polynomial antiderivatives

Termwise polynomial antiderivation over any `CPoly` representation, with its denotation law and
dense/sparse execution witnesses. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

namespace CPoly

variable {P : Type u → Type u} [CPoly P]
variable {α : Type u} [CField α]

/-- Termwise polynomial antiderivative with zero constant coefficient. -/
def antiderivative (p : P α) : P α :=
  ofFn (degBound p + 1) fun
    | 0 => CCommRing.zero
    | i + 1 => CField.div (coeff p i) (CField.natCast (i + 1))

/-- The selected antiderivative has zero constant coefficient. -/
@[simp] theorem coeff_antiderivative_zero (p : P α) :
    coeff (antiderivative p) 0 = CCommRing.zero := by
  rw [antiderivative, coeff_ofFn, if_pos (by omega)]

variable [CFieldSpec.{u,v} α]

/-- The selected antiderivative denotes a polynomial with zero constant coefficient. -/
@[simp] theorem coeff_toPoly_antiderivative_zero (p : P α) :
    (toPoly (antiderivative p)).coeff 0 = 0 := by
  rw [coeff_toPoly, coeff_antiderivative_zero, CRingSpec.toR_zero]

/-- Formal differentiation cancels the selected termwise antiderivative in characteristic zero. -/
@[denote] theorem derivative_toPoly_antiderivative [CharZero (CFieldSpec.K α)] (p : P α) :
    (toPoly (antiderivative p)).derivative = toPoly p := by
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_derivative, coeff_toPoly, coeff_toPoly]
  simp only [toR_eq_toK]
  by_cases hi : i < degBound p
  · rw [antiderivative, coeff_ofFn, if_pos (by omega)]
    have hsucc : i + 1 = Nat.succ i := by omega
    rw [hsucc]
    simp only
    change CFieldSpec.toK (CField.div (coeff p i) (CField.natCast (i + 1))) *
        ((i : CFieldSpec.K α) + 1) = CFieldSpec.toK (coeff p i)
    rw [CFieldSpec.toK_div, CFieldSpec.toK_natCast]
    have hcast : ((i + 1 : ℕ) : CFieldSpec.K α) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero i
    push_cast
    field_simp
  · have hle : degBound p ≤ i := Nat.le_of_not_gt hi
    rw [antiderivative, coeff_ofFn, if_neg (by omega), CFieldSpec.toK_zero,
      zero_mul, coeff_ge p i hle, CFieldSpec.toK_zero]

end CPoly

namespace DensePoly

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α]

/-- Dense denotation reads the selected antiderivative with zero constant coefficient. -/
@[simp] theorem coeff_toPoly_antiderivative_zero (p : DensePoly α) :
    (toPoly (CPoly.antiderivative p)).coeff 0 = 0 := by
  rw [← toPoly_list_eq]
  exact CPoly.coeff_toPoly_antiderivative_zero p

/-- Dense denotation inherits the representation-independent antiderivative law. -/
@[denote] theorem derivative_toPoly_antiderivative [CharZero (CFieldSpec.K α)] (p : DensePoly α) :
    (toPoly (CPoly.antiderivative p)).derivative = toPoly p := by
  rw [← toPoly_list_eq, ← toPoly_list_eq]
  exact CPoly.derivative_toPoly_antiderivative p

end DensePoly

/-! ### Representation-independence validation -/

/-- Dense antiderivation returns the expected low-to-high coefficient list. -/
example : CPoly.antiderivative ([2, 6] : DensePoly ℚ) = [0, 2, 3] := by
  ccompute

/-- Sparse antiderivation executes through the same representation-independent definition. -/
example :
    CPoly.antiderivative (CPoly.SparsePoly.ofList [(0, 2), (1, 6)] : CPoly.SparsePoly ℚ) =
      CPoly.SparsePoly.ofList [(0, 0), (1, 2), (2, 3)] := by
  ccompute

end DeepWiki.SymbolicIntegration
