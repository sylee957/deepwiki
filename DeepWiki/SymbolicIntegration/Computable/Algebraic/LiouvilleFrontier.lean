import DeepWiki.SymbolicIntegration.Computable.LiouvilleStructure

/-! # Algebraic Liouville frontier bridge

Bridge from weak-Liouville descent to the algebraic-completeness frontier predicates.
-/

open scoped Differential
open Polynomial Differential

namespace DeepWiki.SymbolicIntegration.LiouvilleStructure

/-! ## `AlgebraicLiouvilleFrontier` over `IsAlgebraicElementary` -/

section DischargeRealFrontier

open DeepWiki.SymbolicIntegration.AlgebraicCompleteness

variable (F : Type*) [Field F] [Differential F] [CharZero F]

omit [CharZero F] in
/-- `HasWeakLiouvilleForm F K g ↔ IsAlgebraicElementary F K g` (definitionally equal; `Iff.rfl`). -/
theorem hasWeakLiouvilleForm_iff_isAlgebraicElementary
    (K : Type*) [Field K] [Differential K] [Algebra F K] (g : F) :
    HasWeakLiouvilleForm F K g ↔ IsAlgebraicElementary F K g := Iff.rfl

omit [CharZero F] in
/-- `AlgebraicLiouvilleFrontier F` follows from the
`HasWeakLiouvilleForm ↔ IsAlgebraicElementary` bridge and Liouville descent. -/
theorem algebraicLiouvilleFrontier_proved : AlgebraicLiouvilleFrontier F := by
  intro K _ _ _ _ _ f h hK
  rw [← hasWeakLiouvilleForm_iff_isAlgebraicElementary] at hK
  rw [← hasWeakLiouvilleForm_iff_isAlgebraicElementary] at h
  exact weakLiouville_propagates F K f h hK

/-- The actual `AlgebraicLiouvilleFrontier` for the finite-dimensional case, `[IsLiouville F K]`
dropped: base non-elementarity propagates up every finite-dimensional `K / F`. -/
theorem isAlgebraicElementary_finiteDimensional_discharge
    (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K]
    [FiniteDimensional F K] (f : F) (h : ¬ IsAlgebraicElementary F F f) :
    ¬ IsAlgebraicElementary F K f := by
  rw [← hasWeakLiouvilleForm_iff_isAlgebraicElementary] at h ⊢
  exact algebraicLiouvilleFrontier_finiteDimensional F K f h

end DischargeRealFrontier

/-! ### Restatements and axiom audit -/

section Restatements

-- The algebraic-completeness frontier follows from Liouville descent.
example (F : Type*) [Field F] [Differential F] [CharZero F] :
    DeepWiki.SymbolicIntegration.AlgebraicCompleteness.AlgebraicLiouvilleFrontier F :=
  algebraicLiouvilleFrontier_proved F

end Restatements

#print axioms algebraicLiouvilleFrontier_proved
#print axioms isAlgebraicElementary_finiteDimensional_discharge

end DeepWiki.SymbolicIntegration.LiouvilleStructure
