import DeepWiki.SymbolicIntegration.AlgebraicCompleteness.Frontier
import DeepWiki.SymbolicIntegration.LiouvilleStructure

/-! # Algebraic Liouville frontier bridge

Bridge from weak-Liouville descent to the algebraic-completeness frontier predicates.
-/

open scoped Differential
open Polynomial Differential

namespace DeepWiki.SymbolicIntegration.LiouvilleStructure

/-! ## `AlgebraicLiouvilleFrontier` over `HasWeakLiouvilleForm` -/

section DischargeFrontier

variable (F : Type*) [Field F] [Differential F]

/-- `AlgebraicLiouvilleFrontier` (as-stated form, over `HasWeakLiouvilleForm`): for every Liouville
extension `K / F`, base non-elementarity propagates up. -/
theorem algebraicLiouvilleFrontier_form :
    ∀ (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K] [IsLiouville F K]
      (f : F), ¬ HasWeakLiouvilleForm F F f → ¬ HasWeakLiouvilleForm F K f := by
  intro K _ _ _ _ _ f h
  exact weakLiouville_propagates F K f h

end DischargeFrontier

section DischargeFrontierAlgebraic

variable (F : Type*) [Field F] [Differential F] [CharZero F]

/-- `AlgebraicLiouvilleFrontier` for the finite-dimensional case, with `[IsLiouville F K]` dropped:
for every finite-dimensional `K / F` (char 0), base non-elementarity propagates up. -/
theorem algebraicLiouvilleFrontier_finiteDimensional
    (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K]
    [FiniteDimensional F K] (f : F) (h : ¬ HasWeakLiouvilleForm F F f) :
    ¬ HasWeakLiouvilleForm F K f := by
  haveI : IsLiouville F K := isLiouville_of_finiteDimensional
  exact weakLiouville_propagates F K f h

end DischargeFrontierAlgebraic

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

-- Finite-dimensional extensions preserve non-elementarity in the Weak Liouville form.
example (F : Type*) [Field F] [Differential F] [CharZero F]
    (K : Type) [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K]
    [FiniteDimensional F K] (f : F) (h : ¬ HasWeakLiouvilleForm F F f) :
    ¬ HasWeakLiouvilleForm F K f :=
  algebraicLiouvilleFrontier_finiteDimensional F K f h

end Restatements

#print axioms algebraicLiouvilleFrontier_form
#print axioms algebraicLiouvilleFrontier_finiteDimensional
#print axioms algebraicLiouvilleFrontier_proved
#print axioms isAlgebraicElementary_finiteDimensional_discharge

end DeepWiki.SymbolicIntegration.LiouvilleStructure
