import DeepWiki.SymbolicIntegration.Engine.PolyPartTowerComplete

/-! # Tangent polynomial-reduction domain

The tangent monomial `η (t² + 1)` is nonlinear, so every canonical polynomial branch belongs to
the complete nonlinear tower-reduction domain independently of its representation.
-/

namespace DeepWiki.SymbolicIntegration

open Polynomial

universe u

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u, u} P]
  {α : Type u} [CField α] [CFieldSpec.{u, u} α] [CDiffField α] [CDiffFieldSpec.{u, u} α]

/-- The semantic tangent monomial condition `Dt = η (t² + 1)` with nonzero `η`. -/
def IsTangentMonomial (Dt : P α) : Prop :=
  ∃ η : CFieldSpec.K α,
    CPoly.toPoly Dt = Polynomial.C η * (1 + Polynomial.X ^ 2) ∧ η ≠ 0

omit [CDiffField α] [CDiffFieldSpec α] in
/-- A nonzero tangent monomial has represented degree two. -/
theorem IsTangentMonomial.cdeg_eq_two {Dt : P α} (h : IsTangentMonomial Dt) :
    CPolyEngine.cdeg Dt = 2 := by
  obtain ⟨η, hDt, hη⟩ := h
  have hbase : (1 + Polynomial.X ^ 2 : Polynomial (CFieldSpec.K α)) ≠ 0 := by
    simpa [add_comm] using
      (Polynomial.monic_X_pow_add_C (a := (1 : CFieldSpec.K α)) (by omega)).ne_zero
  rw [LawfulCPolyEngine.cdeg_eq_natDegree, hDt,
    Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr hη) hbase]
  simp [Polynomial.natDegree_add_eq_right_of_natDegree_lt]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Every polynomial is in the nonlinear reduction domain of a tangent monomial. -/
theorem IsTangentMonomial.nonlinearPolynomialReductionDomain {Dt p : P α}
    (h : IsTangentMonomial Dt) :
    DensePoly.nonlinearPolynomialReductionDomain .nonlinear Dt p :=
  ⟨rfl, by rw [h.cdeg_eq_two]⟩

/-- The nonlinear tower reduction has a normal-form result for every tangent polynomial branch. -/
theorem IsTangentMonomial.nonlinearReduction_exists [CharZero (CFieldSpec.K α)]
    {Dt p : P α} (h : IsTangentMonomial Dt) :
    ∃ out : PolynomialReductionResult P α,
      IsPolynomialReduction .nonlinear Dt p out := by
  obtain ⟨out, _hrun, hout⟩ := DensePoly.towerPolynomialReduction_nonlinear_runs Dt
    p (by rw [h.cdeg_eq_two])
  exact ⟨out, hout⟩

end DeepWiki.SymbolicIntegration
