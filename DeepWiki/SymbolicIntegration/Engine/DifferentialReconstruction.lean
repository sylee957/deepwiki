import DeepWiki.SymbolicIntegration.Engine.DifferentialAssembly

/-! # Explicit-differential logarithmic reconstruction

Algebraic reconstruction lemmas for the selected monomial differential.  They combine certified
polynomial-special and normal branches into one rational-plus-logarithmic result without using a
global coefficient derivative.
-/

namespace DeepWiki.SymbolicIntegration

open CFrac Polynomial DynamicPolynomialReduction

universe u

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,u} P]
variable {α : Type u} [CField α] [CFieldSpec.{u,u} α]

omit [LawfulCPolyEngine P] in
/-- Explicit logarithmic residue sums respect list concatenation. -/
theorem differentialLogResidueSum_append
    (C : MonomialDifferentialContext (P := P) α) (Dt : P α)
    (left right : List (α × P α)) :
    differentialLogResidueSum C Dt (left ++ right) =
      differentialLogResidueSum C Dt left + differentialLogResidueSum C Dt right := by
  simp only [differentialLogResidueSum, List.map_append, List.sum_append]

omit [LawfulCPolyEngine P] in
/-- An explicit polynomial-reduction certificate yields its rational antiderivative identity. -/
theorem differentialPolynomialReduction_antiderivative_sound
    (C : MonomialDifferentialContext (P := P) α) (kind : PolynomialReductionKind) (Dt p q r : P α)
    (hreduce : IsDifferentialPolynomialReduction (P := P) (α := α)
      C.differential kind Dt p ⟨q, r⟩) :
    C.fractionDeriv Dt (fieldFracP q CPoly.one) =
      fieldFracP p CPoly.one - fieldFracP r CPoly.one := by
  simp only [fieldFracP, CPoly.toPoly_one, map_one, div_one]
  rw [MonomialDifferentialContext.fractionDeriv_algebraMap]
  have hmap := congrArg (am α) hreduce.1
  rw [map_add] at hmap
  exact eq_sub_iff_add_eq.mpr hmap.symm

/-- Adding a rational term to an explicit integral result adds their selected differential values. -/
theorem differentialCombineSN_value
    (C : MonomialDifferentialContext (P := P) α) (Dt snum sden : P α) (nrm : IntegralResult α P)
    (rationalVal normalVal : RatFunc (CFieldSpec.K α))
    (hsden : CPoly.toPoly sden ≠ 0) (hnrmDen : CPoly.toPoly nrm.rational.2 ≠ 0)
    (hrational : C.fractionDeriv Dt (fieldFracP snum sden) = rationalVal)
    (hnormal : C.fractionDeriv Dt (fieldFracP nrm.rational.1 nrm.rational.2) +
      differentialLogResidueSum C Dt nrm.logs = normalVal) :
    C.fractionDeriv Dt
        (fieldFracP (combineSN snum sden nrm).rational.1 (combineSN snum sden nrm).rational.2) +
      differentialLogResidueSum C Dt (combineSN snum sden nrm).logs = rationalVal + normalVal := by
  have hAsden : am α (CPoly.toPoly sden) ≠ 0 := am_ne_zero hsden
  have hAnrmDen : am α (CPoly.toPoly nrm.rational.2) ≠ 0 := am_ne_zero hnrmDen
  have hcombine : fieldFracP
      (CPolyEngine.add (CPolyEngine.mul snum nrm.rational.2)
        (CPolyEngine.mul nrm.rational.1 sden))
      (CPolyEngine.mul sden nrm.rational.2) =
      fieldFracP snum sden + fieldFracP nrm.rational.1 nrm.rational.2 := by
    simp only [fieldFracP, LawfulCPolyEngine.toPoly_add, LawfulCPolyEngine.toPoly_mul,
      map_add, map_mul]
    field_simp
  simp only [combineSN, combineRationalParts]
  rw [hcombine, map_add, hrational]
  linear_combination hnormal

/-- Two explicit certified partial results combine into their reconstructed fraction identity. -/
theorem differentialCombineIntegralResults
    (C : MonomialDifferentialContext (P := P) α) (Dt a d cn dn : P α)
    (left right : IntegralResult α P) (leftVal : RatFunc (CFieldSpec.K α))
    (hleftDen : CPoly.toPoly left.rational.2 ≠ 0)
    (hrightDen : CPoly.toPoly right.rational.2 ≠ 0)
    (hleft : C.fractionDeriv Dt (fieldFracP left.rational.1 left.rational.2) +
      differentialLogResidueSum C Dt left.logs = leftVal)
    (hright : IsDifferentialIntegralResultP C Dt cn dn right)
    (hrecon : leftVal + fieldFracP cn dn = fieldFracP a d) :
    IsDifferentialIntegralResultP C Dt a d (combineIntegralResults left right) := by
  have hAleft : am α (CPoly.toPoly left.rational.2) ≠ 0 := am_ne_zero hleftDen
  have hAright : am α (CPoly.toPoly right.rational.2) ≠ 0 := am_ne_zero hrightDen
  have hcombine : fieldFracP
      (CPolyEngine.add (CPolyEngine.mul left.rational.1 right.rational.2)
        (CPolyEngine.mul right.rational.1 left.rational.2))
      (CPolyEngine.mul left.rational.2 right.rational.2) =
      fieldFracP left.rational.1 left.rational.2 + fieldFracP right.rational.1 right.rational.2 := by
    simp only [fieldFracP, LawfulCPolyEngine.toPoly_add, LawfulCPolyEngine.toPoly_mul,
      map_add, map_mul]
    field_simp
  change C.fractionDeriv Dt
      (fieldFracP
        (CPolyEngine.add (CPolyEngine.mul left.rational.1 right.rational.2)
          (CPolyEngine.mul right.rational.1 left.rational.2))
        (CPolyEngine.mul left.rational.2 right.rational.2)) +
      differentialLogResidueSum C Dt (left.logs ++ right.logs) = fieldFracP a d
  rw [hcombine, map_add, differentialLogResidueSum_append]
  calc
    (C.fractionDeriv Dt (fieldFracP left.rational.1 left.rational.2) +
          C.fractionDeriv Dt (fieldFracP right.rational.1 right.rational.2)) +
        (differentialLogResidueSum C Dt left.logs + differentialLogResidueSum C Dt right.logs) =
        (C.fractionDeriv Dt (fieldFracP left.rational.1 left.rational.2) +
          differentialLogResidueSum C Dt left.logs) +
          (C.fractionDeriv Dt (fieldFracP right.rational.1 right.rational.2) +
            differentialLogResidueSum C Dt right.logs) := by ring
    _ = leftVal + fieldFracP cn dn := by rw [hleft, hright]
    _ = fieldFracP a d := hrecon

end DeepWiki.SymbolicIntegration
