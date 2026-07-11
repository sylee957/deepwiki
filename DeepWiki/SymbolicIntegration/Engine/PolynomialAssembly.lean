import DeepWiki.SymbolicIntegration.Engine.Assemble
import DeepWiki.SymbolicIntegration.Engine.PolyPartTower

/-! # Polynomial-reduction stage in one-level Risch assembly

This module inserts the representation-neutral polynomial-reduction capability between canonical
representation and monomial-case special integration. Its soundness theorem uses only stage contracts. -/

namespace DeepWiki.SymbolicIntegration

open CFrac Polynomial

universe u

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,u} P]
variable {α : Type u} [CField α] [CFieldSpec.{u,u} α] [CDiffField α] [CDiffFieldSpec.{u,u} α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Add a polynomial antiderivative to a represented special fraction's numerator. -/
def polynomialSpecialNumerator (q snum sden : P α) : P α :=
  CPolyEngine.add (CPolyEngine.mul q sden) snum

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The represented fraction built by `polynomialSpecialNumerator` is `q + snum / sden`. -/
theorem fieldFracP_polynomialSpecialNumerator (q snum sden : P α)
    (hsden : CPoly.toPoly sden ≠ 0) :
    fieldFracP (polynomialSpecialNumerator q snum sden) sden =
      fieldFracP q CPoly.one + fieldFracP snum sden := by
  have hden : CFrac.am α (CPoly.toPoly sden) ≠ 0 := CFrac.am_ne_zero hsden
  have hnum : CFrac.am α (CPoly.toPoly (polynomialSpecialNumerator q snum sden)) =
      CFrac.am α (CPoly.toPoly q) * CFrac.am α (CPoly.toPoly sden) +
        CFrac.am α (CPoly.toPoly snum) := by
    rw [polynomialSpecialNumerator, LawfulCPolyEngine.toPoly_add,
      LawfulCPolyEngine.toPoly_mul, map_add, map_mul]
  rw [fieldFracP, fieldFracP, fieldFracP, CPoly.toPoly_one, map_one, div_one, hnum]
  field_simp [hden]

set_option linter.unusedSectionVars false in
/-- A polynomial-reduction reconstruction equation yields the corresponding polynomial derivative identity. -/
theorem polynomialReduction_antiderivative_sound (Dt p q r : P α)
    (hreduce : CPoly.toPoly p = Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly q)
      + CPoly.toPoly r) :
    towerFractionFieldDerivP Dt (fieldFracP q CPoly.one) =
      fieldFracP p CPoly.one - fieldFracP r CPoly.one := by
  simp only [fieldFracP, CPoly.toPoly_one, map_one, div_one]
  rw [towerFractionFieldDerivP, extendDeriv_algebraMap]
  change CFrac.am α (Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly q)) = _
  have hmap := congrArg (CFrac.am α) hreduce
  rw [map_add] at hmap
  exact eq_sub_iff_add_eq.mpr hmap.symm

/-- Execute a one-level Risch assembly with an explicit polynomial-reduction stage. -/
def assembleOneLevelWithPolynomial (R : CPolynomialReduction P α) (kind : PolynomialReductionKind)
    (fuel : ℕ) (C : CMonomialCase P α) [CCanonicalRepresentation P α]
    [CHermiteReduction P α] [CResidueSource P α] [CResidueLogPart P α]
    (Dt a d : P α) : Option (IntegralResult α P) := do
  let split := canonicalResult Dt a d
  let reduced ← R.reduce kind Dt fuel split.polynomial
  let (snum, sden) ← C.integrateSpecial Dt reduced.remainder split.specialNum split.specialDen
  let before ← reduceNormal Dt split.normalNum split.normalDen
  let normal ← C.postprocessNormal Dt before
  pure (combineSN (polynomialSpecialNumerator reduced.antiderivative snum sden) sden normal)

set_option maxHeartbeats 800000 in
/-- A successful polynomial-aware one-level assembly is an integral result of its input. -/
theorem assembleOneLevelWithPolynomial_sound (R : CPolynomialReduction P α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind) (fuel : ℕ)
    (C : CMonomialCase P α) [CCanonicalRepresentation P α]
    [LawfulCCanonicalRepresentation (P := P) (α := α)] [LawfulCMonomialCase C]
    [CHermiteReduction P α] [LawfulCHermiteReduction (P := P) (α := α)]
    [CResidueSource P α] [CResidueLogPart P α]
    [LawfulCResidueLogPart (P := P) (α := α)]
    (Dt a d : P α) (out : IntegralResult α P)
    (hd : CPoly.toPoly d ≠ 0) (hdegree : (CPoly.toPoly Dt).natDegree ≤ 1)
    (hrun : assembleOneLevelWithPolynomial R kind fuel C Dt a d = some out) :
    IsIntegralResultP Dt a d out := by
  cases hreduce : R.reduce kind Dt fuel (canonicalResult Dt a d).polynomial with
  | none => simp [assembleOneLevelWithPolynomial, hreduce] at hrun
  | some reduced =>
    cases hspecial : C.integrateSpecial Dt reduced.remainder
        (canonicalResult Dt a d).specialNum (canonicalResult Dt a d).specialDen with
    | none => simp [assembleOneLevelWithPolynomial, hreduce, hspecial] at hrun
    | some special =>
      obtain ⟨snum, sden⟩ := special
      cases hnormal : reduceNormal Dt (canonicalResult Dt a d).normalNum
          (canonicalResult Dt a d).normalDen with
      | none => simp [assembleOneLevelWithPolynomial, hreduce, hnormal] at hrun
      | some before =>
        cases hpost : C.postprocessNormal Dt before with
        | none => simp [assembleOneLevelWithPolynomial, hreduce, hnormal, hpost] at hrun
        | some normal =>
          have hout : combineSN (polynomialSpecialNumerator reduced.antiderivative snum sden)
              sden normal = out := by
            simpa [assembleOneLevelWithPolynomial, hreduce, hspecial, hnormal, hpost] using hrun
          subst out
          have hred := LawfulCPolynomialReduction.sound (C := R) kind Dt fuel
            (canonicalResult Dt a d).polynomial reduced hreduce
          have hq := polynomialReduction_antiderivative_sound Dt
            (canonicalResult Dt a d).polynomial reduced.antiderivative reduced.remainder hred
          obtain ⟨hsden, hspecialField⟩ := LawfulCMonomialCase.special_sound (C := C) Dt
            reduced.remainder (canonicalResult Dt a d).specialNum
            (canonicalResult Dt a d).specialDen snum sden hspecial
          have hpolySpecial := fieldFracP_polynomialSpecialNumerator reduced.antiderivative snum sden hsden
          have hspecialFull : towerFractionFieldDerivP Dt
              (fieldFracP (polynomialSpecialNumerator reduced.antiderivative snum sden) sden) =
              fieldFracP (canonicalResult Dt a d).polynomial CPoly.one +
                fieldFracP (canonicalResult Dt a d).specialNum
                  (canonicalResult Dt a d).specialDen := by
            rw [hpolySpecial, map_add, hq, hspecialField]
            ring
          have hnormalDen := LawfulCCanonicalRepresentation.normalDen_nonzero Dt a d hd
          have hnormalForm := LawfulCCanonicalRepresentation.normal_isNormalSqfree Dt a d hd
          have hnormalProper := LawfulCCanonicalRepresentation.normal_proper Dt a d hd
          have hbefore := reduceNormal_sound (P := P) (α := α) Dt
            (canonicalResult Dt a d).normalNum
            (canonicalResult Dt a d).normalDen before hnormalDen hnormalForm hnormalProper hdegree hnormal
          have hbeforeDen := reduceNormal_rationalDen_nonzero (P := P) (α := α) Dt
            (canonicalResult Dt a d).normalNum
            (canonicalResult Dt a d).normalDen before hnormalDen hnormalForm hnormal
          have hnormalResult := LawfulCMonomialCase.postprocessNormal_sound (C := C) Dt
            (canonicalResult Dt a d).normalNum (canonicalResult Dt a d).normalDen before normal hbefore hpost
          have hnormalResultDen := LawfulCMonomialCase.postprocessNormal_den_nonzero (C := C) Dt
            before normal hbeforeDen hpost
          have hcanonical := LawfulCCanonicalRepresentation.reconstruction Dt a d hd
          refine combineSN_isIntegralResultP Dt a d (canonicalResult Dt a d).normalNum
            (canonicalResult Dt a d).normalDen
            (polynomialSpecialNumerator reduced.antiderivative snum sden) sden normal
            (fieldFracP (canonicalResult Dt a d).polynomial CPoly.one +
              fieldFracP (canonicalResult Dt a d).specialNum
                (canonicalResult Dt a d).specialDen)
            hsden hnormalResultDen hspecialFull hnormalResult ?_
          simpa only [add_assoc] using hcanonical

end DeepWiki.SymbolicIntegration
