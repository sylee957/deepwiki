import DeepWiki.SymbolicIntegration.Engine.Assemble
import DeepWiki.SymbolicIntegration.Engine.PolyPartTower

/-! # Contract-based one-level Risch assembly

This module composes canonical representation, polynomial reduction, normal reduction, and a
monomial-case solver. Its soundness and relative-completeness theorems use only stage contracts. -/

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

/-- Execute one-level Risch assembly from explicit polynomial- and normal-reduction operations. -/
def assembleOneLevel (R : CPolynomialReduction P α) (kind : PolynomialReductionKind)
    (N : CNormalReduction P α) (fuel : ℕ) (C : CMonomialCase P α)
    [CCanonicalRepresentation P α]
    (Dt a d : P α) : Option (IntegralResult α P) := do
  let split := canonicalResult Dt a d
  let reduced ← R.reduce kind Dt fuel split.polynomial
  let (snum, sden) ← C.integrateSpecial Dt reduced.remainder split.specialNum split.specialDen
  let before ← N.reduce Dt split.normalNum split.normalDen
  let normal ← C.postprocessNormal Dt before
  pure (combineSN (polynomialSpecialNumerator reduced.antiderivative snum sden) sden normal)

/-- Explicit stage-decomposed hypotheses under which contract-based one-level assembly is complete. -/
structure OneLevelAssemblyWitness (R : CPolynomialReduction P α)
    (kind : PolynomialReductionKind) (normalDomain : NormalReductionDomain P α)
    (Dt a d : P α) [CCanonicalRepresentation P α] : Prop where
  /-- The requested polynomial normal form exists. -/
  polynomial_reduction_exists :
    ∃ reduced, IsPolynomialReduction kind Dt (canonicalResult Dt a d).polynomial reduced
  /-- Every reduction selected by the executable stage leaves a solvable monomial special part. -/
  special_antiderivative : ∀ (fuel : ℕ) (reduced : PolynomialReductionResult P α),
    R.reduce kind Dt fuel (canonicalResult Dt a d).polynomial = some reduced →
      ∃ (snum sden : P α),
        CPoly.toPoly sden ≠ 0 ∧
        towerFractionFieldDerivP Dt (fieldFracP snum sden) =
          fieldFracP reduced.remainder CPoly.one +
            fieldFracP (canonicalResult Dt a d).specialNum
              (canonicalResult Dt a d).specialDen
  /-- The canonical normal branch lies in the selected normal reducer's semantic domain. -/
  normal_domain : normalDomain Dt (canonicalResult Dt a d).normalNum
    (canonicalResult Dt a d).normalDen
  /-- The canonical normal branch has a certified normal-form antiderivative. -/
  normal_integrable : IsNormalPartIntegrable Dt (canonicalResult Dt a d).normalNum
    (canonicalResult Dt a d).normalDen

omit [LawfulCPolyEngine P] in
/-- Complete stage contracts compose into eventual success of contract-based one-level assembly. -/
theorem assembleOneLevel_complete (R : CPolynomialReduction P α)
    [LawfulCPolynomialReduction R] [CompleteCPolynomialReduction R]
    (kind : PolynomialReductionKind) (N : CNormalReduction P α)
    (normalDomain : NormalReductionDomain P α)
    [LawfulCNormalReduction N normalDomain] [CompleteCNormalReduction N normalDomain]
    (C : CMonomialCase P α)
    [LawfulCMonomialCase C] [CompleteCMonomialCase C]
    [CCanonicalRepresentation P α]
    [LawfulCCanonicalRepresentation (P := P) (α := α)]
    (Dt a d : P α) (hd : CPoly.toPoly d ≠ 0)
    (hwitness : OneLevelAssemblyWitness R kind normalDomain Dt a d) :
    ∃ fuel out, assembleOneLevel R kind N fuel C Dt a d = some out := by
  obtain ⟨fuel, reduced, hreduce⟩ := CompleteCPolynomialReduction.relative_complete
    (C := R) kind Dt (canonicalResult Dt a d).polynomial
      hwitness.polynomial_reduction_exists
  obtain ⟨snum, sden, hsden, hspecialSemantic⟩ :=
    hwitness.special_antiderivative fuel reduced hreduce
  obtain ⟨special, hspecial⟩ := CompleteCMonomialCase.special_complete (C := C) Dt
    reduced.remainder (canonicalResult Dt a d).specialNum
    (canonicalResult Dt a d).specialDen snum sden hsden hspecialSemantic
  obtain ⟨snum', sden'⟩ := special
  have hnormalDen := LawfulCCanonicalRepresentation.normalDen_nonzero Dt a d hd
  obtain ⟨before, hnormal, hbefore⟩ := CompleteCNormalReduction.relative_complete (N := N)
    Dt
    (canonicalResult Dt a d).normalNum (canonicalResult Dt a d).normalDen
    hwitness.normal_domain hnormalDen hwitness.normal_integrable
  obtain ⟨normal, hpost⟩ := CompleteCMonomialCase.postprocess_complete (C := C) Dt
    (canonicalResult Dt a d).normalNum (canonicalResult Dt a d).normalDen before hbefore
  refine ⟨fuel, combineSN (polynomialSpecialNumerator reduced.antiderivative snum' sden')
    sden' normal, ?_⟩
  simp only [assembleOneLevel, hreduce, hspecial, hnormal, hpost, Option.bind_eq_bind,
    Option.bind_some]
  rfl

set_option maxHeartbeats 800000 in
/-- A successful contract-based one-level assembly is an integral result of its input. -/
theorem assembleOneLevel_sound (R : CPolynomialReduction P α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind) (fuel : ℕ)
    (N : CNormalReduction P α) (normalDomain : NormalReductionDomain P α)
    [LawfulCNormalReduction N normalDomain] (C : CMonomialCase P α)
    [CCanonicalRepresentation P α]
    [LawfulCCanonicalRepresentation (P := P) (α := α)] [LawfulCMonomialCase C]
    (Dt a d : P α) (out : IntegralResult α P)
    (hd : CPoly.toPoly d ≠ 0)
    (hnormalDomain : normalDomain Dt (canonicalResult Dt a d).normalNum
      (canonicalResult Dt a d).normalDen)
    (hrun : assembleOneLevel R kind N fuel C Dt a d = some out) :
    IsIntegralResultP Dt a d out := by
  cases hreduce : R.reduce kind Dt fuel (canonicalResult Dt a d).polynomial with
  | none => simp [assembleOneLevel, hreduce] at hrun
  | some reduced =>
    cases hspecial : C.integrateSpecial Dt reduced.remainder
        (canonicalResult Dt a d).specialNum (canonicalResult Dt a d).specialDen with
    | none => simp [assembleOneLevel, hreduce, hspecial] at hrun
    | some special =>
      obtain ⟨snum, sden⟩ := special
      cases hnormal : N.reduce Dt (canonicalResult Dt a d).normalNum
          (canonicalResult Dt a d).normalDen with
      | none => simp [assembleOneLevel, hreduce, hnormal] at hrun
      | some before =>
        cases hpost : C.postprocessNormal Dt before with
        | none => simp [assembleOneLevel, hreduce, hnormal, hpost] at hrun
        | some normal =>
          have hout : combineSN (polynomialSpecialNumerator reduced.antiderivative snum sden)
              sden normal = out := by
            simpa [assembleOneLevel, hreduce, hspecial, hnormal, hpost] using hrun
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
          have hbefore := LawfulCNormalReduction.sound (N := N) Dt
            (canonicalResult Dt a d).normalNum
            (canonicalResult Dt a d).normalDen before hnormalDomain hnormalDen hnormal
          have hbeforeDen := LawfulCNormalReduction.rationalDen_nonzero (N := N) Dt
            (canonicalResult Dt a d).normalNum
            (canonicalResult Dt a d).normalDen before hnormalDomain hnormalDen hnormal
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
