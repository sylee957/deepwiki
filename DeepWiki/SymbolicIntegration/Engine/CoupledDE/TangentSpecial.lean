import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentCapability
import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentPolynomial
import DeepWiki.SymbolicIntegration.Engine.RecursiveCoefficient
import DeepWiki.SymbolicIntegration.Engine.Tower.LogTower
import DeepWiki.ComputableAlgebra.PolyAntiderivative

/-! # Recursive hypertangent special integration

Executable outer recursion for Bronstein's hypertangent reduced and polynomial algorithms. The raw
candidate generator is paired with the certificate-checked tangent operation before public use. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

universe u

/-- Prop-free tangent-special operation whose lower coefficient results retain recursive tower logs. -/
structure CTowerTangentSpecialIntegrator (n : ℕ) where
  /-- Integrate a tangent special part over `Kₙ₊₁`, preserving lower log syntax. -/
  integrate : CTangentCoefficientSolver (DenseFracTower (n + 1)) → ℕ →
    DensePoly (DenseFracTower (n + 1)) → DensePoly (DenseFracTower (n + 1)) →
    DensePoly (DenseFracTower (n + 1)) → DensePoly (DenseFracTower (n + 1)) →
      Option (TowerIntegralResult (n + 1))

/-- The hypertangent base polynomial `t² + 1`. -/
def tangentBase {α : Type u} [CCommRing α] : DensePoly α :=
  [CCommRing.one, CCommRing.zero, CCommRing.one]

/-- Test equality of dense tower polynomials through the executable zero test. -/
private def tangentPolyEq {α : Type u} [CCommRing α] (p q : DensePoly α) : Bool :=
  CPolyEngine.cisZero (CPolyEngine.sub p q)

/-- A successful executable polynomial equality test yields equality of denotations. -/
private theorem toPoly_eq_of_tangentPolyEq {α : Type u} [CField α] [CFieldSpec α]
    (p q : DensePoly α) (h : tangentPolyEq p q = true) : CPoly.toPoly p = CPoly.toPoly q := by
  unfold tangentPolyEq at h
  have hzero := (LawfulCPolyEngine.cisZero_iff (P := DensePoly) (CPolyEngine.sub p q)).mp h
  rw [CPolyEngine.toPoly_sub, sub_eq_zero] at hzero
  exact hzero

/-- The executable tangent-shape check yields the semantic nonzero monomial condition. -/
private theorem isTangentMonomial_of_tangentPolyEq {α : Type u} [CField α] [CFieldSpec α]
    (Dt : DensePoly α) (alpha : α) (halpha : CCommRing.isZero alpha = false)
    (hshape : tangentPolyEq Dt [alpha, CCommRing.zero, alpha] = true) :
    IsTangentMonomial Dt := by
  refine ⟨CFieldSpec.toK alpha, ?_, ?_⟩
  · unfold tangentPolyEq at hshape
    calc
      CPoly.toPoly Dt = CPoly.toPoly ([alpha, CCommRing.zero, alpha] : DensePoly α) :=
        toPoly_eq_of_tangentPolyEq Dt [alpha, CCommRing.zero, alpha] hshape
      _ = DensePoly.toPoly ([alpha, CCommRing.zero, alpha] : DensePoly α) :=
        toPoly_list_eq _
      _ = Polynomial.C (CFieldSpec.toK alpha) * (1 + Polynomial.X ^ 2) := by
        simp only [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil, toR_eq_toK,
          CFieldSpec.toK_zero, map_zero, mul_zero, add_zero, zero_add]
        ring
  · intro hzero
    exact (Bool.eq_false_iff.mp halpha)
      ((CFieldSpec.isZero_iff alpha).mpr hzero)

/-- Read a rational-function coefficient as a polynomial when its stored denominator is `1`. -/
private def tangentCoefficientPolynomial? (x : DenseFrac ℚ) : Option (DensePoly ℚ) :=
  if CPolyEngine.cisZero
      (CPolyEngine.sub (CFrac.den x) (CPoly.one : DensePoly ℚ)) then
    some (CFrac.num x)
  else none

/-- Adapt the polynomial `ℚ[x][t]` cancellation kernel to coefficient-field coupled candidates. -/
private def tangentPolynomialCoefficientCandidate (S : CTangentPolynomialCoupledSolver) :
    CTangentCoefficientSolver (DenseFrac ℚ) where
  solve fuel coupling a b := do
    let couplingPoly ← tangentCoefficientPolynomial? coupling
    let aPoly ← tangentCoefficientPolynomial? a
    let bPoly ← tangentCoefficientPolynomial? b
    let solution ← S.solve fuel (CPoly.czero : DensePoly ℚ) couplingPoly [aPoly] [bPoly] 0
    let cPoly := CPoly.coeff solution.1 0
    let dPoly := CPoly.coeff solution.2 0
    some (CFrac.ofPoly cPoly, CFrac.ofPoly dPoly)

/-- Checked coefficient-field realization backed by the polynomial tangent cancellation kernel. -/
def tangentPolynomialCoefficientSolver (S : CTangentPolynomialCoupledSolver) :
    CTangentCoefficientSolver (DenseFrac ℚ) :=
  checkedTangentCoefficientSolver (tangentPolynomialCoefficientCandidate S)

/-- The checked polynomial-backed coefficient solver satisfies the field-level coupled contract. -/
instance instLawfulCTangentCoefficientSolverPolynomial (S : CTangentPolynomialCoupledSolver) :
    LawfulCTangentCoefficientSolver (tangentPolynomialCoefficientSolver S) := by
  unfold tangentPolynomialCoefficientSolver
  infer_instance

/-- The polynomial-backed coefficient solver is complete on its exact checked acceptance domain. -/
instance instCompleteCTangentCoefficientSolverPolynomial (S : CTangentPolynomialCoupledSolver) :
    CompleteCTangentCoefficientSolver (tangentPolynomialCoefficientSolver S)
      (checkedTangentCoefficientDomain (tangentPolynomialCoefficientCandidate S)) := by
  unfold tangentPolynomialCoefficientSolver
  infer_instance

/-- Clear a represented rational function to a selected common polynomial denominator. -/
private def tangentClearAt (commonDen : DensePoly ℚ) (x : DenseFrac ℚ) : DensePoly ℚ :=
  CPolyEngine.mul (CFrac.num x) (CPolyEuclidean.div commonDen (CFrac.den x))

/-- Bounded rational-function candidate generator for the tangent coefficient system. -/
private def tangentRationalCoefficientCandidate [CLinearSolve ℚ] :
    CTangentCoefficientSolver (DenseFrac ℚ) where
  solve degreeBound coupling a b :=
    let candidateDen := [CFrac.den coupling, CFrac.den a, CFrac.den b].foldl
      (fun acc den => CPoly.lcm acc den) (CPoly.one : DensePoly ℚ)
    let basis : List (DenseFrac ℚ) :=
      (List.range (degreeBound + 1)).map fun i =>
        CField.div
          (CFrac.ofPoly (CPolyEngine.monomial (P := DensePoly) (1 : ℚ) i))
          (CFrac.ofPoly candidateDen)
    let columns : List (DenseFrac ℚ × DenseFrac ℚ) :=
      basis.map (fun z =>
        (CDiffField.cderiv z, CCommRing.mul coupling z)) ++
      basis.map (fun z =>
        (CCommRing.neg (CCommRing.mul coupling z), CDiffField.cderiv z))
    let allDenominators :=
      columns.flatMap (fun col => [CFrac.den col.1, CFrac.den col.2]) ++
        [CFrac.den a, CFrac.den b]
    let commonDen := allDenominators.foldl
      (fun acc den => CPoly.lcm acc den) (CPoly.one : DensePoly ℚ)
    let clearedColumns := columns.map fun col =>
      (tangentClearAt commonDen col.1, tangentClearAt commonDen col.2)
    let clearedA := tangentClearAt commonDen a
    let clearedB := tangentClearAt commonDen b
    let nrows := (clearedColumns.flatMap (fun col => [CPolyEngine.cdeg col.1,
      CPolyEngine.cdeg col.2]) ++ [CPolyEngine.cdeg clearedA, CPolyEngine.cdeg clearedB]).foldl
        Nat.max 0 + 1
    let matrix :=
      (List.range nrows).map (fun i => clearedColumns.map fun col => CPoly.coeff col.1 i) ++
      (List.range nrows).map (fun i => clearedColumns.map fun col => CPoly.coeff col.2 i)
    let rhs := CPoly.coeffs clearedA nrows ++ CPoly.coeffs clearedB nrows
    match CLinearSolve.solveAny matrix rhs (2 * (degreeBound + 1)) with
    | none => none
    | some solution =>
        let cNum : DensePoly ℚ := CPoly.ofFn (degreeBound + 1) fun i => solution.getD i 0
        let dNum : DensePoly ℚ := CPoly.ofFn (degreeBound + 1) fun i =>
          solution.getD (degreeBound + 1 + i) 0
        some (CField.div (CFrac.ofPoly cNum) (CFrac.ofPoly candidateDen),
          CField.div (CFrac.ofPoly dNum) (CFrac.ofPoly candidateDen))

/-- Checked bounded rational-function realization of tangent coefficient coupled solving. -/
def tangentRationalCoefficientSolver [CLinearSolve ℚ] :
    CTangentCoefficientSolver (DenseFrac ℚ) :=
  checkedTangentCoefficientSolver tangentRationalCoefficientCandidate

/-- The checked bounded rational coefficient solver satisfies the coupled field equations. -/
instance instLawfulCTangentCoefficientSolverRational [CLinearSolve ℚ] :
    LawfulCTangentCoefficientSolver tangentRationalCoefficientSolver := by
  unfold tangentRationalCoefficientSolver
  infer_instance

/-- The bounded rational coefficient solver is complete on its exact checked acceptance domain. -/
instance instCompleteCTangentCoefficientSolverRational [CLinearSolve ℚ] :
    CompleteCTangentCoefficientSolver tangentRationalCoefficientSolver
      (checkedTangentCoefficientDomain tangentRationalCoefficientCandidate) := by
  unfold tangentRationalCoefficientSolver
  infer_instance

/-- Recognize an exact power of `t² + 1`, bounded by the supplied fuel. -/
private def tangentBasePower? {α : Type u} [CField α] : ℕ → DensePoly α → Option ℕ
  | 0, den =>
      if tangentPolyEq den (CPoly.one : DensePoly α) then some 0 else none
  | fuel + 1, den =>
      if tangentPolyEq den (CPoly.one : DensePoly α) then some 0
      else
        let qr := CPolyEuclidean.divmod den tangentBase
        if CPolyEngine.cisZero qr.2 then
          (tangentBasePower? fuel qr.1).map Nat.succ
        else none

/-- The tangent base `t² + 1` has nonzero denotation. -/
private theorem tangentBase_toPoly_ne_zero {α : Type u} [CField α] [CFieldSpec α] :
    CPoly.toPoly (tangentBase : DensePoly α) ≠ 0 := by
  rw [tangentBase, toPoly_list_eq]
  simp only [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil, toR_eq_toK, mul_zero, add_zero]
  intro hzero
  have hcoeff := congrArg (fun p : Polynomial (CFieldSpec.K α) => p.coeff 2) hzero
  simp at hcoeff
  rw [CFieldSpec.toK_one] at hcoeff
  exact one_ne_zero hcoeff

/-- A recognized tangent-base power denotes the corresponding power of `t² + 1`. -/
private theorem tangentBasePower?_sound {α : Type u} [CField α] [CFieldSpec α]
    (fuel m : ℕ) (den : DensePoly α)
    (h : tangentBasePower? fuel den = some m) :
    CPoly.toPoly den = CPoly.toPoly (tangentBase : DensePoly α) ^ m := by
  induction fuel generalizing den m with
  | zero =>
      unfold tangentBasePower? at h
      split at h
      · rename_i hden
        have hm : m = 0 := Option.some.inj h |>.symm
        subst m
        rw [toPoly_eq_of_tangentPolyEq den CPoly.one hden, CPoly.toPoly_one]
        simp
      · simp at h
  | succ fuel ih =>
      unfold tangentBasePower? at h
      split at h
      · rename_i hden
        have hm : m = 0 := Option.some.inj h |>.symm
        subst m
        rw [toPoly_eq_of_tangentPolyEq den CPoly.one hden, CPoly.toPoly_one]
        simp
      · rename_i hden
        let qr := CPolyEuclidean.divmod den (tangentBase : DensePoly α)
        change (if CPolyEngine.cisZero qr.2 = true then
          (tangentBasePower? fuel qr.1).map Nat.succ else none) = some m at h
        split at h
        · rename_i hrem
          cases hquot : tangentBasePower? fuel qr.1 with
          | none => simp [hquot] at h
          | some k =>
              simp only [hquot, Option.map_some, Option.some.injEq] at h
              have hm : m = k + 1 := h.symm
              subst m
              have hquotient := ih k qr.1 hquot
              have hbase : CPoly.toPoly (tangentBase : DensePoly α) ≠ 0 :=
                tangentBase_toPoly_ne_zero
              have hremzero : CPoly.toPoly qr.2 = 0 :=
                (LawfulCPolyEngine.cisZero_iff (P := DensePoly) qr.2).mp hrem
              have hdiv : CPoly.toPoly den = CPoly.toPoly qr.1 *
                  CPoly.toPoly (tangentBase : DensePoly α) + CPoly.toPoly qr.2 := by
                simpa only [qr, CPolyEuclidean.div, CPolyEuclidean.mod] using
                  (LawfulCPolyEuclidean.divmod_spec (P := DensePoly) den tangentBase hbase)
              rw [hdiv, hremzero, add_zero, hquotient, pow_succ]
        · simp at h

/-- A recognized tangent-base power has nonzero denotation. -/
private theorem tangentBasePower?_den_nonzero {α : Type u} [CField α] [CFieldSpec α]
    (fuel m : ℕ) (den : DensePoly α)
    (h : tangentBasePower? fuel den = some m) : CPoly.toPoly den ≠ 0 := by
  rw [tangentBasePower?_sound fuel m den h]
  exact pow_ne_zero _ tangentBase_toPoly_ne_zero

/-- Candidate produced by reduced hypertangent recursion together with its polynomial residual. -/
private structure TangentReducedCandidate (α : Type u) where
  /-- Rational antiderivative accumulated while lowering the pole order. -/
  rational : DensePoly α × DensePoly α
  /-- Polynomial residual remaining after all powers of `t² + 1` have been removed. -/
  remainder : DensePoly α

/-- Semantic identity represented by one successful tangent pole-lowering result. -/
private def IsTangentReducedCandidate {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    (alpha : α) (num den : DensePoly α) (out : TangentReducedCandidate α) : Prop :=
  CPoly.toPoly out.rational.2 ≠ 0 ∧
    towerFractionFieldDerivP ([alpha, CCommRing.zero, alpha] : DensePoly α)
        (fieldFracP out.rational.1 out.rational.2) +
      fieldFracP out.remainder CPoly.one = fieldFracP num den

/-- Semantic identity required of one coupled tangent pole-lowering correction. -/
private def IsTangentReducedStep {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    (alpha : α) (num den correction nextNum nextDen : DensePoly α) : Prop :=
  CPoly.toPoly den ≠ 0 ∧ CPoly.toPoly nextDen ≠ 0 ∧
    towerFractionFieldDerivP ([alpha, CCommRing.zero, alpha] : DensePoly α)
        (fieldFracP correction den) + fieldFracP nextNum nextDen = fieldFracP num den

/-- Recursive domain in which every selected pole-lowering coupled system is semantically solvable. -/
def TangentReducedCompleteDomain {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    (S : CTangentCoefficientSolver α) (solverDomain : TangentCoefficientDomain (α := α))
    (alpha : α) : (m : ℕ) → DensePoly α → DensePoly α → Prop
  | 0, _num, den => CPoly.toPoly den = 1
  | m + 1, num, den =>
      let numDiv := CPolyEuclidean.divmod num tangentBase
      let denDiv := CPolyEuclidean.divmod den tangentBase
      let a := CPoly.coeff numDiv.2 1
      let b := CPoly.coeff numDiv.2 0
      let coupling := CCommRing.mul (CField.natCast (2 * (m + 1))) alpha
      CPolyEngine.cisZero denDiv.2 = true ∧
        solverDomain coupling a b ∧ IsTangentCoefficientSolvable coupling a b ∧
        ∀ fuel solution, S.solve fuel coupling a b = some solution →
          let oneMinusTwoM : α :=
            CField.sub CCommRing.one (CField.natCast (2 * (m + 1)))
          let correction := CCommRing.mul (CCommRing.mul solution.1 alpha) oneMinusTwoM
          let nextNum := CPolyEngine.sub numDiv.1 [correction]
          IsTangentReducedStep alpha num den [solution.2, solution.1] nextNum denDiv.1 ∧
            TangentReducedCompleteDomain S solverDomain alpha m nextNum denDiv.1

/-- Lower the `(t² + 1)` pole order by Bronstein's coupled-system recurrence. -/
private def tangentReducedCandidate {α : Type u} [CField α] [CDiffField α]
    (S : CTangentCoefficientSolver α) (coupledFuel : ℕ) (alpha : α) :
    (m : ℕ) → DensePoly α → DensePoly α → Option (TangentReducedCandidate α)
  | 0, num, _den =>
      some { rational := (CPoly.czero, CPoly.one), remainder := num }
  | m + 1, num, den => do
      let stageFuel := Nat.unpair coupledFuel
      let numDiv := CPolyEuclidean.divmod num tangentBase
      let denDiv := CPolyEuclidean.divmod den tangentBase
      if !CPolyEngine.cisZero denDiv.2 then none
      else
        let a := CPoly.coeff numDiv.2 1
        let b := CPoly.coeff numDiv.2 0
        let coupling := CCommRing.mul (CField.natCast (2 * (m + 1))) alpha
        let solution ← S.solve stageFuel.1 coupling a b
        let c := solution.1
        let d := solution.2
        let oneMinusTwoM : α :=
          CField.sub CCommRing.one (CField.natCast (2 * (m + 1)))
        let correction := CCommRing.mul (CCommRing.mul c alpha) oneMinusTwoM
        let nextNum := CPolyEngine.sub numDiv.1 [correction]
        let rest ← tangentReducedCandidate S stageFuel.2 alpha m nextNum denDiv.1
        let q0 : DensePoly α × DensePoly α := ([d, c], den)
        some {
          rational := combineRationalParts q0.1 q0.2 rest.rational.1 rest.rational.2
          remainder := rest.remainder
        }

/-- The terminal pole-lowering result is sound once its residual denominator is `1`. -/
private theorem tangentReducedCandidate_zero_sound
    {α : Type u} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] (alpha : α) (num den : DensePoly α)
    (hden : CPoly.toPoly den = 1) :
    IsTangentReducedCandidate alpha num den
      { rational := (CPoly.czero, CPoly.one), remainder := num } := by
  constructor
  · rw [CPoly.toPoly_one]
    exact one_ne_zero
  · change towerFractionFieldDerivP ([alpha, CCommRing.zero, alpha] : DensePoly α)
        (fieldFracP CPoly.czero CPoly.one) + fieldFracP num CPoly.one = fieldFracP num den
    simp only [fieldFracP, CPoly.toPoly_czero, CPoly.toPoly_one, map_zero, map_one,
      div_one, map_zero, zero_add, hden]

/-- `combineRationalParts` denotes the sum of its two represented fractions. -/
private theorem fieldFracP_combineRationalParts {α : Type u} [CField α] [CFieldSpec α]
    (a b c d : DensePoly α) (hb : CPoly.toPoly b ≠ 0) (hd : CPoly.toPoly d ≠ 0) :
    fieldFracP (combineRationalParts a b c d).1 (combineRationalParts a b c d).2 =
      fieldFracP a b + fieldFracP c d := by
  have hb' : CFrac.am α (CPoly.toPoly b) ≠ 0 := CFrac.am_ne_zero hb
  have hd' : CFrac.am α (CPoly.toPoly d) ≠ 0 := CFrac.am_ne_zero hd
  simp only [combineRationalParts, fieldFracP, LawfulCPolyEngine.toPoly_add,
    LawfulCPolyEngine.toPoly_mul, map_add, map_mul]
  field_simp [hb', hd']

/-- Every successful pole-lowering run satisfies the stepwise rational derivative invariant. -/
private theorem tangentReducedCandidate_sound
    {α : Type u} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] (S : CTangentCoefficientSolver α)
    (solverDomain : TangentCoefficientDomain (α := α))
    (alpha : α) (m fuel : ℕ) (num den : DensePoly α) (out : TangentReducedCandidate α)
    (hdomain : TangentReducedCompleteDomain S solverDomain alpha m num den)
    (hrun : tangentReducedCandidate S fuel alpha m num den = some out) :
    IsTangentReducedCandidate alpha num den out := by
  induction m generalizing fuel num den out with
  | zero =>
      simp only [tangentReducedCandidate] at hrun
      have hout : out = { rational := (CPoly.czero, CPoly.one), remainder := num } :=
        (Option.some.inj hrun).symm
      rw [hout]
      exact tangentReducedCandidate_zero_sound alpha num den hdomain
  | succ m ih =>
      simp only [TangentReducedCompleteDomain] at hdomain
      let stageFuel := Nat.unpair fuel
      let numDiv := CPolyEuclidean.divmod num tangentBase
      let denDiv := CPolyEuclidean.divmod den tangentBase
      let a := CPoly.coeff numDiv.2 1
      let b := CPoly.coeff numDiv.2 0
      let coupling := CCommRing.mul (CField.natCast (2 * (m + 1))) alpha
      obtain ⟨hden, _hsolverDomain, _hsolvable, hnext⟩ := hdomain
      simp only [tangentReducedCandidate, hden, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte] at hrun
      simp [Option.bind_eq_some_iff] at hrun
      obtain ⟨c, d, hsolve, rest, hrest, hout⟩ := hrun
      let solution : α × α := (c, d)
      let oneMinusTwoM : α :=
        CField.sub CCommRing.one (CField.natCast (2 * (m + 1)))
      let correction := CCommRing.mul (CCommRing.mul solution.1 alpha) oneMinusTwoM
      let nextNum := CPolyEngine.sub numDiv.1 [correction]
      have hsolve' : S.solve stageFuel.1 coupling a b = some solution := by
        change S.solve stageFuel.1 coupling a b = some solution at hsolve
        exact hsolve
      have hstepAndDomain := hnext stageFuel.1 solution hsolve'
      have hstep : IsTangentReducedStep alpha num den [solution.2, solution.1]
          nextNum denDiv.1 := by
        simpa only [oneMinusTwoM, correction, nextNum] using hstepAndDomain.1
      have hrestDomain : TangentReducedCompleteDomain S solverDomain alpha m nextNum denDiv.1 := by
        simpa only [oneMinusTwoM, correction, nextNum] using hstepAndDomain.2
      have hrest' : tangentReducedCandidate S stageFuel.2 alpha m nextNum denDiv.1 = some rest := by
        change tangentReducedCandidate S stageFuel.2 alpha m nextNum denDiv.1 = some rest at hrest
        exact hrest
      have hrestSound := ih stageFuel.2 nextNum denDiv.1 rest hrestDomain hrest'
      have hout' : out = {
              rational := combineRationalParts ([solution.2, solution.1] : DensePoly α) den
                rest.rational.1 rest.rational.2
              remainder := rest.remainder } := hout.symm
      rw [hout']
      constructor
      · change CPoly.toPoly (CPolyEngine.mul den rest.rational.2) ≠ 0
        rw [LawfulCPolyEngine.toPoly_mul]
        exact mul_ne_zero hstep.1 hrestSound.1
      · rw [fieldFracP_combineRationalParts ([solution.2, solution.1] : DensePoly α) den
          rest.rational.1 rest.rational.2 hstep.1 hrestSound.1, map_add]
        calc
          (towerFractionFieldDerivP ([alpha, CCommRing.zero, alpha] : DensePoly α)
                (fieldFracP [solution.2, solution.1] den) +
              towerFractionFieldDerivP ([alpha, CCommRing.zero, alpha] : DensePoly α)
                (fieldFracP rest.rational.1 rest.rational.2)) +
              fieldFracP rest.remainder CPoly.one =
              towerFractionFieldDerivP ([alpha, CCommRing.zero, alpha] : DensePoly α)
                (fieldFracP [solution.2, solution.1] den) +
                (towerFractionFieldDerivP ([alpha, CCommRing.zero, alpha] : DensePoly α)
                  (fieldFracP rest.rational.1 rest.rational.2) +
                  fieldFracP rest.remainder CPoly.one) := by ring
          _ = towerFractionFieldDerivP ([alpha, CCommRing.zero, alpha] : DensePoly α)
                (fieldFracP [solution.2, solution.1] den) + fieldFracP nextNum denDiv.1 := by
                rw [hrestSound.2]
          _ = fieldFracP num den := hstep.2.2

/-- A constant dense polynomial denotes the corresponding coefficient-field element. -/
private theorem fieldFracP_singleton {α : Type u} [CField α] [CFieldSpec α]
    (x : α) :
    fieldFracP ([x] : DensePoly α) CPoly.one =
      CFrac.am α (Polynomial.C (CFieldSpec.toK x)) := by
  change fieldFracP ([x] : DensePoly α) ([CCommRing.one] : DensePoly α) = _
  simp only [fieldFracP, toPoly_list_eq, DensePoly.toPolyG_cons, DensePoly.toPolyG_nil,
    mul_zero, add_zero, toR_eq_toK, CFieldSpec.toK_one, map_one, div_one]

/-- The tower derivation of a coefficient embedded as a constant polynomial is its coefficient derivation. -/
private theorem towerFractionFieldDerivP_singleton {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    (Dt : DensePoly α) (x : α) :
    towerFractionFieldDerivP Dt (fieldFracP ([x] : DensePoly α) CPoly.one) =
      CFrac.am α (Polynomial.C (CFieldSpec.toK (CDiffField.cderiv x))) := by
  rw [fieldFracP_singleton, towerFractionFieldDerivP, extendDeriv_algebraMap,
    Differential.implicitDeriv_C, ← CDiffFieldSpec.toK_cderiv]

/-- The polynomial embedding of a scalar is the coefficient-to-fraction-field embedding. -/
private theorem am_C_eq_algebraMap {α : Type u} [CField α] [CFieldSpec α]
    (x : CFieldSpec.K α) :
    CFrac.am α (Polynomial.C x) = algebraMap (CFieldSpec.K α) (RatFunc (CFieldSpec.K α)) x := by
  rw [CFrac.am, ← Polynomial.algebraMap_eq]
  exact (IsScalarTower.algebraMap_apply (CFieldSpec.K α) (Polynomial (CFieldSpec.K α))
    (RatFunc (CFieldSpec.K α)) x).symm

/-- Lifting coefficient-field logarithms to constant polynomials preserves their residue sum. -/
private theorem logResidueSumP_liftCoefficientLogs {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    (Dt : DensePoly α) (logs : List (α × α)) :
    logResidueSumP Dt (logs.map fun cv => (cv.1, [cv.2])) =
      CFrac.am α (Polynomial.C (coefficientLogSum logs)) := by
  induction logs with
  | nil => simp [logResidueSumP, coefficientLogSum]
  | cons cv rest ih =>
      rw [List.map_cons, logResidueSumP_cons, ih, coefficientLogSum_cons]
      have hratio :
          CFrac.am α (CPoly.toPoly (CPolyEngine.monomialDeriv Dt ([cv.2] : DensePoly α))) /
              CFrac.am α (CPoly.toPoly ([cv.2] : DensePoly α)) =
              CFrac.am α (Polynomial.C (CFieldSpec.toK (CDiffField.cderiv cv.2))) /
              CFrac.am α (Polynomial.C (CFieldSpec.toK cv.2)) := by
        have hsingle : CFrac.am α (CPoly.toPoly ([cv.2] : DensePoly α)) =
            fieldFracP ([cv.2] : DensePoly α) CPoly.one := by
          rw [fieldFracP_singleton]
          simp only [toPoly_list_eq, DensePoly.toPolyG_cons, DensePoly.toPolyG_nil,
            mul_zero, add_zero, toR_eq_toK]
        rw [← towerFractionFieldDerivP_logDeriv, hsingle,
          towerFractionFieldDerivP_singleton, fieldFracP_singleton]
      rw [hratio, Polynomial.C_add, Polynomial.C_mul,
        map_add (CFrac.am α), map_mul (CFrac.am α),
        am_C_eq_algebraMap, am_C_eq_algebraMap,
        am_C_eq_algebraMap, am_C_eq_algebraMap, am_C_eq_algebraMap,
        map_div₀ (algebraMap (CFieldSpec.K α) (RatFunc (CFieldSpec.K α)))]

/-- A dense polynomial guarded to degree at most one is its constant and linear coefficient tail. -/
private theorem toPoly_eq_constant_add_linear {α : Type u} [CField α] [CFieldSpec α]
    (p : DensePoly α) (hdegree : ¬ 1 < CPolyEngine.cdeg p) :
    CPoly.toPoly p = Polynomial.C (CFieldSpec.toK (CPoly.coeff p 0)) +
      Polynomial.C (CFieldSpec.toK (CPoly.coeff p 1)) * Polynomial.X := by
  have hdegree' : (CPoly.toPoly p).natDegree ≤ 1 := by
    rw [← LawfulCPolyEngine.cdeg_eq_natDegree]
    omega
  calc
    CPoly.toPoly p = Polynomial.C ((CPoly.toPoly p).coeff 1) * Polynomial.X +
        Polynomial.C ((CPoly.toPoly p).coeff 0) :=
      Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le hdegree')
    _ = Polynomial.C (CFieldSpec.toK (CPoly.coeff p 0)) +
        Polynomial.C (CFieldSpec.toK (CPoly.coeff p 1)) * Polynomial.X := by
      rw [CPoly.coeff_toPoly, CPoly.coeff_toPoly]
      simp only [toR_eq_toK]
      ring

/-- Under `Dt = α(t²+1)`, the tangent base differentiates to `2αt(t²+1)`. -/
private theorem toPoly_monomialDeriv_tangentBase {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α]
    (Dt : DensePoly α) (alpha : α)
    (hDt : CPoly.toPoly Dt = Polynomial.C (CFieldSpec.toK alpha) *
      (1 + Polynomial.X ^ 2)) :
    CPoly.toPoly (CPolyEngine.monomialDeriv Dt (tangentBase : DensePoly α)) =
      (2 : Polynomial (CFieldSpec.K α)) * Polynomial.C (CFieldSpec.toK alpha) * Polynomial.X *
        CPoly.toPoly (tangentBase : DensePoly α) := by
  have hbase : CPoly.toPoly (tangentBase : DensePoly α) = 1 + Polynomial.X ^ 2 := by
    rw [tangentBase, toPoly_list_eq]
    simp only [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil, toR_eq_toK,
      CFieldSpec.toK_one, CFieldSpec.toK_zero, map_zero, map_one, mul_zero, add_zero, zero_add]
    ring
  rw [CPolyEngine.toPoly_monomialDeriv, hbase, hDt,
    show (1 : Polynomial (CFieldSpec.K α)) = Polynomial.C 1 by simp,
    map_add, Differential.implicitDeriv_C]
  rw [show (Polynomial.X ^ 2 : Polynomial (CFieldSpec.K α)) = Polynomial.X * Polynomial.X by ring,
    Derivation.leibniz, Differential.implicitDeriv_X]
  simp only [map_one, Derivation.map_one_eq_zero, map_zero, zero_add, smul_eq_mul]
  ring

/-- A linear dense polynomial denotes its coefficient times the tower variable. -/
private theorem fieldFracP_linear {α : Type u} [CField α] [CFieldSpec α] (x : α) :
    fieldFracP ([CCommRing.zero, x] : DensePoly α) CPoly.one =
      CFrac.am α (Polynomial.C (CFieldSpec.toK x) * Polynomial.X) := by
  change fieldFracP ([CCommRing.zero, x] : DensePoly α) ([CCommRing.one] : DensePoly α) = _
  simp only [fieldFracP, toPoly_list_eq, DensePoly.toPolyG_cons, DensePoly.toPolyG_nil,
    toR_eq_toK, CFieldSpec.toK_zero, CFieldSpec.toK_one, map_zero, map_one, mul_zero,
    zero_add, add_zero, div_one]
  congr 1
  ring

/-- The tangent logarithm integrates the linear residue for `Dt = α(t²+1)`. -/
private theorem logResidueSumP_tangentBase {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    (Dt : DensePoly α) (alpha linear : α) (halpha : CFieldSpec.toK alpha ≠ 0)
    (hDt : CPoly.toPoly Dt = Polynomial.C (CFieldSpec.toK alpha) *
      (1 + Polynomial.X ^ 2)) :
    logResidueSumP Dt
        [(CField.div linear (CCommRing.mul (CField.natCast 2) alpha), tangentBase)] =
      fieldFracP ([CCommRing.zero, linear] : DensePoly α) CPoly.one := by
  let coefficient := CField.div linear (CCommRing.mul (CField.natCast 2) alpha)
  have htwoAlpha : (2 : CFieldSpec.K α) * CFieldSpec.toK alpha ≠ 0 := by
    exact mul_ne_zero (by norm_num) halpha
  have hcoefficient : CFieldSpec.toK coefficient *
      ((2 : CFieldSpec.K α) * CFieldSpec.toK alpha) = CFieldSpec.toK linear := by
    simp only [coefficient, CFieldSpec.toK_div, CFieldSpec.toK_mul, CFieldSpec.toK_natCast]
    exact div_mul_cancel₀ _ htwoAlpha
  have hbase : CFrac.am α (CPoly.toPoly (tangentBase : DensePoly α)) ≠ 0 :=
    CFrac.am_ne_zero tangentBase_toPoly_ne_zero
  have hderiv := toPoly_monomialDeriv_tangentBase Dt alpha hDt
  rw [show (CField.div linear (CCommRing.mul (CField.natCast 2) alpha)) = coefficient from rfl,
    logResidueSumP_cons, logResidueSumP_nil, add_zero, fieldFracP_linear, hderiv]
  simp only [map_mul]
  field_simp [hbase]
  have hamTwo : CFrac.am α (2 : Polynomial (CFieldSpec.K α)) =
      algebraMap (CFieldSpec.K α) (RatFunc (CFieldSpec.K α)) (2 : CFieldSpec.K α) := by
    rw [show (2 : Polynomial (CFieldSpec.K α)) = Polynomial.C (2 : CFieldSpec.K α) from
      (Polynomial.C_eq_natCast 2).symm,
      am_C_eq_algebraMap]
  rw [hamTwo]
  rw [am_C_eq_algebraMap (CFieldSpec.toK coefficient),
    am_C_eq_algebraMap (CFieldSpec.toK alpha), am_C_eq_algebraMap (CFieldSpec.toK linear)]
  have hmapProduct :
      algebraMap (CFieldSpec.K α) (RatFunc (CFieldSpec.K α)) (CFieldSpec.toK coefficient) *
          algebraMap (CFieldSpec.K α) (RatFunc (CFieldSpec.K α)) (2 : CFieldSpec.K α) *
          algebraMap (CFieldSpec.K α) (RatFunc (CFieldSpec.K α)) (CFieldSpec.toK alpha) =
        algebraMap (CFieldSpec.K α) (RatFunc (CFieldSpec.K α))
          (CFieldSpec.toK coefficient * 2 * CFieldSpec.toK alpha) := by
    rw [map_mul, map_mul]
  have hproduct : CFieldSpec.toK coefficient * 2 * CFieldSpec.toK alpha =
      CFieldSpec.toK linear := by
    calc
      CFieldSpec.toK coefficient * 2 * CFieldSpec.toK alpha =
          CFieldSpec.toK coefficient * (2 * CFieldSpec.toK alpha) := by ring
      _ = CFieldSpec.toK linear := hcoefficient
  rw [hmapProduct, hproduct]
  ring

/-- A coefficient-field elementary result remains an antiderivative after lifting to constant polynomials. -/
private theorem coefficientResult_lift_sound {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    (Dt : DensePoly α) (constantPart : α) (result : CoefficientIntegralResult α)
    (hresult : IsCoefficientIntegralResult constantPart result) :
    towerFractionFieldDerivP Dt
        (fieldFracP ([result.rational] : DensePoly α) CPoly.one) +
      logResidueSumP Dt (result.logs.map fun cv => (cv.1, [cv.2])) =
    fieldFracP ([constantPart] : DensePoly α) CPoly.one := by
  obtain ⟨hidentity, _hconstants, _hargs⟩ := hresult
  rw [towerFractionFieldDerivP_singleton, logResidueSumP_liftCoefficientLogs,
    fieldFracP_singleton, am_C_eq_algebraMap, am_C_eq_algebraMap, am_C_eq_algebraMap,
    ← map_add (algebraMap (CFieldSpec.K α) (RatFunc (CFieldSpec.K α))), hidentity]

/-- A nonzero coefficient remains nonzero when represented as a constant dense polynomial. -/
private theorem toPoly_singleton_ne_zero {α : Type u} [CField α] [CFieldSpec α]
    (x : α) (hx : CFieldSpec.toK x ≠ 0) : CPoly.toPoly ([x] : DensePoly α) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun p : Polynomial (CFieldSpec.K α) => p.coeff 0) hzero
  rw [toPoly_list_eq] at hcoeff
  simp [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil, toR_eq_toK] at hcoeff
  exact hx hcoeff

/-- Lifted lower-field logarithms retain their constant coefficients. -/
private theorem liftedCoefficientLogs_constants {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] (c : α) (result : CoefficientIntegralResult α)
    (hresult : IsCoefficientIntegralResult (α := α) c result) :
    ∀ cv ∈ result.logs.map (fun entry => (entry.1, ([entry.2] : DensePoly α))),
      CFieldSpec.toK (CDiffField.cderiv cv.1) = 0 := by
  obtain ⟨_identity, hconstants, _args⟩ := hresult
  intro cv hcv
  obtain ⟨source, hsource, hcv⟩ := List.mem_map.mp hcv
  subst cv
  exact hconstants source hsource

/-- Lifted lower-field logarithms retain nonzero polynomial arguments. -/
private theorem liftedCoefficientLogs_arguments {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] (c : α) (result : CoefficientIntegralResult α)
    (hresult : IsCoefficientIntegralResult (α := α) c result) :
    ∀ cv ∈ result.logs.map (fun entry => (entry.1, ([entry.2] : DensePoly α))),
      CPoly.toPoly cv.2 ≠ 0 := by
  obtain ⟨_identity, _constants, hargs⟩ := hresult
  intro cv hcv
  obtain ⟨source, hsource, hcv⟩ := List.mem_map.mp hcv
  subst cv
  exact toPoly_singleton_ne_zero source.2 (hargs source hsource)

/-- The empty coefficient result integrates a coefficient whose denotation is zero. -/
private theorem zeroCoefficientResult_sound {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] (c : α) (hzero : CFieldSpec.toK c = 0) :
    IsCoefficientIntegralResult c { rational := CCommRing.zero, logs := [] } := by
  refine ⟨?_, ?_, ?_⟩
  · change CFieldSpec.toK (CDiffField.cderiv (CCommRing.zero : α)) +
        coefficientLogSum ([] : List (α × α)) = CFieldSpec.toK c
    have hderivZero :
        CFieldSpec.toK (CDiffField.cderiv (CCommRing.zero : α)) = 0 := by
      rw [CDiffFieldSpec.toK_cderiv, CFieldSpec.toK_zero, map_zero]
    rw [hderivZero, hzero]
    simp [coefficientLogSum]
  · simp
  · simp

/-- Lifted coefficient logs and the optional tangent-base log are genuine. -/
private theorem coefficientTangentLogs_genuine {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] (remainder : DensePoly α) (alpha : α)
    (result : CoefficientIntegralResult α)
    (hresult : IsCoefficientIntegralResult (CPoly.coeff remainder 0) result)
    (hconstant : CFieldSpec.toK (CDiffField.cderiv
      (CField.div (CPoly.coeff remainder 1)
        (CCommRing.mul (CField.natCast 2) alpha))) = 0) :
    (∀ cv ∈ (result.logs.map fun entry => (entry.1, ([entry.2] : DensePoly α))) ++
        if CCommRing.isZero (CField.div (CPoly.coeff remainder 1)
          (CCommRing.mul (CField.natCast 2) alpha)) then [] else
          [(CField.div (CPoly.coeff remainder 1)
            (CCommRing.mul (CField.natCast 2) alpha), tangentBase)],
      CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
    (∀ cv ∈ (result.logs.map fun entry => (entry.1, ([entry.2] : DensePoly α))) ++
        if CCommRing.isZero (CField.div (CPoly.coeff remainder 1)
          (CCommRing.mul (CField.natCast 2) alpha)) then [] else
          [(CField.div (CPoly.coeff remainder 1)
            (CCommRing.mul (CField.natCast 2) alpha), tangentBase)],
      CPoly.toPoly cv.2 ≠ 0) := by
  constructor
  · intro cv hcv
    rw [List.mem_append] at hcv
    rcases hcv with hcv | hcv
    · exact liftedCoefficientLogs_constants (CPoly.coeff remainder 0) result hresult cv hcv
    · split at hcv
      · simp at hcv
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcv
        subst cv
        exact hconstant
  · intro cv hcv
    rw [List.mem_append] at hcv
    rcases hcv with hcv | hcv
    · exact liftedCoefficientLogs_arguments (CPoly.coeff remainder 0) result hresult cv hcv
    · split at hcv
      · simp at hcv
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcv
        subst cv
        exact tangentBase_toPoly_ne_zero

/-- A degree-at-most-one polynomial fraction splits into its constant and linear parts. -/
private theorem fieldFracP_lowDegree_split {α : Type u} [CField α] [CFieldSpec α]
    (p : DensePoly α) (hdegree : ¬ 1 < CPolyEngine.cdeg p) :
    fieldFracP p CPoly.one =
      fieldFracP ([CPoly.coeff p 0] : DensePoly α) CPoly.one +
        fieldFracP ([CCommRing.zero, CPoly.coeff p 1] : DensePoly α) CPoly.one := by
  have hpoly := toPoly_eq_constant_add_linear p hdegree
  rw [fieldFracP, fieldFracP, fieldFracP]
  have hone : CFrac.am α (CPoly.toPoly (CPoly.one : DensePoly α)) = 1 := by
    change CFrac.am α (CPoly.toPoly ([CCommRing.one] : DensePoly α)) = 1
    simp only [toPoly_list_eq, DensePoly.toPolyG_cons, DensePoly.toPolyG_nil,
      toR_eq_toK, CFieldSpec.toK_one, map_one]
    simp
  simp only [hone, div_one]
  change CFrac.am α (CPoly.toPoly p) =
    CFrac.am α (CPoly.toPoly ([CPoly.coeff p 0] : DensePoly α)) +
      CFrac.am α (CPoly.toPoly ([CCommRing.zero, CPoly.coeff p 1] : DensePoly α))
  rw [hpoly]
  simp only [toPoly_list_eq, DensePoly.toPolyG_cons, DensePoly.toPolyG_nil, toR_eq_toK,
    CFieldSpec.toK_zero, mul_zero, add_zero, map_add, map_mul]
  simp
  ring

/-- Adding a constant polynomial lifts addition through the represented polynomial fraction. -/
private theorem fieldFracP_add_singleton {α : Type u} [CField α] [CFieldSpec α]
    (p : DensePoly α) (x : α) :
    fieldFracP (CPolyEngine.add p [x]) CPoly.one =
      fieldFracP p CPoly.one + fieldFracP ([x] : DensePoly α) CPoly.one := by
  rw [fieldFracP, fieldFracP, fieldFracP]
  have hone : CFrac.am α (CPoly.toPoly (CPoly.one : DensePoly α)) = 1 := by
    change CFrac.am α (CPoly.toPoly ([CCommRing.one] : DensePoly α)) = 1
    simp only [toPoly_list_eq, DensePoly.toPolyG_cons, DensePoly.toPolyG_nil,
      toR_eq_toK, CFieldSpec.toK_one, map_one]
    simp
  simp only [LawfulCPolyEngine.toPoly_add, hone, div_one, map_add]

/-- Represented polynomial fractions with denominator one preserve addition. -/
private theorem fieldFracP_add_one {α : Type u} [CField α] [CFieldSpec α]
    (p q : DensePoly α) :
    fieldFracP (CPolyEngine.add p q) CPoly.one =
      fieldFracP p CPoly.one + fieldFracP q CPoly.one := by
  rw [fieldFracP, fieldFracP, fieldFracP]
  have hone : CFrac.am α (CPoly.toPoly (CPoly.one : DensePoly α)) = 1 := by
    change CFrac.am α (CPoly.toPoly ([CCommRing.one] : DensePoly α)) = 1
    simp only [toPoly_list_eq, DensePoly.toPolyG_cons, DensePoly.toPolyG_nil,
      toR_eq_toK, CFieldSpec.toK_one, map_one]
    simp
  simp only [LawfulCPolyEngine.toPoly_add, hone, div_one, map_add]

/-- Lower-field logs followed by the tangent log integrate a degree-at-most-one residual. -/
private theorem tangentTail_with_log_sound {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    (Dt : DensePoly α) (alpha : α) (remainder : DensePoly α)
    (result : CoefficientIntegralResult α)
    (halpha : CFieldSpec.toK alpha ≠ 0)
    (hDt : CPoly.toPoly Dt = Polynomial.C (CFieldSpec.toK alpha) *
      (1 + Polynomial.X ^ 2))
    (hdegree : ¬ 1 < CPolyEngine.cdeg remainder)
    (hresult : IsCoefficientIntegralResult (CPoly.coeff remainder 0) result) :
    towerFractionFieldDerivP Dt
        (fieldFracP ([result.rational] : DensePoly α) CPoly.one) +
      logResidueSumP Dt
        ((result.logs.map fun cv => (cv.1, [cv.2])) ++
          [(CField.div (CPoly.coeff remainder 1)
            (CCommRing.mul (CField.natCast 2) alpha), tangentBase)]) =
        fieldFracP remainder CPoly.one := by
  rw [logResidueSumP_append]
  calc
    towerFractionFieldDerivP Dt
          (fieldFracP ([result.rational] : DensePoly α) CPoly.one) +
        (logResidueSumP Dt (result.logs.map fun cv => (cv.1, [cv.2])) +
          logResidueSumP Dt
            [(CField.div (CPoly.coeff remainder 1)
              (CCommRing.mul (CField.natCast 2) alpha), tangentBase)]) =
        (towerFractionFieldDerivP Dt
          (fieldFracP ([result.rational] : DensePoly α) CPoly.one) +
          logResidueSumP Dt (result.logs.map fun cv => (cv.1, [cv.2]))) +
          logResidueSumP Dt
            [(CField.div (CPoly.coeff remainder 1)
              (CCommRing.mul (CField.natCast 2) alpha), tangentBase)] := by ring
    _ = fieldFracP ([CPoly.coeff remainder 0] : DensePoly α) CPoly.one +
          fieldFracP ([CCommRing.zero, CPoly.coeff remainder 1] : DensePoly α) CPoly.one := by
          rw [coefficientResult_lift_sound Dt (CPoly.coeff remainder 0) result hresult,
            logResidueSumP_tangentBase Dt alpha (CPoly.coeff remainder 1) halpha hDt]
    _ = fieldFracP remainder CPoly.one :=
      (fieldFracP_lowDegree_split remainder hdegree).symm

/-- If the tangent-log coefficient is zero, omitting that log preserves the tail identity. -/
private theorem tangentTail_without_log_sound {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    (Dt : DensePoly α) (alpha : α) (remainder : DensePoly α)
    (result : CoefficientIntegralResult α)
    (halpha : CFieldSpec.toK alpha ≠ 0)
    (hDt : CPoly.toPoly Dt = Polynomial.C (CFieldSpec.toK alpha) *
      (1 + Polynomial.X ^ 2))
    (hdegree : ¬ 1 < CPolyEngine.cdeg remainder)
    (hresult : IsCoefficientIntegralResult (CPoly.coeff remainder 0) result)
    (hzero : CCommRing.isZero
      (CField.div (CPoly.coeff remainder 1)
        (CCommRing.mul (CField.natCast 2) alpha)) = true) :
    towerFractionFieldDerivP Dt
        (fieldFracP ([result.rational] : DensePoly α) CPoly.one) +
      logResidueSumP Dt (result.logs.map fun cv => (cv.1, [cv.2])) =
        fieldFracP remainder CPoly.one := by
  let coefficient := CField.div (CPoly.coeff remainder 1)
    (CCommRing.mul (CField.natCast 2) alpha)
  have hcoefficient : CFieldSpec.toK coefficient = 0 := by
    change CFieldSpec.toK (CField.div (CPoly.coeff remainder 1)
      (CCommRing.mul (CField.natCast 2) alpha)) = 0
    exact (CFieldSpec.isZero_iff _).mp hzero
  have htangent : logResidueSumP Dt [(coefficient, tangentBase)] = 0 := by
    rw [logResidueSumP_cons, logResidueSumP_nil, add_zero, hcoefficient]
    simp
  have htail := tangentTail_with_log_sound Dt alpha remainder result halpha hDt hdegree hresult
  rw [logResidueSumP_append, htangent, add_zero] at htail
  exact htail

/-- Polynomial reduction followed by the lifted coefficient and tangent tail integrates the polynomial input. -/
private theorem polynomialTail_sound {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    (Dt fp reducedRemainder : DensePoly α) (polynomial : PolynomialReductionResult DensePoly α)
    (result : CoefficientIntegralResult α) (logs : List (α × DensePoly α))
    (htail : towerFractionFieldDerivP Dt
        (fieldFracP ([result.rational] : DensePoly α) CPoly.one) +
      logResidueSumP Dt logs = fieldFracP polynomial.remainder CPoly.one)
    (hreduce : CPoly.toPoly (CPolyEngine.add fp reducedRemainder) =
      Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly polynomial.antiderivative) +
        CPoly.toPoly polynomial.remainder) :
    towerFractionFieldDerivP Dt
        (fieldFracP (CPolyEngine.add polynomial.antiderivative [result.rational]) CPoly.one) +
      logResidueSumP Dt logs =
        fieldFracP fp CPoly.one + fieldFracP reducedRemainder CPoly.one := by
  have hanti : towerFractionFieldDerivP Dt
      (fieldFracP polynomial.antiderivative CPoly.one) =
        fieldFracP (CPolyEngine.add fp reducedRemainder) CPoly.one -
          fieldFracP polynomial.remainder CPoly.one := by
    simp only [fieldFracP, CPoly.toPoly_one, map_one, div_one]
    rw [towerFractionFieldDerivP, extendDeriv_algebraMap]
    change CFrac.am α
        (Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly polynomial.antiderivative)) = _
    have hmap := congrArg (CFrac.am α) hreduce
    rw [map_add] at hmap
    exact eq_sub_iff_add_eq.mpr hmap.symm
  rw [fieldFracP_add_singleton, map_add]
  calc
    (towerFractionFieldDerivP Dt (fieldFracP polynomial.antiderivative CPoly.one) +
        towerFractionFieldDerivP Dt
          (fieldFracP ([result.rational] : DensePoly α) CPoly.one)) +
        logResidueSumP Dt logs =
      towerFractionFieldDerivP Dt (fieldFracP polynomial.antiderivative CPoly.one) +
        (towerFractionFieldDerivP Dt
          (fieldFracP ([result.rational] : DensePoly α) CPoly.one) +
          logResidueSumP Dt logs) := by ring
    _ = (fieldFracP (CPolyEngine.add fp reducedRemainder) CPoly.one -
          fieldFracP polynomial.remainder CPoly.one) + fieldFracP polynomial.remainder CPoly.one := by
          rw [hanti, htail]
    _ = fieldFracP (CPolyEngine.add fp reducedRemainder) CPoly.one := by ring
    _ = fieldFracP fp CPoly.one + fieldFracP reducedRemainder CPoly.one :=
      fieldFracP_add_one fp reducedRemainder

/-- Combining the reduced rational part with a sound polynomial tail reconstructs the special input. -/
private theorem combineReducedTail_sound {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    (Dt fp b ds : DensePoly α) (alpha : α) (reduced : TangentReducedCandidate α)
    (tail : DensePoly α) (logs : List (α × DensePoly α))
    (hDt : CPoly.toPoly Dt = CPoly.toPoly ([alpha, CCommRing.zero, alpha] : DensePoly α))
    (hreduced : IsTangentReducedCandidate alpha b ds reduced)
    (htail : towerFractionFieldDerivP Dt (fieldFracP tail CPoly.one) +
      logResidueSumP Dt logs = fieldFracP fp CPoly.one + fieldFracP reduced.remainder CPoly.one) :
    CPoly.toPoly (combineRationalParts reduced.rational.1 reduced.rational.2 tail CPoly.one).2 ≠ 0 ∧
      towerFractionFieldDerivP Dt
        (fieldFracP (combineRationalParts reduced.rational.1 reduced.rational.2 tail CPoly.one).1
          (combineRationalParts reduced.rational.1 reduced.rational.2 tail CPoly.one).2) +
        logResidueSumP Dt logs = fieldFracP fp CPoly.one + fieldFracP b ds := by
  constructor
  · change CPoly.toPoly (CPolyEngine.mul reduced.rational.2 CPoly.one) ≠ 0
    rw [LawfulCPolyEngine.toPoly_mul, CPoly.toPoly_one]
    exact mul_ne_zero hreduced.1 one_ne_zero
  · rw [fieldFracP_combineRationalParts reduced.rational.1 reduced.rational.2 tail CPoly.one
      hreduced.1 (by rw [CPoly.toPoly_one]; exact one_ne_zero), map_add]
    calc
      (towerFractionFieldDerivP Dt (fieldFracP reduced.rational.1 reduced.rational.2) +
          towerFractionFieldDerivP Dt (fieldFracP tail CPoly.one)) + logResidueSumP Dt logs =
        towerFractionFieldDerivP Dt (fieldFracP reduced.rational.1 reduced.rational.2) +
          (towerFractionFieldDerivP Dt (fieldFracP tail CPoly.one) + logResidueSumP Dt logs) := by
          ring
      _ = towerFractionFieldDerivP Dt (fieldFracP reduced.rational.1 reduced.rational.2) +
          (fieldFracP fp CPoly.one + fieldFracP reduced.remainder CPoly.one) := by
          rw [htail]
      _ = fieldFracP fp CPoly.one +
          (towerFractionFieldDerivP Dt (fieldFracP reduced.rational.1 reduced.rational.2) +
            fieldFracP reduced.remainder CPoly.one) := by ring
      _ = fieldFracP fp CPoly.one + fieldFracP b ds := by
        have hderiv : towerFractionFieldDerivP Dt =
            towerFractionFieldDerivP ([alpha, CCommRing.zero, alpha] : DensePoly α) := by
          unfold towerFractionFieldDerivP
          rw [hDt]
        rw [hderiv, hreduced.2]

/-- Complete coupled solving supplies a finite encoded budget for every pole-lowering step. -/
private theorem tangentReducedCandidate_complete {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    (S : CTangentCoefficientSolver α) (solverDomain : TangentCoefficientDomain (α := α))
    [LawfulCTangentCoefficientSolver S] [CompleteCTangentCoefficientSolver S solverDomain]
    (alpha : α) (m : ℕ) (num den : DensePoly α)
    (hdomain : TangentReducedCompleteDomain S solverDomain alpha m num den) :
    ∃ fuel out, tangentReducedCandidate S fuel alpha m num den = some out := by
  induction m generalizing num den with
  | zero =>
      exact ⟨0, { rational := (CPoly.czero, CPoly.one), remainder := num }, rfl⟩
  | succ m ih =>
      simp only [TangentReducedCompleteDomain] at hdomain
      let numDiv := CPolyEuclidean.divmod num tangentBase
      let denDiv := CPolyEuclidean.divmod den tangentBase
      let a := CPoly.coeff numDiv.2 1
      let b := CPoly.coeff numDiv.2 0
      let coupling := CCommRing.mul (CField.natCast (2 * (m + 1))) alpha
      obtain ⟨hden, hsolverDomain, hsolvable, hnext⟩ := hdomain
      obtain ⟨solveFuel, c, d, hsolve⟩ := CompleteCTangentCoefficientSolver.complete
        (C := S) (domain := solverDomain) coupling a b hsolverDomain hsolvable
      let oneMinusTwoM : α := CField.sub CCommRing.one (CField.natCast (2 * (m + 1)))
      let correction := CCommRing.mul (CCommRing.mul c alpha) oneMinusTwoM
      have hrestDomain : TangentReducedCompleteDomain S solverDomain alpha m
          (CPolyEngine.sub numDiv.1 [correction]) denDiv.1 := by
        simpa only [numDiv, denDiv, a, b, coupling, oneMinusTwoM, correction] using
          (hnext solveFuel (c, d) hsolve).2
      obtain ⟨restFuel, rest, hrest⟩ := ih
        (CPolyEngine.sub numDiv.1 [correction]) denDiv.1 hrestDomain
      refine ⟨Nat.pair solveFuel restFuel, ?_, ?_⟩
      · exact {
          rational := combineRationalParts ([d, c] : DensePoly α) den
            rest.rational.1 rest.rational.2
          remainder := rest.remainder }
      ·
        simp only [tangentReducedCandidate, Nat.unpair_pair]
        rw [hden]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        change (do
          let solution ← S.solve solveFuel coupling a b
          let rest ← tangentReducedCandidate S restFuel alpha m
            (CPolyEngine.sub numDiv.1
              [CCommRing.mul (CCommRing.mul solution.1 alpha) oneMinusTwoM]) denDiv.1
          some ({
            rational := combineRationalParts ([solution.2, solution.1] : DensePoly α) den
              rest.rational.1 rest.rational.2
            remainder := rest.remainder } : TangentReducedCandidate α)) = some ({
              rational := combineRationalParts ([d, c] : DensePoly α) den
                rest.rational.1 rest.rational.2
              remainder := rest.remainder } : TangentReducedCandidate α)
        rw [hsolve]
        change (do
          let rest ← tangentReducedCandidate S restFuel alpha m
            (CPolyEngine.sub numDiv.1 [correction]) denDiv.1
          some ({
            rational := combineRationalParts ([d, c] : DensePoly α) den
              rest.rational.1 rest.rational.2
            remainder := rest.remainder } : TangentReducedCandidate α)) = some ({
              rational := combineRationalParts ([d, c] : DensePoly α) den
                rest.rational.1 rest.rational.2
              remainder := rest.remainder } : TangentReducedCandidate α)
        rw [hrest]
        rfl

/-- Finish a reduced tangent candidate through polynomial and coefficient-field integration. -/
private def finishTangentCandidate {α : Type} [CField α] [CDiffField α]
    (R : CPolynomialReduction DensePoly α) (I : CRecursiveElementaryIntegrator α)
    (Dt fp : DensePoly α) (alpha : α) (reduced : TangentReducedCandidate α)
    (polynomialFuel coefficientFuel : ℕ) : Option (IntegralResult α) := do
  let polynomialInput := CPolyEngine.add fp reduced.remainder
  let polynomial ← R.reduce .nonlinear Dt polynomialFuel polynomialInput
  if decide (1 < CPolyEngine.cdeg polynomial.remainder) then none
  else
    let constantPart := CPoly.coeff polynomial.remainder 0
    let linearPart := CPoly.coeff polynomial.remainder 1
    let coefficientResult ←
      if CCommRing.isZero constantPart then
        some ({ rational := CCommRing.zero, logs := [] } : CoefficientIntegralResult α)
      else I.integrate coefficientFuel constantPart
    let twoAlpha := CCommRing.mul (CField.natCast 2) alpha
    let logCoefficient := CField.div linearPart twoAlpha
    if !CCommRing.isZero (CDiffField.cderiv logCoefficient) then none
    else
      let polynomialAntiderivative :=
        CPolyEngine.add polynomial.antiderivative [coefficientResult.rational]
      let rational := combineRationalParts reduced.rational.1 reduced.rational.2
        polynomialAntiderivative CPoly.one
      let coefficientLogs := coefficientResult.logs.map fun cv => (cv.1, [cv.2])
      let tangentLogs :=
        if CCommRing.isZero logCoefficient then [] else [(logCoefficient, tangentBase)]
      some { rational, logs := coefficientLogs ++ tangentLogs }

/-- Build the local tangent contribution of a recursive tower-special result. -/
noncomputable def tangentTowerLocalResult (n : ℕ)
    (Dt : DensePoly (DenseFracTower (n + 1)))
    (rational : DensePoly (DenseFracTower (n + 1)) × DensePoly (DenseFracTower (n + 1)))
    (logCoefficient : DenseFracTower (n + 1)) : TowerIntegralResult (n + 1) :=
  TowerIntegralResult.ofIntegralResult Dt
    ({ rational, logs := if CCommRing.isZero logCoefficient then []
      else [(logCoefficient, tangentBase)] } : IntegralResult (DenseFracTower (n + 1)))

/-- The local tangent logarithm is genuine when its coefficient is constant. -/
theorem tangentTowerLocalResult_logsGenuine (n : ℕ)
    (Dt : DensePoly (DenseFracTower (n + 1)))
    (rational : DensePoly (DenseFracTower (n + 1)) × DensePoly (DenseFracTower (n + 1)))
    (logCoefficient : DenseFracTower (n + 1))
    (hconstant : CFieldSpec.toK (CDiffField.cderiv logCoefficient) = 0) :
    (tangentTowerLocalResult n Dt rational logCoefficient).LogsGenuine := by
  apply TowerIntegralResult.logsGenuine_ofIntegralResult
  · intro log hlog
    split at hlog
    · simp at hlog
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hlog
      subst log
      exact hconstant
  · intro log hlog
    split at hlog
    · simp at hlog
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hlog
      subst log
      exact tangentBase_toPoly_ne_zero

/-- Appending a genuine lower result preserves genuine logs in tangent reconstruction. -/
theorem tangentTowerResult_logsGenuine (n : ℕ)
    (Dt : DensePoly (DenseFracTower (n + 1)))
    (rational : DensePoly (DenseFracTower (n + 1)) × DensePoly (DenseFracTower (n + 1)))
    (logCoefficient : DenseFracTower (n + 1)) (lower : TowerIntegralResult n)
    (hconstant : CFieldSpec.toK (CDiffField.cderiv logCoefficient) = 0)
    (hlower : lower.LogsGenuine) :
    ((tangentTowerLocalResult n Dt rational logCoefficient).appendInherited lower).LogsGenuine :=
  TowerIntegralResult.logsGenuine_appendInherited _ _
    (tangentTowerLocalResult_logsGenuine n Dt rational logCoefficient hconstant) hlower

/-- Finish a reduced tangent candidate while retaining the lower stage's recursive log syntax. -/
noncomputable def finishTowerTangentCandidate (n : ℕ)
    (R : CPolynomialReduction DensePoly (DenseFracTower (n + 1)))
    (C : TowerCoefficientStage n)
    (Dt fp : DensePoly (DenseFracTower (n + 1))) (alpha : DenseFracTower (n + 1))
    (reduced : TangentReducedCandidate (DenseFracTower (n + 1)))
    (polynomialFuel coefficientFuel : ℕ) : Option (TowerIntegralResult (n + 1)) := do
  let polynomialInput := CPolyEngine.add fp reduced.remainder
  let polynomial ← R.reduce .nonlinear Dt polynomialFuel polynomialInput
  if decide (1 < CPolyEngine.cdeg polynomial.remainder) then none
  else
    let constantPart := CPoly.coeff polynomial.remainder 0
    let linearPart := CPoly.coeff polynomial.remainder 1
    let coefficientResult ←
      if CCommRing.isZero constantPart then
        some ({ rational := CCommRing.zero, logs := [] } : TowerIntegralResult n)
      else C.stage.run coefficientFuel constantPart
    let twoAlpha := CCommRing.mul (CField.natCast 2) alpha
    let logCoefficient := CField.div linearPart twoAlpha
    if !CCommRing.isZero (CDiffField.cderiv logCoefficient) then none
    else
      let polynomialAntiderivative :=
        CPolyEngine.add polynomial.antiderivative [coefficientResult.rational]
      let rational := combineRationalParts reduced.rational.1 reduced.rational.2
        polynomialAntiderivative CPoly.one
      let localResult := tangentTowerLocalResult n Dt rational logCoefficient
      some (localResult.appendInherited coefficientResult)

/-- Raw recursive hypertangent candidate that preserves a lower tower stage's logarithmic syntax. -/
noncomputable def towerTangentSpecialCandidate (n : ℕ)
    (R : CPolynomialReduction DensePoly (DenseFracTower (n + 1)))
    (C : TowerCoefficientStage n) : CTowerTangentSpecialIntegrator n where
  integrate S fuel Dt fp b ds := do
    let denominatorStage := Nat.unpair fuel
    let coupledStage := Nat.unpair denominatorStage.2
    let polynomialStage := Nat.unpair coupledStage.2
    let alpha := CPoly.coeff Dt 2
    if CCommRing.isZero alpha then none
    else if !tangentPolyEq Dt [alpha, CCommRing.zero, alpha] then none
    else
      let m : ℕ ← tangentBasePower? (α := DenseFracTower (n + 1)) denominatorStage.1 ds
      let reduced ← tangentReducedCandidate S coupledStage.1 alpha m b ds
      finishTowerTangentCandidate n R C Dt fp alpha reduced polynomialStage.1 polynomialStage.2

/-- Raw recursive hypertangent candidate generator parameterized by coefficient-field integration. -/
private def recursiveTangentSpecialCandidate {α : Type} [CField α] [CDiffField α]
    (R : CPolynomialReduction DensePoly α) (I : CRecursiveElementaryIntegrator α) :
    CTangentSpecialIntegrator α where
  integrate S fuel Dt fp b ds := do
    let denominatorStage := Nat.unpair fuel
    let coupledStage := Nat.unpair denominatorStage.2
    let polynomialStage := Nat.unpair coupledStage.2
    let alpha := CPoly.coeff Dt 2
    if CCommRing.isZero alpha then none
    else if !tangentPolyEq Dt [alpha, CCommRing.zero, alpha] then none
    else
      let m : ℕ ← tangentBasePower? (α := α) denominatorStage.1 ds
      let reduced ← tangentReducedCandidate (α := α) S coupledStage.1 alpha m b ds
      finishTangentCandidate R I Dt fp alpha reduced polynomialStage.1 polynomialStage.2

/-- Generic stagewise domain used when an arbitrary polynomial reducer is selected. -/
private def recursiveTangentCandidateManualDomain {α : Type} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    (S : CTangentCoefficientSolver α) (solverDomain : TangentCoefficientDomain (α := α))
    (R : CPolynomialReduction DensePoly α)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    (coefficientDomain : RecursiveElementaryDomain (α := α)) :
    TangentSpecialDomain α := fun Dt fp b ds =>
  let alpha := CPoly.coeff Dt 2
  CCommRing.isZero alpha = false ∧
    tangentPolyEq Dt [alpha, CCommRing.zero, alpha] = true ∧
    ∃ denominatorFuel m,
      tangentBasePower? denominatorFuel ds = some m ∧
        TangentReducedCompleteDomain S solverDomain alpha m b ds ∧
        ∀ coupledFuel reduced,
          tangentReducedCandidate S coupledFuel alpha m b ds = some reduced →
            let polynomialInput := CPolyEngine.add fp reduced.remainder
            polynomialDomain .nonlinear Dt polynomialInput ∧
              (∃ out, IsPolynomialReduction .nonlinear Dt polynomialInput out) ∧
              ∀ polynomialFuel polynomial,
                R.reduce .nonlinear Dt polynomialFuel polynomialInput = some polynomial →
                  ¬1 < CPolyEngine.cdeg polynomial.remainder ∧
                    let constantPart := CPoly.coeff polynomial.remainder 0
                    let linearPart := CPoly.coeff polynomial.remainder 1
                    (CCommRing.isZero constantPart = false →
                      coefficientDomain constantPart ∧
                        IsCoefficientElementarilyIntegrable constantPart) ∧
                    CCommRing.isZero
                      (CDiffField.cderiv
                        (CField.div linearPart
                          (CCommRing.mul (CField.natCast 2) alpha))) = true

/-- The tangent raw candidate uses the representation-independent special-result certificate. -/
private abbrev IsTangentSpecialCandidateOutput {α : Type u} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    (Dt fp b ds : DensePoly α) (out : IntegralResult α) : Prop :=
  IsMonomialSpecialResult Dt fp b ds out

/-- Complete coupled, polynomial, and coefficient stages supply a certified outer candidate. -/
private theorem recursiveTangentSpecialCandidate_complete_manual
    {α : Type} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    (S : CTangentCoefficientSolver α) (solverDomain : TangentCoefficientDomain (α := α))
    [LawfulCTangentCoefficientSolver S] [CompleteCTangentCoefficientSolver S solverDomain]
    (R : CPolynomialReduction DensePoly α)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    [LawfulCPolynomialReduction R] [CompleteCPolynomialReduction R polynomialDomain]
    (I : CRecursiveElementaryIntegrator α) (coefficientDomain : RecursiveElementaryDomain (α := α))
    [LawfulCRecursiveElementaryIntegrator I]
    [CompleteCRecursiveElementaryIntegrator I coefficientDomain]
    (Dt fp b ds : DensePoly α)
    (hdomain : recursiveTangentCandidateManualDomain S solverDomain R polynomialDomain
      coefficientDomain Dt fp b ds) :
    ∃ fuel out, (recursiveTangentSpecialCandidate R I).integrate S fuel Dt fp b ds = some out ∧
      IsTangentSpecialCandidateOutput Dt fp b ds out := by
  simp only [recursiveTangentCandidateManualDomain] at hdomain
  obtain ⟨halpha, hDt, denominatorFuel, m, hdenominator, hreducedDomain, hcontinuation⟩ :=
    hdomain
  obtain ⟨coupledFuel, reduced, hreduced⟩ := tangentReducedCandidate_complete
    S solverDomain (CPoly.coeff Dt 2) m b ds hreducedDomain
  let polynomialInput := CPolyEngine.add fp reduced.remainder
  obtain ⟨hpolynomialDomain, hpolynomialExists, hnext⟩ :=
    hcontinuation coupledFuel reduced hreduced
  obtain ⟨polynomialFuel, polynomial, hpolynomial, hpolynomialSpec⟩ :=
    CompleteCPolynomialReduction.relative_complete (C := R) (domain := polynomialDomain)
      .nonlinear Dt polynomialInput hpolynomialDomain hpolynomialExists
  obtain ⟨hdegree, hcoefficient, hlogCoefficient⟩ :=
    hnext polynomialFuel polynomial hpolynomial
  have hdegreeBool : decide (1 < CPolyEngine.cdeg polynomial.remainder) = false := by
    simp only [decide_eq_false_iff_not]
    exact hdegree
  let constantPart := CPoly.coeff polynomial.remainder 0
  by_cases hconstant : CCommRing.isZero constantPart = true
  · let coefficientResult : CoefficientIntegralResult α :=
      { rational := CCommRing.zero, logs := [] }
    let logCoefficient := CField.div (CPoly.coeff polynomial.remainder 1)
      (CCommRing.mul (CField.natCast 2) (CPoly.coeff Dt 2))
    let logs : List (α × DensePoly α) :=
      (coefficientResult.logs.map fun cv => (cv.1, [cv.2])) ++
        if CCommRing.isZero logCoefficient then [] else [(logCoefficient, tangentBase)]
    let tail := CPolyEngine.add polynomial.antiderivative [coefficientResult.rational]
    let out : IntegralResult α := {
      rational := combineRationalParts reduced.rational.1 reduced.rational.2 tail CPoly.one
      logs := logs }
    refine ⟨Nat.pair denominatorFuel
        (Nat.pair coupledFuel (Nat.pair polynomialFuel 0)), out, ?_, ?_⟩
    · dsimp [out, tail, logs, coefficientResult, logCoefficient]
      simp only [recursiveTangentSpecialCandidate, Nat.unpair_pair]
      rw [halpha, hDt, hdenominator]
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
      change (tangentReducedCandidate S coupledFuel (CPoly.coeff Dt 2) m b ds).bind
        (fun reduced => finishTangentCandidate R I Dt fp (CPoly.coeff Dt 2) reduced
          polynomialFuel 0) = _
      rw [hreduced]
      simp only [Option.bind_some, finishTangentCandidate]
      rw [hpolynomial]
      change (if decide (1 < CPolyEngine.cdeg polynomial.remainder) then none else _) = _
      rw [hdegreeBool]
      change CCommRing.isZero (CPoly.coeff polynomial.remainder 0) = true at hconstant
      rw [hconstant]
      change (if !CCommRing.isZero
          (CDiffField.cderiv
            (CField.div (CPoly.coeff polynomial.remainder 1)
              (CCommRing.mul (CField.natCast 2) (CPoly.coeff Dt 2)))) then none else _) = _
      rw [hlogCoefficient]
      rfl
    · have halphaK : CFieldSpec.toK (CPoly.coeff Dt 2) ≠ 0 := by
        intro hzero
        exact (Bool.eq_false_iff.mp halpha)
          ((CFieldSpec.isZero_iff _).mpr hzero)
      have hDtList : CPoly.toPoly Dt =
          CPoly.toPoly ([CPoly.coeff Dt 2, CCommRing.zero, CPoly.coeff Dt 2] : DensePoly α) :=
        toPoly_eq_of_tangentPolyEq Dt _ hDt
      have hDtPoly : CPoly.toPoly Dt = Polynomial.C (CFieldSpec.toK (CPoly.coeff Dt 2)) *
          (1 + Polynomial.X ^ 2) := by
        rw [hDtList, toPoly_list_eq]
        simp only [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil, toR_eq_toK,
          CFieldSpec.toK_zero, map_zero, mul_zero, add_zero, zero_add]
        ring
      have hresult : IsCoefficientIntegralResult constantPart coefficientResult := by
        dsimp [constantPart, coefficientResult]
        exact zeroCoefficientResult_sound _ ((CFieldSpec.isZero_iff _).mp hconstant)
      have hlogConstant : CFieldSpec.toK (CDiffField.cderiv logCoefficient) = 0 := by
        dsimp [logCoefficient]
        exact (CFieldSpec.isZero_iff _).mp hlogCoefficient
      have htail : towerFractionFieldDerivP Dt
          (fieldFracP ([coefficientResult.rational] : DensePoly α) CPoly.one) +
        logResidueSumP Dt logs = fieldFracP polynomial.remainder CPoly.one := by
        dsimp only [logs]
        by_cases hlog : CCommRing.isZero logCoefficient = true
        · rw [hlog]
          simp only [↓reduceIte, List.append_nil]
          simpa only [logCoefficient] using tangentTail_without_log_sound Dt (CPoly.coeff Dt 2)
            polynomial.remainder coefficientResult halphaK hDtPoly hdegree hresult (by
              simpa only [logCoefficient] using hlog)
        · have hlogFalse : CCommRing.isZero logCoefficient = false :=
            Bool.eq_false_of_not_eq_true hlog
          rw [hlogFalse]
          simp only [Bool.false_eq_true, ↓reduceIte]
          simpa only [logCoefficient] using tangentTail_with_log_sound Dt (CPoly.coeff Dt 2)
            polynomial.remainder coefficientResult halphaK hDtPoly hdegree hresult
      have hpolyTail := polynomialTail_sound Dt fp reduced.remainder polynomial coefficientResult logs
        htail hpolynomialSpec.1
      have hreducedSound := tangentReducedCandidate_sound S solverDomain (CPoly.coeff Dt 2) m
        coupledFuel b ds reduced hreducedDomain hreduced
      have hcombined := combineReducedTail_sound Dt fp b ds (CPoly.coeff Dt 2) reduced tail logs
        hDtList hreducedSound hpolyTail
      obtain ⟨hconstants, hargs⟩ := coefficientTangentLogs_genuine polynomial.remainder
        (CPoly.coeff Dt 2) coefficientResult hresult hlogConstant
      exact ⟨hcombined.1, by simpa only [out, logs] using hconstants,
        by simpa only [out, logs] using hargs, by simpa only [out, tail, logs] using hcombined.2⟩
  · have hconstantFalse : CCommRing.isZero constantPart = false := by
      exact Bool.eq_false_of_not_eq_true hconstant
    obtain ⟨hcoefficientDomain, hcoefficientIntegrable⟩ := hcoefficient hconstantFalse
    obtain ⟨coefficientFuel, coefficientResult, hcoefficientRun⟩ :=
      CompleteCRecursiveElementaryIntegrator.complete (C := I) (domain := coefficientDomain)
        constantPart hcoefficientDomain hcoefficientIntegrable
    let logCoefficient := CField.div (CPoly.coeff polynomial.remainder 1)
      (CCommRing.mul (CField.natCast 2) (CPoly.coeff Dt 2))
    let logs : List (α × DensePoly α) :=
      (coefficientResult.logs.map fun cv => (cv.1, [cv.2])) ++
        if CCommRing.isZero logCoefficient then [] else [(logCoefficient, tangentBase)]
    let tail := CPolyEngine.add polynomial.antiderivative [coefficientResult.rational]
    let out : IntegralResult α := {
      rational := combineRationalParts reduced.rational.1 reduced.rational.2 tail CPoly.one
      logs := logs }
    refine ⟨Nat.pair denominatorFuel
        (Nat.pair coupledFuel (Nat.pair polynomialFuel coefficientFuel)), out, ?_, ?_⟩
    · dsimp [out, tail, logs, logCoefficient]
      simp only [recursiveTangentSpecialCandidate, Nat.unpair_pair]
      rw [halpha, hDt, hdenominator]
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
      change (tangentReducedCandidate S coupledFuel (CPoly.coeff Dt 2) m b ds).bind
        (fun reduced => finishTangentCandidate R I Dt fp (CPoly.coeff Dt 2) reduced
          polynomialFuel coefficientFuel) = _
      rw [hreduced]
      simp only [Option.bind_some, finishTangentCandidate]
      rw [hpolynomial]
      change (if decide (1 < CPolyEngine.cdeg polynomial.remainder) then none else _) = _
      rw [hdegreeBool]
      change CCommRing.isZero (CPoly.coeff polynomial.remainder 0) = false at hconstantFalse
      rw [hconstantFalse]
      rw [hcoefficientRun]
      change (if !CCommRing.isZero
          (CDiffField.cderiv
            (CField.div (CPoly.coeff polynomial.remainder 1)
              (CCommRing.mul (CField.natCast 2) (CPoly.coeff Dt 2)))) then none else _) = _
      rw [hlogCoefficient]
      rfl
    · have halphaK : CFieldSpec.toK (CPoly.coeff Dt 2) ≠ 0 := by
        intro hzero
        exact (Bool.eq_false_iff.mp halpha)
          ((CFieldSpec.isZero_iff _).mpr hzero)
      have hDtList : CPoly.toPoly Dt =
          CPoly.toPoly ([CPoly.coeff Dt 2, CCommRing.zero, CPoly.coeff Dt 2] : DensePoly α) :=
        toPoly_eq_of_tangentPolyEq Dt _ hDt
      have hDtPoly : CPoly.toPoly Dt = Polynomial.C (CFieldSpec.toK (CPoly.coeff Dt 2)) *
          (1 + Polynomial.X ^ 2) := by
        rw [hDtList, toPoly_list_eq]
        simp only [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil, toR_eq_toK,
          CFieldSpec.toK_zero, map_zero, mul_zero, add_zero, zero_add]
        ring
      have hresult : IsCoefficientIntegralResult constantPart coefficientResult :=
        LawfulCRecursiveElementaryIntegrator.sound coefficientFuel constantPart coefficientResult
          hcoefficientRun
      have hlogConstant : CFieldSpec.toK (CDiffField.cderiv logCoefficient) = 0 := by
        dsimp [logCoefficient]
        exact (CFieldSpec.isZero_iff _).mp hlogCoefficient
      have htail : towerFractionFieldDerivP Dt
          (fieldFracP ([coefficientResult.rational] : DensePoly α) CPoly.one) +
        logResidueSumP Dt logs = fieldFracP polynomial.remainder CPoly.one := by
        dsimp only [logs]
        by_cases hlog : CCommRing.isZero logCoefficient = true
        · rw [hlog]
          simp only [↓reduceIte, List.append_nil]
          simpa only [logCoefficient] using tangentTail_without_log_sound Dt (CPoly.coeff Dt 2)
            polynomial.remainder coefficientResult halphaK hDtPoly hdegree hresult (by
              simpa only [logCoefficient] using hlog)
        · have hlogFalse : CCommRing.isZero logCoefficient = false :=
            Bool.eq_false_of_not_eq_true hlog
          rw [hlogFalse]
          simp only [Bool.false_eq_true, ↓reduceIte]
          simpa only [logCoefficient] using tangentTail_with_log_sound Dt (CPoly.coeff Dt 2)
            polynomial.remainder coefficientResult halphaK hDtPoly hdegree hresult
      have hpolyTail := polynomialTail_sound Dt fp reduced.remainder polynomial coefficientResult logs
        htail hpolynomialSpec.1
      have hreducedSound := tangentReducedCandidate_sound S solverDomain (CPoly.coeff Dt 2) m
        coupledFuel b ds reduced hreducedDomain hreduced
      have hcombined := combineReducedTail_sound Dt fp b ds (CPoly.coeff Dt 2) reduced tail logs
        hDtList hreducedSound hpolyTail
      obtain ⟨hconstants, hargs⟩ := coefficientTangentLogs_genuine polynomial.remainder
        (CPoly.coeff Dt 2) coefficientResult hresult hlogConstant
      exact ⟨hcombined.1, by simpa only [out, logs] using hconstants,
        by simpa only [out, logs] using hargs, by simpa only [out, tail, logs] using hcombined.2⟩

/-- Stagewise tangent domain with nonlinear polynomial completeness internalized to the tower reducer. -/
private def recursiveTangentCandidateDomain {α : Type} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    (S : CTangentCoefficientSolver α) (solverDomain : TangentCoefficientDomain (α := α))
    (coefficientDomain : RecursiveElementaryDomain (α := α)) : TangentSpecialDomain α :=
  fun Dt fp b ds =>
    let alpha := CPoly.coeff Dt 2
    CCommRing.isZero alpha = false ∧
      tangentPolyEq Dt [alpha, CCommRing.zero, alpha] = true ∧
      ∃ denominatorFuel m,
        tangentBasePower? denominatorFuel ds = some m ∧
          TangentReducedCompleteDomain S solverDomain alpha m b ds ∧
          ∀ coupledFuel reduced,
            tangentReducedCandidate S coupledFuel alpha m b ds = some reduced →
              let polynomialInput := CPolyEngine.add fp reduced.remainder
              ∀ polynomialFuel polynomial,
                DensePoly.towerPolynomialReduction.reduce .nonlinear Dt polynomialFuel polynomialInput =
                    some polynomial →
                  ¬1 < CPolyEngine.cdeg polynomial.remainder ∧
                    let constantPart := CPoly.coeff polynomial.remainder 0
                    let linearPart := CPoly.coeff polynomial.remainder 1
                    (CCommRing.isZero constantPart = false →
                      coefficientDomain constantPart ∧
                        IsCoefficientElementarilyIntegrable constantPart) ∧
                    CCommRing.isZero
                      (CDiffField.cderiv
                        (CField.div linearPart
                          (CCommRing.mul (CField.natCast 2) alpha))) = true

/-- The tangent monomial bridge supplies the generic polynomial obligations for the tower reducer. -/
private theorem recursiveTangentCandidateDomain_to_manual
    {α : Type} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    (S : CTangentCoefficientSolver α) (solverDomain : TangentCoefficientDomain (α := α))
    (coefficientDomain : RecursiveElementaryDomain (α := α))
    (Dt fp b ds : DensePoly α)
    (hdomain : recursiveTangentCandidateDomain S solverDomain coefficientDomain Dt fp b ds) :
    recursiveTangentCandidateManualDomain S solverDomain DensePoly.towerPolynomialReduction
      DensePoly.nonlinearPolynomialReductionDomain coefficientDomain Dt fp b ds := by
  simp only [recursiveTangentCandidateDomain, recursiveTangentCandidateManualDomain] at hdomain ⊢
  obtain ⟨halpha, hshape, denominatorFuel, m, hdenominator, hreducedDomain, hnext⟩ := hdomain
  refine ⟨halpha, hshape, denominatorFuel, m, hdenominator, hreducedDomain, ?_⟩
  intro coupledFuel reduced hrun
  let polynomialInput := CPolyEngine.add fp reduced.remainder
  have htangent : IsTangentMonomial Dt :=
    isTangentMonomial_of_tangentPolyEq Dt (CPoly.coeff Dt 2) halpha hshape
  refine ⟨htangent.nonlinearPolynomialReductionDomain,
    htangent.nonlinearReduction_exists, ?_⟩
  simpa only [polynomialInput] using hnext coupledFuel reduced hrun

/-- The tower-specialized tangent candidate eventually succeeds without external polynomial witnesses. -/
private theorem recursiveTangentSpecialCandidate_complete
    {α : Type} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    (S : CTangentCoefficientSolver α) (solverDomain : TangentCoefficientDomain (α := α))
    [LawfulCTangentCoefficientSolver S] [CompleteCTangentCoefficientSolver S solverDomain]
    (I : CRecursiveElementaryIntegrator α) (coefficientDomain : RecursiveElementaryDomain (α := α))
    [LawfulCRecursiveElementaryIntegrator I]
    [CompleteCRecursiveElementaryIntegrator I coefficientDomain]
    (Dt fp b ds : DensePoly α)
    (hdomain : recursiveTangentCandidateDomain S solverDomain coefficientDomain Dt fp b ds) :
    ∃ fuel out, (recursiveTangentSpecialCandidate DensePoly.towerPolynomialReduction I).integrate S fuel
      Dt fp b ds = some out := by
  obtain ⟨fuel, out, hrun, _certificate⟩ := recursiveTangentSpecialCandidate_complete_manual S solverDomain
    DensePoly.towerPolynomialReduction DensePoly.nonlinearPolynomialReductionDomain I coefficientDomain
    Dt fp b ds (recursiveTangentCandidateDomain_to_manual S solverDomain coefficientDomain Dt fp b ds
      hdomain)
  exact ⟨fuel, out, hrun⟩

/-- The tower-specialized raw candidate returns a complete semantic output certificate. -/
private theorem recursiveTangentSpecialCandidate_complete_certified
    {α : Type} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    (S : CTangentCoefficientSolver α) (solverDomain : TangentCoefficientDomain (α := α))
    [LawfulCTangentCoefficientSolver S] [CompleteCTangentCoefficientSolver S solverDomain]
    (I : CRecursiveElementaryIntegrator α) (coefficientDomain : RecursiveElementaryDomain (α := α))
    [LawfulCRecursiveElementaryIntegrator I]
    [CompleteCRecursiveElementaryIntegrator I coefficientDomain]
    (Dt fp b ds : DensePoly α)
    (hdomain : recursiveTangentCandidateDomain S solverDomain coefficientDomain Dt fp b ds) :
    ∃ fuel out, (recursiveTangentSpecialCandidate DensePoly.towerPolynomialReduction I).integrate S fuel
      Dt fp b ds = some out ∧ IsTangentSpecialCandidateOutput Dt fp b ds out := by
  exact recursiveTangentSpecialCandidate_complete_manual S solverDomain
    DensePoly.towerPolynomialReduction DensePoly.nonlinearPolynomialReductionDomain I coefficientDomain
    Dt fp b ds (recursiveTangentCandidateDomain_to_manual S solverDomain coefficientDomain Dt fp b ds
      hdomain)

/-- Certificate-checked recursive hypertangent special integrator. -/
def recursiveTangentSpecialIntegrator {α : Type} [CField α] [CDiffField α]
    (R : CPolynomialReduction DensePoly α) (I : CRecursiveElementaryIntegrator α) :
    CTangentSpecialIntegrator α :=
  checkedTangentSpecialIntegrator (recursiveTangentSpecialCandidate R I)

/-- Explicit acceptance domain of the recursive hypertangent special integrator. -/
def recursiveTangentSpecialDomain {α : Type} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    (S : CTangentCoefficientSolver α) (R : CPolynomialReduction DensePoly α)
    (I : CRecursiveElementaryIntegrator α) : TangentSpecialDomain α :=
  checkedTangentSpecialDomain S (recursiveTangentSpecialCandidate R I)

/-- The certified recursive hypertangent operation satisfies its denotational contract. -/
instance instLawfulCTangentSpecialIntegratorRecursive
    {α : Type} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] (S : CTangentCoefficientSolver α)
    (R : CPolynomialReduction DensePoly α) (I : CRecursiveElementaryIntegrator α) :
    LawfulCTangentSpecialIntegrator S (recursiveTangentSpecialIntegrator R I) := by
  unfold recursiveTangentSpecialIntegrator
  infer_instance

/-- The certified recursive hypertangent operation is complete on its explicit acceptance domain. -/
instance instCompleteCTangentSpecialIntegratorRecursive
    {α : Type} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] (S : CTangentCoefficientSolver α)
    (R : CPolynomialReduction DensePoly α) (I : CRecursiveElementaryIntegrator α) :
    CompleteCTangentSpecialIntegrator S (recursiveTangentSpecialIntegrator R I)
      (recursiveTangentSpecialDomain S R I) := by
  unfold recursiveTangentSpecialIntegrator recursiveTangentSpecialDomain
  infer_instance

/-- The checked tower tangent stage is complete on the reduced compositional domain. -/
instance instCompleteCTangentSpecialIntegratorRecursiveReducedDomain
    {α : Type} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    (S : CTangentCoefficientSolver α) (solverDomain : TangentCoefficientDomain (α := α))
    [LawfulCTangentCoefficientSolver S] [CompleteCTangentCoefficientSolver S solverDomain]
    (I : CRecursiveElementaryIntegrator α) (coefficientDomain : RecursiveElementaryDomain (α := α))
    [LawfulCRecursiveElementaryIntegrator I]
    [CompleteCRecursiveElementaryIntegrator I coefficientDomain] :
    CompleteCTangentSpecialIntegrator S
      (recursiveTangentSpecialIntegrator DensePoly.towerPolynomialReduction I)
      (recursiveTangentCandidateDomain S solverDomain coefficientDomain) where
  complete Dt fp b ds _res hdomain _hsden _hderiv := by
    have hdomain' := hdomain
    simp only [recursiveTangentCandidateDomain] at hdomain'
    obtain ⟨_halpha, _hshape, denominatorFuel, m, hdenominator, _hreduced, _hnext⟩ := hdomain'
    have hds : CPoly.toPoly ds ≠ 0 :=
      tangentBasePower?_den_nonzero denominatorFuel m ds hdenominator
    obtain ⟨fuel, out, hraw, hout⟩ := recursiveTangentSpecialCandidate_complete_certified
      S solverDomain I coefficientDomain Dt fp b ds hdomain
    obtain ⟨houtDen, hconstants, hargs, hidentity⟩ := hout
    have hcheck : CPoly.checkIdentity Dt out (polynomialSpecialNumerator fp b ds) ds = true := by
      apply checkIdentityP_of_field_identity Dt out (polynomialSpecialNumerator fp b ds) ds
        houtDen hds hargs
      change towerFractionFieldDerivP Dt (fieldFracP out.rational.1 out.rational.2) +
          logResidueSumP Dt out.logs = fieldFracP (polynomialSpecialNumerator fp b ds) ds
      rw [fieldFracP_polynomialSpecialNumerator fp b ds hds]
      exact hidentity
    have hdsBool : DensePoly.cisZero ds = false := by
      rw [Bool.eq_false_iff]
      intro hzero
      exact hds (by simpa only [toPoly_list_eq] using (cisZeroG_iff ds).mp hzero)
    have houtBool : DensePoly.cisZero out.rational.2 = false := by
      rw [Bool.eq_false_iff]
      intro hzero
      exact houtDen (by simpa only [toPoly_list_eq] using
        (cisZeroG_iff out.rational.2).mp hzero)
    have hargsBool : out.logs.all (fun cv => !DensePoly.cisZero cv.2) = true :=
      List.all_eq_true.mpr fun cv hcv => by
        have hzfalse : DensePoly.cisZero cv.2 = false := by
          rw [Bool.eq_false_iff]
          intro hzero
          exact hargs cv hcv (by simpa only [toPoly_list_eq] using
            (cisZeroG_iff cv.2).mp hzero)
        simpa using hzfalse
    have hconstantsBool :
        out.logs.all (fun cv => CCommRing.isZero (CDiffField.cderiv cv.1)) = true :=
      List.all_eq_true.mpr fun cv hcv =>
        (CFieldSpec.isZero_iff (CDiffField.cderiv cv.1)).mpr (hconstants cv hcv)
    refine ⟨fuel, out, ?_⟩
    simp [recursiveTangentSpecialIntegrator, checkedTangentSpecialIntegrator, hraw, hdsBool,
      houtBool, hargsBool, hconstantsBool, hcheck]

/-- Public compositional domain for the checked tower tangent-special stage. -/
def recursiveTangentSpecialCompositionalDomain {α : Type} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    (S : CTangentCoefficientSolver α) (solverDomain : TangentCoefficientDomain (α := α))
    (coefficientDomain : RecursiveElementaryDomain (α := α)) : TangentSpecialDomain α :=
  recursiveTangentCandidateDomain S solverDomain coefficientDomain

/-- The public compositional tangent domain inherits the checked-stage completeness proof. -/
instance instCompleteCTangentSpecialIntegratorRecursiveCompositionalDomain
    {α : Type} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    (S : CTangentCoefficientSolver α) (solverDomain : TangentCoefficientDomain (α := α))
    [LawfulCTangentCoefficientSolver S] [CompleteCTangentCoefficientSolver S solverDomain]
    (I : CRecursiveElementaryIntegrator α) (coefficientDomain : RecursiveElementaryDomain (α := α))
    [LawfulCRecursiveElementaryIntegrator I]
    [CompleteCRecursiveElementaryIntegrator I coefficientDomain] :
    CompleteCTangentSpecialIntegrator S
      (recursiveTangentSpecialIntegrator DensePoly.towerPolynomialReduction I)
      (recursiveTangentSpecialCompositionalDomain S solverDomain coefficientDomain) := by
  unfold recursiveTangentSpecialCompositionalDomain
  infer_instance

section GenericRischLevel

variable {α : Type} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Install a recursive tangent special stage and coupled solver into a dense Risch level. -/
def recursiveTangentRischLevel
    (R : CPolynomialReduction DensePoly α)
    (kind : PolynomialReductionKind) (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α) (I : CRecursiveElementaryIntegrator α)
    [CCanonicalRepresentation DensePoly α] : CRischLevel DensePoly α :=
  tangentRischLevel R kind raw S
    (recursiveTangentSpecialCandidate R I)

/-- Exact stage-acceptance domain of a dense recursive tangent level. -/
def recursiveTangentRischLevelCompleteDomain
    (R : CPolynomialReduction DensePoly α)
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α) (I : CRecursiveElementaryIntegrator α)
    [CCanonicalRepresentation DensePoly α] : RischLevelDomain DensePoly α :=
  tangentRischLevelCompleteDomain R kind polynomialDomain raw S
    (recursiveTangentSpecialCandidate R I)

/-- Compositional complete domain for the tower-specialized recursive tangent Risch level. -/
def recursiveTowerTangentRischLevelCompositionalDomain {α : Type} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    (raw : CNormalReduction DensePoly α) (S : CTangentCoefficientSolver α)
    (solverDomain : TangentCoefficientDomain (α := α))
    (coefficientDomain : RecursiveElementaryDomain (α := α))
    [CCanonicalRepresentation DensePoly α] : RischLevelDomain DensePoly α :=
  oneLevelRischCompleteDomain DensePoly.towerPolynomialReduction .nonlinear
    DensePoly.nonlinearPolynomialReductionDomain (tangentNormalCompleteDomain raw)
    (recursiveTangentSpecialCompositionalDomain S solverDomain coefficientDomain)

/-- The tower-specialized recursive tangent Risch level is complete on its compositional domain. -/
instance instLawfulCRischLevelRecursiveTowerTangentCompositional
    {α : Type} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)]
    (raw : CNormalReduction DensePoly α) (S : CTangentCoefficientSolver α)
    (solverDomain : TangentCoefficientDomain (α := α)) (I : CRecursiveElementaryIntegrator α)
    (coefficientDomain : RecursiveElementaryDomain (α := α))
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulCRischLevel
      (recursiveTangentRischLevel DensePoly.towerPolynomialReduction .nonlinear raw S I)
      (recursiveTowerTangentRischLevelCompositionalDomain raw S solverDomain coefficientDomain) := by
  let specialDomain := recursiveTangentSpecialCompositionalDomain S solverDomain coefficientDomain
  let special := checkedTangentMonomialCase S
    (recursiveTangentSpecialCandidate DensePoly.towerPolynomialReduction I)
  letI : LawfulCMonomialCase special := by
    dsimp [special, checkedTangentMonomialCase]
    infer_instance
  constructor
  intro fuel Dt a d res hdomain hden hrun
  change oneLevelRischCompleteDomain DensePoly.towerPolynomialReduction .nonlinear
    DensePoly.nonlinearPolynomialReductionDomain (tangentNormalCompleteDomain raw)
    specialDomain Dt a d at hdomain
  apply oneLevelRisch_sound DensePoly.towerPolynomialReduction .nonlinear fuel
    (tangentNormalReduction raw) (tangentNormalCompleteDomain raw) special Dt a d res hden hdomain.1
  simpa [recursiveTangentRischLevel, tangentRischLevel, special] using hrun

/-- The compositional recursive tangent level emits only genuine logarithmic reconstruction data. -/
instance instLawfulGenuineCRischLevelRecursiveTowerTangentCompositional
    {α : Type} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)]
    (raw : CNormalReduction DensePoly α) (S : CTangentCoefficientSolver α)
    (solverDomain : TangentCoefficientDomain (α := α)) (I : CRecursiveElementaryIntegrator α)
    (coefficientDomain : RecursiveElementaryDomain (α := α))
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulGenuineCRischLevel
      (recursiveTangentRischLevel DensePoly.towerPolynomialReduction .nonlinear raw S I)
      (recursiveTowerTangentRischLevelCompositionalDomain raw S solverDomain coefficientDomain) := by
  exact instLawfulGenuineCRischLevelCompleteDomain DensePoly.towerPolynomialReduction .nonlinear
    DensePoly.nonlinearPolynomialReductionDomain (tangentNormalReduction raw)
    (tangentNormalCompleteDomain raw)
    (recursiveTangentSpecialCompositionalDomain S solverDomain coefficientDomain)
    (checkedTangentMonomialCase S
      (recursiveTangentSpecialCandidate DensePoly.towerPolynomialReduction I))

/-- The tower-specialized recursive tangent Risch level is complete on its compositional domain. -/
instance instCompleteCRischLevelRecursiveTowerTangentCompositional
    {α : Type} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    (raw : CNormalReduction DensePoly α) (S : CTangentCoefficientSolver α)
    (solverDomain : TangentCoefficientDomain (α := α))
    [LawfulCTangentCoefficientSolver S] [CompleteCTangentCoefficientSolver S solverDomain]
    (I : CRecursiveElementaryIntegrator α) (coefficientDomain : RecursiveElementaryDomain (α := α))
    [LawfulCRecursiveElementaryIntegrator I]
    [CompleteCRecursiveElementaryIntegrator I coefficientDomain]
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    CompleteCRischLevel
      (recursiveTangentRischLevel DensePoly.towerPolynomialReduction .nonlinear raw S I)
      (recursiveTowerTangentRischLevelCompositionalDomain raw S solverDomain coefficientDomain) := by
  let specialDomain := recursiveTangentSpecialCompositionalDomain S solverDomain coefficientDomain
  let special := checkedTangentMonomialCase S
    (recursiveTangentSpecialCandidate DensePoly.towerPolynomialReduction I)
  letI : CompleteCMonomialCase special specialDomain := by
    dsimp [special, specialDomain, checkedTangentMonomialCase]
    exact instCompleteCMonomialCaseTangent S
      (recursiveTangentSpecialIntegrator DensePoly.towerPolynomialReduction I)
      (recursiveTangentSpecialCompositionalDomain S solverDomain coefficientDomain)
  letI : LawfulCMonomialCase special := by
    dsimp [special, checkedTangentMonomialCase]
    infer_instance
  unfold recursiveTangentRischLevel recursiveTowerTangentRischLevelCompositionalDomain
  exact completeCRischLevel DensePoly.towerPolynomialReduction .nonlinear
    DensePoly.nonlinearPolynomialReductionDomain (tangentNormalReduction raw)
    (tangentNormalCompleteDomain raw)
    special specialDomain

/-- A dense recursive tangent level inherits generic contract-based soundness. -/
instance instLawfulCRischLevelRecursiveTangent
    (R : CPolynomialReduction DensePoly α) [LawfulCPolynomialReduction R]
    (kind : PolynomialReductionKind) (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α) (I : CRecursiveElementaryIntegrator α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulCRischLevel (recursiveTangentRischLevel R kind raw S I)
      (oneLevelRischSoundDomain tangentNormalDomain) := by
  unfold recursiveTangentRischLevel
  infer_instance

/-- The dense recursive tangent level returns genuine elementary logarithmic terms. -/
instance instLawfulGenuineCRischLevelRecursiveTangent
    (R : CPolynomialReduction DensePoly α) [LawfulCPolynomialReduction R]
    (kind : PolynomialReductionKind) (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α) (I : CRecursiveElementaryIntegrator α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulGenuineCRischLevel (recursiveTangentRischLevel R kind raw S I)
      (oneLevelRischSoundDomain tangentNormalDomain) := by
  unfold recursiveTangentRischLevel
  infer_instance

/-- A dense recursive tangent level is lawful on its exact acceptance domain. -/
instance instLawfulCRischLevelRecursiveTangentCompleteDomain
    (R : CPolynomialReduction DensePoly α) [LawfulCPolynomialReduction R]
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α) (I : CRecursiveElementaryIntegrator α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulCRischLevel (recursiveTangentRischLevel R kind raw S I)
      (recursiveTangentRischLevelCompleteDomain R kind polynomialDomain raw S I) := by
  unfold recursiveTangentRischLevel recursiveTangentRischLevelCompleteDomain
  infer_instance

/-- The exact dense recursive tangent domain inherits genuine-output soundness. -/
instance instLawfulGenuineCRischLevelRecursiveTangentCompleteDomain
    (R : CPolynomialReduction DensePoly α) [LawfulCPolynomialReduction R]
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α) (I : CRecursiveElementaryIntegrator α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulGenuineCRischLevel (recursiveTangentRischLevel R kind raw S I)
      (recursiveTangentRischLevelCompleteDomain R kind polynomialDomain raw S I) := by
  unfold recursiveTangentRischLevel recursiveTangentRischLevelCompleteDomain
  infer_instance

/-- A dense recursive tangent level is complete on its exact acceptance domain. -/
instance instCompleteCRischLevelRecursiveTangent
    (R : CPolynomialReduction DensePoly α) [LawfulCPolynomialReduction R]
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    [CompleteCPolynomialReduction R polynomialDomain]
    (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α) (I : CRecursiveElementaryIntegrator α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    CompleteCRischLevel (recursiveTangentRischLevel R kind raw S I)
      (recursiveTangentRischLevelCompleteDomain R kind polynomialDomain raw S I) := by
  unfold recursiveTangentRischLevel recursiveTangentRischLevelCompleteDomain
  infer_instance

end GenericRischLevel

/-! ## Executable validation -/

/-- The rational coefficient `1/x`. -/
private def tangentInvX : DenseFrac ℚ :=
  CField.div (CFrac.ofPoly [1]) (CFrac.ofPoly [0, 1])

/-- The rational coefficient `-1/x²`. -/
private def tangentNegInvXSq : DenseFrac ℚ :=
  CCommRing.neg (CField.div (CFrac.ofPoly [1]) (CFrac.ofPoly [0, 0, 1]))

/-- The rational coupled solver clears denominators to find `c = 1/x`, `d = 0`. -/
example :
    (tangentRationalCoefficientSolver.solve 1 CCommRing.one tangentNegInvXSq tangentInvX).isSome = true := by
  ccompute

/-- Polynomial-only coefficient integrator used to exercise the outer tangent recursion over `ℚ(x)`. -/
private def tangentPolynomialCoefficientIntegrator :
    CRecursiveElementaryIntegrator (DenseFrac ℚ) where
  integrate _fuel c :=
    if CPolyEngine.cisZero
        (CPolyEngine.sub (CFrac.den c) (CPoly.one : DensePoly ℚ)) then
      some { rational := CFrac.ofPoly (CPoly.antiderivative (CFrac.num c)), logs := [] }
    else none

/-- Coefficient integrator returning the lower-field identity `∫1/x = log x`. -/
private def tangentLogCoefficientIntegrator :
    CRecursiveElementaryIntegrator (DenseFrac ℚ) where
  integrate _fuel c :=
    if CCommRing.isZero (CField.sub c tangentInvX) then
      some {
        rational := CCommRing.zero
        logs := [(CCommRing.one, CFrac.ofPoly [0, 1])]
      }
    else none

/-- Bronstein's three-step `(t²+1)` example numerator `t⁵+t³-x²t+1`. -/
private def tangentRecursiveExampleNumerator : DensePoly (DenseFrac ℚ) :=
  [CFrac.ofPoly [1], CFrac.ofPoly [0, 0, -1], CCommRing.zero,
    CFrac.ofPoly [1], CCommRing.zero, CFrac.ofPoly [1]]

/-- The certified recursion succeeds on the pole-order-three hypertangent example. -/
example :
    ((recursiveTangentSpecialIntegrator (α := DenseFrac ℚ)
        (DensePoly.towerPolynomialReduction (P := DensePoly) (α := DenseFrac ℚ))
        tangentPolynomialCoefficientIntegrator).integrate
      (tangentPolynomialCoefficientSolver tangentPolynomialCoupledSolver)
        (Nat.pair 4
          (Nat.pair (Nat.pair 3 (Nat.pair 3 (Nat.pair 3 0))) (Nat.pair 8 8)))
        tangentBase CPoly.czero tangentRecursiveExampleNumerator
        (CPoly.cpow tangentBase 3)).isSome = true := by
  ccompute

/-- The recursive polynomial tail lifts a logarithm returned by the coefficient field. -/
example :
    ((recursiveTangentSpecialIntegrator (α := DenseFrac ℚ)
        (DensePoly.towerPolynomialReduction (P := DensePoly) (α := DenseFrac ℚ))
        tangentLogCoefficientIntegrator).integrate
      (tangentPolynomialCoefficientSolver tangentPolynomialCoupledSolver)
        (Nat.pair 0 (Nat.pair 0 (Nat.pair 1 1)))
        tangentBase [tangentInvX] CPoly.czero CPoly.one).map
          (fun out => out.logs.length) = some 1 := by
  ccompute

/-- The polynomial stage emits `log(t²+1)` for the derivative `2t/(t²+1)`. -/
example :
    ((recursiveTangentSpecialIntegrator (α := DenseFrac ℚ)
        (DensePoly.towerPolynomialReduction (P := DensePoly) (α := DenseFrac ℚ))
        tangentPolynomialCoefficientIntegrator).integrate
      (tangentPolynomialCoefficientSolver tangentPolynomialCoupledSolver)
        (Nat.pair 1 (Nat.pair 1 (Nat.pair 2 2)))
        tangentBase [CCommRing.zero, CField.natCast 2]
        CPoly.czero CPoly.one).map (fun out => out.logs.length) = some 1 := by
  ccompute

end DeepWiki.SymbolicIntegration
