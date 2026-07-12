import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentCapability
import DeepWiki.SymbolicIntegration.Engine.RecursiveCoefficient
import DeepWiki.ComputableAlgebra.PolyAntiderivative

/-! # Recursive hypertangent special integration

Executable outer recursion for Bronstein's hypertangent reduced and polynomial algorithms. The raw
candidate generator is paired with the certificate-checked tangent operation before public use. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

universe u

/-- Finite search bounds for recursive hypertangent special integration. -/
structure TangentSpecialConfig where
  /-- Fuel for recognizing a denominator as a power of `t² + 1`. -/
  denominatorFuel : ℕ
  /-- Fuel for the final nonlinear polynomial reduction. -/
  polynomialFuel : ℕ
  /-- Degree bound supplied to each coefficient-field coupled solve. -/
  coefficientDegreeBound : ℕ

/-- The hypertangent base polynomial `t² + 1`. -/
def tangentBase {α : Type u} [CCommRing α] : DensePoly α :=
  [CCommRing.one, CCommRing.zero, CCommRing.one]

/-- Test equality of dense tower polynomials through the executable zero test. -/
private def tangentPolyEq {α : Type u} [CCommRing α] (p q : DensePoly α) : Bool :=
  CPolyEngine.cisZero (CPolyEngine.sub p q)

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

/-- Candidate produced by reduced hypertangent recursion together with its polynomial residual. -/
private structure TangentReducedCandidate (α : Type u) where
  /-- Rational antiderivative accumulated while lowering the pole order. -/
  rational : DensePoly α × DensePoly α
  /-- Polynomial residual remaining after all powers of `t² + 1` have been removed. -/
  remainder : DensePoly α

/-- Lower the `(t² + 1)` pole order by Bronstein's coupled-system recurrence. -/
private def tangentReducedCandidate {α : Type u} [CField α] [CDiffField α]
    (S : CTangentCoefficientSolver α) (degreeBound : ℕ) (alpha : α) :
    (m : ℕ) → DensePoly α → DensePoly α → Option (TangentReducedCandidate α)
  | 0, num, _den =>
      some { rational := (CPoly.czero, CPoly.one), remainder := num }
  | m + 1, num, den => do
      let numDiv := CPolyEuclidean.divmod num tangentBase
      let denDiv := CPolyEuclidean.divmod den tangentBase
      if !CPolyEngine.cisZero denDiv.2 then none
      else
        let a := CPoly.coeff numDiv.2 1
        let b := CPoly.coeff numDiv.2 0
        let coupling := CCommRing.mul (CField.natCast (2 * (m + 1))) alpha
        let solution ← S.solve degreeBound coupling a b
        let c := solution.1
        let d := solution.2
        let oneMinusTwoM : α :=
          CField.sub CCommRing.one (CField.natCast (2 * (m + 1)))
        let correction := CCommRing.mul (CCommRing.mul c alpha) oneMinusTwoM
        let nextNum := CPolyEngine.sub numDiv.1 [correction]
        let rest ← tangentReducedCandidate S degreeBound alpha m nextNum denDiv.1
        let q0 : DensePoly α × DensePoly α := ([d, c], den)
        some {
          rational := combineRationalParts q0.1 q0.2 rest.rational.1 rest.rational.2
          remainder := rest.remainder
        }

/-- Raw recursive hypertangent candidate generator parameterized by coefficient-field integration. -/
private def recursiveTangentSpecialCandidate {α : Type} [CField α] [CDiffField α]
    (config : TangentSpecialConfig) (I : CRecursiveCoefficientIntegrator α) :
    CTangentSpecialIntegrator α where
  integrate S Dt fp b ds := do
    let alpha := CPoly.coeff Dt 2
    if CCommRing.isZero alpha then none
    else if !tangentPolyEq Dt [alpha, CCommRing.zero, alpha] then none
    else
      let m : ℕ ← tangentBasePower? (α := α) config.denominatorFuel ds
      let reduced ← tangentReducedCandidate (α := α) S config.coefficientDegreeBound alpha m b ds
      let polynomialInput := CPolyEngine.add fp reduced.remainder
      let polynomial := DensePoly.cPolyReduceTower Dt config.polynomialFuel polynomialInput
      if decide (1 < CPolyEngine.cdeg polynomial.2) then none
      else
        let constantPart := CPoly.coeff polynomial.2 0
        let linearPart := CPoly.coeff polynomial.2 1
        let constantAntiderivative ←
          if CCommRing.isZero constantPart then some CCommRing.zero
          else I.integrate constantPart
        let twoAlpha := CCommRing.mul (CField.natCast 2) alpha
        let logCoefficient := CField.div linearPart twoAlpha
        if !CCommRing.isZero (CDiffField.cderiv logCoefficient) then none
        else
          let polynomialAntiderivative :=
            CPolyEngine.add polynomial.1 [constantAntiderivative]
          let rational := combineRationalParts reduced.rational.1 reduced.rational.2
            polynomialAntiderivative CPoly.one
          let logs :=
            if CCommRing.isZero logCoefficient then [] else [(logCoefficient, tangentBase)]
          some { rational, logs }

/-- Certificate-checked recursive hypertangent special integrator. -/
def recursiveTangentSpecialIntegrator {α : Type} [CField α] [CDiffField α]
    (config : TangentSpecialConfig) (I : CRecursiveCoefficientIntegrator α) :
    CTangentSpecialIntegrator α :=
  checkedTangentSpecialIntegrator (recursiveTangentSpecialCandidate config I)

/-- Explicit acceptance domain of the recursive hypertangent special integrator. -/
def recursiveTangentSpecialDomain {α : Type} [CField α] [CFieldSpec α]
    [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    (S : CTangentCoefficientSolver α) (config : TangentSpecialConfig)
    (I : CRecursiveCoefficientIntegrator α) : TangentSpecialDomain α :=
  checkedTangentSpecialDomain S (recursiveTangentSpecialCandidate config I)

/-- The certified recursive hypertangent operation satisfies its denotational contract. -/
instance instLawfulCTangentSpecialIntegratorRecursive
    {α : Type} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] (S : CTangentCoefficientSolver α)
    (config : TangentSpecialConfig) (I : CRecursiveCoefficientIntegrator α) :
    LawfulCTangentSpecialIntegrator S (recursiveTangentSpecialIntegrator config I) := by
  unfold recursiveTangentSpecialIntegrator
  infer_instance

/-- The certified recursive hypertangent operation is complete on its explicit acceptance domain. -/
instance instCompleteCTangentSpecialIntegratorRecursive
    {α : Type} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] (S : CTangentCoefficientSolver α)
    (config : TangentSpecialConfig) (I : CRecursiveCoefficientIntegrator α) :
    CompleteCTangentSpecialIntegrator S (recursiveTangentSpecialIntegrator config I)
      (recursiveTangentSpecialDomain S config I) := by
  unfold recursiveTangentSpecialIntegrator recursiveTangentSpecialDomain
  infer_instance

section GenericRischLevel

variable {α : Type} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Install a recursive tangent special stage and coupled solver into a dense Risch level. -/
def recursiveTangentRischLevel
    (R : CPolynomialReduction DensePoly α)
    (kind : PolynomialReductionKind) (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α)
    (config : TangentSpecialConfig) (I : CRecursiveCoefficientIntegrator α)
    [CCanonicalRepresentation DensePoly α] : CRischLevel DensePoly α :=
  tangentRischLevel R kind raw S
    (recursiveTangentSpecialCandidate config I)

/-- Exact stage-acceptance domain of a dense recursive tangent level. -/
def recursiveTangentRischLevelCompleteDomain
    (R : CPolynomialReduction DensePoly α)
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α)
    (config : TangentSpecialConfig) (I : CRecursiveCoefficientIntegrator α)
    [CCanonicalRepresentation DensePoly α] : RischLevelDomain DensePoly α :=
  tangentRischLevelCompleteDomain R kind polynomialDomain raw S
    (recursiveTangentSpecialCandidate config I)

/-- A dense recursive tangent level inherits generic contract-based soundness. -/
instance instLawfulCRischLevelRecursiveTangent
    (R : CPolynomialReduction DensePoly α) [LawfulCPolynomialReduction R]
    (kind : PolynomialReductionKind) (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α)
    (config : TangentSpecialConfig) (I : CRecursiveCoefficientIntegrator α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulCRischLevel (recursiveTangentRischLevel R kind raw S config I)
      (oneLevelRischSoundDomain tangentNormalDomain) := by
  unfold recursiveTangentRischLevel
  infer_instance

/-- A dense recursive tangent level is lawful on its exact acceptance domain. -/
instance instLawfulCRischLevelRecursiveTangentCompleteDomain
    (R : CPolynomialReduction DensePoly α) [LawfulCPolynomialReduction R]
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α)
    (config : TangentSpecialConfig) (I : CRecursiveCoefficientIntegrator α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulCRischLevel (recursiveTangentRischLevel R kind raw S config I)
      (recursiveTangentRischLevelCompleteDomain R kind polynomialDomain raw S config I) := by
  unfold recursiveTangentRischLevel recursiveTangentRischLevelCompleteDomain
  infer_instance

/-- A dense recursive tangent level is complete on its exact acceptance domain. -/
instance instCompleteCRischLevelRecursiveTangent
    (R : CPolynomialReduction DensePoly α) [LawfulCPolynomialReduction R]
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    [CompleteCPolynomialReduction R polynomialDomain]
    (raw : CNormalReduction DensePoly α)
    (S : CTangentCoefficientSolver α)
    (config : TangentSpecialConfig) (I : CRecursiveCoefficientIntegrator α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    CompleteCRischLevel (recursiveTangentRischLevel R kind raw S config I)
      (recursiveTangentRischLevelCompleteDomain R kind polynomialDomain raw S config I) := by
  unfold recursiveTangentRischLevel recursiveTangentRischLevelCompleteDomain
  infer_instance

/-- Install a recursive tangent special stage and coupled solver into a sparse Risch level. -/
def sparseRecursiveTangentRischLevel
    (R : CPolynomialReduction CPoly.SparsePoly α)
    (kind : PolynomialReductionKind) (raw : CNormalReduction CPoly.SparsePoly α)
    (S : CTangentCoefficientSolver α)
    (config : TangentSpecialConfig) (I : CRecursiveCoefficientIntegrator α)
    [CCanonicalRepresentation CPoly.SparsePoly α] :
    CRischLevel CPoly.SparsePoly α :=
  sparseTangentRischLevel R kind raw S
    (recursiveTangentSpecialCandidate config I)

/-- Exact transported stage-acceptance domain of the selected sparse recursive tangent level. -/
def sparseRecursiveTangentRischLevelCompleteDomain
    (R : CPolynomialReduction CPoly.SparsePoly α)
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain CPoly.SparsePoly α)
    (raw : CNormalReduction CPoly.SparsePoly α)
    (S : CTangentCoefficientSolver α)
    (config : TangentSpecialConfig) (I : CRecursiveCoefficientIntegrator α)
    [CCanonicalRepresentation CPoly.SparsePoly α] :
    RischLevelDomain CPoly.SparsePoly α :=
  sparseTangentRischLevelCompleteDomain R kind polynomialDomain raw S
    (recursiveTangentSpecialCandidate config I)

/-- The selected sparse recursive tangent level inherits soundness through representation transport. -/
instance instLawfulCRischLevelSparseRecursiveTangent
    (R : CPolynomialReduction CPoly.SparsePoly α) [LawfulCPolynomialReduction R]
    (kind : PolynomialReductionKind)
    (raw : CNormalReduction CPoly.SparsePoly α)
    (S : CTangentCoefficientSolver α)
    (config : TangentSpecialConfig) (I : CRecursiveCoefficientIntegrator α)
    [CCanonicalRepresentation CPoly.SparsePoly α]
    [LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := α)] :
    LawfulCRischLevel (sparseRecursiveTangentRischLevel R kind raw S config I)
      (oneLevelRischSoundDomain
        (checkedNormalReductionDomain (P := CPoly.SparsePoly) (α := α))) := by
  unfold sparseRecursiveTangentRischLevel
  infer_instance

/-- The selected sparse recursive tangent level is lawful on its transported acceptance domain. -/
instance instLawfulCRischLevelSparseRecursiveTangentCompleteDomain
    (R : CPolynomialReduction CPoly.SparsePoly α) [LawfulCPolynomialReduction R]
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain CPoly.SparsePoly α)
    (raw : CNormalReduction CPoly.SparsePoly α)
    (S : CTangentCoefficientSolver α)
    (config : TangentSpecialConfig) (I : CRecursiveCoefficientIntegrator α)
    [CCanonicalRepresentation CPoly.SparsePoly α]
    [LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := α)] :
    LawfulCRischLevel (sparseRecursiveTangentRischLevel R kind raw S config I)
      (sparseRecursiveTangentRischLevelCompleteDomain
        R kind polynomialDomain raw S config I) := by
  unfold sparseRecursiveTangentRischLevel sparseRecursiveTangentRischLevelCompleteDomain
  infer_instance

/-- The selected sparse recursive tangent level is complete on its transported acceptance domain. -/
instance instCompleteCRischLevelSparseRecursiveTangent
    (R : CPolynomialReduction CPoly.SparsePoly α) [LawfulCPolynomialReduction R]
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain CPoly.SparsePoly α)
    [CompleteCPolynomialReduction R polynomialDomain]
    (raw : CNormalReduction CPoly.SparsePoly α)
    (S : CTangentCoefficientSolver α)
    (config : TangentSpecialConfig) (I : CRecursiveCoefficientIntegrator α)
    [CCanonicalRepresentation CPoly.SparsePoly α]
    [LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := α)] :
    CompleteCRischLevel (sparseRecursiveTangentRischLevel R kind raw S config I)
      (sparseRecursiveTangentRischLevelCompleteDomain
        R kind polynomialDomain raw S config I) := by
  unfold sparseRecursiveTangentRischLevel sparseRecursiveTangentRischLevelCompleteDomain
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
    CRecursiveCoefficientIntegrator (DenseFrac ℚ) where
  integrate c :=
    if CPolyEngine.cisZero
        (CPolyEngine.sub (CFrac.den c) (CPoly.one : DensePoly ℚ)) then
      some (CFrac.ofPoly (CPoly.antiderivative (CFrac.num c)))
    else none

/-- Bronstein's three-step `(t²+1)` example numerator `t⁵+t³-x²t+1`. -/
private def tangentRecursiveExampleNumerator : DensePoly (DenseFrac ℚ) :=
  [CFrac.ofPoly [1], CFrac.ofPoly [0, 0, -1], CCommRing.zero,
    CFrac.ofPoly [1], CCommRing.zero, CFrac.ofPoly [1]]

/-- The certified recursion succeeds on the pole-order-three hypertangent example. -/
example :
    ((recursiveTangentSpecialIntegrator (α := DenseFrac ℚ)
        { denominatorFuel := 4, polynomialFuel := 8, coefficientDegreeBound := 3 }
        tangentPolynomialCoefficientIntegrator).integrate
      (tangentPolynomialCoefficientSolver tangentPolynomialCoupledSolver)
        tangentBase CPoly.czero tangentRecursiveExampleNumerator
        (CPoly.cpow tangentBase 3)).isSome = true := by
  ccompute

/-- The polynomial stage emits `log(t²+1)` for the derivative `2t/(t²+1)`. -/
example :
    ((recursiveTangentSpecialIntegrator (α := DenseFrac ℚ)
        { denominatorFuel := 1, polynomialFuel := 2, coefficientDegreeBound := 1 }
        tangentPolynomialCoefficientIntegrator).integrate
      (tangentPolynomialCoefficientSolver tangentPolynomialCoupledSolver)
        tangentBase [CCommRing.zero, CField.natCast 2]
        CPoly.czero CPoly.one).map (fun out => out.logs.length) = some 1 := by
  ccompute

end DeepWiki.SymbolicIntegration
