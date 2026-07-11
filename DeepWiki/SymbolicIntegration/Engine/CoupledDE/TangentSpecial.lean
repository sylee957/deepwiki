import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentCapability
import DeepWiki.SymbolicIntegration.Engine.RecursiveCoefficient
import DeepWiki.ComputableAlgebra.PolyAntiderivative

/-! # Recursive hypertangent special integration

Executable outer recursion for Bronstein's hypertangent reduced and polynomial algorithms. The raw
candidate generator is paired with the certificate-checked tangent operation before public use. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-- Finite search bounds for recursive hypertangent special integration. -/
structure TangentSpecialConfig where
  /-- Fuel for recognizing a denominator as a power of `t² + 1`. -/
  denominatorFuel : ℕ
  /-- Fuel for the final nonlinear polynomial reduction. -/
  polynomialFuel : ℕ
  /-- Degree bound supplied to each coefficient-field coupled solve. -/
  coefficientDegreeBound : ℕ

/-- The hypertangent base polynomial `t² + 1`. -/
def tangentBase : DensePoly (DenseFrac ℚ) :=
  [CCommRing.one, CCommRing.zero, CCommRing.one]

/-- Test equality of dense tower polynomials through the executable zero test. -/
private def tangentPolyEq (p q : DensePoly (DenseFrac ℚ)) : Bool :=
  CPolyEngine.cisZero (CPolyEngine.sub p q)

/-- Read a rational-function coefficient as a polynomial when its stored denominator is `1`. -/
private def tangentCoefficientPolynomial? (x : DenseFrac ℚ) : Option (DensePoly ℚ) :=
  if CPolyEngine.cisZero
      (CPolyEngine.sub (CFrac.den x) (CPoly.one : DensePoly ℚ)) then
    some (CFrac.num x)
  else none

/-- Recognize an exact power of `t² + 1`, bounded by the supplied fuel. -/
private def tangentBasePower? : ℕ → DensePoly (DenseFrac ℚ) → Option ℕ
  | 0, den =>
      if tangentPolyEq den (CPoly.one : DensePoly (DenseFrac ℚ)) then some 0 else none
  | fuel + 1, den =>
      if tangentPolyEq den (CPoly.one : DensePoly (DenseFrac ℚ)) then some 0
      else
        let qr := CPolyEuclidean.divmod den tangentBase
        if CPolyEngine.cisZero qr.2 then
          (tangentBasePower? fuel qr.1).map Nat.succ
        else none

/-- Candidate produced by reduced hypertangent recursion together with its polynomial residual. -/
private structure TangentReducedCandidate where
  /-- Rational antiderivative accumulated while lowering the pole order. -/
  rational : DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ)
  /-- Polynomial residual remaining after all powers of `t² + 1` have been removed. -/
  remainder : DensePoly (DenseFrac ℚ)

/-- Lower the `(t² + 1)` pole order by Bronstein's coupled-system recurrence. -/
private def tangentReducedCandidate (S : CTangentCoupledSolver) (degreeBound : ℕ)
    (alpha : DenseFrac ℚ) (alphaPoly : DensePoly ℚ) :
    (m : ℕ) → DensePoly (DenseFrac ℚ) → DensePoly (DenseFrac ℚ) →
      Option TangentReducedCandidate
  | 0, num, _den =>
      some { rational := (CPoly.czero, CPoly.one), remainder := num }
  | m + 1, num, den => do
      let numDiv := CPolyEuclidean.divmod num tangentBase
      let denDiv := CPolyEuclidean.divmod den tangentBase
      if !CPolyEngine.cisZero denDiv.2 then none
      else
        let a := CPoly.coeff numDiv.2 1
        let b := CPoly.coeff numDiv.2 0
        let aPoly ← tangentCoefficientPolynomial? a
        let bPoly ← tangentCoefficientPolynomial? b
        let coupling := CPolyEngine.scale (((2 * (m + 1) : ℕ) : ℚ)) alphaPoly
        let solution ← S.solve degreeBound (CPoly.czero : DensePoly ℚ) coupling
          [aPoly] [bPoly] 0
        let cPoly := CPoly.coeff solution.1 0
        let dPoly := CPoly.coeff solution.2 0
        let c : DenseFrac ℚ := CFrac.ofPoly cPoly
        let d : DenseFrac ℚ := CFrac.ofPoly dPoly
        let oneMinusTwoM : DenseFrac ℚ :=
          CField.sub CCommRing.one (CField.natCast (2 * (m + 1)))
        let correction := CCommRing.mul (CCommRing.mul c alpha) oneMinusTwoM
        let nextNum := CPolyEngine.sub numDiv.1 [correction]
        let rest ← tangentReducedCandidate S degreeBound alpha alphaPoly m nextNum denDiv.1
        let q0 : DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ) := ([d, c], den)
        some {
          rational := combineRationalParts q0.1 q0.2 rest.rational.1 rest.rational.2
          remainder := rest.remainder
        }

/-- Raw recursive hypertangent candidate generator parameterized by coefficient-field integration. -/
private def recursiveTangentSpecialCandidate (config : TangentSpecialConfig)
    (I : CRecursiveCoefficientIntegrator (DenseFrac ℚ)) : CTangentSpecialIntegrator where
  integrate S Dt fp b ds := do
    let alpha := CPoly.coeff Dt 2
    if CCommRing.isZero alpha then none
    else if !tangentPolyEq Dt [alpha, CCommRing.zero, alpha] then none
    else
      let alphaPoly ← tangentCoefficientPolynomial? alpha
      let m ← tangentBasePower? config.denominatorFuel ds
      let reduced ← tangentReducedCandidate S config.coefficientDegreeBound alpha alphaPoly m b ds
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
def recursiveTangentSpecialIntegrator (config : TangentSpecialConfig)
    (I : CRecursiveCoefficientIntegrator (DenseFrac ℚ)) : CTangentSpecialIntegrator :=
  checkedTangentSpecialIntegrator (recursiveTangentSpecialCandidate config I)

/-- Explicit acceptance domain of the recursive hypertangent special integrator. -/
def recursiveTangentSpecialDomain (S : CTangentCoupledSolver) (config : TangentSpecialConfig)
    (I : CRecursiveCoefficientIntegrator (DenseFrac ℚ)) : TangentSpecialDomain :=
  checkedTangentSpecialDomain S (recursiveTangentSpecialCandidate config I)

/-- The certified recursive hypertangent operation satisfies its denotational contract. -/
instance instLawfulCTangentSpecialIntegratorRecursive (S : CTangentCoupledSolver)
    (config : TangentSpecialConfig) (I : CRecursiveCoefficientIntegrator (DenseFrac ℚ)) :
    LawfulCTangentSpecialIntegrator S (recursiveTangentSpecialIntegrator config I) := by
  unfold recursiveTangentSpecialIntegrator
  infer_instance

/-- The certified recursive hypertangent operation is complete on its explicit acceptance domain. -/
instance instCompleteCTangentSpecialIntegratorRecursive (S : CTangentCoupledSolver)
    (config : TangentSpecialConfig) (I : CRecursiveCoefficientIntegrator (DenseFrac ℚ)) :
    CompleteCTangentSpecialIntegrator S (recursiveTangentSpecialIntegrator config I)
      (recursiveTangentSpecialDomain S config I) := by
  unfold recursiveTangentSpecialIntegrator recursiveTangentSpecialDomain
  infer_instance

/-! ## Executable validation -/

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
    ((recursiveTangentSpecialIntegrator
        { denominatorFuel := 4, polynomialFuel := 8, coefficientDegreeBound := 3 }
        tangentPolynomialCoefficientIntegrator).integrate
      tangentCoupledSolver tangentBase CPoly.czero tangentRecursiveExampleNumerator
        (CPoly.cpow tangentBase 3)).isSome = true := by
  ccompute

/-- The polynomial stage emits `log(t²+1)` for the derivative `2t/(t²+1)`. -/
example :
    ((recursiveTangentSpecialIntegrator
        { denominatorFuel := 1, polynomialFuel := 2, coefficientDegreeBound := 1 }
        tangentPolynomialCoefficientIntegrator).integrate
      tangentCoupledSolver tangentBase [CCommRing.zero, CField.natCast 2]
        CPoly.czero CPoly.one).map (fun out => out.logs.length) = some 1 := by
  ccompute

end DeepWiki.SymbolicIntegration
