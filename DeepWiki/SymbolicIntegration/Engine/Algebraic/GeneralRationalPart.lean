import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalWellFounded
import DeepWiki.SymbolicIntegration.Engine.Algebraic.IntegralBasisFull

/-! # Rational part of the algebraic-function integral

The algebraic Hermite reduction over the integral basis: reduce an algebraic-function integrand to one
with only simple finite poles, accumulating the rational part `v`. For the decoupled (diagonal)
hyperelliptic case `y² = ρ` this is the `radDeriv`-validated Case-3 reduction; for genus-0 curves the
rational part is the whole integral. Worked on the cusp `y² = x³` (`∫ y dx`, `∫ x·y dx`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem DensePoly

/-! ### The cusp `y² = x³` (genus 0): the integral basis bounds the finite poles

`f = y² − x³` over `ℚ(x)`, with `integralBasis f = [1, y/x]`: a function has no finite poles iff its
coordinates over `[1, y/x]` are polynomials in `x`. Both `y` and `x·y` have polynomial coordinates, so
with genus 0 their integrals are purely rational. -/

/-- The cusp radicand `ρ = x³ ∈ ℚ(x)` (so `y² = ρ`), for the diagonal radical derivation `radDeriv 2 ρ`. -/
def gcuspRho : DenseFrac ℚ := CFrac.ofPoly [0, 0, 0, 1]

/-- The cusp integral basis is `[1, y/x]`, integral and maximal: `(y/x)² = x` and `isMaximalOrder` holds,
the maximal-order datum the algebraic Hermite reduction consumes. -/
theorem gcusp_integralBasis_eq :
    (cisZero (csub ((integralBasis cuspF).getD 1 [])
          [CCommRing.zero, CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)])
      && cisZero (csub ((integralBasis cuspF).getD 0 []) [CCommRing.one])
      && cisZero (csub (CPoly.mulMod cuspF ((integralBasis cuspF).getD 1 [])
            ((integralBasis cuspF).getD 1 [])) [CFrac.ofPoly [0, 1]])
      && isMaximalOrder cuspF (integralBasis cuspF)) = true := by native_decide

/-! ### Target 1: `∫ y dx = (2/5)·x·y` on `y² = x³`

The integrand is `y = [0, 1]`; the rational part is `v = (2/5)·x·y = [0, (2/5)x]`, with
`radDeriv 2 (x³) v = y`. -/

/-- The rational part of `∫ y dx`: `v = (2/5)·x·y` as `RadElem (DenseFrac ℚ)` `[0, (2/5)x]`. -/
def gcuspVY : RadElem (DenseFrac ℚ) := [CCommRing.zero, CFrac.ofPoly [0, 2/5]]

/-- The integrand `y = [0, 1]` as `RadElem (DenseFrac ℚ)`. -/
def gcuspY : RadElem (DenseFrac ℚ) := [CCommRing.zero, CCommRing.one]

/-- `∫ y dx = (2/5)·x·y` on `y² = x³`: the diagonal radical derivation `radDeriv 2 (x³)` of the rational
part `v = (2/5)·x·y` equals the integrand `y`, via `DensePoly.cisZero` of `radDeriv 2 ρ v − y`. -/
theorem cusp_intY_radDeriv :
    DensePoly.cisZero (DensePoly.csub (radDeriv 2 gcuspRho gcuspVY) gcuspY) = true := by native_decide

/-! #### Target 1, derived from the integrand by the Case-3 `C/y` driver

Since `y·y = ρ`, the integrand `y` equals `ρ/y = x³/y`, a `C/y` Case-3 form with `C = ρ = x³`. The
driver `radIntegrateCase3Wf cderiv ρ g C` (`g = ½ρ' = (3/2)x²`) lowers `deg C`, returning `Crem = 0`
(fully rational) and `vNum = (2/5)x⁴`, so `v = vNum/y = (2/5)x·y`. -/

/-- The cusp radicand `ρ = x³` as a `ℚ[x]` polynomial, for the Case-3 driver. -/
def gcuspRhoP : DensePoly ℚ := [0, 0, 0, 1]

/-- `g = ½ρ' = (3/2)x²` over `ℚ[x]`, the diagonal `(ρ/y)' = g/y`. -/
def gcuspGP : DensePoly ℚ := cscale (1/2 : ℚ) (cderiv gcuspRhoP)

/-- The Case-3 driver run on `∫ y dx = ∫ x³/y` (`C = ρ = x³`): `radIntegrateCase3Wf cderiv ρ g ρ =
(Crem, vNum)`, expected `(0, (2/5)x⁴)`. -/
def gcuspYRun : DensePoly ℚ × DensePoly ℚ := radIntegrateCase3Wf cderiv gcuspRhoP gcuspGP gcuspRhoP

/-- The driver derives `Crem = 0` and `vNum = (2/5)x⁴` for `∫ y dx`: the Case-3 `C/y` degree-lowering on
`C = x³` returns a zero leftover residual and rational-part numerator `vNum = (2/5)x⁴`, via `cisZero` of
`Crem` and of `vNum − (2/5)x⁴`. -/
theorem cusp_intY_driver_eq :
    (cisZero gcuspYRun.1 && cisZero (csub gcuspYRun.2 [0, 0, 0, 0, 2/5])) = true := by native_decide

/-- The driver-produced rational part `v = vNum/y` lifted to `RadElem (DenseFrac ℚ)` `[0, vNum/ρ]`; with
`vNum = (2/5)x⁴`, `ρ = x³` this is `[0, (2/5)x]`. -/
def gcuspVYlift : RadElem (DenseFrac ℚ) :=
  [CCommRing.zero, CField.div (CFrac.ofPoly gcuspYRun.2) gcuspRho]

/-- The integrand's rational part `(C − Crem)/y` lifted to `RadElem (DenseFrac ℚ)` `[0, (C − Crem)/ρ]`; with
`C = x³`, `Crem = 0` this is `[0, 1] = y`. -/
def gcuspYRatLift : RadElem (DenseFrac ℚ) :=
  [CCommRing.zero, CField.div (CFrac.ofPoly (csub gcuspRhoP gcuspYRun.1)) gcuspRho]

/-- The Case-3 driver integrates `∫ y dx` end-to-end: `radDeriv 2 (x³)` of the driver-produced rational
part `v = (2/5)x·y` equals the integrand's rational part `(C − Crem)/y = y`, via `DensePoly.cisZero` of the
difference. -/
theorem cusp_intY_driver_integrates :
    DensePoly.cisZero (DensePoly.csub (radDeriv 2 gcuspRho gcuspVYlift) gcuspYRatLift) = true := by native_decide

/-- `∫ y dx` is fully rational: the Case-3 reduction leaves `Crem = 0`, so there is no simple-pole
residual and no logarithmic part, via `cisZero gcuspYRun.1`. -/
theorem cusp_intY_fully_rational : cisZero gcuspYRun.1 = true := by native_decide

/-! ### A second genus-0 target: `∫ x·y dx = (2/7)·x²·y` on `y² = x³`

The integrand `x·y = [0, x]` has rational part `v = (2/7)·x²·y = [0, (2/7)x²]`. Derived from the
integrand: `xy = x⁴/y`, so the Case-3 driver on `C = x⁴` returns `(Crem = 0, vNum = (2/7)x⁵)`. -/

/-- The rational part of `∫ x·y dx`: `v = (2/7)·x²·y` as `RadElem (DenseFrac ℚ)` `[0, (2/7)x²]`. -/
def gcuspVXY : RadElem (DenseFrac ℚ) := [CCommRing.zero, CFrac.ofPoly [0, 0, 2/7]]

/-- The integrand `x·y = [0, x]` as `RadElem (DenseFrac ℚ)`. -/
def gcuspXY : RadElem (DenseFrac ℚ) := [CCommRing.zero, CFrac.ofPoly [0, 1]]

/-- `∫ x·y dx = (2/7)·x²·y` on `y² = x³`: the diagonal radical derivation `radDeriv 2 (x³)` of
`v = (2/7)·x²·y` equals `x·y`, via `DensePoly.cisZero` of `radDeriv 2 ρ v − xy`. -/
theorem cusp_intXY_radDeriv :
    DensePoly.cisZero (DensePoly.csub (radDeriv 2 gcuspRho gcuspVXY) gcuspXY) = true := by native_decide

/-- The Case-3 driver run on `∫ x·y dx = ∫ x⁴/y` (`C = x⁴`): `radIntegrateCase3Wf cderiv ρ g (x⁴) =
(Crem, vNum)`, expected `(0, (2/7)x⁵)`. -/
def gcuspXYRun : DensePoly ℚ × DensePoly ℚ := radIntegrateCase3Wf cderiv gcuspRhoP gcuspGP [0, 0, 0, 0, 1]

/-- The driver derives `Crem = 0` and `vNum = (2/7)x⁵` for `∫ x·y dx`: the Case-3 `C/y` degree-lowering on
`C = x⁴` returns a zero leftover and rational-part numerator `vNum = (2/7)x⁵`, via `cisZero` of `Crem`
and of `vNum − (2/7)x⁵`. -/
theorem cusp_intXY_driver_eq :
    (cisZero gcuspXYRun.1 && cisZero (csub gcuspXYRun.2 [0, 0, 0, 0, 0, 2/7])) = true := by
  native_decide

/-- The driver-produced rational part `v = vNum/y` for `∫ x·y dx`, lifted to `RadElem (DenseFrac ℚ)`:
`[0, vNum/ρ] = [0, (2/7)x²]`. -/
def gcuspVXYlift : RadElem (DenseFrac ℚ) :=
  [CCommRing.zero, CField.div (CFrac.ofPoly gcuspXYRun.2) gcuspRho]

/-- The integrand's rational part `(x⁴ − Crem)/y` lifted to `RadElem (DenseFrac ℚ)` `[0, (x⁴ − Crem)/ρ]`;
with `Crem = 0` this is `[0, x] = x·y`. -/
def gcuspXYRatLift : RadElem (DenseFrac ℚ) :=
  [CCommRing.zero, CField.div (CFrac.ofPoly (csub [0, 0, 0, 0, 1] gcuspXYRun.1)) gcuspRho]

/-- The Case-3 driver integrates `∫ x·y dx` end-to-end: `radDeriv 2 (x³)` of the driver-produced
`v = (2/7)x²·y` equals the integrand `x·y`, via `DensePoly.cisZero` of the difference. -/
theorem cusp_intXY_driver_integrates :
    DensePoly.cisZero (DensePoly.csub (radDeriv 2 gcuspRho gcuspVXYlift) gcuspXYRatLift) = true := by native_decide

/-! ### Related pieces

The reduction above is the decoupled (diagonal) hyperelliptic case, covering all `y² = ρ` curves. The
non-diagonal general carrier (a coupled `n×n` congruence over `K(x)/(V)`, solved by Cramer's rule with
the inputs `integralBasis f`, `CPoly.mulMod`/`trace`/`CPoly.reduceMod`, and the basis derivatives) and the simple-pole
residual feeding the logarithmic part for genus `> 0` (residues via `genResidueResultant` → divisors →
torsion) are the continuations; the rational part here is complete for genus 0. -/

end DeepWiki.SymbolicIntegration
