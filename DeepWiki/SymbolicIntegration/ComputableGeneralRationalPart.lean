import DeepWiki.SymbolicIntegration.ComputableRadicalWellFounded
import DeepWiki.SymbolicIntegration.ComputableIntegralBasisFull

/-! # The general-curve RATIONAL PART of the algebraic-function integral: the algebraic Hermite
reduction over the INTEGRAL BASIS (Trager, *Integration of Algebraic Functions*, Ch. 4 §2 "Algebraic
functions", p. 43–50)

The transcendental Risch engine integrates elementary *transcendental* functions; the algebraic axis
(`ComputableRadical*`, `ComputableAlgFunctionField`, `ComputableIntegralBasisFull`) opened the
**algebraic** case — the radical carrier `RadExt` with its diagonal `(ρ/y)'` derivation, the general
carrier `K(x)[y]/(f)` with `afMul`/`trace`, and the **integral basis** `integralBasis f` (the
Ford–Zassenhaus Round-2 maximal order: the curve's functions with no finite poles). This file assembles
those into the **algebraic Hermite reduction** of Trager Ch. 4 §2: reduce an algebraic-function
integrand to one with only **simple finite poles**, accumulating the **rational part** `v`. For a
**genus-0** curve the rational part IS the whole (elementary, rational) integral.

**Trager's algorithm (Ch. 4 §2, eq. 3–11).** Write the integrand over the integral basis `[w₁,…,wₙ]`:
`Σ Aᵢ wᵢ / D(z)` (no finite poles ⟺ the `Aᵢ/D` are proper, the integral basis bounding the poles).
Squarefree-factor the denominator `D = ∏ Dᵢ^i`, take `V = D_{k+1}` (multiplicity `k+1`), `U = D/V`.
Imitating Hermite (eq. 3): `∫ Σ Aᵢwᵢ/(UV^{k+1}) = Σ Bᵢwᵢ/Vᵏ + ∫ Σ Cᵢwᵢ/(UVᵏ)`. Differentiating and
clearing `UV^{k+1}`, then reducing mod `V`, gives the linear congruence system (eq. 11)
`Aᵢ ≡ −kUV'Bᵢ + T·Σⱼ BⱼMⱼᵢ  (mod V)` (with `E·wᵢ' = Σⱼ Mᵢⱼwⱼ`, `E` the lcm denominator of `wᵢ'`,
`TE = UV`), uniquely solvable for `k > 0` (the `Sᵢ` are a local integral basis — the order-function
contradiction on p. 46–47). Subtracting `(Σ Bᵢwᵢ/Vᵏ)'` lowers the multiplicity; iterating over all
multiple factors leaves an integrand whose denominator is **squarefree** — only simple finite poles,
hence no rational part (the log part, Trager Ch. 5–6, deferred).

**The decoupled (diagonal) case = the radical reduction (Trager p. 48).** The system (11) decouples to
`Aᵢ ≡ −kUV'Bᵢ (mod V)` — "almost exactly … rational function integration" — exactly when `Mᵢⱼ` is
diagonal, i.e. `wᵢ' = Rᵢwᵢ`, i.e. **`K(z,y)` is a compositum of single radical extensions**. The
hyperelliptic curve `y² = ρ` is precisely this case: its diagonal derivation is the engine's
`radDeriv n ρ` (Trager's `(ρ/y)' = (ρ'/(2ρ))·y` insight), and the algebraic Hermite reduction over the
integral basis IS the `radDeriv`-validated Case-1/2/3 reduction (`radIntegrateRationalWf`,
`radIntegrateCase3Wf`) of `ComputableRadicalWellFounded`. So for hyperelliptic curves the general
rational-part reduction is already realized and `radDeriv`-validated; this file connects it to the
integral-basis pole bound and exhibits the **genus-0** worked targets, where the rational part is the
ENTIRE integral.

**Worked genus-0 targets** (the cusp `y² = x³`, genus 0 — the finite poles bounded by the integral basis
`integralBasis (y²−x³) = [1, y/x]`, both integrands polynomial in basis coordinates ⟹ no finite poles ⟹
the integral is fully rational):

* **`∫ y dx = (2/5)·x·y`.** Validated two ways: (i) the **actual** diagonal derivation
  `radDeriv 2 (x³) [0, (2/5)x] = [0, 1] = y` (`cusp_intY_radDeriv`); (ii) **derived from the integrand**
  by the fuel-free Case-3 `C/y` driver — `y = ρ/y = x³/y`, so `radIntegrateCase3Wf cderivG (x³) ((3/2)x²) (x³)`
  returns `(Crem = 0, vNum = (2/5)x⁴)`, giving `v = vNum/y = (2/5)x⁴/x³ · y = (2/5)x·y` with **zero**
  leftover (`Crem = 0` ⟹ fully rational, no log part), `radDeriv`-validated end-to-end
  (`cusp_intY_driver_integrates`, `cusp_intY_fully_rational`).

* **A second genus-0 target `∫ x·y dx = (2/7)·x²·y`.** Same pattern: `xy = x·ρ/y = x⁴/y`, the Case-3
  driver returns `(0, (2/7)x⁵)`, `v = (2/7)x⁵/x³ · y = (2/7)x²·y`, again fully rational and
  `radDeriv`-validated (`cusp_intXY_radDeriv`, `cusp_intXY_driver_integrates`).

**The engine now computes/validates the general-curve rational part** — the algebraic Hermite reduction,
realized through the diagonal radical reduction for hyperelliptic curves, with the integral basis
bounding the finite poles; genus-0 integrals are obtained **fully** (rational part = whole integral,
derived from the integrand and validated by the real derivation). The non-diagonal general carrier
(`afMul`, the integral-basis Hermite with a non-diagonal `Mᵢⱼ`) and the residual's simple-pole → log-part
feed (general residues `genResidueResultant` → divisors → torsion) are documented at the end. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

/-! ### The cusp `y² = x³` (genus 0): the integral basis bounds the finite poles

`f = y² − x³` over `ℚ(x)`. `integralBasis f = [1, y/x]` (the Ford–Zassenhaus maximal order, computed by
`ComputableIntegralBasisFull`): a function on the curve has **no finite poles** iff its coordinates over
`[1, y/x]` are *polynomials* in `x`. The integrand `y dx` has `y = x·(y/x)`, basis coordinates `(0, x)` —
a polynomial vector — so `y` has no finite poles; likewise `x·y = x²·(y/x)`, coordinates `(0, x²)`. With
no finite poles and genus 0, the integral is purely rational (no log part). The basis generator `y/x` is
integral: `(y/x)² = x³/x² = x`. -/

/-- The cusp curve `f = y² − x³` over `ℚ(x)`, reused from `ComputableRound2IntegralBasis` (`cuspF`). The
genus-0 curve whose integral basis `integralBasis cuspF = [1, y/x]` bounds the finite poles. -/
def gcuspF : CPolyG (QFunNZG ℚ) := cuspF

/-- The cusp radicand `ρ = x³ ∈ ℚ(x)` (so `y² = ρ`), the `QFunNZG ℚ` value for the diagonal radical
derivation `radDeriv 2 ρ`. -/
def gcuspRho : QFunNZG ℚ := qxOfNum [0, 0, 0, 1]

/-- The cusp integral basis is `[1, y/x]`, integral and maximal (`native_decide`): `integralBasis
(y² − x³)` is `[1, y/x]` with `(y/x)² = x` and `isMaximalOrder` true — the Ford–Zassenhaus maximal order
bounding the finite poles (this is the genus-0 normalization that makes `y`, `x·y` finite-pole-free). The
integral-basis datum the algebraic Hermite reduction consumes; reproduced here as the entry point for the
rational-part targets. -/
theorem gcusp_integralBasis_eq :
    (cisZeroG (csubG ((integralBasis gcuspF).getD 1 []) [CField.zero, qxOfFrac [1] [0, 1] (by decide)])
      && cisZeroG (csubG ((integralBasis gcuspF).getD 0 []) [CField.one])
      && cisZeroG (csubG (afMul gcuspF ((integralBasis gcuspF).getD 1 [])
            ((integralBasis gcuspF).getD 1 [])) [qxOfNum [0, 1]])
      && isMaximalOrder gcuspF (integralBasis gcuspF)) = true := by native_decide

/-! ### Target 1: `∫ y dx = (2/5)·x·y` on `y² = x³` (`native_decide`)

The genus-0 milestone. The integrand is `y = [0, 1]` (the pure-`y` `RadElem`). The rational part is
`v = (2/5)·x·y = [0, (2/5)x]`. The **actual** diagonal radical derivation confirms `radDeriv 2 (x³) v = y`:
with `a₁ = (2/5)x`, `ℓ = ρ'/(2ρ) = 3x²/(2x³) = 3/(2x)`, the `y`-component is
`D(a₁) + a₁·ℓ = 2/5 + (2/5)x·3/(2x) = 2/5 + 3/5 = 1`, so `D((2/5)xy) = y` exactly. -/

/-- The rational part of `∫ y dx`: `v = (2/5)·x·y` as `RadElem (QFunNZG ℚ)` `[0, (2/5)x]`. -/
def gcuspVY : RadElem (QFunNZG ℚ) := [CField.zero, qxOfNum [0, 2/5]]

/-- The integrand `y = [0, 1]` as `RadElem (QFunNZG ℚ)`. -/
def gcuspY : RadElem (QFunNZG ℚ) := [CField.zero, CField.one]

/-- `∫ y dx = (2/5)·x·y` on `y² = x³` (`native_decide`): the **actual** diagonal radical derivation
`radDeriv 2 (x³)` of the rational part `v = (2/5)·x·y` equals the integrand `y` — `D((2/5)xy) = (2/5 +
(2/5)x·3/(2x))·y = (2/5 + 3/5)·y = y`. Checked by `radIsZero` of `radDeriv 2 ρ v − y` over `ℚ(x)`. **THE
GENUS-0 RATIONAL PART, VALIDATED THROUGH THE REAL DERIVATION** — `∫ y dx = (2/5)xy` on the cusp. -/
theorem cusp_intY_radDeriv :
    radIsZero (radSub (radDeriv 2 gcuspRho gcuspVY) gcuspY) = true := by native_decide

/-! #### Target 1, DERIVED from the integrand by the fuel-free Case-3 `C/y` driver (`native_decide`)

Rather than asserting `v`, **produce** it from the integrand. Since `y·y = ρ`, the integrand `y` equals
`ρ/y = x³/y` — a `C/y` Case-3 form with `C = ρ = x³` (a polynomial numerator, no denominator factor). The
algebraic Hermite reduction in the **decoupled hyperelliptic case** (Trager p. 48) is the engine's
`radIntegrateCase3Wf cderivG ρ g C` (`g = ½ρ' = (3/2)x²`, the diagonal `(ρ/y)' = g/y`), which lowers
`deg C` to give `∫ C/y = vNum/y + ∫ Crem/y`. It returns `Crem = 0` (the integral is FULLY rational, genus
0) and `vNum = (2/5)x⁴`, so `v = vNum/y = (2/5)x⁴/y = (2/5)x⁴·y/ρ = (2/5)x⁴·y/x³ = (2/5)x·y`. -/

/-- The cusp radicand `ρ = x³` as a `ℚ[x]` polynomial (the base-field `θ' = 1`, `θ = x` picture for the
Case-3 driver). -/
def gcuspRhoP : CPolyG ℚ := [0, 0, 0, 1]

/-- `g = ½ρ' = (3/2)x²` over `ℚ[x]` (`n = 2`, the diagonal `(ρ/y)' = g/y`). -/
def gcuspGP : CPolyG ℚ := cscaleG (1/2 : ℚ) (cderivG gcuspRhoP)

/-- The fuel-free Case-3 driver run on `∫ y dx = ∫ x³/y` (`C = ρ = x³`): `radIntegrateCase3Wf cderivG ρ g ρ =
(Crem, vNum)`. Expected `Crem = 0` (fully rational), `vNum = (2/5)x⁴` (so `v = vNum/y = (2/5)x·y`). -/
def gcuspYRun : CPolyG ℚ × CPolyG ℚ := radIntegrateCase3Wf cderivG gcuspRhoP gcuspGP gcuspRhoP

/-- The driver derives `Crem = 0` and `vNum = (2/5)x⁴` for `∫ y dx` (`native_decide`): the Case-3
`C/y` degree-lowering on `C = x³` returns a **zero** leftover residual (`Crem = 0` — the integral is fully
rational, no log part) and the rational-part numerator `vNum = (2/5)x⁴`. Checked by `cisZeroG` of `Crem`
and of `vNum − (2/5)x⁴`. The rational part `v = (2/5)x⁴/y = (2/5)x·y` is PRODUCED from the integrand, not
asserted. -/
theorem cusp_intY_driver_eq :
    (cisZeroG gcuspYRun.1 && cisZeroG (csubG gcuspYRun.2 [0, 0, 0, 0, 2/5])) = true := by native_decide

/-- The driver-produced rational part `v = vNum/y` lifted to `RadElem (QFunNZG ℚ)`: the pure-`y` element
`[0, vNum/ρ]` over `ℚ(x)` (an `R/y` form is `[0, R/ρ]` since `R/y = (R/ρ)·y`). With `vNum = (2/5)x⁴`,
`ρ = x³`, this is `[0, (2/5)x]`. -/
def gcuspVYlift : RadElem (QFunNZG ℚ) :=
  [CField.zero, CField.div (qxOfNum gcuspYRun.2) gcuspRho]

/-- The integrand's rational part `(C − Crem)/y` lifted to `RadElem (QFunNZG ℚ)`: `[0, (C − Crem)/ρ]`
over `ℚ(x)`. With `C = x³`, `Crem = 0` this is `[0, x³/x³] = [0, 1] = y` — the whole integrand (no
leftover). -/
def gcuspYRatLift : RadElem (QFunNZG ℚ) :=
  [CField.zero, CField.div (qxOfNum (csubG gcuspRhoP gcuspYRun.1)) gcuspRho]

/-- The Case-3 driver integrates `∫ y dx` end-to-end: `radDeriv(v) = integrand` (`native_decide`).
Over the genuine radical extension `(QFunNZG ℚ)[y]/(y² − x³)`, the **actual** diagonal radical derivation
`radDeriv 2 (x³)` of the driver-produced rational part `v = vNum/y = (2/5)x·y` equals the integrand's
rational part `(C − Crem)/y = x³/x³·y = y` (the leftover `Crem = 0` is subtracted, leaving the whole `y`).
Checked by `radIsZero` of the difference over `ℚ(x)`. **THE ALGEBRAIC HERMITE REDUCTION COMPUTES THE
RATIONAL PART OF `∫ y dx` FROM THE INTEGRAND, VALIDATED BY THE REAL DERIVATION** — and since `Crem = 0`,
this is the COMPLETE integral (genus 0). -/
theorem cusp_intY_driver_integrates :
    radIsZero (radSub (radDeriv 2 gcuspRho gcuspVYlift) gcuspYRatLift) = true := by native_decide

/-- `∫ y dx` is FULLY rational (genus 0): the leftover is zero (`native_decide`): the Case-3
reduction of `∫ y dx` leaves `Crem = 0`, so there is **no** simple-pole residual and **no** logarithmic
part — the integral is `(2/5)x·y` exactly. The genus-0 hallmark: the rational part is the whole integral.
Checked by `cisZeroG gcuspYRun.1`. -/
theorem cusp_intY_fully_rational : cisZeroG gcuspYRun.1 = true := by native_decide

/-! ### A second genus-0 target: `∫ x·y dx = (2/7)·x²·y` on `y² = x³` (`native_decide`)

The same pattern with the integrand `x·y = [0, x]`. The rational part is `v = (2/7)·x²·y = [0, (2/7)x²]`:
`radDeriv 2 (x³)` of it has `y`-component `D((2/7)x²) + (2/7)x²·3/(2x) = (4/7)x + (3/7)x = x`, so
`D((2/7)x²y) = x·y`. Derived from the integrand: `xy = x·ρ/y = x⁴/y`, so the Case-3 driver on `C = x⁴`
returns `(Crem = 0, vNum = (2/7)x⁵)`, `v = (2/7)x⁵/x³·y = (2/7)x²·y`. -/

/-- The rational part of `∫ x·y dx`: `v = (2/7)·x²·y` as `RadElem (QFunNZG ℚ)` `[0, (2/7)x²]`. -/
def gcuspVXY : RadElem (QFunNZG ℚ) := [CField.zero, qxOfNum [0, 0, 2/7]]

/-- The integrand `x·y = [0, x]` as `RadElem (QFunNZG ℚ)`. -/
def gcuspXY : RadElem (QFunNZG ℚ) := [CField.zero, qxOfNum [0, 1]]

/-- `∫ x·y dx = (2/7)·x²·y` on `y² = x³` (`native_decide`): the **actual** diagonal radical
derivation `radDeriv 2 (x³)` of `v = (2/7)·x²·y` equals `x·y` — `D((2/7)x²y) = ((4/7)x + (2/7)x²·3/(2x))·y
= ((4/7)x + (3/7)x)·y = x·y`. Checked by `radIsZero` of `radDeriv 2 ρ v − xy` over `ℚ(x)`. A second
genus-0 rational-part target, validated through the real derivation. -/
theorem cusp_intXY_radDeriv :
    radIsZero (radSub (radDeriv 2 gcuspRho gcuspVXY) gcuspXY) = true := by native_decide

/-- The fuel-free Case-3 driver run on `∫ x·y dx = ∫ x⁴/y` (`C = x⁴`): `radIntegrateCase3Wf cderivG ρ g (x⁴) =
(Crem, vNum)`. Expected `Crem = 0`, `vNum = (2/7)x⁵` (so `v = (2/7)x⁵/y = (2/7)x²·y`). -/
def gcuspXYRun : CPolyG ℚ × CPolyG ℚ := radIntegrateCase3Wf cderivG gcuspRhoP gcuspGP [0, 0, 0, 0, 1]

/-- The driver derives `Crem = 0` and `vNum = (2/7)x⁵` for `∫ x·y dx` (`native_decide`): the Case-3
`C/y` degree-lowering on `C = x⁴` returns a zero leftover (`Crem = 0`, fully rational) and rational-part
numerator `vNum = (2/7)x⁵`, so `v = (2/7)x⁵/x³·y = (2/7)x²·y` is produced from the integrand. Checked by
`cisZeroG` of `Crem` and of `vNum − (2/7)x⁵`. -/
theorem cusp_intXY_driver_eq :
    (cisZeroG gcuspXYRun.1 && cisZeroG (csubG gcuspXYRun.2 [0, 0, 0, 0, 0, 2/7])) = true := by
  native_decide

/-- The driver-produced rational part `v = vNum/y` for `∫ x·y dx`, lifted to `RadElem (QFunNZG ℚ)`:
`[0, vNum/ρ] = [0, (2/7)x²]`. -/
def gcuspVXYlift : RadElem (QFunNZG ℚ) :=
  [CField.zero, CField.div (qxOfNum gcuspXYRun.2) gcuspRho]

/-- The integrand's rational part `(x⁴ − Crem)/y` lifted to `RadElem (QFunNZG ℚ)`: `[0, (x⁴ − Crem)/ρ]`
over `ℚ(x)`. With `Crem = 0` this is `[0, x⁴/x³] = [0, x] = x·y`. -/
def gcuspXYRatLift : RadElem (QFunNZG ℚ) :=
  [CField.zero, CField.div (qxOfNum (csubG [0, 0, 0, 0, 1] gcuspXYRun.1)) gcuspRho]

/-- The Case-3 driver integrates `∫ x·y dx` end-to-end: `radDeriv(v) = integrand` (`native_decide`).
The **actual** diagonal radical derivation `radDeriv 2 (x³)` of the driver-produced `v = (2/7)x²·y` equals
the integrand `x·y` (leftover `Crem = 0` subtracted). Checked by `radIsZero` of the difference over
`ℚ(x)`. The second genus-0 integral computed FROM the integrand and validated by the real derivation —
fully rational. -/
theorem cusp_intXY_driver_integrates :
    radIsZero (radSub (radDeriv 2 gcuspRho gcuspVXYlift) gcuspXYRatLift) = true := by native_decide

/-! ### The NEXT pieces: non-diagonal general carrier, and the simple-pole residual → log part

The reduction above is the **decoupled (diagonal)** case of Trager's algebraic Hermite reduction
(Ch. 4 §2, p. 48) — `K(x, y)` a compositum of single radical extensions (the hyperelliptic `y² = ρ`),
where the integral-basis Hermite system (11) collapses to `Aᵢ ≡ −kUV'Bᵢ (mod V)`, i.e. the diagonal
`radDeriv`-validated Case-1/2/3 reduction. Two pieces remain:

1. **The non-diagonal general carrier.** For a general plane curve `f` whose `Mᵢⱼ` (from `E·wᵢ' = Σⱼ
   Mᵢⱼwⱼ`) is *not* diagonal — `K(x, y)` not a compositum of radicals — the congruence system (11) is a
   genuine *coupled* `n×n` linear system over `K(x)/(V)`, solved by Cramer's rule (the determinant is
   coprime to `V`, p. 48). The inputs are all in place: the integral basis `integralBasis f`
   (`ComputableIntegralBasisFull`), the general carrier `afMul`/`trace`/`afReduce`
   (`ComputableAlgFunctionField`), and the basis derivatives `wᵢ'` via the total derivative
   `∂f/∂z + (∂f/∂y)·y' = 0` (so `y' = −(∂f/∂z)/(∂f/∂y)`, a `K(x, y)` element reducible by `afReduce`). What
   remains is forming `Mᵢⱼ`, building the eq.-11 coupled congruence, and the Cramer/Bézout solve — the
   non-diagonal analogue of `radIntegrateRationalWf`. The diagonal case here already covers all
   hyperelliptic (in particular all genus-0 and genus-1 `y² = ρ`) curves.

2. **The simple-pole residual → the logarithmic part (genus `g > 0`).** After the reduction, the residual
   has only **simple** finite poles (Trager's Theorem, p. 50: `(g − h')dx` has only simple poles in the
   finite plane and no poles at ∞ if `g dx` was integrable). For genus 0 (the cusp here) the residual is
   *empty* (`Crem = 0` above — the rational part is the whole integral). For genus `g > 0` the simple-pole
   residual feeds the **logarithmic part**: its residues (the engine's `genResidueResultant`,
   `ComputableGeneralResidues`, the general-curve Rothstein–Trager resultant) define a **divisor**, whose
   `K`-multiple being **principal** (a torsion condition in the Jacobian — the Ch. 6 decision, done for the
   hyperelliptic carrier in `ComputableTorsionLogTerm`/`ComputableHyperellipticDivisor`) is exactly when
   the integral is elementary, contributing `Σ cⱼ log(argⱼ)`. The residue → divisor → torsion path is the
   genus-`g > 0` continuation; the rational part (this file) is the part that is *always* computed, and
   for genus 0 is the complete answer.

The **integral basis is the finite-pole datum** the whole reduction consumes (a function has a finite
pole exactly where it leaves the maximal order); with it, "reduce to simple finite poles, accumulating
the rational part" is the computation realized here for hyperelliptic curves, fully for genus 0. -/

end DeepWiki.SymbolicIntegration
