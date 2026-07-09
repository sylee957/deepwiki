import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension

/-! # Simple-radical rational-part integration driver

Iterates a single-step rational-part reduction over the simple-radical carrier
`α[y]/(yⁿ − f)`, assembling the accumulated rational part `v` and validating
`D(v) = rational-part-of-integrand` through the diagonal derivation `radDeriv`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPoly

namespace CPoly

variable {α : Type*} [CField α]

/-! ### The iterated Case-1 rational-part reduction

Iterates the single-step Hermite reduction from multiplicity `k₀` down to `1`, telescoping the
rational part over the common denominator `V^{k₀−1}`. -/

/-- Iterated Case-1 reduction: one Hermite step per unit of `fuel`, accumulating the cofactor
contribution `B·f·V^{k0−k}` into `vNum` and recursing on `−radCase1Residual` at `k−1`; returns the
leftover `k = 1` numerator and the assembled rational-part numerator `vNum`. -/
def radReduceCase1Iterate (der : CPoly α → CPoly α) (V Df f g : CPoly α) (k0 : ℕ) :
    ℕ → ℕ → CPoly α → CPoly α → CPoly α × CPoly α
  | 0, _, C, vNum => (C, vNum)
  | fuel + 1, k, C, vNum =>
    if k ≤ 1 then (C, vNum)
    else
      let B := radCase1Cofactor k V Df f C
      let Bder := der B
      let D := radCase1Residual k V Df f g B C Bder
      -- contribution `B·f/(V^{k−1}y)` over the common denominator `V^{k0−1}`: `B·f·V^{k0−k}`
      let contrib := cmulG (cmulG B f) (cpowG V (k0 - k))
      radReduceCase1Iterate der V Df f g k0 fuel (k - 1) (cnegG D) (caddG vNum contrib)

/-- The simple-radical rational-part driver: `∫ C/(V^{k0}y)` over `yⁿ = f` with `V` squarefree coprime
to `f`. Computes `Df = V'` and runs `radReduceCase1Iterate` from `k0` down to `1`, returning the leftover
`k = 1` numerator `Crem` and the accumulated rational-part numerator `vNum` over `V^{k0−1}·y`. -/
def radIntegrateCase1 (der : CPoly α → CPoly α) (V f g : CPoly α) (k0 : ℕ) (C : CPoly α) :
    CPoly α × CPoly α :=
  radReduceCase1Iterate der V (der V) f g k0 k0 k0 C []

end CPoly

/-! ### The driver integrates `∫ 1/((x−1)³√x)` end-to-end

Over `y² = x`, `V = x − 1`, `k₀ = 3`, `C₀ = 1`, the driver runs two Hermite steps and its accumulated
rational part `v`, lifted to `(QFunNZG ℚ)[y]/(y² − x)`, satisfies `radDeriv 2 x v = C₀/(V³y) − Crem/(Vy)`. -/

open RadElem CPoly

/-- Driver example radicand `f = x` (`y² = x`, `y = √x`), as `ℚ[x]` `[0, 1]`. -/
def sqrtxF : CPoly ℚ := [0, 1]

/-- Driver example denominator factor `V = x − 1` (squarefree, coprime to `f = x`), `[−1, 1]`. -/
def sqrtxV : CPoly ℚ := [-1, 1]

/-- Driver example Case-1 helper `g = ((n−1)/n)·f' = (1/2)·1 = 1/2` (`n = 2`, `(f/y)' = g/y`), `[1/2]`. -/
def sqrtxG : CPoly ℚ := cscaleG (1/2 : ℚ) (cderivG sqrtxF)

/-- Driver example numerator `C₀ = 1` (integrand `1/((x−1)³√x)`), `[1]`. -/
def sqrtxC : CPoly ℚ := [1]

/-- The driver run on `∫ 1/((x−1)³√x)`: two Hermite steps, returning `(Crem, vNum)` with `vNum` over
`V² = (x−1)²`. -/
def sqrtxRun : CPoly ℚ × CPoly ℚ := radIntegrateCase1 cderivG sqrtxV sqrtxF sqrtxG 3 sqrtxC

/-- The accumulated rational-part numerator is `vNum = (3/4)x² − (5/4)x` over `V² = (x−1)²`. -/
theorem sqrtxRun_vNum_eq :
    cisZeroG (csubG sqrtxRun.2 [(0 : ℚ), -5/4, 3/4]) = true := by native_decide

/-- The leftover `k = 1` residual is `Crem = 3/8` (the term `∫ (3/8)/((x−1)√x)`). -/
theorem sqrtxRun_remainder_eq :
    cisZeroG (csubG sqrtxRun.1 [(3/8 : ℚ)]) = true := by native_decide

/-- The radicand `f = x` lifted to `ℚ(x)` (`QFunNZG ℚ`), the Picture-B radicand for `radDeriv 2`. -/
def sqrtxFqx : QFunNZG ℚ := qxOfNum [0, 1]

/-- The common-denominator power `V² = (x−1)²` as a `ℚ[x]` polynomial (the denominator of `vNum`). -/
def sqrtxV2 : CPoly ℚ := cpowG sqrtxV 2

/-- The initial denominator power `V³ = (x−1)³` as a `ℚ[x]` polynomial (the integrand's denominator). -/
def sqrtxV3 : CPoly ℚ := cpowG sqrtxV 3

/-- The rational part `v = vNum/(V²·y)` lifted to `RadElem (QFunNZG ℚ)` as `[0, vNum/(V²·f)]`. -/
def sqrtxVlift : RadElem (QFunNZG ℚ) :=
  [CField.zero, CField.div (qxOfNum sqrtxRun.2) (qxOfNum (cmulG sqrtxV2 sqrtxF))]

/-- The integrand's rational part `C₀/(V³y) − Crem/(Vy)` lifted to `RadElem (QFunNZG ℚ)` as
`[0, C₀/(V³·f) − Crem/(V·f)]`. -/
def sqrtxRatLift : RadElem (QFunNZG ℚ) :=
  [CField.zero,
    CField.sub (CField.div (qxOfNum sqrtxC) (qxOfNum (cmulG sqrtxV3 sqrtxF)))
      (CField.div (qxOfNum sqrtxRun.1) (qxOfNum (cmulG sqrtxV sqrtxF)))]

/-- The driver integrates `∫ 1/((x−1)³√x)`: `radDeriv 2 x (lift v) = lift(C₀/(V³√x) − Crem/(V√x))` over
`ℚ(x)`, checked by `radIsZero` of the difference. -/
theorem sqrtxDriver_integrates :
    radIsZero (radSub (radDeriv 2 sqrtxFqx sqrtxVlift) sqrtxRatLift) = true := by native_decide

/-! ### The driver integrates `∫ 1/((x−1)³√(x³+1))` end-to-end

The same driver on the elliptic radicand `y² = x³ + 1`, `V = x − 1`, `k₀ = 3`, `C₀ = 1`: the assembled
rational part `v` satisfies `radDeriv 2 (x³+1) (lift v) = lift(C₀/(V³√(x³+1)) − Crem/(V√(x³+1)))`. -/

/-- Headline-radicand example `f = x³ + 1` (`y² = x³+1`, `y = √(x³+1)`), as `ℚ[x]` `[1,0,0,1]`. -/
def cubeF : CPoly ℚ := [1, 0, 0, 1]

/-- Headline-radicand denominator factor `V = x − 1` (coprime to `f = x³+1`: `f(1) = 2 ≠ 0`), `[−1, 1]`. -/
def cubeV : CPoly ℚ := [-1, 1]

/-- Headline-radicand Case-1 helper `g = ((n−1)/n)·f' = (1/2)·3x² = (3/2)x²` (`n = 2`, `(f/y)' = g/y`). -/
def cubeG : CPoly ℚ := cscaleG (1/2 : ℚ) (cderivG cubeF)

/-- Headline-radicand numerator `C₀ = 1` (integrand `1/((x−1)³√(x³+1))`), `[1]`. -/
def cubeC : CPoly ℚ := [1]

/-- The driver run on `∫ 1/((x−1)³√(x³+1))`: two Hermite steps, returning `(Crem, vNum)` with `vNum`
over `V² = (x−1)²`. -/
def cubeRun : CPoly ℚ × CPoly ℚ := radIntegrateCase1 cderivG cubeV cubeF cubeG 3 cubeC

/-- The headline radicand `f = x³ + 1` lifted to `ℚ(x)` (`QFunNZG ℚ`), the Picture-B radicand. -/
def cubeFqx : QFunNZG ℚ := qxOfNum [1, 0, 0, 1]

/-- The rational part `v = vNum/(V²·y)` lifted to `RadElem (QFunNZG ℚ)` — the pure-`y` element
`[0, vNum/(V²·f)]` over `ℚ(x)`. -/
def cubeVlift : RadElem (QFunNZG ℚ) :=
  [CField.zero, CField.div (qxOfNum cubeRun.2) (qxOfNum (cmulG (cpowG cubeV 2) cubeF))]

/-- The integrand's rational part `C₀/(V³y) − Crem/(Vy)` lifted to `RadElem (QFunNZG ℚ)` — the pure-`y`
element `[0, C₀/(V³·f) − Crem/(V·f)]` over `ℚ(x)`. -/
def cubeRatLift : RadElem (QFunNZG ℚ) :=
  [CField.zero,
    CField.sub (CField.div (qxOfNum cubeC) (qxOfNum (cmulG (cpowG cubeV 3) cubeF)))
      (CField.div (qxOfNum cubeRun.1) (qxOfNum (cmulG cubeV cubeF)))]

/-- The driver integrates `∫ 1/((x−1)³√(x³+1))` on the elliptic curve `y² = x³ + 1`:
`radDeriv 2 (x³+1) (lift v) = lift(C₀/(V³√(x³+1)) − Crem/(V√(x³+1)))`, checked by `radIsZero`. -/
theorem cubeDriver_integrates :
    radIsZero (radSub (radDeriv 2 cubeFqx cubeVlift) cubeRatLift) = true := by native_decide

end DeepWiki.SymbolicIntegration
