import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalCase2
import DeepWiki.SymbolicIntegration.Engine.Tower.Integrate
import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCore

/-! # The general simple-radical rational-part integrator

The multi-case rational-part front-end for `∫ R/(B·y)` over `y² = ρ`, whose denominator `B` mixes
`V`-factors (coprime to `ρ`, Case 1) and `W`-factors (dividing `ρ`, Case 2). Provides the iterated
Case-2 and Case-3 reductions, the partial-fraction front-end, and concrete multi-case driver
validations through the diagonal derivation `radDeriv`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem DensePoly

namespace DensePoly

variable {α : Type*} [CField α]

/-! ### The iterated Case-2 rational-part reduction

For `W ∣ ρ` the Hermite step `k → k−1` accumulates `B·ρ·W^{k0−k}` into `vNum` over the common
denominator `W^{k0}·y` and recurses on the negated residual `−D`. -/

/-- Iterated Case-2 reduction `radReduceCase2Iterate W h ρ k0 fuel k C vNum = (Crem, vNumOut)`: at
multiplicity `k ≥ 2` solve the cofactor `B = radCase2CofactorC` (`h = ρ/W`), form the residual
`D = radCase2ResidualC`, accumulate `B·ρ·W^{k0−k}` into `vNum`, recurse on `−D` at `k−1`; bottom at
`k ≤ 1` returning `(C, vNum)`. One step per unit of `fuel`. Generic over `[CField α]`. -/
def radReduceCase2Iterate (W h ρ : DensePoly α) (k0 : ℕ) :
    ℕ → ℕ → DensePoly α → DensePoly α → DensePoly α × DensePoly α
  | 0, _, C, vNum => (C, vNum)
  | fuel + 1, k, C, vNum =>
    if k ≤ 1 then (C, vNum)
    else
      let B := radCase2CofactorC k W h C
      let D := radCase2ResidualC k W h C B
      -- contribution `B·ρ/(Wᵏy)` over the common denominator `W^{k0}`: `B·ρ·W^{k0−k}`
      let contrib := cmul (cmul B ρ) (cpow W (k0 - k))
      radReduceCase2Iterate W h ρ k0 fuel (k - 1) (cneg D) (cadd vNum contrib)

/-- Case-2 simple-radical rational-part driver `radIntegrateCase2 W ρ k0 C = (Crem, vNum)` for
`∫ C/(W^{k0}y)` over `y² = ρ`, `W ∣ ρ`: computes `h = ρ/W` and runs `radReduceCase2Iterate` from `k0`
down to `1`. Master identity `∫ C/(W^{k0}y) = vNum/(W^{k0}y) + ∫ Crem/(Wy)`. Generic over `[CField α]`. -/
def radIntegrateCase2 (W ρ : DensePoly α) (k0 : ℕ) (C : DensePoly α) : DensePoly α × DensePoly α :=
  radReduceCase2Iterate W (cdivWf ρ W) ρ k0 k0 k0 C []

/-! ### The iterated Case-3 (`C/y`) degree-lowering

The leftover `C/y` (`C` a polynomial) has its degree lowered by cancelling the leading term with a
leading-coefficient monomial `B`, accumulating `B·f` into `vNum` over the common denominator `y`,
until `deg C < deg f`. -/

/-- Iterated Case-3 reduction `radReduceCase3Iterate der f g fuel C vNum = (Crem, vNumOut)`: while
`deg C ≥ deg f`, cancel the leading term of `C` with `B = radCase3Cofactor f g C`, form the residual
`D = radCase3Residual`, accumulate `B·f` into `vNum`, recurse on `−D`; bottom at `deg C < deg f`. `der`
the base derivation, `f` the radicand, `g` from `(f/y)' = g/y`. Generic over `[CField α]`. -/
def radReduceCase3Iterate (der : DensePoly α → DensePoly α) (f g : DensePoly α) :
    ℕ → DensePoly α → DensePoly α → DensePoly α × DensePoly α
  | 0, C, vNum => (C, vNum)
  | fuel + 1, C, vNum =>
    if cisZero C || cdeg C < cdeg f then (C, vNum)
    else
      let B := radCase3Cofactor f g C
      let D := radCase3Residual f g B C (der B)
      radReduceCase3Iterate der f g fuel (cneg D) (cadd vNum (cmul B f))

/-- Case-3 simple-radical rational-part driver `radIntegrateCase3 der f g C = (Crem, vNum)` for `∫ C/y`
over `y² = f`: runs `radReduceCase3Iterate` (fuel `deg C + 1`), returning the irreducible leftover `Crem`
and the numerator `vNum`. Master identity `∫ C/y = vNum/y + ∫ Crem/y`. Generic over `[CField α]`. -/
def radIntegrateCase3 (der : DensePoly α → DensePoly α) (f g C : DensePoly α) : DensePoly α × DensePoly α :=
  radReduceCase3Iterate der f g (cdeg C + 1) C []

/-! ### The partial-fraction front-end

The integrand `R/(B·y)` has `B` decomposed into coprime prime-power factors and `R`
partial-fractioned across them before the resulting pieces are handled by the case reductions. -/

/-- Partial fraction across coprime prime-powers `radPartialFractionCoprime R Gs = [N₁,…,Nₘ]`: for
pairwise-coprime `Gs` with `B = ∏Gᵢ` and proper `R`, returns `Nᵢ` with `R/B = Σᵢ Nᵢ/Gᵢ`,
`deg Nᵢ < deg Gᵢ`, by iterating the Bézout split `cdiophantine`. Generic over `[CField α]`. -/
def radPartialFractionCoprime : DensePoly α → List (DensePoly α) → List (DensePoly α)
  | _, [] => []
  | R, G :: rest =>
    let P := cprod rest
    let (Ni, c) := cdiophantine P G R   -- `Ni·P + c·G = R`, `deg Ni < deg G`
    Ni :: radPartialFractionCoprime c rest

end DensePoly

/-! ### The iterated Case-2 reduction validates `∫ 1/(x³·√(x³−x))`

`θ = x`, radicand `ρ = x³ − x`, `W = x`, `k₀ = 3`, `C₀ = 1`: two Case-2 steps, validated through
`radDeriv 2 (x³−x)`. -/

open RadElem DensePoly

/-- Radicand `ρ = x³ − x = x(x−1)(x+1)` (`y² = ρ`, squarefree), `ℚ[x]` `[0,−1,0,1]`. -/
def c2itRho : DensePoly ℚ := [0, -1, 0, 1]

/-- Squarefree factor `W = x` (a branch place of `√(x³−x)`, `W ∣ ρ`), `[0,1]`. -/
def c2itW : DensePoly ℚ := [0, 1]

/-- Numerator `C₀ = 1` (integrand `1/(x³·√(x³−x))`), `[1]`. -/
def c2itC : DensePoly ℚ := [1]

/-- The Case-2 run `radIntegrateCase2 W ρ 3 C = (Crem, vNum)` on `∫ 1/(x³·√(x³−x))`: two steps, returning
the residual and the numerator over `W³ = x³`. -/
def c2itRun : DensePoly ℚ × DensePoly ℚ := radIntegrateCase2 c2itW c2itRho 3 c2itC

/-- The radicand `ρ = x³ − x` lifted to `ℚ(x)` (`CFrac ℚ`), the radicand for `radDeriv 2`. -/
def c2itRhoQx : CFrac ℚ := qxOfNum [0, -1, 0, 1]

/-- The common-denominator power `W³ = x³` as a `ℚ[x]` polynomial. -/
def c2itW3 : DensePoly ℚ := cpow c2itW 3

/-- The rational part `v = vNum/(W³·y)` lifted to `RadElem (CFrac ℚ)` as `[0, vNum/(W³·ρ)]`. -/
def c2itVlift : RadElem (CFrac ℚ) :=
  [CField.zero, CField.div (qxOfNum c2itRun.2) (qxOfNum (cmul c2itW3 c2itRho))]

/-- The integrand's rational part `C₀/(W³y) − Crem/(Wy)` lifted to `RadElem (CFrac ℚ)`. -/
def c2itRatLift : RadElem (CFrac ℚ) :=
  [CField.zero,
    CField.sub (CField.div (qxOfNum c2itC) (qxOfNum (cmul c2itW3 c2itRho)))
      (CField.div (qxOfNum c2itRun.1) (qxOfNum (cmul c2itW c2itRho)))]

/-- The Case-2 iterate integrates `∫ 1/(x³·√(x³−x))`: `radDeriv 2 (x³−x)` of the rational part
`v = vNum/(W³√(x³−x))` equals `C₀/(W³√(x³−x)) − Crem/(W√(x³−x))`, the rational part of the integrand. -/
theorem c2itDriver_integrates :
    radIsZero (radSub (radDeriv 2 c2itRhoQx c2itVlift) c2itRatLift) = true := by native_decide

/-! ### The iterated Case-3 reduction validates `∫ x⁴/√(x³+1)`

`θ = x`, radicand `ρ = x³ + 1`, numerator `C = x⁴`, `g = ½ρ'`: the `C/y` degree-lowering, validated
through `radDeriv 2 (x³+1)`. -/

/-- Radicand `ρ = x³ + 1` (`y² = ρ`, `y = √(x³+1)`), `ℚ[x]` `[1,0,0,1]`. -/
def c3itRho : DensePoly ℚ := [1, 0, 0, 1]

/-- Helper `g = ½ρ' = (3/2)x²` (`(f/y)' = g/y`). -/
def c3it : DensePoly ℚ := cscale (1/2 : ℚ) (cderiv c3itRho)

/-- Numerator `C = x⁴` (integrand `x⁴/√(x³+1)`, `deg C ≥ deg ρ`), `[0,0,0,0,1]`. -/
def c3itC : DensePoly ℚ := [0, 0, 0, 0, 1]

/-- The Case-3 run `radIntegrateCase3 cderiv ρ g C = (Crem, vNum)` on `∫ x⁴/√(x³+1)`, returning the
irreducible residual and the numerator over `y`. -/
def c3itRun : DensePoly ℚ × DensePoly ℚ := radIntegrateCase3 cderiv c3itRho c3it c3itC

/-- The radicand `ρ = x³ + 1` lifted to `ℚ(x)` (`CFrac ℚ`), the radicand for `radDeriv 2`. -/
def c3itRhoQx : CFrac ℚ := qxOfNum [1, 0, 0, 1]

/-- The rational part `v = vNum/y` lifted to `RadElem (CFrac ℚ)` as `[0, vNum/ρ]`. -/
def c3itVlift : RadElem (CFrac ℚ) :=
  [CField.zero, CField.div (qxOfNum c3itRun.2) (qxOfNum c3itRho)]

/-- The integrand's rational part `C/y − Crem/y` lifted to `RadElem (CFrac ℚ)` as `[0, (C − Crem)/ρ]`. -/
def c3itRatLift : RadElem (CFrac ℚ) :=
  [CField.zero, CField.div (qxOfNum (csub c3itC c3itRun.1)) (qxOfNum c3itRho)]

/-- The Case-3 iterate integrates `∫ x⁴/√(x³+1)`: `radDeriv 2 (x³+1)` of the rational part `v = vNum/√(x³+1)`
equals `x⁴/√(x³+1) − Crem/√(x³+1)`, the rational part of the integrand. -/
theorem c3itDriver_integrates :
    radIsZero (radSub (radDeriv 2 c3itRhoQx c3itVlift) c3itRatLift) = true := by native_decide

/-! ### The multi-case dispatch integrates `∫ 1/((x−1)²x²·√x)`

A general integrand whose denominator mixes a `V`-factor `(x−1)` and a `W`-factor `x` over `y² = ρ = x`:
the driver squarefree-decomposes `B = (x−1)²·x²`, splits into prime-powers `[(x−1)², x²]`,
partial-fractions, dispatches `(x−1)` to Case 1 and `x` to Case 2, and assembles `v = v_V + v_W`. -/

/-- Radicand `ρ = x` (`y² = x`, `y = √x`), as `ℚ[x]` `[0, 1]`. -/
def mcRho : DensePoly ℚ := [0, 1]

/-- Numerator `R = 1` (integrand `1/((x−1)²x²·√x)`), `[1]`. -/
def mcR : DensePoly ℚ := [1]

/-- Denominator `B = (x−1)²·x² = x⁴ − 2x³ + x²`, presented unfactored `[0,0,1,−2,1]`. -/
def mcB : DensePoly ℚ := cmul (cpow [-1, 1] 2) (cpow [0, 1] 2)

/-- The radicand `ρ = x` as `CFrac ℚ`, the base of the `RadElem` lift for the multi-case
`∫ 1/((x−1)²x²·√x)` validation. -/
def mcRhoQx : CFrac ℚ := qxOfNum [0, 1]
