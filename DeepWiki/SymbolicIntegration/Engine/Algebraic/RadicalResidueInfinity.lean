import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgebraicResidues

/-! # Residue at infinity for simple-radical differentials

The residue at infinity of a differential `f dx` on `y² = ρ(x)` is the finite residue at `t = 0` of the
differential transformed under `x = 1/t`. `radTransformAtInfinity` performs the coordinate transform,
and the existing residue resultant reads off the residue at the place `t = 0`, either as the full
transformed resultant (`cAlgResidueAtInfinity`) or the isolated `t = 0` place (`cResidueAtInfinityPlace`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPoly

variable {α : Type*} [CField α]

/-! ### Common-`t`-power cancellation after reverse-coefficient substitution -/

/-- **Count leading-zero coefficients** of a `CPoly` (initial `isZero` run length) — the order of
vanishing at `t = 0`, i.e. the `t`-power dividing `p`. -/
def cleadingZerosG (p : CPoly α) : ℕ := (p.takeWhile (fun a => CField.isZero a)).length

/-- **Common `t`-power** `commonTPow ps` shared by every `CPoly` in `ps`: the `min` of their
leading-zero counts (`0` for the empty list). The maximal `t^k` dividing all of `ps` simultaneously. -/
def commonTPow (ps : List (CPoly α)) : ℕ :=
  match ps.map cleadingZerosG with
  | [] => 0
  | n :: ns => ns.foldl Nat.min n

/-- **Divide a `CPoly` by `t^k`** by dropping `k` low coefficients (`p.drop k`). Sound only when the
first `k` coefficients are zero (the caller guarantees this via `commonTPow`); realizes division by the
monomial `t^k`. -/
def cdropTPowG (k : ℕ) (p : CPoly α) : CPoly α := (p : List α).drop k

/-! ### The coordinate transform at infinity -/

/-- The `x = 1/t` coordinate transform at infinity `radTransformAtInfinity ρ g₀ g₁ D = (ρ̃, g̃₀, g̃₁, D̃)`
for `f dx = (g₀ + g₁·y)/D dx` on `y² = ρ`. With `m = ⌈deg ρ/2⌉`, `N = max(deg g₀, deg g₁, deg D)`, and
`revₖ p := t^k·p(1/t)`: `ρ̃ = rev_{2m} ρ`, `g̃₀ = −t^m·rev_N g₀`, `g̃₁ = −rev_N g₁`, `D̃ = t^{m+2}·rev_N D`,
with the common `t`-power cancelled so `∞` stays a simple pole. Generic over `[CField α]`. -/
def radTransformAtInfinity (rho g0 g1 D : CPoly α) :
    CPoly α × CPoly α × CPoly α × CPoly α :=
  let d := cdegG rho
  let m := (d + 1) / 2                                            -- ⌈d/2⌉
  let N := max (max (cdegG g0) (cdegG g1)) (cdegG D)
  let rhoT := creverseDegG (2 * m) rho                           -- t^{2m}·ρ(1/t)
  let g0raw := cnegG (cshiftG m (creverseDegG N g0))             -- −t^m·rev_N g₀
  let g1raw := cnegG (creverseDegG N g1)                         -- −rev_N g₁
  let Draw := cshiftG (m + 2) (creverseDegG N D)                 -- t^{m+2}·rev_N D
  let k := commonTPow [g0raw, g1raw, Draw]
  (cnormG rhoT, cnormG (cdropTPowG k g0raw), cnormG (cdropTPowG k g1raw), cnormG (cdropTPowG k Draw))

/-! ### The residue-at-infinity resultant (full + isolated-place) -/

/-- Full residue-at-infinity resultant `cAlgResidueAtInfinity ρ g₀ g₁ D = R̃(Z) ∈ K[Z]`: the residue
resultant `cAlgResidueResultant` on the `x = 1/t`-transformed data. `R̃(Z) = res_t((Z·D̃' − g̃₀)² −
g̃₁²·ρ̃, D̃)` factors over the roots of `D̃`; the residue at infinity is the `t = 0` factor. -/
def cAlgResidueAtInfinity (rho g0 g1 D : CPoly α) : CPoly α :=
  let (rhoT, g0T, g1T, DT) := radTransformAtInfinity rho g0 g1 D
  cAlgResidueResultant DT rhoT g0T g1T

/-- Isolated residue at the place `t = 0` (the residue at infinity) `cResidueAtInfinityPlace fuel ρ g₀ g₁ D
= (Z·D̃'(0) − g̃₀(0))² − g̃₁(0)²·ρ̃(0) ∈ K[Z]`, built from the constants `D̃'(0), g̃₀(0), g̃₁(0), ρ̃(0)`.
Isolates the single place `t = 0`, staying correct (residue `0`) even when `∞` is not a pole. -/
def cResidueAtInfinityPlace (fuel : ℕ) (rho g0 g1 D : CPoly α) : CPoly α :=
  let (rhoT, g0T, g1T, DT) := radTransformAtInfinity rho g0 g1 D
  let Dp0 := cevalG (cderivG DT) CField.zero                     -- D̃'(0)
  let a0 := cevalG g0T CField.zero                               -- g̃₀(0)
  let b0 := cevalG g1T CField.zero                               -- g̃₁(0)
  let r0 := cevalG rhoT CField.zero                              -- ρ̃(0)
  let lin : CPoly α := [CField.neg a0, Dp0]                     -- D̃'(0)·Z − g̃₀(0)
  let _ := fuel
  csubG (cmulG lin lin) [CField.mul (CField.mul b0 b0) r0]       -- (·)² − g̃₁(0)²·ρ̃(0)

end CPoly

/-! ### Validation: `∫ dx/√(x²+1)` (arcsinh) and `∫ dx/√(x²−1)` (arccosh) — residues at ∞

For `∫ dx/√(x² + 1)` on `y² = x² + 1`: `g = y` (`g₀ = 0, g₁ = 1`), `D = x² + 1`; the transform gives
`(ρ̃, g̃₀, g̃₁, D̃) = (1 + t², 0, −1, t(1 + t²))`, `t = 0` place residue resultant `Z² − 1`, residues `±1`.
The arccosh case is identical with `ρ = x² − 1`. -/

open CPoly

/-- arcsinh radicand `ρ = x² + 1` (curve `y² = x² + 1`), `ℚ[x]` `[1, 0, 1]`. -/
def arcsinhInf_rho : CPoly ℚ := [1, 0, 1]
/-- arcsinh numerator low part `g₀ = 0` (`g = y`). -/
def arcsinhInf_g0 : CPoly ℚ := []
/-- arcsinh numerator `y`-coefficient `g₁ = 1` (`g = y`), `ℚ[x]` `[1]`. -/
def arcsinhInf_g1 : CPoly ℚ := [1]
/-- arcsinh denominator `D = ρ = x² + 1` (`f = 1/y = y/ρ`), `ℚ[x]` `[1, 0, 1]`. -/
def arcsinhInf_D : CPoly ℚ := [1, 0, 1]

/-- arccosh radicand `ρ = x² − 1` (curve `y² = x² − 1`), `ℚ[x]` `[−1, 0, 1]`. -/
def arccoshInf_rho : CPoly ℚ := [-1, 0, 1]
/-- arccosh denominator `D = ρ = x² − 1`, `ℚ[x]` `[−1, 0, 1]`. -/
def arccoshInf_D : CPoly ℚ := [-1, 0, 1]

-- Sanity print: `(ρ̃, g̃₀, g̃₁, D̃) = (1+t², 0, −1, t(1+t²))`, then the `t=0` place residue `Z²−1`.
#eval (radTransformAtInfinity arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D : CPoly ℚ × CPoly ℚ × CPoly ℚ × CPoly ℚ)
#eval (cnormG (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D) : List ℚ)

/-- The `x = 1/t` transform of `(x² + 1, 0, 1, x² + 1)` is `(1 + t², 0, −1, t(1 + t²))`, the common `t²`
cancelled so `D̃ = t(1 + t²)` keeps `∞` a simple pole. -/
theorem arcsinhInf_transform_eq :
    radTransformAtInfinity arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D
      = ([1, 0, 1], [], [-1], [0, 1, 0, 1]) := by native_decide

/-- Residue at infinity of `∫ dx/√(x² + 1)` is `±1`: the isolated `t = 0` place residue resultant is
`Z² − 1`, the log term `log(x + √(x² + 1)) = arcsinh(x)`. -/
theorem arcsinhInf_residue_eq :
    cisZeroG (csubG (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D)
      [-1, 0, 1]) = true := by native_decide

/-- The full transformed resultant exposes the same `±1`: `R̃(Z) = 16·Z⁴·(Z² − 1)`; the factor `Z² − 1` is
the `t = 0` place (residues `±1`), the `Z⁴` the zero-residue branch places `t = ±i`. -/
theorem arcsinhInf_full_resultant_eq :
    cisZeroG (csubG (cAlgResidueAtInfinity arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D)
      [0, 0, 0, 0, -16, 0, 16]) = true := by native_decide

/-- `±1` are residues at ∞; `2` is not: `cIsResidue` on the isolated place resultant `Z² − 1` accepts
`Z = ±1` and rejects `Z = 2`. -/
theorem arcsinhInf_isResidue :
    cIsResidue (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D)
        (1 : ℚ) = true
    ∧ cIsResidue (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D)
        (-1 : ℚ) = true
    ∧ cIsResidue (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D)
        (2 : ℚ) = false := by
  native_decide

/-- Residue at infinity of `∫ dx/√(x² − 1)` (arccosh) is `±1`: the isolated `t = 0` place residue resultant
is `Z² − 1`, the log term `log(x + √(x² − 1)) = arccosh(x)`. -/
theorem arccoshInf_residue_eq :
    cisZeroG (csubG (cResidueAtInfinityPlace 30 arccoshInf_rho arcsinhInf_g0 arcsinhInf_g1 arccoshInf_D)
      [-1, 0, 1]) = true := by native_decide

/-! ### The residue theorem as cross-check

For `∫ dx/√(x² ± 1)` the finite residue resultant is a pure power of `Z` (all finite residues `0`) while
the residue at infinity is `±1`, summing to `0`. -/

/-- All finite residues of `∫ dx/√(x² + 1)` vanish: the finite residue resultant `cAlgResidueResultant D ρ
g₀ g₁ = 16·Z⁴`, a pure `Z`-power. -/
theorem arcsinhInf_finite_residues_zero :
    cisZeroG (csubG (cAlgResidueResultant arcsinhInf_D arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1)
      [0, 0, 0, 0, 16]) = true := by native_decide

/-- The residue theorem for `∫ dx/√(x² + 1)`: finite residues all `0` and residues at ∞ are `±1`, summing
to `0`. The ∞ side is certified by `cResiduesMatch` on `Z² − 1`. -/
theorem arcsinhInf_residue_theorem :
    cResiduesMatch (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D) [1, -1] = true
    ∧ cisZeroG (cAlgResidueResultant arcsinhInf_D arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1) = false
    ∧ cResiduesMatch (cAlgResidueResultant arcsinhInf_D arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1) [0, 0, 0, 0] = true := by
  native_decide

/-! ### A differential with both finite and ∞ residues nonzero

`∫ √(x² + 1)/(x² − x) dx`, `f = y/(x² − x)` on `y² = x² + 1`: the finite resultant is `(Z² − 1)(Z² − 2)`
(residues `±1, ±√2`), the residue at ∞ is `Z² − 1` (residues `±1`); both sum to `0`. -/

/-- both-nonzero radicand `ρ = x² + 1`, `ℚ[x]` `[1, 0, 1]`. -/
def bothInf_rho : CPoly ℚ := [1, 0, 1]
/-- both-nonzero numerator `g = y` (`g₀ = 0`). -/
def bothInf_g0 : CPoly ℚ := []
/-- both-nonzero numerator `y`-coefficient `g₁ = 1`. -/
def bothInf_g1 : CPoly ℚ := [1]
/-- both-nonzero denominator `D = x² − x = x(x − 1)`, `ℚ[x]` `[0, −1, 1]`. -/
def bothInf_D : CPoly ℚ := [0, -1, 1]

-- Sanity: finite `(Z²−1)(Z²−2) = Z⁴−3Z²+2`, then the ∞ place `Z²−1`.
#eval (cnormG (cAlgResidueResultant bothInf_D bothInf_rho bothInf_g0 bothInf_g1) : List ℚ)
#eval (cnormG (cResidueAtInfinityPlace 40 bothInf_rho bothInf_g0 bothInf_g1 bothInf_D) : List ℚ)

/-- Finite residue resultant of `∫ √(x²+1)/(x²−x) dx` is `(Z²−1)(Z²−2) = Z⁴ − 3Z² + 2`, finite residues
`±1` (pole `x = 0`) and `±√2` (pole `x = 1`). -/
theorem bothInf_finite_resultant_eq :
    cisZeroG (csubG (cAlgResidueResultant bothInf_D bothInf_rho bothInf_g0 bothInf_g1)
      [2, 0, -3, 0, 1]) = true := by native_decide

/-- Residue at infinity of `∫ √(x²+1)/(x²−x) dx` is `±1`: the isolated `t = 0` place resultant is `Z² − 1`,
so this differential has nontrivial residues at both finite poles and infinity. -/
theorem bothInf_infinity_residue_eq :
    cisZeroG (csubG (cResidueAtInfinityPlace 40 bothInf_rho bothInf_g0 bothInf_g1 bothInf_D)
      [-1, 0, 1]) = true := by native_decide

/-- The residue theorem for `∫ √(x²+1)/(x²−x) dx`: finite + ∞ residues sum to `0`. Via Vieta, each resultant
has vanishing second-leading coefficient (checked: the `Z³` coefficient of the finite resultant and the
`Z¹` coefficient of the ∞ resultant are both `0`), so each root-sum is `0`. -/
theorem bothInf_residue_theorem :
    ((cnormG (cAlgResidueResultant bothInf_D bothInf_rho bothInf_g0 bothInf_g1) : List ℚ).getD 3 0 = 0)
    ∧ ((cnormG (cResidueAtInfinityPlace 40 bothInf_rho bothInf_g0 bothInf_g1 bothInf_D) : List ℚ).getD 1 0 = 0)
    ∧ cisZeroG (cAlgResidueResultant bothInf_D bothInf_rho bothInf_g0 bothInf_g1) = false
    ∧ cisZeroG (cResidueAtInfinityPlace 40 bothInf_rho bothInf_g0 bothInf_g1 bothInf_D) = false := by
  native_decide

/-! ### The odd-`deg ρ` case — a branch place at infinity

When `deg ρ` is odd, `∞` is a single branch place and the transform degenerates: `ρ̃(0) = 0`, so
`ỹ² = ρ̃` is ramified at `t = 0` (a Puiseux place), beyond the simple-pole residue resultant. Probed
on `∫ dx/√(x³)`, where the transform yields `ρ̃ = t`. -/

/-- Odd-degree probe radicand `ρ = x³`, `ℚ[x]` `[0, 0, 0, 1]` (branch place at ∞). -/
def oddInf_rho : CPoly ℚ := [0, 0, 0, 1]
/-- Odd-degree probe denominator `D = x³` (`f = 1/y = y/ρ`), `ℚ[x]` `[0, 0, 0, 1]`. -/
def oddInf_D : CPoly ℚ := [0, 0, 0, 1]

-- Probe: `ρ̃ = t` (deg 1, odd ⇒ ramified — `ỹ = √t` Puiseux), place computation degenerates to `−Z²`.
#eval (radTransformAtInfinity oddInf_rho arcsinhInf_g0 arcsinhInf_g1 oddInf_D : CPoly ℚ × CPoly ℚ × CPoly ℚ × CPoly ℚ)
#eval (cnormG (cResidueAtInfinityPlace 30 oddInf_rho arcsinhInf_g0 arcsinhInf_g1 oddInf_D) : List ℚ)

/-- The odd-degree transform leaves a ramified radicand: `∫ dx/√(x³)` transforms to `ρ̃ = t = [0, 1]`
(`ρ̃(0) = 0`), so `ỹ² = ρ̃` is ramified at `t = 0` — a Puiseux place beyond the simple-pole residue
resultant. -/
theorem oddInf_radicand_ramified :
    (radTransformAtInfinity oddInf_rho arcsinhInf_g0 arcsinhInf_g1 oddInf_D).1 = [0, 1] := by
  native_decide

/-! ### Restatement and axioms -/

/-- The engine computes the residue at infinity of `∫ dx/√(x² + 1)` — via `radTransformAtInfinity` plus the
residue norm localized at `t = 0` — as `Z² − 1`, residues `±1`. -/
example : cisZeroG (csubG
    (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D) [-1, 0, 1])
    = true := by native_decide

#print axioms arcsinhInf_transform_eq
#print axioms arcsinhInf_residue_eq
#print axioms arcsinhInf_residue_theorem

end DeepWiki.SymbolicIntegration
