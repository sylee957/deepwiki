import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgebraicResidues

/-! # Residue at infinity for simple-radical differentials

The residue at infinity of a differential `f dx` on `y² = ρ(x)` is the finite residue at `t = 0` of the
differential transformed under `x = 1/t`. `radTransformAtInfinity` performs the coordinate transform,
and the existing residue resultant reads off the residue at the place `t = 0`, either as the full
transformed resultant (`cAlgResidueAtInfinity`) or the isolated `t = 0` place (`cResidueAtInfinityPlace`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u

namespace DensePoly

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
variable {α : Type u} [CField α]

/-! ### Common-`t`-power cancellation after reverse-coefficient substitution -/

/-- **Count leading-zero coefficients** of a represented polynomial — the order of
vanishing at `t = 0`, i.e. the `t`-power dividing `p`. -/
def cleadingZeros (p : P α) : ℕ :=
  ((List.range (CPoly.degBound p)).takeWhile
    (fun i => CCommRing.isZero (CPoly.coeff p i))).length

/-- **Common `t`-power** `commonTPow ps` shared by every represented polynomial in `ps`: the `min` of their
leading-zero counts (`0` for the empty list). The maximal `t^k` dividing all of `ps` simultaneously. -/
def commonTPow (ps : List (P α)) : ℕ :=
  match ps.map cleadingZeros with
  | [] => 0
  | n :: ns => ns.foldl Nat.min n

/-- **Divide by `t^k`** by dropping `k` low coefficients. Sound only when the
first `k` coefficients are zero (the caller guarantees this via `commonTPow`); realizes division by the
monomial `t^k`. -/
def cdropTPow (k : ℕ) (p : P α) : P α :=
  CPoly.ofFn (CPoly.degBound p - k) (fun i => CPoly.coeff p (i + k))

omit [CPolyEngine P] in
/-- Coefficient reading for division by a represented `t^k`. -/
theorem coeff_cdropTPow (k i : ℕ) (p : P α) :
    CPoly.coeff (cdropTPow k p) i =
      if i < CPoly.degBound p - k then CPoly.coeff p (i + k) else CCommRing.zero := by
  rw [cdropTPow, CPoly.coeff_ofFn]

example :
    let p : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(2, 3), (4, 5)]
    cleadingZeros p = 2 ∧ CPoly.coeff (cdropTPow 2 p) 0 = 3
      ∧ CPoly.coeff (cdropTPow 2 p) 2 = 5 := by
  native_decide

/-! ### The coordinate transform at infinity -/

/-- The `x = 1/t` coordinate transform at infinity `radTransformAtInfinity ρ g₀ g₁ D = (ρ̃, g̃₀, g̃₁, D̃)`
for `f dx = (g₀ + g₁·y)/D dx` on `y² = ρ`. With `m = ⌈deg ρ/2⌉`, `N = max(deg g₀, deg g₁, deg D)`, and
`revₖ p := t^k·p(1/t)`: `ρ̃ = rev_{2m} ρ`, `g̃₀ = −t^m·rev_N g₀`, `g̃₁ = −rev_N g₁`, `D̃ = t^{m+2}·rev_N D`,
with the common `t`-power cancelled so `∞` stays a simple pole. Generic over `[CField α]`. -/
def radTransformAtInfinity (rho g0 g1 D : P α) : P α × P α × P α × P α :=
  let d := CPolyEngine.cdeg rho
  let m := (d + 1) / 2                                            -- ⌈d/2⌉
  let N := max (max (CPolyEngine.cdeg g0) (CPolyEngine.cdeg g1)) (CPolyEngine.cdeg D)
  let rhoT := CPoly.creverseDeg (2 * m) rho                    -- t^{2m}·ρ(1/t)
  let g0raw := CPolyEngine.neg (CPoly.cshift m (CPoly.creverseDeg N g0)) -- −t^m·rev_N g₀
  let g1raw := CPolyEngine.neg (CPoly.creverseDeg N g1)        -- −rev_N g₁
  let Draw := CPoly.cshift (m + 2) (CPoly.creverseDeg N D)     -- t^{m+2}·rev_N D
  let k := commonTPow [g0raw, g1raw, Draw]
  (CPolyEngine.cnorm rhoT, CPolyEngine.cnorm (cdropTPow k g0raw),
    CPolyEngine.cnorm (cdropTPow k g1raw), CPolyEngine.cnorm (cdropTPow k Draw))

/-! ### The residue-at-infinity resultant (full + isolated-place) -/

/-- Full residue-at-infinity resultant `cAlgResidueAtInfinity ρ g₀ g₁ D = R̃(Z) ∈ K[Z]`: the residue
resultant `cAlgResidueResultant` on the `x = 1/t`-transformed data. `R̃(Z) = res_t((Z·D̃' − g̃₀)² −
g̃₁²·ρ̃, D̃)` factors over the roots of `D̃`; the residue at infinity is the `t = 0` factor. -/
def cAlgResidueAtInfinity (rho g0 g1 D : DensePoly α) : DensePoly α :=
  let (rhoT, g0T, g1T, DT) := radTransformAtInfinity rho g0 g1 D
  cAlgResidueResultant DT rhoT g0T g1T

/-- Isolated residue at the place `t = 0` (the residue at infinity) `cResidueAtInfinityPlace fuel ρ g₀ g₁ D
= (Z·D̃'(0) − g̃₀(0))² − g̃₁(0)²·ρ̃(0) ∈ K[Z]`, built from the constants `D̃'(0), g̃₀(0), g̃₁(0), ρ̃(0)`.
Isolates the single place `t = 0`, staying correct (residue `0`) even when `∞` is not a pole. -/
def cResidueAtInfinityPlace (fuel : ℕ) (rho g0 g1 D : P α) : P α :=
  let (rhoT, g0T, g1T, DT) := radTransformAtInfinity rho g0 g1 D
  let Dp0 := CPolyEngine.eval (CPolyEngine.deriv DT) CCommRing.zero -- D̃'(0)
  let a0 := CPolyEngine.eval g0T CCommRing.zero                     -- g̃₀(0)
  let b0 := CPolyEngine.eval g1T CCommRing.zero                     -- g̃₁(0)
  let r0 := CPolyEngine.eval rhoT CCommRing.zero                    -- ρ̃(0)
  let lin : P α := CPolyEngine.ofCoeffList [CCommRing.neg a0, Dp0] -- D̃'(0)·Z − g̃₀(0)
  let _ := fuel
  CPolyEngine.sub (CPolyEngine.mul lin lin)
    (CPolyEngine.ofCoeffList [CCommRing.mul (CCommRing.mul b0 b0) r0]) -- (·)² − g̃₁(0)²·ρ̃(0)

example :
    let ofList : List ℚ → CPoly.SparsePoly ℚ := CPolyEngine.ofCoeffList
    CPolyEngine.cisZero
      (CPolyEngine.sub (cResidueAtInfinityPlace 30
        (ofList [1, 0, 1]) (ofList []) (ofList [1]) (ofList [1, 0, 1]))
        (ofList [-1, 0, 1])) = true := by
  native_decide

end DensePoly

/-! ### Validation: `∫ dx/√(x²+1)` (arcsinh) and `∫ dx/√(x²−1)` (arccosh) — residues at ∞

For `∫ dx/√(x² + 1)` on `y² = x² + 1`: `g = y` (`g₀ = 0, g₁ = 1`), `D = x² + 1`; the transform gives
`(ρ̃, g̃₀, g̃₁, D̃) = (1 + t², 0, −1, t(1 + t²))`, `t = 0` place residue resultant `Z² − 1`, residues `±1`.
The arccosh case is identical with `ρ = x² − 1`. -/

open DensePoly

/-- arcsinh radicand `ρ = x² + 1` (curve `y² = x² + 1`), `ℚ[x]` `[1, 0, 1]`. -/
def arcsinhInf_rho : DensePoly ℚ := [1, 0, 1]
/-- arcsinh numerator low part `g₀ = 0` (`g = y`). -/
def arcsinhInf_g0 : DensePoly ℚ := []
/-- arcsinh numerator `y`-coefficient `g₁ = 1` (`g = y`), `ℚ[x]` `[1]`. -/
def arcsinhInf_g1 : DensePoly ℚ := [1]
/-- arcsinh denominator `D = ρ = x² + 1` (`f = 1/y = y/ρ`), `ℚ[x]` `[1, 0, 1]`. -/
def arcsinhInf_D : DensePoly ℚ := [1, 0, 1]

/-- arccosh radicand `ρ = x² − 1` (curve `y² = x² − 1`), `ℚ[x]` `[−1, 0, 1]`. -/
def arccoshInf_rho : DensePoly ℚ := [-1, 0, 1]
/-- arccosh denominator `D = ρ = x² − 1`, `ℚ[x]` `[−1, 0, 1]`. -/
def arccoshInf_D : DensePoly ℚ := [-1, 0, 1]

-- Sanity print: `(ρ̃, g̃₀, g̃₁, D̃) = (1+t², 0, −1, t(1+t²))`, then the `t=0` place residue `Z²−1`.
#eval (radTransformAtInfinity arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D : DensePoly ℚ × DensePoly ℚ × DensePoly ℚ × DensePoly ℚ)
#eval (cnorm (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D) : List ℚ)

/-- The `x = 1/t` transform of `(x² + 1, 0, 1, x² + 1)` is `(1 + t², 0, −1, t(1 + t²))`, the common `t²`
cancelled so `D̃ = t(1 + t²)` keeps `∞` a simple pole. -/
theorem arcsinhInf_transform_eq :
    radTransformAtInfinity arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D
      = ([1, 0, 1], [], [-1], [0, 1, 0, 1]) := by native_decide

/-- Residue at infinity of `∫ dx/√(x² + 1)` is `±1`: the isolated `t = 0` place residue resultant is
`Z² − 1`, the log term `log(x + √(x² + 1)) = arcsinh(x)`. -/
theorem arcsinhInf_residue_eq :
    cisZero (csub (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D)
      [-1, 0, 1]) = true := by native_decide

/-- The full transformed resultant exposes the same `±1`: `R̃(Z) = 16·Z⁴·(Z² − 1)`; the factor `Z² − 1` is
the `t = 0` place (residues `±1`), the `Z⁴` the zero-residue branch places `t = ±i`. -/
theorem arcsinhInf_full_resultant_eq :
    cisZero (csub (cAlgResidueAtInfinity arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D)
      [0, 0, 0, 0, -16, 0, 16]) = true := by native_decide

/-- `±1` are residues at ∞; `2` is not: `CPoly.isRoot` on the isolated place resultant `Z² − 1` accepts
`Z = ±1` and rejects `Z = 2`. -/
theorem arcsinhInf_isResidue :
    CPoly.isRoot (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D)
        (1 : ℚ) = true
    ∧ CPoly.isRoot (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D)
        (-1 : ℚ) = true
    ∧ CPoly.isRoot (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D)
        (2 : ℚ) = false := by
  native_decide

/-- Residue at infinity of `∫ dx/√(x² − 1)` (arccosh) is `±1`: the isolated `t = 0` place residue resultant
is `Z² − 1`, the log term `log(x + √(x² − 1)) = arccosh(x)`. -/
theorem arccoshInf_residue_eq :
    cisZero (csub (cResidueAtInfinityPlace 30 arccoshInf_rho arcsinhInf_g0 arcsinhInf_g1 arccoshInf_D)
      [-1, 0, 1]) = true := by native_decide

/-! ### The residue theorem as cross-check

For `∫ dx/√(x² ± 1)` the finite residue resultant is a pure power of `Z` (all finite residues `0`) while
the residue at infinity is `±1`, summing to `0`. -/

/-- All finite residues of `∫ dx/√(x² + 1)` vanish: the finite residue resultant `cAlgResidueResultant D ρ
g₀ g₁ = 16·Z⁴`, a pure `Z`-power. -/
theorem arcsinhInf_finite_residues_zero :
    cisZero (csub (cAlgResidueResultant arcsinhInf_D arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1)
      [0, 0, 0, 0, 16]) = true := by native_decide

/-- The residue theorem for `∫ dx/√(x² + 1)`: finite residues all `0` and residues at ∞ are `±1`, summing
to `0`. The ∞ side is certified by `CPoly.matchesLinearFactors` on `Z² − 1`. -/
theorem arcsinhInf_residue_theorem :
    CPoly.matchesLinearFactors (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D) [1, -1] = true
    ∧ cisZero (cAlgResidueResultant arcsinhInf_D arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1) = false
    ∧ CPoly.matchesLinearFactors (cAlgResidueResultant arcsinhInf_D arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1) [0, 0, 0, 0] = true := by
  native_decide

/-! ### A differential with both finite and ∞ residues nonzero

`∫ √(x² + 1)/(x² − x) dx`, `f = y/(x² − x)` on `y² = x² + 1`: the finite resultant is `(Z² − 1)(Z² − 2)`
(residues `±1, ±√2`), the residue at ∞ is `Z² − 1` (residues `±1`); both sum to `0`. -/

/-- both-nonzero radicand `ρ = x² + 1`, `ℚ[x]` `[1, 0, 1]`. -/
def bothInf_rho : DensePoly ℚ := [1, 0, 1]
/-- both-nonzero numerator `g = y` (`g₀ = 0`). -/
def bothInf_g0 : DensePoly ℚ := []
/-- both-nonzero numerator `y`-coefficient `g₁ = 1`. -/
def bothInf_g1 : DensePoly ℚ := [1]
/-- both-nonzero denominator `D = x² − x = x(x − 1)`, `ℚ[x]` `[0, −1, 1]`. -/
def bothInf_D : DensePoly ℚ := [0, -1, 1]

-- Sanity: finite `(Z²−1)(Z²−2) = Z⁴−3Z²+2`, then the ∞ place `Z²−1`.
#eval (cnorm (cAlgResidueResultant bothInf_D bothInf_rho bothInf_g0 bothInf_g1) : List ℚ)
#eval (cnorm (cResidueAtInfinityPlace 40 bothInf_rho bothInf_g0 bothInf_g1 bothInf_D) : List ℚ)

/-- Finite residue resultant of `∫ √(x²+1)/(x²−x) dx` is `(Z²−1)(Z²−2) = Z⁴ − 3Z² + 2`, finite residues
`±1` (pole `x = 0`) and `±√2` (pole `x = 1`). -/
theorem bothInf_finite_resultant_eq :
    cisZero (csub (cAlgResidueResultant bothInf_D bothInf_rho bothInf_g0 bothInf_g1)
      [2, 0, -3, 0, 1]) = true := by native_decide

/-- Residue at infinity of `∫ √(x²+1)/(x²−x) dx` is `±1`: the isolated `t = 0` place resultant is `Z² − 1`,
so this differential has nontrivial residues at both finite poles and infinity. -/
theorem bothInf_infinity_residue_eq :
    cisZero (csub (cResidueAtInfinityPlace 40 bothInf_rho bothInf_g0 bothInf_g1 bothInf_D)
      [-1, 0, 1]) = true := by native_decide

/-- The residue theorem for `∫ √(x²+1)/(x²−x) dx`: finite + ∞ residues sum to `0`. Via Vieta, each resultant
has vanishing second-leading coefficient (checked: the `Z³` coefficient of the finite resultant and the
`Z¹` coefficient of the ∞ resultant are both `0`), so each root-sum is `0`. -/
theorem bothInf_residue_theorem :
    ((cnorm (cAlgResidueResultant bothInf_D bothInf_rho bothInf_g0 bothInf_g1) : List ℚ).getD 3 0 = 0)
    ∧ ((cnorm (cResidueAtInfinityPlace 40 bothInf_rho bothInf_g0 bothInf_g1 bothInf_D) : List ℚ).getD 1 0 = 0)
    ∧ cisZero (cAlgResidueResultant bothInf_D bothInf_rho bothInf_g0 bothInf_g1) = false
    ∧ cisZero (cResidueAtInfinityPlace 40 bothInf_rho bothInf_g0 bothInf_g1 bothInf_D) = false := by
  native_decide

/-! ### The odd-`deg ρ` case — a branch place at infinity

When `deg ρ` is odd, `∞` is a single branch place and the transform degenerates: `ρ̃(0) = 0`, so
`ỹ² = ρ̃` is ramified at `t = 0` (a Puiseux place), beyond the simple-pole residue resultant. Probed
on `∫ dx/√(x³)`, where the transform yields `ρ̃ = t`. -/

/-- Odd-degree probe radicand `ρ = x³`, `ℚ[x]` `[0, 0, 0, 1]` (branch place at ∞). -/
def oddInf_rho : DensePoly ℚ := [0, 0, 0, 1]
/-- Odd-degree probe denominator `D = x³` (`f = 1/y = y/ρ`), `ℚ[x]` `[0, 0, 0, 1]`. -/
def oddInf_D : DensePoly ℚ := [0, 0, 0, 1]

-- Probe: `ρ̃ = t` (deg 1, odd ⇒ ramified — `ỹ = √t` Puiseux), place computation degenerates to `−Z²`.
#eval (radTransformAtInfinity oddInf_rho arcsinhInf_g0 arcsinhInf_g1 oddInf_D : DensePoly ℚ × DensePoly ℚ × DensePoly ℚ × DensePoly ℚ)
#eval (cnorm (cResidueAtInfinityPlace 30 oddInf_rho arcsinhInf_g0 arcsinhInf_g1 oddInf_D) : List ℚ)

/-- The odd-degree transform leaves a ramified radicand: `∫ dx/√(x³)` transforms to `ρ̃ = t = [0, 1]`
(`ρ̃(0) = 0`), so `ỹ² = ρ̃` is ramified at `t = 0` — a Puiseux place beyond the simple-pole residue
resultant. -/
theorem oddInf_radicand_ramified :
    (radTransformAtInfinity oddInf_rho arcsinhInf_g0 arcsinhInf_g1 oddInf_D).1 = [0, 1] := by
  native_decide

/-! ### Axiom audit -/

#print axioms arcsinhInf_transform_eq
#print axioms arcsinhInf_residue_eq
#print axioms arcsinhInf_residue_theorem

end DeepWiki.SymbolicIntegration
