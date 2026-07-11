import DeepWiki.SymbolicIntegration.Engine.Tower.Integrate
import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgebraicResidues
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.ComputableAlgebra.PolySquarefree

/-! # Algebraic-function integration: the simple-radical integral basis

For a simple radical extension `ℚ(x)[y]/(y² − ρ)` (`ρ ∈ ℚ[x]`) the integral closure of `ℚ[x]` has the
explicit basis `[1, y/d]`, where `ρ = d²·s` splits into the square part `d = ∏ᵢ Pᵢ^{⌊i/2⌋}` and the
squarefree part `s = ρ/d² = ∏_{i odd} Pᵢ` (from the multiplicity-indexed squarefree factorization). The
basis is represented by the pair `(d, s)` with `(y/d)² = s`. The executable checks cover `d²·s = ρ`, `s`
squarefree (`y/d` integral), and `y/(d·P)` not integral for nonconstant `P` (maximality); plus the basis
discriminant `4s` and the hyperelliptic genus `⌈deg s/2⌉ − 1`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u

namespace CPoly

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
  [CPolySquarefree P]
variable {α : Type u} [CField α]

/-! ### The square-part / squarefree-part split for `n = 2`

`ρ = d²·s`: `d = ∏ᵢ Pᵢ^{⌊i/2⌋}` and `s = ∏_{i odd} Pᵢ` (squarefree), from the multiplicity-indexed
squarefree factorization `ρ = ∏ᵢ Pᵢ^i` (`cSqfreeYunFF`). -/

/-- Square part `radSquarePart ρ = d = ∏ᵢ Pᵢ^{⌊i/2⌋}`: the root of the largest square divisor of `ρ`
(each squarefree part `Pᵢ` of multiplicity `i` contributes `Pᵢ^{⌊i/2⌋}`), so `d² ∣ ρ` and `ρ/d²` is
squarefree. Monic. -/
def radSquarePart (ρ : P α) : P α :=
  (squarefreeYun ρ).zipIdx.foldl
    (fun acc (Pi, i) => CPolyEngine.mul acc (CPoly.cpow Pi ((i + 1) / 2))) CPoly.one

/-- Squarefree part `radSquarefreePart ρ = s = ∏_{i odd} Pᵢ = ρ/d²`: one copy of each odd-multiplicity
factor `Pᵢ`, so `ρ = d²·s` with `d = radSquarePart` and `s` squarefree by construction. Monic. -/
def radSquarefreePart (ρ : P α) : P α :=
  (squarefreeYun ρ).zipIdx.foldl
    (fun acc (Pi, i) => if (i + 1) % 2 = 1 then CPolyEngine.mul acc Pi else acc) CPoly.one

/-! ### The integral basis `[1, y/d]`

`d = radSquarePart ρ`, `s = radSquarefreePart ρ`; `(y/d)² = s` is squarefree hence integral, and `y/d` is
the maximal integral element of the form `y/q`. Returned as the pair `(d, s)`. -/

/-- The simple-radical integral basis `radIntegralBasis ρ = (d, s)` for `ℚ[x][y]/(y² − ρ)`: the integral
closure of `ℚ[x]` has basis `[1, y/d]` with `d = radSquarePart ρ`, `s = radSquarefreePart ρ = ρ/d²`
squarefree, `(y/d)² = s` (`[1, y]` for squarefree `ρ`). -/
def radIntegralBasis (ρ : P α) : P α × P α :=
  (radSquarePart ρ, radSquarefreePart ρ)

/-! ### Integral-closure validation predicates

The basis `[1, y/d]` is integral and maximal iff: (a) the split is exact, `d²·s = ρ`, so `s = ρ/d²` is a
genuine polynomial (`y/d` satisfies the monic `T² − s = 0` over `ℚ[x]`) and `s` is squarefree
(`gcd(s, s') = 1`); (b) for any nonconstant `P`, `y/(d·P)` is NOT integral — its would-be minimal
polynomial `T² − s/P²` is not over `ℚ[x]`, i.e. `P² ∤ s`, which holds for every nonconstant `P` exactly
because `s` is squarefree. -/

/-- **The square-part split is exact** `radSplitExact ρ`: `d²·s = ρ` where `(d, s) = radIntegralBasis
ρ` — so `s = ρ/d²` is a genuine `ℚ[x]` polynomial (no fractional residue), the precondition that `y/d`
satisfies the monic `T² − s = 0` over `ℚ[x]`. Checked by `cisZero (d²·s − ρ)`, comparing monic-normalized
(the Yun factors are monic, so `d, s` are; `ρ` is taken monic). Representation-independent. -/
def radSplitExact (ρ : P α) : Bool :=
  let d := radSquarePart ρ
  let s := radSquarefreePart ρ
  CPolyEngine.cisZero
    (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.mul d d) s) (CPolyEngine.cmonic ρ))

/-- **`y/d` is integral: `s` is squarefree** `radSquarefreePartIsSquarefree ρ`: `gcd(s, s') = 1`
(constant) where `s = radSquarefreePart ρ`. Together with `radSplitExact` this is exactly "`y/d` is
integral over `ℚ[x]`" — `(y/d)² = s` is a squarefree polynomial, so `y/d` is a root of the monic
`T² − s ∈ ℚ[x][T]` and the integral closure contains it. Checked by `cdeg (gcd s s') = 0` through the
selected Euclidean capability. -/
def radSquarefreePartIsSquarefree (ρ : P α) : Bool :=
  let s := radSquarefreePart ρ
  CPolyEngine.cdeg (CPolyEuclidean.gcdExt s (CPolyEngine.deriv s)).1 = 0

/-- `radNotIntegralFactor ρ P` checks that `P² ∤ s` for nonconstant `P`, where
`s = radSquarefreePart ρ`. The basis-maximality witness — `y/(d·P)` would need minimal polynomial
`T² − s/P²` over `ℚ[x]`, but `P² ∤ s` (since `s` is squarefree, no nonconstant square divides it), so
`s/P²` is not a polynomial and `y/(d·P)` is not integral. Hence `y/d` is the maximal integral element of
the form `y/q`. Returns `true` (= "not integral", `P² ∤ s`) for nonconstant `P`; `false` for constant `P`
(`y/d` itself, which is integral). Checked by `¬ (P² ∣ s)` via `CPolyEuclidean.dvd`.
Representation-independent. -/
def radNotIntegralFactor (ρ factor : P α) : Bool :=
  let s := radSquarefreePart ρ
  if CPolyEngine.cdeg factor = 0 then false
  else !(CPolyEuclidean.dvd (CPolyEngine.mul factor factor) s)

/-! ### Discriminant and genus of the simple-radical basis

For `y² = s` with `s` squarefree, the minimal polynomial of `y/d` is `T² − s`, whose discriminant is
`4s` (up to the unit `1`). The genus of the hyperelliptic curve `y² = s` with `s` squarefree of degree
`m` is `g = ⌈m/2⌉ − 1`. `radSplitExact` guarantees `s = ρ/d²` is the genuine squarefree radicand. -/

/-- **Basis discriminant** `radBasisDiscriminant ρ = 4·s` — the discriminant of the minimal
polynomial `T² − s` of the basis element `y/d` (`s = radSquarefreePart ρ`): `disc(T² − s) = 0² − 4·1·(−s)
= 4s`. The polynomial discriminant `disc(T² + bT + c) = b² − 4c` at `b = 0, c = −s`. (Up to the unit `1`
this is `s` itself; the `4` is the classical normalization.) Representation-independent. -/
def radBasisDiscriminant (ρ : P α) : P α :=
  CPolyEngine.scale (CField.natCast 4) (radSquarefreePart ρ)

/-- **Genus** `radGenus ρ = ⌈deg s / 2⌉ − 1` — the genus of the hyperelliptic curve `y² = s`
(`s = radSquarefreePart ρ` squarefree of degree `m`): `g = ⌈m/2⌉ − 1 = (m + 1)/2 − 1` (`ℕ`-division, so
`(m + 1)/2` is `⌈m/2⌉`). For simple radicals `y² = s`, `g = 0` (rational) for `deg s ≤ 2`, `g = 1`
(elliptic) for `deg s ∈ {3, 4}`, etc. Representation-independent. -/
def radGenus (ρ : P α) : ℕ :=
  let m := CPolyEngine.cdeg (radSquarefreePart ρ)
  (m + 1) / 2 - 1

end CPoly

/-- The sparse simple-radical basis for `(x - 1)²(x + 2)` is `[1, y/(x - 1)]`. -/
example :
    let rho : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(0, 2), (1, -3), (3, 1)]
    let basis := CPoly.radIntegralBasis rho
    CPolyEngine.cisZero
          (CPolyEngine.sub basis.1 (CPoly.SparsePoly.ofList [(0, -1), (1, 1)])) = true
      ∧ CPolyEngine.cisZero
          (CPolyEngine.sub basis.2 (CPoly.SparsePoly.ofList [(0, 2), (1, 1)])) = true
      ∧ CPoly.radSplitExact rho = true
      ∧ CPoly.radSquarefreePartIsSquarefree rho = true := by
  ccompute

/-! ## Examples over `ℚ[x]` (`native_decide`)

`α = ℚ`, so `DensePoly ℚ = ℚ[x]` and the radicand `ρ ∈ ℚ[x]` is a coefficient list (low to high). All
operations are list/`ℚ` arithmetic; the `CFracGcdCore ℚ` / `CField ℚ` instances reduce in the native
compiler. -/

open CPoly

/-! ### The square-part / squarefree-part split computes

`ρ = x³+1` (squarefree → `d = 1, s = ρ`); `ρ = x³+x² = x²(x+1)` (→ `d = x, s = x+1`); `ρ = x⁵−x⁴ =
x⁴(x−1)` (→ `d = x², s = x−1`). -/

/-- The radicand `ρ = x³ + 1 ∈ ℚ[x]` (`[1,0,0,1]`), squarefree. -/
def basisRhoX3p1 : DensePoly ℚ := [1, 0, 0, 1]

/-- The radicand `ρ = x³ + x² = x²(x+1) ∈ ℚ[x]` (`[0,0,1,1]`), square part `x`. -/
def basisRhoX3pX2 : DensePoly ℚ := [0, 0, 1, 1]

/-- The radicand `ρ = x⁵ − x⁴ = x⁴(x−1) ∈ ℚ[x]` (`[0,0,0,0,-1,1]`), square part `x²`. -/
def basisRhoX5mX4 : DensePoly ℚ := [0, 0, 0, 0, -1, 1]

/-- **Squarefree `ρ = x³+1` ⇒ `d = 1`** (`native_decide`): the square part of a squarefree radicand is the
unit `1`, so the basis is `[1, y]`. -/
theorem radSquarePart_x3p1 :
    cisZero (csub (radSquarePart basisRhoX3p1) [CCommRing.one]) = true := by native_decide

/-- **Squarefree `ρ = x³+1` ⇒ `s = x³+1`** (`native_decide`): the squarefree part of a squarefree radicand
is the radicand itself (monic). -/
theorem radSquarefreePart_x3p1 :
    cisZero (csub (radSquarefreePart basisRhoX3p1) (cmonic basisRhoX3p1)) = true := by
  native_decide

/-- **`ρ = x²(x+1) ⇒ d = x`** (`native_decide`): the square part of `x³ + x²` is `x` (one copy of the
multiplicity-2 factor `x`). -/
theorem radSquarePart_x3pX2 :
    cisZero (csub (radSquarePart basisRhoX3pX2) [0, 1]) = true := by native_decide

/-- **`ρ = x²(x+1) ⇒ s = x+1`** (`native_decide`): the squarefree part of `x³ + x²` is `x + 1` (the
odd-multiplicity factor; the even factor `x²` goes entirely into `d²`). -/
theorem radSquarefreePart_x3pX2 :
    cisZero (csub (radSquarefreePart basisRhoX3pX2) [1, 1]) = true := by native_decide

/-- **`ρ = x⁴(x−1) ⇒ d = x²`** (`native_decide`): the square part of `x⁵ − x⁴` is `x²` (two copies of the
multiplicity-4 factor `x`). -/
theorem radSquarePart_x5mX4 :
    cisZero (csub (radSquarePart basisRhoX5mX4) [0, 0, 1]) = true := by native_decide

/-- **`ρ = x⁴(x−1) ⇒ s = x−1`** (`native_decide`): the squarefree part of `x⁵ − x⁴` is `x − 1` (the
odd-multiplicity factor; `x⁴ = (x²)²` is entirely the square part). -/
theorem radSquarefreePart_x5mX4 :
    cisZero (csub (radSquarefreePart basisRhoX5mX4) [-1, 1]) = true := by native_decide

/-! ### The integral basis validates: `[1, y/d]` is the integral closure (`native_decide`)

For each radicand: the split `d²·s = ρ` is exact (`s` a genuine polynomial), `s` is squarefree (`y/d`
integral), and `y/(d·P)` is not integral for a sample nonconstant `P` (maximality). -/

/-- `radSplitExact` holds for `x²(x+1)` (`native_decide`): `x²·(x+1) = x³ + x²`, so
`s = ρ/d² = x+1 ∈ ℚ[x]` is a genuine polynomial — `y/d = y/x` satisfies the monic `T² − (x+1) = 0` over
`ℚ[x]`. -/
theorem radSplitExact_x3pX2 : radSplitExact basisRhoX3pX2 = true := by native_decide

/-- `radSplitExact` holds for `x⁴(x−1)` (`native_decide`): `(x²)²·(x−1) = x⁵ − x⁴`, so
`s = x−1 ∈ ℚ[x]` and `y/x²` satisfies `T² − (x−1) = 0`. -/
theorem radSplitExact_x5mX4 : radSplitExact basisRhoX5mX4 = true := by native_decide

/-- `radSplitExact` holds for squarefree `x³+1` (`native_decide`): `1²·(x³+1) = x³+1`. -/
theorem radSplitExact_x3p1 : radSplitExact basisRhoX3p1 = true := by native_decide

/-- `s = x+1` is squarefree (`native_decide`): `gcd(s, s') = gcd(x+1, 1) = 1`, so
the minimal polynomial `T² − (x+1)` has squarefree constant term — `y/x` is in the integral closure
(closure half 1, the squarefree certificate). -/
theorem radSquarefree_x3pX2 : radSquarefreePartIsSquarefree basisRhoX3pX2 = true := by native_decide

/-- `s = x³+1` is squarefree (`native_decide`): `gcd(x³+1, 3x²) = 1`, so `y = y/1` is integral
(`[1, y]` is the closure for squarefree radicand). -/
theorem radSquarefree_x3p1 : radSquarefreePartIsSquarefree basisRhoX3p1 = true := by native_decide

/-- `s = x−1` is squarefree (`native_decide`): `gcd(x−1, 1) = 1`, so `y/x²` is integral. -/
theorem radSquarefree_x5mX4 : radSquarefreePartIsSquarefree basisRhoX5mX4 = true := by native_decide

/-- `y/(x·(x+1))` is not integral for `x²(x+1)` (`native_decide`): with `P = x+1`,
`P² = (x+1)² ∤ s = x+1` (the squarefree `s` has no nonconstant square divisor), so the would-be minimal
polynomial `T² − (x+1)/(x+1)²` is not over `ℚ[x]`. Hence `y/d = y/x` is the maximal integral element of
the form `y/q` (closure half 2, maximality). -/
theorem radNotIntegral_x3pX2 :
    radNotIntegralFactor basisRhoX3pX2 [1, 1] = true := by native_decide

/-- `y/(x²·(x−1))` is not integral for `x⁴(x−1)` (`native_decide`): with `P = x−1`,
`(x−1)² ∤ (x−1) = s`, so dividing the basis denominator further leaves the integral closure. Maximality of
`y/x²`. -/
theorem radNotIntegral_x5mX4 :
    radNotIntegralFactor basisRhoX5mX4 [-1, 1] = true := by native_decide

/-- `y/x` is not integral for the squarefree `x³+1` (`native_decide`): with
`P = x`, `x² ∤ x³+1`, so `y/x` is not integral — `y = y/1` is already maximal (the basis `[1, y]` cannot
be improved). Maximality for the squarefree case. -/
theorem radNotIntegral_x3p1 :
    radNotIntegralFactor basisRhoX3p1 [0, 1] = true := by native_decide

/-- The simple-radical integral-basis certificates validate for three sample radicands
(`native_decide`): the split is exact, the squarefree part is squarefree, and the displayed denominator
extensions are not integral. -/
theorem radIntegralBasis_validates :
    (radSplitExact basisRhoX3p1 = true
      ∧ radSquarefreePartIsSquarefree basisRhoX3p1 = true
      ∧ radNotIntegralFactor basisRhoX3p1 [0, 1] = true)
    ∧ (radSplitExact basisRhoX3pX2 = true
      ∧ radSquarefreePartIsSquarefree basisRhoX3pX2 = true
      ∧ radNotIntegralFactor basisRhoX3pX2 [1, 1] = true)
    ∧ (radSplitExact basisRhoX5mX4 = true
      ∧ radSquarefreePartIsSquarefree basisRhoX5mX4 = true
      ∧ radNotIntegralFactor basisRhoX5mX4 [-1, 1] = true) := by native_decide

/-! ### Discriminant and genus (`native_decide`)

The basis discriminant `4s`, and the hyperelliptic genus `⌈deg s/2⌉ − 1`: `y² = x` (genus 0, rational),
`y² = x³+1` (genus 1, elliptic ✓), `y² = x⁵+1` (genus 2). -/

/-- The radicand `ρ = x ∈ ℚ[x]` (`[0,1]`), `y² = x` (the parabola / rational curve). -/
def basisRhoX : DensePoly ℚ := [0, 1]

/-- The radicand `ρ = x⁵ + 1 ∈ ℚ[x]` (`[1,0,0,0,0,1]`), `y² = x⁵+1` (genus-2 hyperelliptic). -/
def basisRhoX5p1 : DensePoly ℚ := [1, 0, 0, 0, 0, 1]

/-- **Discriminant `disc = 4(x+1)` for `x²(x+1)`** (`native_decide`): the basis `[1, y/x]` has minimal
polynomial `T² − (x+1)`, discriminant `4(x+1) = 4x + 4` (`[4,4]`). -/
theorem radBasisDiscriminant_x3pX2 :
    cisZero (csub (radBasisDiscriminant basisRhoX3pX2) [4, 4]) = true := by native_decide

/-- **Discriminant `disc = 4(x³+1)` for the squarefree `x³+1`** (`native_decide`): basis `[1, y]`,
minimal polynomial `T² − (x³+1)`, discriminant `4(x³+1) = 4 + 4x³` (`[4,0,0,4]`). -/
theorem radBasisDiscriminant_x3p1 :
    cisZero (csub (radBasisDiscriminant basisRhoX3p1) [4, 0, 0, 4]) = true := by native_decide

/-- Genus `0` for `y² = x` (`native_decide`): `deg s = 1`, so `⌈1/2⌉ − 1 = 0`. -/
theorem radGenus_x : radGenus basisRhoX = 0 := by native_decide

/-- Genus `1` for `y² = x³+1` (`native_decide`): `deg s = 3`, so `⌈3/2⌉ − 1 = 1`. -/
theorem radGenus_x3p1 : radGenus basisRhoX3p1 = 1 := by native_decide

/-- Genus `2` for `y² = x⁵+1` (`native_decide`): `deg s = 5`, so `⌈5/2⌉ − 1 = 2`. -/
theorem radGenus_x5p1 : radGenus basisRhoX5p1 = 2 := by native_decide

/-- The simple-radical genus computation returns `0`, `1`, and `2` for the sample radicands
(`native_decide`). -/
theorem radGenus_validates :
    radGenus basisRhoX = 0 ∧ radGenus basisRhoX3p1 = 1 ∧ radGenus basisRhoX5p1 = 2 := by
  native_decide

end DeepWiki.SymbolicIntegration
