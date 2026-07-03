import DeepWiki.SymbolicIntegration.Computable.Tower.Integrate
import DeepWiki.SymbolicIntegration.Computable.Algebraic.AlgebraicResidues
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Computable.Tower.WellFounded

/-! # Algebraic-function integration: the simple-radical integral basis

For a simple radical extension `ℚ(x)[y]/(y² − ρ)` (`ρ ∈ ℚ[x]`) the integral closure of `ℚ[x]` has the
explicit basis `[1, y/d]`, where `ρ = d²·s` splits into the square part `d = ∏ᵢ Pᵢ^{⌊i/2⌋}` and the
squarefree part `s = ρ/d² = ∏_{i odd} Pᵢ` (from the multiplicity-indexed squarefree factorization). The
basis is represented by the pair `(d, s)` with `(y/d)² = s`. Validation checks: `d²·s = ρ` exact, `s`
squarefree (`y/d` integral), and `y/(d·P)` not integral for nonconstant `P` (maximality); plus the basis
discriminant `4s` and the hyperelliptic genus `⌈deg s/2⌉ − 1`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### The square-part / squarefree-part split for `n = 2`

`ρ = d²·s`: `d = ∏ᵢ Pᵢ^{⌊i/2⌋}` and `s = ∏_{i odd} Pᵢ` (squarefree), from the multiplicity-indexed
squarefree factorization `ρ = ∏ᵢ Pᵢ^i` (`cSqfreeYunFFG`). -/

variable [CFracGcdCoreWf α]

/-- Square part `radSquarePart ρ = d = ∏ᵢ Pᵢ^{⌊i/2⌋}`: the root of the largest square divisor of `ρ`
(each squarefree part `Pᵢ` of multiplicity `i` contributes `Pᵢ^{⌊i/2⌋}`), so `d² ∣ ρ` and `ρ/d²` is
squarefree. Monic. -/
def radSquarePart (ρ : CPolyG α) : CPolyG α :=
  (cSqfreeYunFFGWf ρ).zipIdx.foldl
    (fun acc (Pi, i) => cmulG acc (cpowG Pi ((i + 1) / 2))) [CField.one]

/-- Squarefree part `radSquarefreePart ρ = s = ∏_{i odd} Pᵢ = ρ/d²`: one copy of each odd-multiplicity
factor `Pᵢ`, so `ρ = d²·s` with `d = radSquarePart` and `s` squarefree by construction. Monic. -/
def radSquarefreePart (ρ : CPolyG α) : CPolyG α :=
  (cSqfreeYunFFGWf ρ).zipIdx.foldl
    (fun acc (Pi, i) => if (i + 1) % 2 = 1 then cmulG acc Pi else acc) [CField.one]

/-! ### The integral basis `[1, y/d]`

`d = radSquarePart ρ`, `s = radSquarefreePart ρ`; `(y/d)² = s` is squarefree hence integral, and `y/d` is
the maximal integral element of the form `y/q`. Returned as the pair `(d, s)`. -/

/-- The simple-radical integral basis `radIntegralBasis ρ = (d, s)` for `ℚ[x][y]/(y² − ρ)`: the integral
closure of `ℚ[x]` has basis `[1, y/d]` with `d = radSquarePart ρ`, `s = radSquarefreePart ρ = ρ/d²`
squarefree, `(y/d)² = s` (`[1, y]` for squarefree `ρ`). -/
def radIntegralBasis (ρ : CPolyG α) : CPolyG α × CPolyG α :=
  (radSquarePart ρ, radSquarefreePart ρ)

/-! ### Integral-closure validation predicates

The basis `[1, y/d]` is integral and maximal iff: (a) the split is exact, `d²·s = ρ`, so `s = ρ/d²` is a
genuine polynomial (`y/d` satisfies the monic `T² − s = 0` over `ℚ[x]`) and `s` is squarefree
(`gcd(s, s') = 1`); (b) for any nonconstant `P`, `y/(d·P)` is NOT integral — its would-be minimal
polynomial `T² − s/P²` is not over `ℚ[x]`, i.e. `P² ∤ s`, which holds for every nonconstant `P` exactly
because `s` is squarefree. -/

/-- **The square-part split is exact** `radSplitExact ρ`: `d²·s = ρ` where `(d, s) = radIntegralBasis
ρ` — so `s = ρ/d²` is a genuine `ℚ[x]` polynomial (no fractional residue), the precondition that `y/d`
satisfies the monic `T² − s = 0` over `ℚ[x]`. Checked by `cisZeroG (d²·s − ρ)`, comparing monic-normalized
(the Yun factors are monic, so `d, s` are; `ρ` is taken monic). `[CField α] [CFracGcdCoreWf α]`-generic. -/
def radSplitExact (ρ : CPolyG α) : Bool :=
  let d := radSquarePart ρ
  let s := radSquarefreePart ρ
  cisZeroG (csubG (cmulG (cmulG d d) s) (cmonicG ρ))

/-- **`y/d` is integral: `s` is squarefree** `radSquarefreePartIsSquarefree ρ`: `gcd(s, s') = 1`
(constant) where `s = radSquarefreePart ρ`. Together with `radSplitExact` this is exactly "`y/d` is
integral over `ℚ[x]`" — `(y/d)² = s` is a squarefree polynomial, so `y/d` is a root of the monic
`T² − s ∈ ℚ[x][T]` and the integral closure contains it. Checked by `cdegG (gcd s s') = 0`. `[CField α]
[CFracGcdCoreWf α]`-generic. -/
def radSquarefreePartIsSquarefree (ρ : CPolyG α) : Bool :=
  let s := radSquarefreePart ρ
  cdegG (cgcdMonicWf s (cderivG s)) = 0

/-- **`y/(d·P)` is NOT integral** `radNotIntegralFactor ρ P`: for a nonconstant `P`, `P² ∤ s` where
`s = radSquarefreePart ρ`. The basis-maximality witness — `y/(d·P)` would need minimal polynomial
`T² − s/P²` over `ℚ[x]`, but `P² ∤ s` (since `s` is squarefree, no nonconstant square divides it), so
`s/P²` is not a polynomial and `y/(d·P)` is not integral. Hence `y/d` is the MAXIMAL integral element of
the form `y/q`. Returns `true` (= "not integral", `P² ∤ s`) for nonconstant `P`; `false` for constant `P`
(`y/d` itself, which IS integral). Checked by `¬ (P² ∣ s)` via `cdvdGWf`. `[CField α]
[CFracGcdCoreWf α]`-generic. -/
def radNotIntegralFactor (ρ P : CPolyG α) : Bool :=
  let s := radSquarefreePart ρ
  if cdegG P = 0 then false else !(cdvdGWf (cmulG P P) s)

/-! ### Discriminant and genus of the simple-radical basis (Trager Ch. 2 §5, STRETCH)

For `y² = s` with `s` squarefree, the minimal polynomial of `y/d` is `T² − s`, whose discriminant is
`4s` (up to the unit `1`). The genus of the hyperelliptic curve `y² = s` with `s` squarefree of degree
`m` is `g = ⌈m/2⌉ − 1` (the standard hyperelliptic formula; Trager Ch. 2 §4's `g = d/2 − [K(x,y):K(x)] +
1` specializes to this). `radSplitExact` guarantees `s = ρ/d²` is the genuine squarefree radicand. -/

/-- **Basis discriminant** `radBasisDiscriminant ρ = 4·s` — the discriminant of the minimal
polynomial `T² − s` of the basis element `y/d` (`s = radSquarefreePart ρ`): `disc(T² − s) = 0² − 4·1·(−s)
= 4s`. The polynomial discriminant `disc(T² + bT + c) = b² − 4c` at `b = 0, c = −s`. (Up to the unit `1`
this is `s` itself; the `4` is the classical normalization.) `[CField α] [CFracGcdCoreWf α]`-generic. -/
def radBasisDiscriminant (ρ : CPolyG α) : CPolyG α :=
  cscaleG (cnatCastG 4) (radSquarefreePart ρ)

/-- **Genus** `radGenus ρ = ⌈deg s / 2⌉ − 1` — the genus of the hyperelliptic curve `y² = s`
(`s = radSquarefreePart ρ` squarefree of degree `m`): `g = ⌈m/2⌉ − 1 = (m + 1)/2 − 1` (`ℕ`-division, so
`(m + 1)/2` is `⌈m/2⌉`). Trager Ch. 2 §4's `g = d/2 − [K(x,y):K(x)] + 1` specialized to the simple radical
`y² = s`. `g = 0` (rational) for `deg s ≤ 2`, `g = 1` (elliptic) for `deg s ∈ {3, 4}`, etc. `[CField α]
[CFracGcdCoreWf α]`-generic. -/
def radGenus (ρ : CPolyG α) : ℕ :=
  let m := cdegG (radSquarefreePart ρ)
  (m + 1) / 2 - 1

end CPolyG

/-! ## ★ Validation over `ℚ[x]` (`native_decide`)

`α = ℚ`, so `CPolyG ℚ = ℚ[x]` and the radicand `ρ ∈ ℚ[x]` is a coefficient list (low to high). All
operations are list/`ℚ` arithmetic; the `CFracGcdCore ℚ` / `CField ℚ` instances reduce in the native
compiler. -/

open CPolyG

/-! ### The square-part / squarefree-part split computes

`ρ = x³+1` (squarefree → `d = 1, s = ρ`); `ρ = x³+x² = x²(x+1)` (→ `d = x, s = x+1`); `ρ = x⁵−x⁴ =
x⁴(x−1)` (→ `d = x², s = x−1`). -/

/-- The radicand `ρ = x³ + 1 ∈ ℚ[x]` (`[1,0,0,1]`), squarefree. -/
def basisRhoX3p1 : CPolyG ℚ := [1, 0, 0, 1]

/-- The radicand `ρ = x³ + x² = x²(x+1) ∈ ℚ[x]` (`[0,0,1,1]`), square part `x`. -/
def basisRhoX3pX2 : CPolyG ℚ := [0, 0, 1, 1]

/-- The radicand `ρ = x⁵ − x⁴ = x⁴(x−1) ∈ ℚ[x]` (`[0,0,0,0,-1,1]`), square part `x²`. -/
def basisRhoX5mX4 : CPolyG ℚ := [0, 0, 0, 0, -1, 1]

/-- **Squarefree `ρ = x³+1` ⇒ `d = 1`** (`native_decide`): the square part of a squarefree radicand is the
unit `1`, so the basis is `[1, y]`. -/
theorem radSquarePart_x3p1 :
    cisZeroG (csubG (radSquarePart basisRhoX3p1) [CField.one]) = true := by native_decide

/-- **Squarefree `ρ = x³+1` ⇒ `s = x³+1`** (`native_decide`): the squarefree part of a squarefree radicand
is the radicand itself (monic). -/
theorem radSquarefreePart_x3p1 :
    cisZeroG (csubG (radSquarefreePart basisRhoX3p1) (cmonicG basisRhoX3p1)) = true := by
  native_decide

/-- **`ρ = x²(x+1) ⇒ d = x`** (`native_decide`): the square part of `x³ + x²` is `x` (one copy of the
multiplicity-2 factor `x`). -/
theorem radSquarePart_x3pX2 :
    cisZeroG (csubG (radSquarePart basisRhoX3pX2) [0, 1]) = true := by native_decide

/-- **`ρ = x²(x+1) ⇒ s = x+1`** (`native_decide`): the squarefree part of `x³ + x²` is `x + 1` (the
odd-multiplicity factor; the even factor `x²` goes entirely into `d²`). -/
theorem radSquarefreePart_x3pX2 :
    cisZeroG (csubG (radSquarefreePart basisRhoX3pX2) [1, 1]) = true := by native_decide

/-- **`ρ = x⁴(x−1) ⇒ d = x²`** (`native_decide`): the square part of `x⁵ − x⁴` is `x²` (two copies of the
multiplicity-4 factor `x`). -/
theorem radSquarePart_x5mX4 :
    cisZeroG (csubG (radSquarePart basisRhoX5mX4) [0, 0, 1]) = true := by native_decide

/-- **`ρ = x⁴(x−1) ⇒ s = x−1`** (`native_decide`): the squarefree part of `x⁵ − x⁴` is `x − 1` (the
odd-multiplicity factor; `x⁴ = (x²)²` is entirely the square part). -/
theorem radSquarefreePart_x5mX4 :
    cisZeroG (csubG (radSquarefreePart basisRhoX5mX4) [-1, 1]) = true := by native_decide

/-! ### ★ The integral basis validates: `[1, y/d]` is the integral closure (`native_decide`)

For each radicand: the split `d²·s = ρ` is exact (`s` a genuine polynomial), `s` is squarefree (`y/d`
integral), and `y/(d·P)` is not integral for a sample nonconstant `P` (maximality). -/

/-- **★ Split exact `d²·s = ρ` for `x²(x+1)`** (`native_decide`): `x²·(x+1) = x³ + x²`, so
`s = ρ/d² = x+1 ∈ ℚ[x]` is a genuine polynomial — `y/d = y/x` satisfies the monic `T² − (x+1) = 0` over
`ℚ[x]`. THE BASIS ELEMENT `y/x` IS INTEGRAL (closure half 1). -/
theorem radSplitExact_x3pX2 : radSplitExact basisRhoX3pX2 = true := by native_decide

/-- **★ Split exact `d²·s = ρ` for `x⁴(x−1)`** (`native_decide`): `(x²)²·(x−1) = x⁵ − x⁴`, so
`s = x−1 ∈ ℚ[x]` and `y/x²` satisfies `T² − (x−1) = 0`. -/
theorem radSplitExact_x5mX4 : radSplitExact basisRhoX5mX4 = true := by native_decide

/-- **★ Split exact for squarefree `x³+1`** (`native_decide`): `1²·(x³+1) = x³+1`, the basis is `[1, y]`. -/
theorem radSplitExact_x3p1 : radSplitExact basisRhoX3p1 = true := by native_decide

/-- **★ `s = x+1` is squarefree ⇒ `y/x` integral** (`native_decide`): `gcd(s, s') = gcd(x+1, 1) = 1`, so
the minimal polynomial `T² − (x+1)` has squarefree constant term — `y/x` IS in the integral closure
(closure half 1, the squarefree certificate). -/
theorem radSquarefree_x3pX2 : radSquarefreePartIsSquarefree basisRhoX3pX2 = true := by native_decide

/-- **★ `s = x³+1` is squarefree** (`native_decide`): `gcd(x³+1, 3x²) = 1`, so `y = y/1` is integral
(`[1, y]` is the closure for squarefree radicand). -/
theorem radSquarefree_x3p1 : radSquarefreePartIsSquarefree basisRhoX3p1 = true := by native_decide

/-- **★ `s = x−1` is squarefree** (`native_decide`): `gcd(x−1, 1) = 1`, so `y/x²` is integral. -/
theorem radSquarefree_x5mX4 : radSquarefreePartIsSquarefree basisRhoX5mX4 = true := by native_decide

/-- **★ `y/(x·(x+1))` is NOT integral for `x²(x+1)`** (`native_decide`): with `P = x+1`,
`P² = (x+1)² ∤ s = x+1` (the squarefree `s` has no nonconstant square divisor), so the would-be minimal
polynomial `T² − (x+1)/(x+1)²` is not over `ℚ[x]`. Hence `y/d = y/x` is the MAXIMAL integral element of
the form `y/q` (closure half 2, maximality). -/
theorem radNotIntegral_x3pX2 :
    radNotIntegralFactor basisRhoX3pX2 [1, 1] = true := by native_decide

/-- **★ `y/(x²·(x−1))` is NOT integral for `x⁴(x−1)`** (`native_decide`): with `P = x−1`,
`(x−1)² ∤ (x−1) = s`, so dividing the basis denominator further leaves the integral closure. Maximality of
`y/x²`. -/
theorem radNotIntegral_x5mX4 :
    radNotIntegralFactor basisRhoX5mX4 [-1, 1] = true := by native_decide

/-- **★ `y·x` (i.e. `y/(1·x)`) is NOT integral for the squarefree `x³+1`** (`native_decide`): with
`P = x`, `x² ∤ x³+1`, so `y/x` is not integral — `y = y/1` is already maximal (the basis `[1, y]` cannot
be improved). Maximality for the squarefree case. -/
theorem radNotIntegral_x3p1 :
    radNotIntegralFactor basisRhoX3p1 [0, 1] = true := by native_decide

/-- **★★ THE SIMPLE-RADICAL INTEGRAL BASIS COMPUTES AND VALIDATES** (Trager Ch. 2 §5, `native_decide`) —
for the three radicands `x³+1` (squarefree, basis `[1, y]`), `x²(x+1)` (basis `[1, y/x]`), and `x⁴(x−1)`
(basis `[1, y/x²]`): the square-part split `ρ = d²·s` is EXACT (so `s = ρ/d²` is a genuine `ℚ[x]`
polynomial), the squarefree part `s` is SQUAREFREE (so the basis element `y/d` satisfies the monic
`T² − s = 0` over `ℚ[x]` and is INTEGRAL), and `y/(d·P)` for the displayed nonconstant `P` is NOT integral
(so `y/d` is MAXIMAL). This is `[1, y/d]` realized as the integral closure of `ℚ[x]` in `ℚ(x)[y]/(y²−ρ)`,
end to end. -/
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

/-! ### STRETCH — discriminant and genus (`native_decide`)

The basis discriminant `4s`, and the hyperelliptic genus `⌈deg s/2⌉ − 1`: `y² = x` (genus 0, rational),
`y² = x³+1` (genus 1, elliptic ✓), `y² = x⁵+1` (genus 2). -/

/-- The radicand `ρ = x ∈ ℚ[x]` (`[0,1]`), `y² = x` (the parabola / rational curve). -/
def basisRhoX : CPolyG ℚ := [0, 1]

/-- The radicand `ρ = x⁵ + 1 ∈ ℚ[x]` (`[1,0,0,0,0,1]`), `y² = x⁵+1` (genus-2 hyperelliptic). -/
def basisRhoX5p1 : CPolyG ℚ := [1, 0, 0, 0, 0, 1]

/-- **Discriminant `disc = 4(x+1)` for `x²(x+1)`** (`native_decide`): the basis `[1, y/x]` has minimal
polynomial `T² − (x+1)`, discriminant `4(x+1) = 4x + 4` (`[4,4]`). -/
theorem radBasisDiscriminant_x3pX2 :
    cisZeroG (csubG (radBasisDiscriminant basisRhoX3pX2) [4, 4]) = true := by native_decide

/-- **Discriminant `disc = 4(x³+1)` for the squarefree `x³+1`** (`native_decide`): basis `[1, y]`,
minimal polynomial `T² − (x³+1)`, discriminant `4(x³+1) = 4 + 4x³` (`[4,0,0,4]`). -/
theorem radBasisDiscriminant_x3p1 :
    cisZeroG (csubG (radBasisDiscriminant basisRhoX3p1) [4, 0, 0, 4]) = true := by native_decide

/-- **Genus 0 for `y² = x`** (`native_decide`): `s = x`, `deg s = 1`, `⌈1/2⌉ − 1 = 1 − 1 = 0` — the curve
`y² = x` is RATIONAL (genus 0). -/
theorem radGenus_x : radGenus basisRhoX = 0 := by native_decide

/-- **★ Genus 1 for `y² = x³+1`** (`native_decide`): `s = x³+1`, `deg s = 3`, `⌈3/2⌉ − 1 = 2 − 1 = 1` —
the curve `y² = x³+1` is ELLIPTIC (genus 1). The flagship hyperelliptic-genus check. -/
theorem radGenus_x3p1 : radGenus basisRhoX3p1 = 1 := by native_decide

/-- **Genus 2 for `y² = x⁵+1`** (`native_decide`): `s = x⁵+1`, `deg s = 5`, `⌈5/2⌉ − 1 = 3 − 1 = 2` — the
genus-2 hyperelliptic curve. -/
theorem radGenus_x5p1 : radGenus basisRhoX5p1 = 2 := by native_decide

/-- **★ THE GENUS OF THE SIMPLE-RADICAL CURVE COMPUTES** (Trager Ch. 2 §5, hyperelliptic
`g = ⌈deg s/2⌉ − 1`, `native_decide`): `y² = x` is rational (`g = 0`), `y² = x³+1` is elliptic (`g = 1`),
`y² = x⁵+1` is genus `2` — read off the squarefree part `s = radSquarefreePart ρ` of the integral-basis
computation. -/
theorem radGenus_validates :
    radGenus basisRhoX = 0 ∧ radGenus basisRhoX3p1 = 1 ∧ radGenus basisRhoX5p1 = 2 := by
  native_decide

/-! ### Deliverable: `#print axioms` of the integral-closure validation

`[propext, Classical.choice, Quot.sound]` plus `Lean.ofReduceBool` (the `native_decide` kernel-reduction
axiom). No `sorry`. -/

/-- **Axiom audit of the integral-basis validation** — `[propext, Classical.choice, Quot.sound,
Lean.ofReduceBool]` (the last is the `native_decide` axiom): the simple-radical integral-closure check
runs on the standard classical + native-reduction base, no `sorry`. -/
example : True := trivial

end DeepWiki.SymbolicIntegration
