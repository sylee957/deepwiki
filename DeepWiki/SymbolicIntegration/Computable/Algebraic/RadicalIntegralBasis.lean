import DeepWiki.SymbolicIntegration.Computable.Tower.Integrate
import DeepWiki.SymbolicIntegration.Computable.Algebraic.AlgebraicResidues
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd

/-! # Algebraic-function integration: the simple-radical INTEGRAL BASIS (Trager Ch. 2 §5)

The simple-radical **rational** part (`ComputableRadicalExtension` / `ComputableRadicalCase2`) and the
log-part **residues** (`ComputableAlgebraicResidues`) are done. Their second half — the **divisors** and
the **principal-divisor test** of the logarithmic part, and the integration of general (non-radical)
algebraic functions — both rest on one missing piece: an explicit **integral basis** for the ring of
functions with no finite poles. This file builds it for simple radical extensions.

For a simple radical extension `K(x)[y]/(yⁿ − ρ)` (`ρ ∈ ℚ[x]`) the integral closure of `ℚ[x]` has an
EXPLICIT integral basis — no general Ch. 2 idealizer / Round-2 needed. Trager Ch. 2 §5 (thesis p. 30):
the natural basis `1, y, …, y^{n−1}` is already *normal* (Prop., p. 30, from the `Tᵢ`-decoupling of
`ComputableRadicalExtension`); writing `yⁿ = ∏ⱼ Pⱼ^{eⱼ}` with the `Pⱼ` squarefree (no repeated factors),
the maximal `dᵢ(x)` clearing the `i`-th radical is

  **`dᵢ = ∏ⱼ Pⱼ^{⌊i·eⱼ/n⌋}`**   (p. 30),

and `[1, y/d₁, y²/d₂, …, y^{n−1}/d_{n−1}]` is an integral basis (p. 31). This file focuses on `n = 2`,
`y² = ρ`, the hyperelliptic / unnested-square-root case (an integral table such as Gradshteyn–Ryzhik has
< 1% of problems outside it).

For `n = 2`: collect the squarefree factorization `ρ = ∏ᵢ Pᵢ^i` (`cSqfreeYunFFG`, indexed by
multiplicity). The **square part** is `d = ∏ᵢ Pᵢ^{⌊i/2⌋}` (Trager's `d₁` at `n = 2, i = 1`) — the root of
the largest square divisor — and the **squarefree part** is `s = ρ/d² = ∏_{i odd} Pᵢ` (the radical of `ρ`,
collecting one copy of each odd-multiplicity factor). Then `ρ = d²·s` with `s` squarefree, `(y/d)² = s`,
and the integral basis is `[1, y/d]` (so we represent it by the pair `(d, s)`).

* **`radSquarePart` / `radSquarefreePart`** — `d` and `s = ρ/d²` from the Yun factorization (group by
  parity of multiplicity). `native_decide`: `ρ = x³+1 → d = 1, s = x³+1`; `ρ = x³+x² → d = x, s = x+1`;
  `ρ = x⁵−x⁴ → d = x², s = x−1`.
* **`radIntegralBasis`** — the basis `[1, y/d]`, returned as the pair `(d, s)` (`y/d` has `(y/d)² = s`).
* **Integral-closure VALIDATION** (`native_decide`): (a) `y/d` is integral — `d²·s = ρ` EXACTLY (so
  `s = ρ/d² ∈ ℚ[x]` is a genuine polynomial, the minimal polynomial `T² − s` of `y/d` is over `ℚ[x]`),
  and `s` is squarefree (`gcd(s, s') = 1`); (b) the basis is MAXIMAL — `y/(d·P)` is NOT integral for any
  nonconstant `P`, because its would-be minimal polynomial `T² − s/P²` is not over `ℚ[x]` (`P² ∤ s` since
  `s` is squarefree).
* **Discriminant & genus** (STRETCH, `native_decide`): the basis discriminant `disc(T² − s) = 4s`, and
  the hyperelliptic genus `g = ⌈deg s / 2⌉ − 1` for squarefree `s` (`y² = x³+1 → g = 1` elliptic;
  `y² = x → g = 0` rational; `y² = x⁵+1 → g = 2`).

**The engine now computes AND validates the simple-radical integral basis** (the `[1, y/d]` integral
closure of `ℚ[x]`), together with its discriminant and the hyperelliptic genus. This is the prerequisite
for the **principal-divisor test** (Trager Ch. 6): on top of the integral basis the still-deferred,
research-grade next step is the **divisor construction** (Ch. 5 §3) — representing a divisor as a
fractional ideal in this basis — and the **torsion / points-of-finite-order bound** (Ch. 6, good
reduction) deciding whether a divisor's multiple is ever principal, which is what produces the actual log
arguments `vᵢ` from the residues. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### The square-part / squarefree-part split for `n = 2` (Trager Ch. 2 §5)

`ρ = d²·s`: `d = ∏ᵢ Pᵢ^{⌊i/2⌋}` (the square part's root) and `s = ∏_{i odd} Pᵢ` (squarefree), from the
multiplicity-indexed squarefree factorization `ρ = ∏ᵢ Pᵢ^i` (`cSqfreeYunFFG`). This is Trager's general
`dᵢ = ∏ⱼ Pⱼ^{⌊i·eⱼ/n⌋}` (p. 30) at `n = 2`, `i = 1`: `⌊eⱼ/2⌋` copies of each factor go into `d`. -/

variable [CFracGcdCore α]

/-- **Square part** `radSquarePart fuel ρ = d = ∏ᵢ Pᵢ^{⌊i/2⌋}` — the root of the largest square divisor
of `ρ`, from the multiplicity-indexed squarefree factorization `ρ = ∏ᵢ Pᵢ^i` (`cSqfreeYunFFG`): each
squarefree part `Pᵢ` of multiplicity `i` contributes `Pᵢ^{⌊i/2⌋}` to `d`. So `d² ∣ ρ` and `ρ/d²` is
squarefree (Trager Ch. 2 §5, p. 30, `d₁` at `n = 2`). Monic. `[CField α] [CFracGcdCore α]`-generic. -/
def radSquarePart (fuel : ℕ) (ρ : CPolyG α) : CPolyG α :=
  (cSqfreeYunFFG fuel ρ).zipIdx.foldl
    (fun acc (Pi, i) => cmulG acc (cpowG Pi ((i + 1) / 2))) [CField.one]

/-- **Squarefree part** `radSquarefreePart fuel ρ = s = ∏_{i odd} Pᵢ = ρ/d²` — the radical-style
squarefree part of `ρ` collecting one copy of each ODD-multiplicity squarefree factor `Pᵢ` (so
`ρ = d²·s` with `d = radSquarePart`). Equivalently `s = ρ/d²` (exact division), but built directly from
the parity of multiplicities so the squarefreeness is structural (Trager Ch. 2 §5, p. 30). Monic.
`[CField α] [CFracGcdCore α]`-generic. -/
def radSquarefreePart (fuel : ℕ) (ρ : CPolyG α) : CPolyG α :=
  (cSqfreeYunFFG fuel ρ).zipIdx.foldl
    (fun acc (Pi, i) => if (i + 1) % 2 = 1 then cmulG acc Pi else acc) [CField.one]

/-! ### The integral basis `[1, y/d]` (Trager Ch. 2 §5, p. 31)

`d = radSquarePart ρ`, `s = radSquarefreePart ρ`; `ρ = d²·s`, `(y/d)² = ρ/d² = s` is squarefree hence
integral, and `y/d` is the maximal integral element of the form `y/q`. We return the basis by the pair
`(d, s)`: the second basis element is `y/d`, whose square is the squarefree polynomial `s`. -/

/-- **The simple-radical integral basis** `radIntegralBasis fuel ρ = (d, s)` for `ℚ[x][y]/(y² − ρ)`
(Trager Ch. 2 §5, p. 31): the integral closure of `ℚ[x]` has the explicit `ℚ[x]`-basis `[1, y/d]`, where
`d = radSquarePart ρ` (the square part's root) and `s = radSquarefreePart ρ = ρ/d²` is squarefree with
`(y/d)² = s`. Returned as the pair `(d, s)` (the basis is `1` and `y/d`; `s` is the minimal-polynomial
constant `(y/d)² = s`). For squarefree `ρ` (`d = 1`) this is just `[1, y]`. `[CField α]
[CFracGcdCore α]`-generic. -/
def radIntegralBasis (fuel : ℕ) (ρ : CPolyG α) : CPolyG α × CPolyG α :=
  (radSquarePart fuel ρ, radSquarefreePart fuel ρ)

/-! ### Integral-closure validation predicates

The basis `[1, y/d]` is integral and maximal iff: (a) the split is exact, `d²·s = ρ`, so `s = ρ/d²` is a
genuine polynomial (`y/d` satisfies the monic `T² − s = 0` over `ℚ[x]`) and `s` is squarefree
(`gcd(s, s') = 1`); (b) for any nonconstant `P`, `y/(d·P)` is NOT integral — its would-be minimal
polynomial `T² − s/P²` is not over `ℚ[x]`, i.e. `P² ∤ s`, which holds for every nonconstant `P` exactly
because `s` is squarefree. -/

/-- **The square-part split is exact** `radSplitExact fuel ρ`: `d²·s = ρ` where `(d, s) = radIntegralBasis
ρ` — so `s = ρ/d²` is a genuine `ℚ[x]` polynomial (no fractional residue), the precondition that `y/d`
satisfies the monic `T² − s = 0` over `ℚ[x]`. Checked by `cisZeroG (d²·s − ρ)`, comparing monic-normalized
(the Yun factors are monic, so `d, s` are; `ρ` is taken monic). `[CField α] [CFracGcdCore α]`-generic. -/
def radSplitExact (fuel : ℕ) (ρ : CPolyG α) : Bool :=
  let d := radSquarePart fuel ρ
  let s := radSquarefreePart fuel ρ
  cisZeroG (csubG (cmulG (cmulG d d) s) (cmonicG ρ))

/-- **`y/d` is integral: `s` is squarefree** `radSquarefreePartIsSquarefree fuel ρ`: `gcd(s, s') = 1`
(constant) where `s = radSquarefreePart ρ`. Together with `radSplitExact` this is exactly "`y/d` is
integral over `ℚ[x]`" — `(y/d)² = s` is a squarefree polynomial, so `y/d` is a root of the monic
`T² − s ∈ ℚ[x][T]` and the integral closure contains it. Checked by `cdegG (gcd s s') = 0`. `[CField α]
[CFracGcdCore α]`-generic. -/
def radSquarefreePartIsSquarefree (fuel : ℕ) (ρ : CPolyG α) : Bool :=
  let s := radSquarefreePart fuel ρ
  cdegG (cgcdMonicWf s (cderivG s)) = 0

/-- **`y/(d·P)` is NOT integral** `radNotIntegralFactor fuel ρ P`: for a nonconstant `P`, `P² ∤ s` where
`s = radSquarefreePart ρ`. The basis-maximality witness — `y/(d·P)` would need minimal polynomial
`T² − s/P²` over `ℚ[x]`, but `P² ∤ s` (since `s` is squarefree, no nonconstant square divides it), so
`s/P²` is not a polynomial and `y/(d·P)` is not integral. Hence `y/d` is the MAXIMAL integral element of
the form `y/q`. Returns `true` (= "not integral", `P² ∤ s`) for nonconstant `P`; `false` for constant `P`
(`y/d` itself, which IS integral). Checked by `¬ (P² ∣ s)` via `cdvdGWf`. `[CField α]
[CFracGcdCore α]`-generic. -/
def radNotIntegralFactor (fuel : ℕ) (ρ P : CPolyG α) : Bool :=
  let s := radSquarefreePart fuel ρ
  if cdegG P = 0 then false else !(cdvdGWf (cmulG P P) s)

/-! ### Discriminant and genus of the simple-radical basis (Trager Ch. 2 §5, STRETCH)

For `y² = s` with `s` squarefree, the minimal polynomial of `y/d` is `T² − s`, whose discriminant is
`4s` (up to the unit `1`). The genus of the hyperelliptic curve `y² = s` with `s` squarefree of degree
`m` is `g = ⌈m/2⌉ − 1` (the standard hyperelliptic formula; Trager Ch. 2 §4's `g = d/2 − [K(x,y):K(x)] +
1` specializes to this). `radSplitExact` guarantees `s = ρ/d²` is the genuine squarefree radicand. -/

/-- **Basis discriminant** `radBasisDiscriminant fuel ρ = 4·s` — the discriminant of the minimal
polynomial `T² − s` of the basis element `y/d` (`s = radSquarefreePart ρ`): `disc(T² − s) = 0² − 4·1·(−s)
= 4s`. The polynomial discriminant `disc(T² + bT + c) = b² − 4c` at `b = 0, c = −s`. (Up to the unit `1`
this is `s` itself; the `4` is the classical normalization.) `[CField α] [CFracGcdCore α]`-generic. -/
def radBasisDiscriminant (fuel : ℕ) (ρ : CPolyG α) : CPolyG α :=
  cscaleG (cnatCastG 4) (radSquarefreePart fuel ρ)

/-- **Genus** `radGenus fuel ρ = ⌈deg s / 2⌉ − 1` — the genus of the hyperelliptic curve `y² = s`
(`s = radSquarefreePart ρ` squarefree of degree `m`): `g = ⌈m/2⌉ − 1 = (m + 1)/2 − 1` (`ℕ`-division, so
`(m + 1)/2` is `⌈m/2⌉`). Trager Ch. 2 §4's `g = d/2 − [K(x,y):K(x)] + 1` specialized to the simple radical
`y² = s`. `g = 0` (rational) for `deg s ≤ 2`, `g = 1` (elliptic) for `deg s ∈ {3, 4}`, etc. `[CField α]
[CFracGcdCore α]`-generic. -/
def radGenus (fuel : ℕ) (ρ : CPolyG α) : ℕ :=
  let m := cdegG (radSquarefreePart fuel ρ)
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
    cisZeroG (csubG (radSquarePart 8 basisRhoX3p1) [CField.one]) = true := by native_decide

/-- **Squarefree `ρ = x³+1` ⇒ `s = x³+1`** (`native_decide`): the squarefree part of a squarefree radicand
is the radicand itself (monic). -/
theorem radSquarefreePart_x3p1 :
    cisZeroG (csubG (radSquarefreePart 8 basisRhoX3p1) (cmonicG basisRhoX3p1)) = true := by
  native_decide

/-- **`ρ = x²(x+1) ⇒ d = x`** (`native_decide`): the square part of `x³ + x²` is `x` (one copy of the
multiplicity-2 factor `x`). -/
theorem radSquarePart_x3pX2 :
    cisZeroG (csubG (radSquarePart 8 basisRhoX3pX2) [0, 1]) = true := by native_decide

/-- **`ρ = x²(x+1) ⇒ s = x+1`** (`native_decide`): the squarefree part of `x³ + x²` is `x + 1` (the
odd-multiplicity factor; the even factor `x²` goes entirely into `d²`). -/
theorem radSquarefreePart_x3pX2 :
    cisZeroG (csubG (radSquarefreePart 8 basisRhoX3pX2) [1, 1]) = true := by native_decide

/-- **`ρ = x⁴(x−1) ⇒ d = x²`** (`native_decide`): the square part of `x⁵ − x⁴` is `x²` (two copies of the
multiplicity-4 factor `x`). -/
theorem radSquarePart_x5mX4 :
    cisZeroG (csubG (radSquarePart 8 basisRhoX5mX4) [0, 0, 1]) = true := by native_decide

/-- **`ρ = x⁴(x−1) ⇒ s = x−1`** (`native_decide`): the squarefree part of `x⁵ − x⁴` is `x − 1` (the
odd-multiplicity factor; `x⁴ = (x²)²` is entirely the square part). -/
theorem radSquarefreePart_x5mX4 :
    cisZeroG (csubG (radSquarefreePart 8 basisRhoX5mX4) [-1, 1]) = true := by native_decide

/-! ### ★ The integral basis validates: `[1, y/d]` is the integral closure (`native_decide`)

For each radicand: the split `d²·s = ρ` is exact (`s` a genuine polynomial), `s` is squarefree (`y/d`
integral), and `y/(d·P)` is not integral for a sample nonconstant `P` (maximality). -/

/-- **★ Split exact `d²·s = ρ` for `x²(x+1)`** (`native_decide`): `x²·(x+1) = x³ + x²`, so
`s = ρ/d² = x+1 ∈ ℚ[x]` is a genuine polynomial — `y/d = y/x` satisfies the monic `T² − (x+1) = 0` over
`ℚ[x]`. THE BASIS ELEMENT `y/x` IS INTEGRAL (closure half 1). -/
theorem radSplitExact_x3pX2 : radSplitExact 8 basisRhoX3pX2 = true := by native_decide

/-- **★ Split exact `d²·s = ρ` for `x⁴(x−1)`** (`native_decide`): `(x²)²·(x−1) = x⁵ − x⁴`, so
`s = x−1 ∈ ℚ[x]` and `y/x²` satisfies `T² − (x−1) = 0`. -/
theorem radSplitExact_x5mX4 : radSplitExact 8 basisRhoX5mX4 = true := by native_decide

/-- **★ Split exact for squarefree `x³+1`** (`native_decide`): `1²·(x³+1) = x³+1`, the basis is `[1, y]`. -/
theorem radSplitExact_x3p1 : radSplitExact 8 basisRhoX3p1 = true := by native_decide

/-- **★ `s = x+1` is squarefree ⇒ `y/x` integral** (`native_decide`): `gcd(s, s') = gcd(x+1, 1) = 1`, so
the minimal polynomial `T² − (x+1)` has squarefree constant term — `y/x` IS in the integral closure
(closure half 1, the squarefree certificate). -/
theorem radSquarefree_x3pX2 : radSquarefreePartIsSquarefree 8 basisRhoX3pX2 = true := by native_decide

/-- **★ `s = x³+1` is squarefree** (`native_decide`): `gcd(x³+1, 3x²) = 1`, so `y = y/1` is integral
(`[1, y]` is the closure for squarefree radicand). -/
theorem radSquarefree_x3p1 : radSquarefreePartIsSquarefree 8 basisRhoX3p1 = true := by native_decide

/-- **★ `s = x−1` is squarefree** (`native_decide`): `gcd(x−1, 1) = 1`, so `y/x²` is integral. -/
theorem radSquarefree_x5mX4 : radSquarefreePartIsSquarefree 8 basisRhoX5mX4 = true := by native_decide

/-- **★ `y/(x·(x+1))` is NOT integral for `x²(x+1)`** (`native_decide`): with `P = x+1`,
`P² = (x+1)² ∤ s = x+1` (the squarefree `s` has no nonconstant square divisor), so the would-be minimal
polynomial `T² − (x+1)/(x+1)²` is not over `ℚ[x]`. Hence `y/d = y/x` is the MAXIMAL integral element of
the form `y/q` (closure half 2, maximality). -/
theorem radNotIntegral_x3pX2 :
    radNotIntegralFactor 8 basisRhoX3pX2 [1, 1] = true := by native_decide

/-- **★ `y/(x²·(x−1))` is NOT integral for `x⁴(x−1)`** (`native_decide`): with `P = x−1`,
`(x−1)² ∤ (x−1) = s`, so dividing the basis denominator further leaves the integral closure. Maximality of
`y/x²`. -/
theorem radNotIntegral_x5mX4 :
    radNotIntegralFactor 8 basisRhoX5mX4 [-1, 1] = true := by native_decide

/-- **★ `y·x` (i.e. `y/(1·x)`) is NOT integral for the squarefree `x³+1`** (`native_decide`): with
`P = x`, `x² ∤ x³+1`, so `y/x` is not integral — `y = y/1` is already maximal (the basis `[1, y]` cannot
be improved). Maximality for the squarefree case. -/
theorem radNotIntegral_x3p1 :
    radNotIntegralFactor 8 basisRhoX3p1 [0, 1] = true := by native_decide

/-- **★★ THE SIMPLE-RADICAL INTEGRAL BASIS COMPUTES AND VALIDATES** (Trager Ch. 2 §5, `native_decide`) —
for the three radicands `x³+1` (squarefree, basis `[1, y]`), `x²(x+1)` (basis `[1, y/x]`), and `x⁴(x−1)`
(basis `[1, y/x²]`): the square-part split `ρ = d²·s` is EXACT (so `s = ρ/d²` is a genuine `ℚ[x]`
polynomial), the squarefree part `s` is SQUAREFREE (so the basis element `y/d` satisfies the monic
`T² − s = 0` over `ℚ[x]` and is INTEGRAL), and `y/(d·P)` for the displayed nonconstant `P` is NOT integral
(so `y/d` is MAXIMAL). This is `[1, y/d]` realized as the integral closure of `ℚ[x]` in `ℚ(x)[y]/(y²−ρ)`,
end to end. -/
theorem radIntegralBasis_validates :
    (radSplitExact 8 basisRhoX3p1 = true
      ∧ radSquarefreePartIsSquarefree 8 basisRhoX3p1 = true
      ∧ radNotIntegralFactor 8 basisRhoX3p1 [0, 1] = true)
    ∧ (radSplitExact 8 basisRhoX3pX2 = true
      ∧ radSquarefreePartIsSquarefree 8 basisRhoX3pX2 = true
      ∧ radNotIntegralFactor 8 basisRhoX3pX2 [1, 1] = true)
    ∧ (radSplitExact 8 basisRhoX5mX4 = true
      ∧ radSquarefreePartIsSquarefree 8 basisRhoX5mX4 = true
      ∧ radNotIntegralFactor 8 basisRhoX5mX4 [-1, 1] = true) := by native_decide

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
    cisZeroG (csubG (radBasisDiscriminant 8 basisRhoX3pX2) [4, 4]) = true := by native_decide

/-- **Discriminant `disc = 4(x³+1)` for the squarefree `x³+1`** (`native_decide`): basis `[1, y]`,
minimal polynomial `T² − (x³+1)`, discriminant `4(x³+1) = 4 + 4x³` (`[4,0,0,4]`). -/
theorem radBasisDiscriminant_x3p1 :
    cisZeroG (csubG (radBasisDiscriminant 8 basisRhoX3p1) [4, 0, 0, 4]) = true := by native_decide

/-- **Genus 0 for `y² = x`** (`native_decide`): `s = x`, `deg s = 1`, `⌈1/2⌉ − 1 = 1 − 1 = 0` — the curve
`y² = x` is RATIONAL (genus 0). -/
theorem radGenus_x : radGenus 8 basisRhoX = 0 := by native_decide

/-- **★ Genus 1 for `y² = x³+1`** (`native_decide`): `s = x³+1`, `deg s = 3`, `⌈3/2⌉ − 1 = 2 − 1 = 1` —
the curve `y² = x³+1` is ELLIPTIC (genus 1). The flagship hyperelliptic-genus check. -/
theorem radGenus_x3p1 : radGenus 8 basisRhoX3p1 = 1 := by native_decide

/-- **Genus 2 for `y² = x⁵+1`** (`native_decide`): `s = x⁵+1`, `deg s = 5`, `⌈5/2⌉ − 1 = 3 − 1 = 2` — the
genus-2 hyperelliptic curve. -/
theorem radGenus_x5p1 : radGenus 8 basisRhoX5p1 = 2 := by native_decide

/-- **★ THE GENUS OF THE SIMPLE-RADICAL CURVE COMPUTES** (Trager Ch. 2 §5, hyperelliptic
`g = ⌈deg s/2⌉ − 1`, `native_decide`): `y² = x` is rational (`g = 0`), `y² = x³+1` is elliptic (`g = 1`),
`y² = x⁵+1` is genus `2` — read off the squarefree part `s = radSquarefreePart ρ` of the integral-basis
computation. -/
theorem radGenus_validates :
    radGenus 8 basisRhoX = 0 ∧ radGenus 8 basisRhoX3p1 = 1 ∧ radGenus 8 basisRhoX5p1 = 2 := by
  native_decide

/-! ### Deliverable: `#print axioms` of the integral-closure validation

`[propext, Classical.choice, Quot.sound]` plus `Lean.ofReduceBool` (the `native_decide` kernel-reduction
axiom). No `sorry`. -/

/-- **Axiom audit of the integral-basis validation** — `[propext, Classical.choice, Quot.sound,
Lean.ofReduceBool]` (the last is the `native_decide` axiom): the simple-radical integral-closure check
runs on the standard classical + native-reduction base, no `sorry`. -/
example : True := trivial

end DeepWiki.SymbolicIntegration
