import DeepWiki.SymbolicIntegration.ComputableHyperellipticDivisor
import DeepWiki.SymbolicIntegration.ComputableFuelFreeGcd

/-! # Cantor's algorithm: the hyperelliptic-Jacobian group law (Trager Ch. 6, Cantor 1987)

The **Mumford representation** (`ComputableHyperellipticDivisor`) gives semi-reduced divisors on the
hyperelliptic curve `y² = ρ(x)` as pairs `(u, v)` (`u` monic, `deg v < deg u`, `u ∣ v² − ρ`). Here we
build the **group law** on these pairs — **Cantor's algorithm** (composition + reduction), the
computational core of the Jacobian arithmetic that the torsion-bound sub-arc (Trager "Integration of
Algebraic Functions", Ch. 6, "Principal Divisors and Points of Finite Order") runs on.

**Composition** `(u₁, v₁) ⊕ (u₂, v₂)` (Cantor 1987, standard hyperelliptic arithmetic):
* `d₁ = gcd(u₁, u₂) = e₁·u₁ + e₂·u₂` (extended gcd → cofactors `e₁, e₂`),
* `d = gcd(d₁, v₁ + v₂) = c₁·d₁ + c₂·(v₁ + v₂)` (second extended gcd), so
  `d = s₁·u₁ + s₂·u₂ + s₃·(v₁ + v₂)` with `s₁ = c₁·e₁`, `s₂ = c₁·e₂`, `s₃ = c₂`,
* `u = u₁·u₂/d²`,  `v = (s₁·u₁·v₂ + s₂·u₂·v₁ + s₃·(v₁·v₂ + ρ))/d  mod u`.

The result is a **semi-reduced** divisor (possibly `deg u > g`).

**Reduction** to `deg u ≤ g` (`g = radGenus ρ`): repeat the step `u ← monic((ρ − v²)/u)`,
`v ← (−v) mod u`; each step strictly lowers `deg u`, terminating at the unique **reduced**
representative of the Jacobian class.

**Group law** `cantorAdd ρ g D₁ D₂ = cantorReduce ρ g (cantorCompose ρ D₁ D₂)`. Identity `(1, 0)`
(`mumfordIdentity`); inverse `mumfordOpposite`.

Mathlib has the abstract `WeierstrassCurve` group law but **no general hyperelliptic Cantor / Mumford
arithmetic**, so — like the rest of this arc — we build it **computationally**, validated by
`native_decide` over `ℚ[x]`.

**★ Flagship validation** — the **elliptic** curve `y² = x³ + 1` *is* its genus-1 Jacobian, the elliptic
group:
* `(0, 1) ⊕ (2, 3) = (−1, 0)`: the chord `y = x + 1` through `(0,1), (2,3)` meets the curve again at
  `(−1, 0)` (a 2-torsion point, its own negative), so the group sum is `(−1, 0)` — Mumford `(x + 1, 0)`.
* `P ⊕ (−P) = O`: `(x, 1) ⊕ mumfordOpposite (x, 1) = (1, 0)` (the identity).
* `2·(0, 1)` (doubling): `cantorAdd (0,1) (0,1)` — valid and reduced (the tangent-line doubling).

Plus a **genus-2** composition on `y² = x⁵ + 1` and `cantorMul ρ g n D` (the `n`-fold sum `n·D`, the
scalar multiple the order computation — the smallest `n` with `n·D = O` — needs next). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### Cantor composition `(u₁, v₁) ⊕ (u₂, v₂)`

The Jacobian group law on Mumford pairs (before reduction). Two extended-gcd steps give the cofactors
`s₁, s₂, s₃` of `d = gcd(u₁, u₂, v₁ + v₂)` over the three generators `u₁, u₂, v₁ + v₂`; then
`u = u₁u₂/d²` (monic), `v = (s₁u₁v₂ + s₂u₂v₁ + s₃(v₁v₂ + ρ))/d mod u`. -/

/-- **Cantor composition** `cantorCompose fuel ρ D₁ D₂ = D₁ ⊕ D₂` — the hyperelliptic-Jacobian group law
on Mumford pairs, producing a *semi-reduced* divisor (Cantor 1987; Trager Ch. 6). With
`d₁ = gcd(u₁, u₂) = e₁u₁ + e₂u₂` (first `cgcdWf`) and `d = gcd(d₁, v₁ + v₂) = c₁d₁ + c₂(v₁ + v₂)`
(second `cgcdWf`), set `s₁ = c₁e₁`, `s₂ = c₁e₂`, `s₃ = c₂` (so `d = s₁u₁ + s₂u₂ + s₃(v₁ + v₂)`); then
`u = monic(u₁u₂/d²)` and `v = (s₁u₁v₂ + s₂u₂v₁ + s₃(v₁v₂ + ρ))/d mod u`. The exact quotients use `cdivWf`
(`d² ∣ u₁u₂`, `d ∣` the numerator by the Bézout identities), the reduction `cmodWf`. Generic over
`[CField α]`. -/
def cantorCompose (_fuel : ℕ) (ρ : CPolyG α) (D₁ D₂ : MumfordDivisor α) : MumfordDivisor α :=
  let u₁ := D₁.u; let v₁ := D₁.v
  let u₂ := D₂.u; let v₂ := D₂.v
  -- first extended gcd: d₁ = gcd(u₁,u₂) = e₁·u₁ + e₂·u₂
  let (d₁, e₁, e₂) := cgcdWf u₁ u₂
  -- second extended gcd: d = gcd(d₁, v₁+v₂) = c₁·d₁ + c₂·(v₁+v₂)
  let vsum := caddG v₁ v₂
  let (d, c₁, c₂) := cgcdWf d₁ vsum
  -- cofactors of d over (u₁, u₂, v₁+v₂)
  let s₁ := cmulG c₁ e₁
  let s₂ := cmulG c₁ e₂
  let s₃ := c₂
  -- u = u₁·u₂/d²  (monic-normalized)
  let d2 := cmulG d d
  let u := cmonicG (cdivWf (cmulG u₁ u₂) d2)
  -- v numerator = s₁·u₁·v₂ + s₂·u₂·v₁ + s₃·(v₁·v₂ + ρ)
  let vnum :=
    caddG (caddG (cmulG s₁ (cmulG u₁ v₂)) (cmulG s₂ (cmulG u₂ v₁)))
      (cmulG s₃ (caddG (cmulG v₁ v₂) ρ))
  -- v = (vnum / d) mod u
  let v := cmodWf (cdivWf vnum d) u
  ⟨u, v⟩

/-! ### Cantor reduction (to `deg u ≤ g`)

The repeated step `u ← monic((ρ − v²)/u)`, `v ← (−v) mod u` strictly lowers `deg u` (`deg ρ = 2g+1` or
`2g+2`, so `deg((ρ − v²)/u) = deg ρ − deg u < deg u` once `deg u > g`), terminating at the unique reduced
representative. Fuel = `deg u` (one step per degree drop). -/

/-- **One Cantor reduction step** `cantorReduceStep fuel ρ (u, v) = (monic((ρ − v²)/u), (−v) mod u)`.
Applied while `deg u > g`: `u' = (ρ − v²)/u` (exact since `u ∣ v² − ρ`), monic-normalized; `v' = (−v) mod
u'`. Lowers `deg u` toward `≤ g`. Generic over `[CField α]`. -/
def cantorReduceStep (_fuel : ℕ) (ρ : CPolyG α) (D : MumfordDivisor α) : MumfordDivisor α :=
  let u := D.u; let v := D.v
  let unew := cmonicG (cdivWf (csubG ρ (cmulG v v)) u)
  let vnew := cmodWf (cnegG v) unew
  ⟨unew, vnew⟩

/-- **Cantor reduction (fuel-bounded)** `cantorReduceAux fuel g ρ (u, v)`: repeatedly apply
`cantorReduceStep` until `deg u ≤ g`, at most `fuel` times. Each step strictly drops `deg u`, so
`fuel = deg u` suffices; the structural recursion guarantees termination regardless. Generic over
`[CField α]`. -/
def cantorReduceAux : ℕ → ℕ → CPolyG α → MumfordDivisor α → MumfordDivisor α
  | 0, _, _, D => D
  | fuel + 1, g, ρ, D =>
    if cdegG D.u ≤ g then D
    else cantorReduceAux fuel g ρ (cantorReduceStep (fuel + 1) ρ D)

/-- **Cantor reduction** `cantorReduce ρ g D` — bring a semi-reduced Mumford pair `(u, v)` to the unique
**reduced** form `deg u ≤ g` (`g = radGenus ρ`) by the repeated step `u ← monic((ρ − v²)/u)`,
`v ← (−v) mod u` (Cantor 1987; Trager Ch. 6). Fuel is `deg u` (each step strictly lowers `deg u`).
Generic over `[CField α]`. -/
def cantorReduce (ρ : CPolyG α) (g : ℕ) (D : MumfordDivisor α) : MumfordDivisor α :=
  cantorReduceAux (cdegG D.u + 1) g ρ D

/-! ### The group law `cantorAdd = reduce ∘ compose` -/

/-- **The Jacobian group law** `cantorAdd ρ g D₁ D₂ = cantorReduce ρ g (cantorCompose ρ D₁ D₂)` — the
sum `D₁ ⊕ D₂` of two reduced divisors on `y² = ρ`, as the unique reduced representative of the class.
Cantor's algorithm: compose, then reduce to `deg u ≤ g` (`g = radGenus ρ`). Identity `mumfordIdentity =
(1, 0)`, inverse `mumfordOpposite`. The `fuel` bounds the composition's gcd/division steps. Generic over
`[CField α]`. -/
def cantorAdd (fuel : ℕ) (ρ : CPolyG α) (g : ℕ) (D₁ D₂ : MumfordDivisor α) : MumfordDivisor α :=
  cantorReduce ρ g (cantorCompose fuel ρ D₁ D₂)

/-! ### Normalized equality of Mumford pairs

`MumfordDivisor`'s derived `DecidableEq` compares the raw coefficient lists, so the zero polynomial `0`
has two encodings — `[]` and `[0]` (a literal-zero cell) — that are *propositionally equal polynomials*
but distinct lists. Cantor's reduction emits the normalized `[]` for a zero `v`, whereas `mumfordPoint
x₀ 0` stores `[0]`. `mumfordNormEq` compares the two pairs **as polynomials** (both `u` and `v` run
through `cnormG`), the mathematically correct equality on Mumford representations. -/

/-- **Normalized equality** of Mumford pairs `mumfordNormEq D₁ D₂`: `cnormG`-equal on both `u` and `v`
— i.e. equal *as polynomials*, independent of trailing-zero list encoding (the zero polynomial is `[]`
or `[0]` indistinguishably). The right equality to test Cantor output against a hand-written point
divisor. Generic over `[CField α]` with `[DecidableEq α]`. -/
def mumfordNormEq [DecidableEq α] (D₁ D₂ : MumfordDivisor α) : Bool :=
  (cnormG D₁.u == cnormG D₂.u) && (cnormG D₁.v == cnormG D₂.v)

/-! ### The scalar multiple `n·D` (`cantorMul`)

The `n`-fold sum `D ⊕ D ⊕ … ⊕ D` (`n` summands), `0·D = O` the identity. The order of `D` is the
smallest `n ≥ 1` with `n·D = O` — the torsion computation the next sub-arc needs. -/

/-- **The scalar multiple** `cantorMul fuel ρ g n D = n·D` (the `n`-fold Cantor sum
`D ⊕ D ⊕ … ⊕ D`), with `0·D = mumfordIdentity = (1, 0)`. By `ℕ`-recursion: `(n+1)·D = D ⊕ (n·D)`. The
order of `D` in the Jacobian is the smallest `n ≥ 1` with `cantorMul … n D = mumfordIdentity` — the
torsion / point-of-finite-order quantity (Trager Ch. 6). Generic over `[CField α]`. -/
def cantorMul (fuel : ℕ) (ρ : CPolyG α) (g : ℕ) : ℕ → MumfordDivisor α → MumfordDivisor α
  | 0, _ => mumfordIdentity
  | n + 1, D => cantorAdd fuel ρ g D (cantorMul fuel ρ g n D)

end CPolyG

/-! ## ★ Validation over `ℚ[x]` (`native_decide`)

`α = ℚ`. The flagship is the **elliptic** curve `y² = x³ + 1` (genus 1, `radGenus = 1`), whose Jacobian
is the elliptic group itself, so Cantor's group law *is* elliptic point addition. -/

open CPolyG

/-! ### The elliptic curve `y² = x³ + 1` and its points (reusing `ComputableHyperellipticDivisor`)

`hypRhoX3p1 = x³ + 1`, points `(0,1)`, `(2,3)`, `(−1,0)`, with `radGenus 8 hypRhoX3p1 = 1`. -/

/-- The genus of `y² = x³ + 1`: `radGenus = 1` (elliptic). Pinned for the group-law checks below. -/
def cantorGenusX3p1 : ℕ := radGenus 8 hypRhoX3p1

/-- **`radGenus (x³+1) = 1`** (`native_decide`): the curve `y² = x³ + 1` is elliptic, genus 1. -/
theorem cantorGenusX3p1_eq : cantorGenusX3p1 = 1 := by native_decide

/-! ### ★ `(0, 1) ⊕ (2, 3) = (−1, 0)` — the flagship chord addition (`native_decide`)

The chord through `(0,1)` and `(2,3)` is `y = x + 1` (slope `1`): it meets `y² = x³ + 1` at a third
point `(x₃, y₃)`. With `(x+1)² = x³ + 1`, i.e. `x³ − x² − 2x = 0 = x(x−2)(x+1)`, the third root is
`x₃ = −1`, `y₃ = x₃ + 1 = 0`. The group sum `(0,1) ⊕ (2,3)` is the *reflection* `(x₃, −y₃) = (−1, 0)` —
but `(−1, 0)` is a 2-torsion (Weierstrass) point, its own reflection, so the sum is exactly `(−1, 0)`,
Mumford `(x + 1, 0)`. -/

/-- The Cantor sum `(0,1) ⊕ (2,3)` on `y² = x³+1`, computed via `cantorAdd`. Expected: `(x+1, 0)`. -/
def cantorSum0123 : MumfordDivisor ℚ := cantorAdd 16 hypRhoX3p1 1 hypPt01 hypPt23

/-- **★ `(0,1) ⊕ (2,3) = (−1,0)` in the elliptic group** (`native_decide`): `cantorAdd hypPt01 hypPt23 =
(x + 1, 0) = mumfordPoint (−1) 0` (as polynomials, `mumfordNormEq`) — the third intersection of the chord
`y = x + 1` with `y² = x³ + 1`, reflected. The 2-torsion point `(−1, 0)`. This is elliptic point
addition, computed by Cantor's composition + reduction. (`mumfordNormEq`, not raw list equality: the
reduced `v = 0` is the normalized `[]`, while `mumfordPoint` stores the literal `[0]` — equal as
polynomials.) -/
theorem cantorSum0123_eq : mumfordNormEq cantorSum0123 (mumfordPoint (-1 : ℚ) 0) = true := by
  native_decide

/-- **★ `(0,1) ⊕ (2,3)` is exactly `(x + 1, 0)`** as the raw reduced Mumford pair `⟨[1, 1], []⟩`
(`native_decide`): `u = x + 1` (`[1,1]`), `v = 0` (normalized to `[]`). The literal output of Cantor's
algorithm, the Mumford representation of `(−1, 0)`. -/
theorem cantorSum0123_raw : cantorSum0123 = (⟨[1, 1], []⟩ : MumfordDivisor ℚ) := by native_decide

/-- **★ The Cantor sum `(0,1) ⊕ (2,3)` is a valid, reduced Mumford divisor** (`native_decide`): the
group-law output `(x + 1, 0)` is monic, `deg v = 0 < 1 = deg u`, `u ∣ v² − ρ` (`(x+1) ∣ −(x³+1)`), and
`deg u = 1 ≤ g = 1`. Cantor's algorithm lands inside the valid reduced divisors. -/
theorem cantorSum0123_valid_reduced :
    mumfordValid hypRhoX3p1 cantorSum0123 = true
    ∧ mumfordIsReduced 1 cantorSum0123 = true := by native_decide

/-! ### ★ `P ⊕ (−P) = O` — the inverse law (`native_decide`)

`(x, 1)` is the point `(0, 1)`; its opposite `mumfordOpposite (x, 1) = (x, −1) = (0, −1) = −P`. Their
Cantor sum reduces to the identity `(1, 0)`: a point plus its reflection cancels in the Jacobian. -/

/-- The Cantor sum `(0,1) ⊕ (0,−1)` of `P = (0,1)` and `−P = mumfordOpposite P`. Expected: identity
`(1, 0)`. -/
def cantorSumPoppP : MumfordDivisor ℚ :=
  cantorAdd 16 hypRhoX3p1 1 hypPt01 (mumfordOpposite hypPt01)

/-- **★ `P ⊕ (−P) = O` (the inverse law)** (`native_decide`): `(0,1) ⊕ (0,−1) = (1, 0) =
mumfordIdentity` — a point and its opposite (reflection) sum to the Jacobian identity. Cantor's
composition + reduction collapses the support `x = 0` (a point and its mirror) to the empty divisor. -/
theorem cantorSumPoppP_eq : cantorSumPoppP = mumfordIdentity := by native_decide

/-- **★ `P ⊕ (−P)` is valid and reduced** (`native_decide`): the identity `(1, 0)` is a valid reduced
divisor (`u = 1` monic, `v = 0`, `deg u = 0 ≤ g`). -/
theorem cantorSumPoppP_valid_reduced :
    mumfordValid hypRhoX3p1 cantorSumPoppP = true
    ∧ mumfordIsReduced 1 cantorSumPoppP = true := by native_decide

/-! ### ★ Doubling `2·(0, 1)` — the tangent-line addition (`native_decide`)

`(0,1) ⊕ (0,1)` is the *doubling* of `P = (0,1)`: the tangent to `y² = x³ + 1` at `(0,1)` (slope
`y' = 3x²/2y = 0` at `x = 0`, the horizontal line `y = 1`) meets the curve again at `x³ + 1 = 1`, i.e.
`x³ = 0` (a triple root at `x = 0`)… so the third intersection is again `x = 0`, and `2P = (0, −1) = −P`
— giving `3P = O`, i.e. `(0, 1)` is a **3-torsion** point (an inflection point). We verify the doubling
computes to a valid reduced divisor and equals `(0, −1)`. -/

/-- The doubling `2·(0,1) = (0,1) ⊕ (0,1)` on `y² = x³+1`, via `cantorAdd`. The point `(0,1)` is an
inflection point (3-torsion), so `2·(0,1) = (0, −1)`. -/
def cantorDouble01 : MumfordDivisor ℚ := cantorAdd 16 hypRhoX3p1 1 hypPt01 hypPt01

/-- **★ The doubling `2·(0,1)` is valid and reduced** (`native_decide`): the tangent-line doubling
produces a valid reduced Mumford divisor (`deg u ≤ g = 1`). -/
theorem cantorDouble01_valid_reduced :
    mumfordValid hypRhoX3p1 cantorDouble01 = true
    ∧ mumfordIsReduced 1 cantorDouble01 = true := by native_decide

/-- **★ `2·(0,1) = (0, −1) = −(0,1)`** (`native_decide`): `(0,1)` is an inflection point of `y² = x³+1`,
so its double is its own opposite `(0, −1)` (hence `(0,1)` is 3-torsion, `3·(0,1) = O`). The tangent at
`(0,1)` is horizontal and meets the curve triply there. -/
theorem cantorDouble01_eq : cantorDouble01 = mumfordPoint (0 : ℚ) (-1) := by native_decide

/-! ### ★ `(0,1)` is 3-torsion: `3·(0,1) = O` via `cantorMul` (`native_decide`)

Since `2·(0,1) = (0,−1) = −(0,1)`, adding one more `(0,1)` gives `3·(0,1) = (0,1) ⊕ (0,−1) = O`. This is
the **order** computation in miniature: the smallest `n` with `n·D = O` is `n = 3` here. `cantorMul`
computes the scalar multiple. -/

/-- **★ `(0,1)` is a 3-torsion point: `3·(0,1) = O`** (`native_decide`): `cantorMul 3 (0,1) =
mumfordIdentity`, while `2·(0,1) = (0,−1) ≠ O` and `1·(0,1) = (0,1) ≠ O`. So the **order** of `(0,1)` in
the Jacobian is `3` — the inflection point of `y² = x³ + 1`. This is the order / point-of-finite-order
computation (Trager Ch. 6) the torsion bound is built on, here run end-to-end by `cantorMul`. -/
theorem cantorMul_pt01_order3 :
    cantorMul 16 hypRhoX3p1 1 3 hypPt01 = mumfordIdentity
    ∧ cantorMul 16 hypRhoX3p1 1 2 hypPt01 ≠ mumfordIdentity
    ∧ cantorMul 16 hypRhoX3p1 1 1 hypPt01 = hypPt01 := by native_decide

/-! ## ★ The genus-2 stretch: `y² = x⁵ + 1` (`native_decide`)

A genuinely hyperelliptic example (`g = 2 > 1`), where Mathlib's elliptic group law does not apply.
`ρ = x⁵ + 1`, `deg ρ = 5 = 2g + 1`, so `g = 2`. Two points `(0,1)` (`1² = 0⁵+1`) and `(−1,0)` (`0² =
(−1)⁵+1 = 0`) give divisors; their Cantor composition stays a valid divisor on the curve. -/

/-- The radicand `ρ = x⁵ + 1 ∈ ℚ[x]` (`[1,0,0,0,0,1]`): the genus-2 hyperelliptic curve `y² = x⁵ + 1`. -/
def hypRhoX5p1 : CPolyG ℚ := [1, 0, 0, 0, 0, 1]

/-- **`radGenus (x⁵+1) = 2`** (`native_decide`): `y² = x⁵ + 1` is a genus-2 hyperelliptic curve (`deg ρ =
5 = 2·2 + 1`), beyond the elliptic case. -/
theorem cantorGenusX5p1_eq : radGenus 8 hypRhoX5p1 = 2 := by native_decide

/-- The point `(0, 1)` on `y² = x⁵ + 1` (`1² = 0⁵ + 1`): Mumford `(x, 1)`. -/
def hypG2Pt01 : MumfordDivisor ℚ := mumfordPoint (0 : ℚ) 1

/-- The point `(−1, 0)` on `y² = x⁵ + 1` (`0² = (−1)⁵ + 1 = 0`): a Weierstrass point, Mumford
`(x + 1, 0)`. -/
def hypG2PtM10 : MumfordDivisor ℚ := mumfordPoint (-1 : ℚ) 0

/-- **★ The genus-2 points are valid Mumford divisors** (`native_decide`): `(0,1)` and `(−1,0)` lie on
`y² = x⁵ + 1`, giving valid pairs. Each is reduced (`deg u = 1 ≤ g = 2`). -/
theorem hypG2_pts_valid :
    mumfordValid hypRhoX5p1 hypG2Pt01 = true
    ∧ mumfordValid hypRhoX5p1 hypG2PtM10 = true
    ∧ mumfordIsReduced 2 hypG2Pt01 = true
    ∧ mumfordIsReduced 2 hypG2PtM10 = true := by native_decide

/-- The genus-2 Cantor sum `(0,1) ⊕ (−1,0)` on `y² = x⁵ + 1`. Distinct support, distinct sheets — the
composition gives a degree-2 divisor `u = x(x+1)`, already reduced (`deg u = 2 ≤ g = 2`). -/
def cantorG2Sum : MumfordDivisor ℚ := cantorAdd 16 hypRhoX5p1 2 hypG2Pt01 hypG2PtM10

/-- **★ The genus-2 Cantor composition `(0,1) ⊕ (−1,0)` is valid and reduced** (`native_decide`): on the
hyperelliptic curve `y² = x⁵ + 1` (`g = 2`), Cantor's group law produces a valid reduced divisor
(`deg u ≤ 2`) — the arithmetic works beyond the elliptic case, where no Mathlib group law exists. -/
theorem cantorG2Sum_valid_reduced :
    mumfordValid hypRhoX5p1 cantorG2Sum = true
    ∧ mumfordIsReduced 2 cantorG2Sum = true := by native_decide

/-- **★ The genus-2 sum `(0,1) ⊕ (−1,0)` is the two-point divisor `(x² + x, …)`** (`native_decide`): the
support is `{0, −1}`, so `u = x·(x+1) = x² + x`. The two points are on different sheets (`y = 1` and
`y = 0`), so the composition keeps both; `v` interpolates them. A genuine genus-2 reduced divisor of
degree `g = 2`. -/
theorem cantorG2Sum_u :
    cantorG2Sum.u = ([0, 1, 1] : CPolyG ℚ) := by native_decide

/-! ## ★ The Cantor-group-law milestone (`native_decide`) -/

/-- **★★ THE HYPERELLIPTIC JACOBIAN GROUP LAW (CANTOR'S ALGORITHM) COMPUTES AND VALIDATES** (Cantor 1987;
Trager Ch. 6, `native_decide`). `cantorCompose` (composition) + `cantorReduce` (reduction) +
`cantorAdd = reduce ∘ compose` + `cantorMul` (scalar multiple) implement the group law on Mumford pairs.
On the **elliptic** curve `y² = x³ + 1` (genus 1 = the elliptic group):
* `(0,1) ⊕ (2,3) = (−1,0)` — chord addition (`cantorSum0123_eq`),
* `P ⊕ (−P) = O` — the inverse law (`cantorSumPoppP_eq`),
* `2·(0,1) = (0,−1)` and `3·(0,1) = O` — doubling and the order-3 (inflection) torsion (`cantorMul`),
all landing in valid reduced divisors. On the **genus-2** curve `y² = x⁵ + 1` (beyond Mathlib's elliptic
group law), `(0,1) ⊕ (−1,0)` composes to a valid reduced degree-2 divisor `(x² + x, …)`. The engine now
computes the hyperelliptic Jacobian group law — the core of the torsion bound (the **order**, smallest
`n` with `n·D = O`, is `cantorMul` searched, next). -/
theorem cantor_group_law_validates :
    -- elliptic group law on y² = x³+1
    (mumfordNormEq cantorSum0123 (mumfordPoint (-1 : ℚ) 0) = true
      ∧ mumfordValid hypRhoX3p1 cantorSum0123 = true
      ∧ mumfordIsReduced 1 cantorSum0123 = true)
    ∧ (cantorSumPoppP = mumfordIdentity
      ∧ mumfordValid hypRhoX3p1 cantorSumPoppP = true)
    ∧ (cantorDouble01 = mumfordPoint (0 : ℚ) (-1)
      ∧ mumfordValid hypRhoX3p1 cantorDouble01 = true
      ∧ mumfordIsReduced 1 cantorDouble01 = true)
    -- the order of (0,1) is 3 (a 3-torsion point)
    ∧ (cantorMul 16 hypRhoX3p1 1 3 hypPt01 = mumfordIdentity
      ∧ cantorMul 16 hypRhoX3p1 1 2 hypPt01 ≠ mumfordIdentity)
    -- genus-2 composition on y² = x⁵+1
    ∧ (mumfordValid hypRhoX5p1 cantorG2Sum = true
      ∧ mumfordIsReduced 2 cantorG2Sum = true
      ∧ cantorG2Sum.u = ([0, 1, 1] : CPolyG ℚ)) := by native_decide

/-! ### Deliverable: `#print axioms`

`[propext, Classical.choice, Quot.sound]` plus `Lean.ofReduceBool` (the `native_decide` kernel-reduction
axiom). No `sorry`. -/

#print axioms cantor_group_law_validates
#print axioms cantorSum0123_eq
#print axioms cantorMul_pt01_order3

/-! ## The next piece: the divisor order → torsion bound

`cantorMul` makes the **order** of `D` (the smallest `n ≥ 1` with `n·D = mumfordIdentity`) computable by
searching `1·D, 2·D, 3·D, …` (`cantorMul_pt01_order3` does this by hand for `(0,1)`, order 3). The
remaining torsion sub-arc (Trager Ch. 6, recorded — not yet formalized — in the
`Sources/Doi_10_1007_b138171` catalog):

1. **The order search** `cantorOrder ρ g D = min { n ≥ 1 | n·D = O }` — a fuel-bounded loop over
   `cantorMul`. The fuel bound is the torsion-subgroup size.

2. **Reduction mod p / good reduction for the BOUND** — the torsion subgroup of `Jac(ℚ)` injects into
   `Jac(𝔽_p)` (finite) for a prime `p` of good reduction (`p ∤ disc ρ`), bounding the order `m ≤
   |Jac(𝔽_p)|` so the order search terminates.

3. **Wiring into the integrator** — when `radLogArgSolveG` returns `none` (the non-principal branch), the
   order `m` scales the candidate residue coefficient to the `(1/m)·log` term, closing the simple-radical
   log part for points of finite order.

The milestone delivered here is Cantor's **composition + reduction + group law + scalar multiple**,
`native_decide`-validated as genuine elliptic point addition and genus-2 hyperelliptic arithmetic. -/

end DeepWiki.SymbolicIntegration
