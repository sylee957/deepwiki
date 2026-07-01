import DeepWiki.SymbolicIntegration.ComputableCantorComposition

/-! # The divisor order + good-reduction torsion bound (Trager Ch. 6 §2-3, "Points of Finite Order")

Cantor's Jacobian arithmetic (`ComputableCantorComposition`) gives the scalar multiple `cantorMul n D`
on Mumford divisors. The **decision step** of Trager's torsion sub-arc ("Integration of Algebraic
Functions", Ch. 6, "Principal Divisors and Points of Finite Order") asks, for a residue divisor `D`:

* is `D` **torsion** — some `m·D = O` (the identity `(1, 0)`) — so the integral is **elementary** with a
  `(1/m)·log` term, or
* is `D` of **infinite order** — `m·D ≠ O` for every `m ≥ 1` — so the integral is **NOT elementary**?

**The order search.** `cantorOrder fuel ρ g D = some m` for the smallest `m ≥ 1` with `m·D = O`, searching
`1·D, 2·D, 3·D, …` (each a `cantorAdd D`, compared to `mumfordIdentity` by `mumfordNormEq`), and `none` if
no `m ≤ fuel` works. The `cantorMul_pt01_order3` fact (`(0,1)` on `y² = x³+1` is order 3) is recovered
here as a clean `cantorOrder … = some 3`.

**The termination bound (good reduction, Ch. 6 §2).** A torsion divisor's order over ℚ **injects** into
`Jac(𝔽_p)` for a prime `p` of good reduction (`p` not dividing the discriminant or a coefficient
denominator): so `order_ℚ(D) ∣ order_{𝔽_p}(reduction of D)`, and in particular
`order_ℚ(D) ≤ order_{𝔽_p}(reduction of D) ≤ |Jac(𝔽_p)|`. Reducing `D` mod `p` and computing its order in
the **finite** group `Jac(𝔽_p)` gives a terminating **ceiling**: search the ℚ-order only up to the 𝔽_p
order; if the ℚ-search reaches the ceiling without hitting `O`, `D` is **non-torsion** ⟹ the integral is
not elementary.

**Running Cantor over 𝔽_p.** The engine's Cantor/Mumford defs are `[CField α]`-generic, so we instantiate
the carrier at `α = ZMod p` (a field for `p` prime). This file supplies the missing **`CField (ZMod p)`**
and **`CFieldSpec (ZMod p)`** instances (`ZMod p`'s own operations; bridge `K = ZMod p`, `toK = id`), and
`mumfordReduceModP` maps the Mumford `(u, v)` coefficients `ℚ → ZMod p`.

* **`cantorOrder`** — the fuel-bounded order search. `native_decide`: `(0,1)` on `y² = x³+1` → order 3;
  `(−1,0)` (2-torsion) → order 2; the identity → order 1.
* **`mumfordReduceModP`** + `cantorOrder` over `ZMod p` — `native_decide`: the `(0,1)` divisor's order mod
  `p = 5, 7` is `3` (= the ℚ-order, a torsion point reduces to the same order), with `|Jac(𝔽_p)|`-bounded.
* **`isTorsionDivisor` / `elementarityViaTorsion`** — the torsion DECISION: wrap `cantorOrder` with the
  𝔽_p order as the ℚ-search ceiling. `some m` = torsion (⟹ elementary, `(1/m)·log`); `none` = non-torsion
  (⟹ not elementary). `native_decide`: the order-3 `(0,1)` (torsion); and the **infinite-order** point
  `(3, 5)` on `y² = x³−2` (a rank-1 curve) — `none`, the famous non-torsion witness, whose orders mod
  `5, 7, 11` are `2, 7, 12` (distinct → no common ℚ-order, the reduction-mod-`p` non-torsion proof).

Mathlib has the abstract `WeierstrassCurve` torsion theory but **no hyperelliptic point counting / order
algorithm**, so — like the rest of this arc — we build it **computationally**, `native_decide`-validated
over `ℚ[x]` and `ZMod p`. This is the decision behind Trager's "points of finite order". -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ## `CField (ZMod p)`: running the engine over the finite field 𝔽_p

`ZMod p` is a field when `p` is prime (`[Fact p.Prime]`), with computable `+`, `*`, `-`, `⁻¹`
(`Nat.gcdA`-based) and `DecidableEq`. Instantiating `[CField α]` at `α = ZMod p` runs **the whole**
Cantor/Mumford engine over 𝔽_p — the finite Jacobian where torsion orders are bounded. The bridge
`CFieldSpec (ZMod p)` is the trivial `K = ZMod p`, `toK = id` (all homomorphism laws `rfl`). -/

/-- **`CField (ZMod p)`** (`p` prime): the finite field 𝔽_p as a computable field — `ZMod p`'s own
`zero`/`one`/`add`/`mul`/`neg`/`inv` (the inverse is `Nat.gcdA`-based, computable) and
`isZero a := decide (a = 0)`. Instantiating the `[CField α]`-generic Cantor/Mumford engine at `α = ZMod p`
runs the Jacobian arithmetic over 𝔽_p — the finite group bounding torsion orders (Trager Ch. 6 §2). -/
instance instCFieldZMod (p : ℕ) [Fact p.Prime] : CField (ZMod p) where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  inv := (·⁻¹)
  isZero a := decide (a = 0)

/-- **`CFieldSpec (ZMod p)`** (`p` prime): the trivial bridge `K = ZMod p`, `toK = id` — every
homomorphism law is `rfl` (the `CField (ZMod p)` operations *are* `ZMod p`'s field operations), and
`isZero_iff` is decidable equality. Certifies the engine's correctness layer over 𝔽_p. -/
instance instCFieldSpecZMod (p : ℕ) [Fact p.Prime] : CFieldSpec (ZMod p) where
  K := ZMod p
  toK := id
  toK_zero := rfl
  toK_one := rfl
  toK_add _ _ := rfl
  toK_mul _ _ := rfl
  toK_neg _ := rfl
  toK_inv _ := rfl
  isZero_iff a := by show decide (a = 0) = true ↔ id a = 0; simp

/-- `Nat.Prime 5` as a `Fact` instance, so `CField (ZMod 5)` resolves for the validations below. -/
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `Nat.Prime 7` as a `Fact` instance, so `CField (ZMod 7)` resolves for the validations below. -/
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- `Nat.Prime 11` as a `Fact` instance, so `CField (ZMod 11)` resolves for the validations below. -/
instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

namespace CPolyG

variable {α : Type*} [CField α] [DecidableEq α]

/-! ### The order search `cantorOrder` (the smallest `m ≥ 1` with `m·D = O`)

`cantorOrder fuel cfuel ρ g D = some m` for the least `m ≥ 1` with `m·D = mumfordIdentity` (compared by
`mumfordNormEq`, the polynomial-equality test that ignores trailing-zero list encoding), searching
`1·D, 2·D, …` by the running accumulator `acc ← cantorAdd D acc`. `fuel` bounds how many multiples are
tried (the torsion-subgroup-size ceiling); `cfuel` is the per-`cantorAdd` gcd/division fuel. Returns
`none` if no `m ≤ fuel` is the order (a candidate for an infinite-order point). -/

/-- **Order-search loop** `cantorOrderAux fuel cfuel ρ g D acc n`: with `acc = n·D` already computed,
test `(n+1)·D = D ⊕ acc` against `mumfordIdentity` (`mumfordNormEq`); on a hit return `some (n+1)`, else
recurse with the new accumulator. `fuel` bounds the remaining multiples to try. Generic over
`[CField α] [DecidableEq α]`. -/
def cantorOrderAux (fuel cfuel : ℕ) (ρ : CPolyG α) (g : ℕ)
    (D acc : MumfordDivisor α) (n : ℕ) : Option ℕ :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let acc := cantorAdd cfuel ρ g D acc
    if mumfordNormEq acc mumfordIdentity then some (n + 1)
    else cantorOrderAux fuel cfuel ρ g D acc (n + 1)

/-- **The divisor order** `cantorOrder fuel cfuel ρ g D = some m` — the smallest `m ≥ 1` with
`m·D = O` (`mumfordIdentity`) on the hyperelliptic Jacobian of `y² = ρ`, searching `1·D, 2·D, …` up to
`fuel` multiples (`mumfordNormEq` comparison; `cfuel` the per-`cantorAdd` fuel). `none` if no `m ≤ fuel`
works — the order exceeds the fuel (a candidate infinite-order / non-torsion point). The **torsion /
point-of-finite-order** quantity (Trager Ch. 6): `some m` says `D` is `m`-torsion ⟹ the simple-radical
integral is elementary with a `(1/m)·log` term. Generic over `[CField α] [DecidableEq α]`; run over
`α = ZMod p` it computes the order in the finite group `Jac(𝔽_p)`. -/
def cantorOrder (fuel cfuel : ℕ) (ρ : CPolyG α) (g : ℕ) (D : MumfordDivisor α) : Option ℕ :=
  cantorOrderAux fuel cfuel ρ g D mumfordIdentity 0

/-- **Is `D` torsion within `fuel`** `cantorIsTorsion fuel cfuel ρ g D`: `true` iff `cantorOrder` finds a
finite order `≤ fuel`. A `Bool` view of `cantorOrder` for the decision wrappers. Generic over
`[CField α] [DecidableEq α]`. -/
def cantorIsTorsion (fuel cfuel : ℕ) (ρ : CPolyG α) (g : ℕ) (D : MumfordDivisor α) : Bool :=
  (cantorOrder fuel cfuel ρ g D).isSome

end CPolyG

/-! ## Reduction modulo `p`: `ℚ → ZMod p` on Mumford coefficients (good reduction, Ch. 6 §2)

A rational divisor `D = (u, v) ∈ ℚ[x]²` reduces mod a prime `p` by mapping each coefficient
`q = num/den ↦ (num : 𝔽_p)·(den : 𝔽_p)⁻¹`. For a **good** prime (`p` dividing neither the discriminant of
`ρ` nor a coefficient denominator), the reduction is a valid divisor on `y² = (ρ mod p)`, and the
reduction map on the Jacobian is an injective homomorphism on prime-to-`p` torsion (Trager Ch. 6 §2). So
the order of `D` mod `p`, computed in the **finite** `Jac(𝔽_p)`, is a multiple of (hence bounds) the
ℚ-order of `D`. -/

open CPolyG

/-- **Coefficient reduction** `ratToZMod p q = (q.num : 𝔽_p)·(q.den : 𝔽_p)⁻¹` — the field map `ℚ → ZMod p`
on a single coefficient (numerator cast times inverse denominator cast). Well-defined and a field
homomorphism when `p` does not divide `q.den` (the good-reduction condition for this coefficient). -/
def ratToZMod (p : ℕ) (q : ℚ) : ZMod p := (q.num : ZMod p) * ((q.den : ZMod p))⁻¹

/-- **Polynomial reduction** `polyToZMod p u` — apply `ratToZMod p` coefficientwise, mapping `u ∈ ℚ[x]` to
`(u mod p) ∈ 𝔽_p[x]` (as `CPolyG` coefficient lists). -/
def polyToZMod (p : ℕ) (u : CPolyG ℚ) : CPolyG (ZMod p) := u.map (ratToZMod p)

/-- **Divisor reduction mod `p`** `mumfordReduceModP p D = (u mod p, v mod p)` — reduce both Mumford
coefficient polynomials `ℚ → 𝔽_p` (Trager Ch. 6 §2, good reduction). For a good prime the result is a
valid divisor on `y² = (ρ mod p)`, and `cantorOrder` over `α = ZMod p` computes its order in the finite
group `Jac(𝔽_p)` — the **ceiling** bounding (and divided by) the ℚ-order of `D`. -/
def mumfordReduceModP (p : ℕ) (D : MumfordDivisor ℚ) : MumfordDivisor (ZMod p) :=
  ⟨polyToZMod p D.u, polyToZMod p D.v⟩

/-- **The 𝔽_p order ceiling** `orderModP p fuel cfuel ρ g D` — the order of `D mod p` in `Jac(𝔽_p)`
(`cantorOrder` over `α = ZMod p`). For a good prime `p`, a multiple of the ℚ-order of `D` (the
reduction-mod-`p` injection, Trager Ch. 6 §2); used as the terminating **ceiling** for the ℚ-order search
in `isTorsionDivisor`. `none` if even the finite-group order exceeds `fuel`. -/
def orderModP (p fuel cfuel : ℕ) [Fact p.Prime] (ρ : CPolyG ℚ) (g : ℕ) (D : MumfordDivisor ℚ) :
    Option ℕ :=
  cantorOrder fuel cfuel (polyToZMod p ρ) g (mumfordReduceModP p D)

/-! ## The torsion DECISION (Trager Ch. 6 §2-3, "points of finite order")

`isTorsionDivisor` uses the 𝔽_p order (`orderModP`) as the terminating ceiling for the ℚ-order search: a
torsion `D` has `order_ℚ(D) ∣ order_{𝔽_p}(D)`, so searching the ℚ-order only up to `order_{𝔽_p}(D)`
suffices. `some m` ⟹ `D` is `m`-torsion ⟹ the integral is **elementary** with a `(1/m)·log` term;
`none` ⟹ `D` is **non-torsion** ⟹ the integral is **NOT elementary**. -/

/-- **The torsion decision** `isTorsionDivisor p cfuel ρ g D` (Trager Ch. 6 §2-3, "points of finite
order"): reduce `D` mod the good prime `p`, compute its order `c` in the **finite** `Jac(𝔽_p)`
(`orderModP`, the terminating ceiling), then search the **ℚ**-order only up to `c`. Returns `some m` (the
ℚ-order, `D` is `m`-torsion) or `none` (the ℚ-search hit the 𝔽_p ceiling without `O`, so `D` is
**non-torsion**). The 𝔽_p ceiling `c` (its own search bounded by `p² + 4 > |Jac(𝔽_p)|` for the small
elliptic examples) is what makes the otherwise-unbounded ℚ-search terminate. `some m` ⟹ elementary with
`(1/m)·log`; `none` ⟹ not elementary. -/
def isTorsionDivisor (p cfuel : ℕ) [Fact p.Prime] (ρ : CPolyG ℚ) (g : ℕ) (D : MumfordDivisor ℚ) :
    Option ℕ :=
  match orderModP p (p ^ 2 + 4) cfuel ρ g D with
  | none => none
  | some ceil => cantorOrder ceil cfuel ρ g D

/-- **The elementarity decision via torsion** `elementarityViaTorsion p cfuel ρ g D`: `true` iff the
residue divisor `D` is torsion (`isTorsionDivisor` returns `some m`) — i.e. the simple-radical integral
**is elementary** (with a `(1/m)·log` term). `false` ⟹ `D` is a point of infinite order ⟹ the integral is
**not elementary**. The Boolean face of Trager's torsion test (Ch. 6 §2-3). -/
def elementarityViaTorsion (p cfuel : ℕ) [Fact p.Prime] (ρ : CPolyG ℚ) (g : ℕ) (D : MumfordDivisor ℚ) :
    Bool :=
  (isTorsionDivisor p cfuel ρ g D).isSome

/-! ## ★ Validation over `ℚ[x]` and `ZMod p` (`native_decide`)

The flagship torsion case is the **elliptic** `y² = x³ + 1`: `(0,1)` is an order-3 (inflection /
3-torsion) point. The flagship **non-torsion** case is `(3, 5)` on `y² = x³ − 2` (a rank-1 curve — the
point has infinite order). -/

open CPolyG

/-! ### The order search over ℚ (`native_decide`)

`cantorOrder` recovers the `cantorMul_pt01_order3` fact as a clean order: `(0,1)` → 3, `(−1,0)` → 2,
identity → 1. -/

/-- **★ The order of `(0,1)` on `y² = x³+1` is 3** (`native_decide`): `cantorOrder hypPt01 = some 3` — the
inflection point is 3-torsion (`3·(0,1) = O`, `2·(0,1) ≠ O`), recovering `cantorMul_pt01_order3` as a
single order computation. This is the torsion order ⟹ a `(1/3)·log` term. -/
theorem cantorOrder_pt01_eq : cantorOrder 8 16 hypRhoX3p1 1 hypPt01 = some 3 := by native_decide

/-- **★ The order of `(−1,0)` on `y² = x³+1` is 2** (`native_decide`): `cantorOrder hypPtM10 = some 2` —
the Weierstrass point `(−1,0)` (`y = 0`, its own opposite) is 2-torsion (`2·(−1,0) = O`). -/
theorem cantorOrder_ptM10_eq : cantorOrder 8 16 hypRhoX3p1 1 hypPtM10 = some 2 := by native_decide

/-- **★ The order of the identity is 1** (`native_decide`): `cantorOrder mumfordIdentity = some 1` —
`1·O = O`, the trivial torsion order. -/
theorem cantorOrder_identity_eq :
    cantorOrder 8 16 hypRhoX3p1 1 (mumfordIdentity : MumfordDivisor ℚ) = some 1 := by native_decide

/-- **★ The order of `(2,3)` on `y² = x³+1` is 6** (`native_decide`): `cantorOrder hypPt23 = some 6` —
`(2,3)` generates the **full** torsion group `ℤ/6ℤ` of `y² = x³+1` (rank 0, torsion `ℤ/6`), so it is
6-torsion. (The order-3 `(0,1)` is `2·(2,3)`, the order-2 `(−1,0)` is `3·(2,3)`.) -/
theorem cantorOrder_pt23_eq : cantorOrder 8 16 hypRhoX3p1 1 hypPt23 = some 6 := by native_decide

/-- **★ A too-small fuel returns `none`** (`native_decide`): `cantorOrder` with fuel 4 on `(2,3)` (true
order 6) returns `none` — the search is bounded, so under-fueling reports "no order within fuel". The
`isTorsionDivisor` decision picks the fuel as the 𝔽_p order so this never under-reports a genuine
torsion order. -/
theorem cantorOrder_pt23_lowfuel_none :
    cantorOrder 4 16 hypRhoX3p1 1 hypPt23 = none := by native_decide

/-! ### Reduction mod `p` and the order in `Jac(𝔽_p)` (`native_decide`)

The `(0,1)` divisor reduces mod `p = 5, 7` to an order-3 point of `Jac(𝔽_p)` (a torsion point keeps its
order under good reduction), and the order divides `|Jac(𝔽_p)|`. -/

/-- The reduction of `y² = x³+1` and the point `(0,1)` mod `p = 5`: the curve and divisor over 𝔽₅. -/
def rhoX3p1Mod5 : CPolyG (ZMod 5) := polyToZMod 5 hypRhoX3p1

/-- The reduction of `(0,1)` mod `p = 5`: a divisor on `y² = x³+1` over 𝔽₅. -/
def pt01Mod5 : MumfordDivisor (ZMod 5) := mumfordReduceModP 5 hypPt01

/-- **★ `(0,1) mod 5` is a valid divisor on `y² = x³+1` over 𝔽₅** (`native_decide`): good reduction at
`p = 5` (5 ∤ disc(x³+1) = −27) keeps the Mumford pair valid over the finite field. -/
theorem pt01Mod5_valid : mumfordValid rhoX3p1Mod5 pt01Mod5 = true := by native_decide

/-- **★ The order of `(0,1)` mod `5` is 3** (`native_decide`): `cantorOrder` over `α = ZMod 5` gives
order 3 — the torsion point `(0,1)` keeps its ℚ-order 3 under good reduction at 5 (Trager Ch. 6 §2: the
reduction map is injective on prime-to-5 torsion, so order is preserved here). The ℚ-order 3 divides
this. -/
theorem cantorOrder_pt01_mod5 : cantorOrder 40 16 rhoX3p1Mod5 1 pt01Mod5 = some 3 := by native_decide

/-- **★ The order of `(0,1)` mod `7` is also 3** (`native_decide`): over 𝔽₇ (good reduction, 7 ∤ −27) the
order of `(0,1)` is again 3, confirming the ℚ-order 3 across two good primes (a torsion point reduces to
the *same* order at every good prime — the reduction-mod-`p` consistency). -/
theorem cantorOrder_pt01_mod7 :
    cantorOrder 40 16 (polyToZMod 7 hypRhoX3p1) 1 (mumfordReduceModP 7 hypPt01) = some 3 := by
  native_decide

/-! ### ★ The torsion DECISION on a torsion point (`native_decide`)

`isTorsionDivisor` decides `(0,1)` is torsion of order 3, using the 𝔽₅ order as the ℚ-search ceiling. -/

/-- **★ `(0,1)` is decided torsion of order 3** (`native_decide`): `isTorsionDivisor 5 (0,1) = some 3` —
the good prime `p = 5` bounds the search (𝔽₅ order 3 is the ceiling), and the ℚ-order is found to be 3.
So the integral is **elementary** with a `(1/3)·log` term (Trager Ch. 6 §3, the principal multiple of the
residue divisor). -/
theorem isTorsionDivisor_pt01 : isTorsionDivisor 5 16 hypRhoX3p1 1 hypPt01 = some 3 := by native_decide

/-- **★ `(−1,0)` is decided torsion of order 2** (`native_decide`): `isTorsionDivisor 7 (−1,0) = some 2` —
the 2-torsion Weierstrass point, deciding elementary with a `(1/2)·log` term. (Uses `p = 7`; 7 ∤
disc.) -/
theorem isTorsionDivisor_ptM10 :
    isTorsionDivisor 7 16 hypRhoX3p1 1 hypPtM10 = some 2 := by native_decide

/-- **★ `elementarityViaTorsion` says `(0,1)` gives an elementary integral** (`native_decide`): the
Boolean decision is `true` — `(0,1)` is torsion, so the simple-radical integral over `y² = x³+1` is
elementary. -/
theorem elementarityViaTorsion_pt01 :
    elementarityViaTorsion 5 16 hypRhoX3p1 1 hypPt01 = true := by native_decide

/-! ## ★ The NON-TORSION witness: `(3, 5)` on `y² = x³ − 2` (`native_decide`)

`y² = x³ − 2` is an elliptic curve of **rank 1** (Mordell–Weil rank 1, trivial torsion): the point
`(3, 5)` (`5² = 25 = 27 − 2 = 3³ − 2`) generates a free ℤ, so it has **infinite order**. The ℚ-order
search runs forever; the good-reduction ceiling makes the decision **terminate** as `none` (non-torsion ⟹
the integral is **NOT elementary**). The orders of `(3,5)` mod `5, 7, 11` are `2, 7, 12` — all *different*
(an infinite-order point reduces to different orders at different primes; a torsion point would not), the
classic reduction-mod-`p` proof that `(3,5)` is non-torsion. -/

/-- The radicand `ρ = x³ − 2 ∈ ℚ[x]` (`[-2,0,0,1]`): the rank-1 elliptic curve `y² = x³ − 2`. -/
def hypRhoX3m2 : CPolyG ℚ := [-2, 0, 0, 1]

/-- The point `(3, 5)` on `y² = x³ − 2` (`5² = 25 = 3³ − 2`): an **infinite-order** point (the curve has
rank 1, trivial torsion). Mumford `(x − 3, 5)`. -/
def hypPt35 : MumfordDivisor ℚ := mumfordPoint (3 : ℚ) 5

/-- **★ `(3,5)` is a valid divisor on `y² = x³−2`** (`native_decide`): `5² = 25 = 27 − 2`, so the Mumford
pair `(x − 3, 5)` lies on the curve. -/
theorem hypPt35_valid : mumfordValid hypRhoX3m2 hypPt35 = true := by native_decide

/-- **★ The ℚ-order of `(3,5)` exceeds 30** (`native_decide`): `cantorOrder` with fuel 30 returns `none` —
`(3,5)` has infinite order on the rank-1 curve `y² = x³−2`, so no multiple `≤ 30` is `O`. The unbounded
ℚ-search alone cannot conclude "non-torsion" (it could in principle find `O` later); the good-reduction
ceiling below is what makes the decision terminate. -/
theorem cantorOrder_pt35_none : cantorOrder 30 24 hypRhoX3m2 1 hypPt35 = none := by native_decide

/-- **★ The orders of `(3,5)` mod `5, 7, 11` are `2, 7, 12`** (`native_decide`): `cantorOrder` over
`α = ZMod p` gives finite orders in each `Jac(𝔽_p)` — but **distinct** ones. A torsion point reduces to
the *same* order (or a fixed multiple) at every good prime; the spread `2, 7, 12` (with `gcd = 1`)
**proves** `(3,5)` is non-torsion (Trager Ch. 6 §2: if `(3,5)` were `m`-torsion, `m` would divide each of
2, 7, 12, forcing `m = 1`, i.e. `(3,5) = O`, false). The reduction-mod-`p` non-torsion certificate. -/
theorem cantorOrder_pt35_modp :
    cantorOrder 60 24 (polyToZMod 5 hypRhoX3m2) 1 (mumfordReduceModP 5 hypPt35) = some 2
    ∧ cantorOrder 60 24 (polyToZMod 7 hypRhoX3m2) 1 (mumfordReduceModP 7 hypPt35) = some 7
    ∧ cantorOrder 60 24 (polyToZMod 11 hypRhoX3m2) 1 (mumfordReduceModP 11 hypPt35) = some 12 := by
  native_decide

/-- **★★ `(3,5)` is decided NON-TORSION** (`native_decide`): `isTorsionDivisor 5 (3,5) = none` — the
good-reduction ceiling (𝔽₅ order 2) bounds the ℚ-search, which finds `2·(3,5) ≠ O` and so concludes
**non-torsion** without searching forever. So the integral of the corresponding algebraic function over
`y² = x³−2` is **NOT elementary** (Trager Ch. 6: a residue divisor of infinite order has no principal
multiple, so its `log` argument is not an algebraic function — the integral is non-elementary). The famous
"points of finite order" decision, here returning the *negative* answer with a terminating certificate. -/
theorem isTorsionDivisor_pt35_none : isTorsionDivisor 5 24 hypRhoX3m2 1 hypPt35 = none := by native_decide

/-- **★ `elementarityViaTorsion` says `(3,5)` gives a NON-elementary integral** (`native_decide`): the
Boolean decision is `false` — `(3,5)` is non-torsion, so the simple-radical integral over `y² = x³−2` is
not elementary. The decision terminates (good reduction) where the naive ℚ-search would not. -/
theorem elementarityViaTorsion_pt35 :
    elementarityViaTorsion 5 24 hypRhoX3m2 1 hypPt35 = false := by native_decide

/-! ## ★ The divisor-order + torsion-decision milestone (`native_decide`) -/

/-- **★★ THE DIVISOR ORDER + GOOD-REDUCTION TORSION DECISION COMPUTE AND VALIDATE** (Trager Ch. 6 §2-3,
"Principal Divisors and Points of Finite Order", `native_decide`). `cantorOrder` (the order search,
smallest `m` with `m·D = O`), `mumfordReduceModP` + `CField (ZMod p)` (running Cantor over the finite
`Jac(𝔽_p)`), and `isTorsionDivisor` / `elementarityViaTorsion` (the decision: 𝔽_p order as the
ℚ-search ceiling) implement Trager's torsion test. On the **elliptic** `y² = x³+1`:
* the order of `(0,1)` is 3 (inflection / 3-torsion), of `(−1,0)` is 2, of the identity is 1;
* `(0,1)` reduces mod `5` and `7` to order-3 points of `Jac(𝔽_p)` (torsion preserved under good
  reduction);
* `isTorsionDivisor` decides `(0,1)` torsion of order 3 ⟹ **elementary** with a `(1/3)·log` term.

On the **rank-1** curve `y² = x³−2`, the point `(3,5)` has **infinite order**: its ℚ-order search runs
past 30 (`none`), its orders mod `5, 7, 11` are the *distinct* `2, 7, 12` (the reduction-mod-`p`
non-torsion certificate), and `isTorsionDivisor` **terminates** as `none` ⟹ the integral is **NOT
elementary**. The engine now computes the hyperelliptic divisor order and **decides torsion** (the
elementarity decision for the non-principal log case) via Cantor + good reduction mod `p` — Trager's
famous "points of finite order" decision, both answers, with terminating certificates. -/
theorem divisor_order_torsion_decision_validates :
    -- the order search over ℚ
    (cantorOrder 8 16 hypRhoX3p1 1 hypPt01 = some 3
      ∧ cantorOrder 8 16 hypRhoX3p1 1 hypPtM10 = some 2
      ∧ cantorOrder 8 16 hypRhoX3p1 1 (mumfordIdentity : MumfordDivisor ℚ) = some 1)
    -- reduction mod p: order preserved at good primes for a torsion point
    ∧ (mumfordValid rhoX3p1Mod5 pt01Mod5 = true
      ∧ cantorOrder 40 16 rhoX3p1Mod5 1 pt01Mod5 = some 3
      ∧ cantorOrder 40 16 (polyToZMod 7 hypRhoX3p1) 1 (mumfordReduceModP 7 hypPt01) = some 3)
    -- the torsion DECISION: (0,1) torsion ⟹ elementary
    ∧ (isTorsionDivisor 5 16 hypRhoX3p1 1 hypPt01 = some 3
      ∧ elementarityViaTorsion 5 16 hypRhoX3p1 1 hypPt01 = true)
    -- the NON-TORSION witness (3,5) on y²=x³−2 ⟹ NOT elementary
    ∧ (mumfordValid hypRhoX3m2 hypPt35 = true
      ∧ cantorOrder 30 24 hypRhoX3m2 1 hypPt35 = none
      ∧ cantorOrder 60 24 (polyToZMod 5 hypRhoX3m2) 1 (mumfordReduceModP 5 hypPt35) = some 2
      ∧ cantorOrder 60 24 (polyToZMod 7 hypRhoX3m2) 1 (mumfordReduceModP 7 hypPt35) = some 7
      ∧ isTorsionDivisor 5 24 hypRhoX3m2 1 hypPt35 = none
      ∧ elementarityViaTorsion 5 24 hypRhoX3m2 1 hypPt35 = false) := by native_decide

/-! ### Deliverable: `#print axioms`

`[propext, Classical.choice, Quot.sound]` plus `Lean.ofReduceBool` (the `native_decide` kernel-reduction
axiom). No `sorry`. -/

#print axioms divisor_order_torsion_decision_validates
#print axioms cantorOrder_pt01_eq
#print axioms isTorsionDivisor_pt35_none

/-! ## The next piece: wiring the order into the integrator's non-principal branch

When `radLogArgSolveG` returns `none` (the non-principal log case: the residue divisor `D` has no single
principal generator), `isTorsionDivisor … = some m` says `m·D` **is** principal — so the candidate residue
coefficient is scaled to a `(1/m)·log` term, closing the simple-radical log part for points of finite
order. This sketch records the wiring; the **full function recovery** — computing the actual generator
`g` with `div(g) = m·D` (so the log argument is `(1/m)·log g`) — is a further piece (the principal-divisor
**reconstruction** of Trager Ch. 6 §1, on top of this decision). -/

/-- **The torsion log-term sketch** `radTorsionLogTerm p cfuel ρ g D`: when the residue divisor `D` is
torsion of order `m` (`isTorsionDivisor = some m`), the simple-radical log part contributes a `(1/m)·log`
term — return `some m` (the log-coefficient denominator) for the integrator's non-principal branch
(`radLogArgSolveG none`), or `none` (non-torsion ⟹ no elementary log term, the integral is not
elementary). This is the *decision* half; the **generator** `g` with `div(g) = m·D` (the actual argument
of `(1/m)·log g`) is the deferred principal-divisor reconstruction (Trager Ch. 6 §1). -/
def radTorsionLogTerm (p cfuel : ℕ) [Fact p.Prime] (ρ : CPolyG ℚ) (g : ℕ) (D : MumfordDivisor ℚ) :
    Option ℕ :=
  isTorsionDivisor p cfuel ρ g D

/-- **★ The torsion log-term sketch fires on `(0,1)`** (`native_decide`): `radTorsionLogTerm 5 (0,1) =
some 3` — the order-3 residue divisor contributes a `(1/3)·log` term to the integral (the generator of
`3·(0,1) = O` being the deferred reconstruction). On the non-torsion `(3,5)` it returns `none` (no
elementary log term). -/
theorem radTorsionLogTerm_examples :
    radTorsionLogTerm 5 16 hypRhoX3p1 1 hypPt01 = some 3
    ∧ radTorsionLogTerm 5 24 hypRhoX3m2 1 hypPt35 = none := by native_decide

end DeepWiki.SymbolicIntegration
