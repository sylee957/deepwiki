import DeepWiki.SymbolicIntegration.Computable.Algebraic.CantorComposition

/-! # Divisor order and the good-reduction torsion decision

`cantorOrder` searches the smallest `m ≥ 1` with `m·D = O` on a hyperelliptic Jacobian, and
`isTorsionDivisor` / `elementarityViaTorsion` decide torsion by using the order of `D mod p` in the
finite `Jac(𝔽_p)` (a good prime, computed via `CField (ZMod p)`) as the terminating ceiling for the
ℚ-order search: `some m` means the integral is elementary with a `(1/m)·log` term, `none` means the
residue divisor has infinite order and the integral is not elementary. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ## `CField (ZMod p)`: running the engine over the finite field 𝔽_p

`ZMod p` is a field for `p` prime, with computable `+`, `*`, `-`, `⁻¹` and `DecidableEq`, so the
`[CField α]`-generic Cantor/Mumford engine runs over 𝔽_p — the finite Jacobian where torsion orders
are bounded. The bridge `CFieldSpec (ZMod p)` is the trivial `K = ZMod p`, `toK = id`. -/

/-- `CField (ZMod p)` (`p` prime): the finite field 𝔽_p as a computable field — `ZMod p`'s own
`zero`/`one`/`add`/`mul`/`neg`/`inv` (the inverse is `Nat.gcdA`-based, computable) and
`isZero a := decide (a = 0)`. -/
instance instCFieldZMod (p : ℕ) [Fact p.Prime] : CField (ZMod p) where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  inv := (·⁻¹)
  isZero a := decide (a = 0)

/-- `CFieldSpec (ZMod p)` (`p` prime): the trivial bridge `K = ZMod p`, `toK = id` — every
homomorphism law is `rfl`, and `isZero_iff` is decidable equality. -/
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

/-- `Nat.Prime 5` as a `Fact` instance, so `CField (ZMod 5)` resolves. -/
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `Nat.Prime 7` as a `Fact` instance, so `CField (ZMod 7)` resolves. -/
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- `Nat.Prime 11` as a `Fact` instance, so `CField (ZMod 11)` resolves. -/
instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

namespace CPolyG

variable {α : Type*} [CField α] [DecidableEq α]

/-! ### The order search `cantorOrder`

`cantorOrder fuel ρ g D = some m` for the least `m ≥ 1` with `m·D = mumfordIdentity` (compared by
`mumfordNormEq`), searching `1·D, 2·D, …` by a running `cantorAdd` accumulator; `none` if no
`m ≤ fuel` works. -/

/-- Order-search loop `cantorOrderAux fuel ρ g D acc n`: with `acc = n·D` already computed, test
`(n+1)·D = D ⊕ acc` against `mumfordIdentity` (`mumfordNormEq`); on a hit return `some (n+1)`, else
recurse with the new accumulator. `fuel` bounds the remaining multiples to try. -/
def cantorOrderAux (fuel : ℕ) (ρ : CPolyG α) (g : ℕ)
    (D acc : MumfordDivisor α) (n : ℕ) : Option ℕ :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let acc := cantorAdd ρ g D acc
    if mumfordNormEq acc mumfordIdentity then some (n + 1)
    else cantorOrderAux fuel ρ g D acc (n + 1)

/-- Divisor order `cantorOrder fuel ρ g D = some m` — the smallest `m ≥ 1` with `m·D = O`
(`mumfordIdentity`) on the hyperelliptic Jacobian of `y² = ρ`, searching up to `fuel` multiples;
`none` if the order exceeds `fuel` (a candidate infinite-order point). `some m` says `D` is
`m`-torsion, so the simple-radical integral is elementary with a `(1/m)·log` term. Run over
`α = ZMod p` it computes the order in the finite group `Jac(𝔽_p)`. -/
def cantorOrder (fuel : ℕ) (ρ : CPolyG α) (g : ℕ) (D : MumfordDivisor α) : Option ℕ :=
  cantorOrderAux fuel ρ g D mumfordIdentity 0

end CPolyG

/-! ## Reduction modulo `p` on Mumford coefficients

For a good prime (`p` dividing neither the discriminant of `ρ` nor a coefficient denominator), the
reduction map on the Jacobian is injective on prime-to-`p` torsion, so the order of `D mod p` in the
finite `Jac(𝔽_p)` is a multiple of — hence bounds — the ℚ-order of `D`. -/

open CPolyG

/-- Coefficient reduction `ratToZMod p q = (q.num : 𝔽_p)·(q.den : 𝔽_p)⁻¹` — the field map
`ℚ → ZMod p` on a single coefficient; a field homomorphism when `p ∤ q.den` (the good-reduction
condition for this coefficient). -/
def ratToZMod (p : ℕ) (q : ℚ) : ZMod p := (q.num : ZMod p) * ((q.den : ZMod p))⁻¹

/-- Polynomial reduction `polyToZMod p u` — apply `ratToZMod p` coefficientwise, mapping `u ∈ ℚ[x]`
to `(u mod p) ∈ 𝔽_p[x]` as `CPolyG` coefficient lists. -/
def polyToZMod (p : ℕ) (u : CPolyG ℚ) : CPolyG (ZMod p) := u.map (ratToZMod p)

/-- Divisor reduction `mumfordReduceModP p D = (u mod p, v mod p)` — reduce both Mumford coefficient
polynomials `ℚ → 𝔽_p`. For a good prime the result is a valid divisor on `y² = (ρ mod p)`. -/
def mumfordReduceModP (p : ℕ) (D : MumfordDivisor ℚ) : MumfordDivisor (ZMod p) :=
  ⟨polyToZMod p D.u, polyToZMod p D.v⟩

/-- 𝔽_p order ceiling `orderModP p fuel ρ g D` — the order of `D mod p` in `Jac(𝔽_p)`
(`cantorOrder` over `α = ZMod p`). For a good prime `p`, a multiple of the ℚ-order of `D`; used as
the terminating ceiling for the ℚ-order search in `isTorsionDivisor`. `none` if even the
finite-group order exceeds `fuel`. -/
def orderModP (p fuel : ℕ) [Fact p.Prime] (ρ : CPolyG ℚ) (g : ℕ) (D : MumfordDivisor ℚ) :
    Option ℕ :=
  cantorOrder fuel (polyToZMod p ρ) g (mumfordReduceModP p D)

/-! ## The torsion decision

A torsion `D` has `order_ℚ(D) ∣ order_{𝔽_p}(D)`, so searching the ℚ-order only up to the 𝔽_p order
suffices — this is what makes the otherwise-unbounded ℚ-search terminate. -/

/-- Torsion decision `isTorsionDivisor p ρ g D`: reduce `D` mod the good prime `p`, compute its
order `c` in the finite `Jac(𝔽_p)` (`orderModP`, with fuel `p² + 4 > |Jac(𝔽_p)|` for the small
elliptic cases), then search the ℚ-order only up to `c`. Returns `some m` (`D` is `m`-torsion, the
integral is elementary with a `(1/m)·log` term) or `none` (the ℚ-search hit the 𝔽_p ceiling without
`O`, so `D` is non-torsion and the integral is not elementary). -/
def isTorsionDivisor (p : ℕ) [Fact p.Prime] (ρ : CPolyG ℚ) (g : ℕ) (D : MumfordDivisor ℚ) :
    Option ℕ :=
  match orderModP p (p ^ 2 + 4) ρ g D with
  | none => none
  | some ceil => cantorOrder ceil ρ g D

/-- Elementarity decision `elementarityViaTorsion p ρ g D`: `true` iff the residue divisor `D` is
torsion (`isTorsionDivisor = some m`) — i.e. the simple-radical integral is elementary with a
`(1/m)·log` term; `false` means `D` has infinite order and the integral is not elementary. -/
def elementarityViaTorsion (p : ℕ) [Fact p.Prime] (ρ : CPolyG ℚ) (g : ℕ) (D : MumfordDivisor ℚ) :
    Bool :=
  (isTorsionDivisor p ρ g D).isSome

/-! ## Validation over `ℚ[x]` and `ZMod p`

The torsion case is the elliptic `y² = x³ + 1` (`(0,1)` is 3-torsion); the non-torsion case is
`(3, 5)` on the rank-1 curve `y² = x³ − 2`. -/

open CPolyG

/-- The order of `(0,1)` on `y² = x³+1` is 3: the inflection point is 3-torsion
(`3·(0,1) = O`, `2·(0,1) ≠ O`). -/
theorem cantorOrder_pt01_eq : cantorOrder 8 hypRhoX3p1 1 hypPt01 = some 3 := by native_decide

/-- The order of `(−1,0)` on `y² = x³+1` is 2: the Weierstrass point (`y = 0`, its own opposite)
is 2-torsion. -/
theorem cantorOrder_ptM10_eq : cantorOrder 8 hypRhoX3p1 1 hypPtM10 = some 2 := by native_decide

/-- The order of the identity is 1: `1·O = O`. -/
theorem cantorOrder_identity_eq :
    cantorOrder 8 hypRhoX3p1 1 (mumfordIdentity : MumfordDivisor ℚ) = some 1 := by native_decide

/-- The order of `(2,3)` on `y² = x³+1` is 6: `(2,3)` generates the full torsion group `ℤ/6ℤ`
(the order-3 `(0,1)` is `2·(2,3)`, the order-2 `(−1,0)` is `3·(2,3)`). -/
theorem cantorOrder_pt23_eq : cantorOrder 8 hypRhoX3p1 1 hypPt23 = some 6 := by native_decide

/-- A too-small fuel returns `none`: `cantorOrder` with fuel 4 on `(2,3)` (true order 6) reports no
order within fuel. `isTorsionDivisor` picks the fuel as the 𝔽_p order, so it never under-reports a
genuine torsion order. -/
theorem cantorOrder_pt23_lowfuel_none :
    cantorOrder 4 hypRhoX3p1 1 hypPt23 = none := by native_decide

/-- The reduction of `y² = x³+1` mod `p = 5`: the curve over 𝔽₅. -/
def rhoX3p1Mod5 : CPolyG (ZMod 5) := polyToZMod 5 hypRhoX3p1

/-- The reduction of `(0,1)` mod `p = 5`: a divisor on `y² = x³+1` over 𝔽₅. -/
def pt01Mod5 : MumfordDivisor (ZMod 5) := mumfordReduceModP 5 hypPt01

/-- `(0,1) mod 5` is a valid divisor on `y² = x³+1` over 𝔽₅ (good reduction: 5 ∤ disc(x³+1) = −27). -/
theorem pt01Mod5_valid : mumfordValid rhoX3p1Mod5 pt01Mod5 = true := by native_decide

/-- The order of `(0,1)` mod `5` is 3: the torsion point keeps its ℚ-order under good reduction
(the reduction map is injective on prime-to-5 torsion). -/
theorem cantorOrder_pt01_mod5 : cantorOrder 40 rhoX3p1Mod5 1 pt01Mod5 = some 3 := by native_decide

/-- The order of `(0,1)` mod `7` is also 3: a torsion point reduces to the same order at every good
prime. -/
theorem cantorOrder_pt01_mod7 :
    cantorOrder 40 (polyToZMod 7 hypRhoX3p1) 1 (mumfordReduceModP 7 hypPt01) = some 3 := by
  native_decide

/-- `(0,1)` is decided torsion of order 3: `isTorsionDivisor` with the good prime `p = 5` (𝔽₅ order
3 as the ceiling) finds ℚ-order 3, so the integral is elementary with a `(1/3)·log` term. -/
theorem isTorsionDivisor_pt01 : isTorsionDivisor 5 hypRhoX3p1 1 hypPt01 = some 3 := by native_decide

/-- `(−1,0)` is decided torsion of order 2 (via the good prime `p = 7`), giving a `(1/2)·log`
term. -/
theorem isTorsionDivisor_ptM10 :
    isTorsionDivisor 7 hypRhoX3p1 1 hypPtM10 = some 2 := by native_decide

/-- `elementarityViaTorsion` decides `(0,1)` gives an elementary integral: `(0,1)` is torsion, so
the simple-radical integral over `y² = x³+1` is elementary. -/
theorem elementarityViaTorsion_pt01 :
    elementarityViaTorsion 5 hypRhoX3p1 1 hypPt01 = true := by native_decide

/-! ## The non-torsion witness: `(3, 5)` on `y² = x³ − 2`

`y² = x³ − 2` has Mordell–Weil rank 1 and trivial torsion, so `(3, 5)` has infinite order. The
orders of `(3,5)` mod `5, 7, 11` are the distinct `2, 7, 12` — a torsion point would reduce to the
same order at every good prime — the classic reduction-mod-`p` non-torsion certificate. -/

/-- The radicand `ρ = x³ − 2 ∈ ℚ[x]` (`[-2,0,0,1]`): the rank-1 elliptic curve `y² = x³ − 2`. -/
def hypRhoX3m2 : CPolyG ℚ := [-2, 0, 0, 1]

/-- The point `(3, 5)` on `y² = x³ − 2` (`5² = 25 = 3³ − 2`): an infinite-order point (the curve
has rank 1 and trivial torsion). Mumford `(x − 3, 5)`. -/
def hypPt35 : MumfordDivisor ℚ := mumfordPoint (3 : ℚ) 5

/-- `(3,5)` is a valid divisor on `y² = x³−2`: `5² = 25 = 27 − 2`. -/
theorem hypPt35_valid : mumfordValid hypRhoX3m2 hypPt35 = true := by native_decide

/-- The ℚ-order of `(3,5)` exceeds 30: no multiple `≤ 30` is `O`. The unbounded ℚ-search alone
cannot conclude non-torsion; the good-reduction ceiling is what makes the decision terminate. -/
theorem cantorOrder_pt35_none : cantorOrder 30 hypRhoX3m2 1 hypPt35 = none := by native_decide

/-- The orders of `(3,5)` mod `5, 7, 11` are `2, 7, 12` — distinct, with `gcd = 1`: if `(3,5)` were
`m`-torsion, `m` would divide each of 2, 7, 12, forcing `m = 1`, i.e. `(3,5) = O`, false. The
reduction-mod-`p` non-torsion certificate. -/
theorem cantorOrder_pt35_modp :
    cantorOrder 60 (polyToZMod 5 hypRhoX3m2) 1 (mumfordReduceModP 5 hypPt35) = some 2
    ∧ cantorOrder 60 (polyToZMod 7 hypRhoX3m2) 1 (mumfordReduceModP 7 hypPt35) = some 7
    ∧ cantorOrder 60 (polyToZMod 11 hypRhoX3m2) 1 (mumfordReduceModP 11 hypPt35) = some 12 := by
  native_decide

/-- `(3,5)` is decided non-torsion: the good-reduction ceiling (𝔽₅ order 2) bounds the ℚ-search,
which finds `2·(3,5) ≠ O` and concludes non-torsion without searching forever. A residue divisor of
infinite order has no principal multiple, so the corresponding integral over `y² = x³−2` is not
elementary. -/
theorem isTorsionDivisor_pt35_none : isTorsionDivisor 5 hypRhoX3m2 1 hypPt35 = none := by native_decide

/-- `elementarityViaTorsion` decides `(3,5)` gives a non-elementary integral: `(3,5)` is
non-torsion, and the decision terminates where the naive ℚ-search would not. -/
theorem elementarityViaTorsion_pt35 :
    elementarityViaTorsion 5 hypRhoX3m2 1 hypPt35 = false := by native_decide

/-- Combined validation of the divisor-order search and the good-reduction torsion decision: on
`y² = x³+1` the orders of `(0,1)`, `(−1,0)`, and the identity are 3, 2, 1; `(0,1)` reduces mod 5
and 7 to order-3 points (torsion preserved under good reduction) and is decided torsion of order 3
(elementary, `(1/3)·log`); on the rank-1 `y² = x³−2` the point `(3,5)` has ℚ-order beyond 30,
distinct orders `2, 7` mod `5, 7`, and is decided non-torsion (not elementary). -/
theorem divisor_order_torsion_decision_validates :
    -- the order search over ℚ
    (cantorOrder 8 hypRhoX3p1 1 hypPt01 = some 3
      ∧ cantorOrder 8 hypRhoX3p1 1 hypPtM10 = some 2
      ∧ cantorOrder 8 hypRhoX3p1 1 (mumfordIdentity : MumfordDivisor ℚ) = some 1)
    -- reduction mod p: order preserved at good primes for a torsion point
    ∧ (mumfordValid rhoX3p1Mod5 pt01Mod5 = true
      ∧ cantorOrder 40 rhoX3p1Mod5 1 pt01Mod5 = some 3
      ∧ cantorOrder 40 (polyToZMod 7 hypRhoX3p1) 1 (mumfordReduceModP 7 hypPt01) = some 3)
    -- the torsion decision: (0,1) torsion ⟹ elementary
    ∧ (isTorsionDivisor 5 hypRhoX3p1 1 hypPt01 = some 3
      ∧ elementarityViaTorsion 5 hypRhoX3p1 1 hypPt01 = true)
    -- the non-torsion witness (3,5) on y²=x³−2 ⟹ not elementary
    ∧ (mumfordValid hypRhoX3m2 hypPt35 = true
      ∧ cantorOrder 30 hypRhoX3m2 1 hypPt35 = none
      ∧ cantorOrder 60 (polyToZMod 5 hypRhoX3m2) 1 (mumfordReduceModP 5 hypPt35) = some 2
      ∧ cantorOrder 60 (polyToZMod 7 hypRhoX3m2) 1 (mumfordReduceModP 7 hypPt35) = some 7
      ∧ isTorsionDivisor 5 hypRhoX3m2 1 hypPt35 = none
      ∧ elementarityViaTorsion 5 hypRhoX3m2 1 hypPt35 = false) := by native_decide

/-- Torsion log-term decision `radTorsionLogTerm p ρ g D`: when the residue divisor `D` is torsion
of order `m` (`isTorsionDivisor = some m`), the simple-radical log part contributes a `(1/m)·log`
term — return `some m` (the log-coefficient denominator) for the integrator's non-principal branch,
or `none` (non-torsion, no elementary log term). The generator `g` with `div(g) = m·D` (the actual
argument of `(1/m)·log g`) is the principal-divisor reconstruction, handled downstream. -/
def radTorsionLogTerm (p : ℕ) [Fact p.Prime] (ρ : CPolyG ℚ) (g : ℕ) (D : MumfordDivisor ℚ) :
    Option ℕ :=
  isTorsionDivisor p ρ g D

/-- `radTorsionLogTerm` returns `some 3` on the 3-torsion `(0,1)` (a `(1/3)·log` term) and `none`
on the non-torsion `(3,5)` (no elementary log term). -/
theorem radTorsionLogTerm_examples :
    radTorsionLogTerm 5 hypRhoX3p1 1 hypPt01 = some 3
    ∧ radTorsionLogTerm 5 hypRhoX3m2 1 hypPt35 = none := by native_decide

end DeepWiki.SymbolicIntegration
