import DeepWiki.SymbolicIntegration.Engine.Algebraic.HyperellipticDivisor
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # Cantor's algorithm: the hyperelliptic-Jacobian group law

The group law on Mumford pairs `(u, v)` for divisors on `y² = ρ(x)`: `cantorCompose` (composition),
`cantorReduce` (reduction to `deg u ≤ g`), `cantorAdd = reduce ∘ compose`, and `cantorMul` (scalar
multiple). Validated by `native_decide` over `ℚ[x]` on the elliptic curve `y² = x³ + 1` and the genus-2
curve `y² = x⁵ + 1`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

variable {α : Type*} [CField α]

/-! ### Cantor composition `(u₁, v₁) ⊕ (u₂, v₂)` -/

/-- Cantor composition `cantorCompose ρ D₁ D₂ = D₁ ⊕ D₂`, the group law on Mumford pairs producing a
semi-reduced divisor. Two extended gcds give cofactors `s₁, s₂, s₃` of `d = gcd(u₁, u₂, v₁ + v₂)`; then
`u = monic(u₁u₂/d²)` and `v = (s₁u₁v₂ + s₂u₂v₁ + s₃(v₁v₂ + ρ))/d mod u`. Generic over `[CField α]`. -/
def cantorCompose (ρ : DensePoly α) (D₁ D₂ : MumfordDivisor α) : MumfordDivisor α :=
  let u₁ := D₁.u; let v₁ := D₁.v
  let u₂ := D₂.u; let v₂ := D₂.v
  -- first extended gcd: d₁ = gcd(u₁,u₂) = e₁·u₁ + e₂·u₂
  let (d₁, e₁, e₂) := CPolyEuclidean.gcdExt u₁ u₂
  -- second extended gcd: d = gcd(d₁, v₁+v₂) = c₁·d₁ + c₂·(v₁+v₂)
  let vsum := cadd v₁ v₂
  let (d, c₁, c₂) := CPolyEuclidean.gcdExt d₁ vsum
  -- cofactors of d over (u₁, u₂, v₁+v₂)
  let s₁ := cmul c₁ e₁
  let s₂ := cmul c₁ e₂
  let s₃ := c₂
  -- u = u₁·u₂/d²  (monic-normalized)
  let d2 := cmul d d
  let u := cmonic (CPolyEuclidean.div (cmul u₁ u₂) d2)
  -- v numerator = s₁·u₁·v₂ + s₂·u₂·v₁ + s₃·(v₁·v₂ + ρ)
  let vnum :=
    cadd (cadd (cmul s₁ (cmul u₁ v₂)) (cmul s₂ (cmul u₂ v₁)))
      (cmul s₃ (cadd (cmul v₁ v₂) ρ))
  -- v = (vnum / d) mod u
  let v := CPolyEuclidean.mod (CPolyEuclidean.div vnum d) u
  ⟨u, v⟩

/-! ### Cantor reduction (to `deg u ≤ g`) -/

/-- One Cantor reduction step `cantorReduceStep ρ (u, v) = (monic((ρ − v²)/u), (−v) mod u)`, lowering
`deg u`. Generic over `[CField α]`. -/
def cantorReduceStep (ρ : DensePoly α) (D : MumfordDivisor α) : MumfordDivisor α :=
  let u := D.u; let v := D.v
  let unew := cmonic (CPolyEuclidean.div (csub ρ (cmul v v)) u)
  let vnew := CPolyEuclidean.mod (cneg v) unew
  ⟨unew, vnew⟩

/-- Cantor reduction driver `cantorReduceAux fuel g ρ (u, v)`: apply `cantorReduceStep` until
`deg u ≤ g`, at most `fuel` times. Generic over `[CField α]`. -/
def cantorReduceAux : ℕ → ℕ → DensePoly α → MumfordDivisor α → MumfordDivisor α
  | 0, _, _, D => D
  | fuel + 1, g, ρ, D =>
    if cdeg D.u ≤ g then D
    else cantorReduceAux fuel g ρ (cantorReduceStep ρ D)

/-- Cantor reduction `cantorReduce ρ g D`: bring a semi-reduced Mumford pair to the unique reduced form
`deg u ≤ g` by repeating `cantorReduceStep`. Generic over `[CField α]`. -/
def cantorReduce (ρ : DensePoly α) (g : ℕ) (D : MumfordDivisor α) : MumfordDivisor α :=
  cantorReduceAux (cdeg D.u + 1) g ρ D

/-! ### The group law `cantorAdd = reduce ∘ compose` -/

/-- The Jacobian group law `cantorAdd ρ g D₁ D₂ = cantorReduce ρ g (cantorCompose ρ D₁ D₂)`: the sum
`D₁ ⊕ D₂` of two reduced divisors on `y² = ρ`, as the unique reduced representative. Generic over
`[CField α]`. -/
def cantorAdd (ρ : DensePoly α) (g : ℕ) (D₁ D₂ : MumfordDivisor α) : MumfordDivisor α :=
  cantorReduce ρ g (cantorCompose ρ D₁ D₂)

/-! ### Normalized equality of Mumford pairs -/

/-- Normalized equality of Mumford pairs `mumfordNormEq D₁ D₂`: `cnorm`-equal on both `u` and `v`, i.e.
equal as polynomials independent of trailing-zero list encoding. Generic over `[CField α]` with
`[DecidableEq α]`. -/
def mumfordNormEq [DecidableEq α] (D₁ D₂ : MumfordDivisor α) : Bool :=
  (cnorm D₁.u == cnorm D₂.u) && (cnorm D₁.v == cnorm D₂.v)

/-! ### The scalar multiple `n·D` (`cantorMul`) -/

/-- The scalar multiple `cantorMul ρ g n D = n·D`, the `n`-fold Cantor sum with `0·D = mumfordIdentity`;
`(n+1)·D = D ⊕ (n·D)`. Generic over `[CField α]`. -/
def cantorMul (ρ : DensePoly α) (g : ℕ) : ℕ → MumfordDivisor α → MumfordDivisor α
  | 0, _ => mumfordIdentity
  | n + 1, D => cantorAdd ρ g D (cantorMul ρ g n D)

end DensePoly

/-! ## Validation over `ℚ[x]`

`α = ℚ`, on the elliptic curve `y² = x³ + 1` (genus 1), whose Jacobian is the elliptic group. -/

open DensePoly

/-! ### The elliptic curve `y² = x³ + 1` and its points -/

/-- The genus of `y² = x³ + 1`: `radGenus = 1` (elliptic). -/
def cantorGenusX3p1 : ℕ := radGenus hypRhoX3p1

/-- `radGenus (x³+1) = 1`: the curve `y² = x³ + 1` is elliptic. -/
theorem cantorGenusX3p1_eq : cantorGenusX3p1 = 1 := by native_decide

/-! ### `(0, 1) ⊕ (2, 3) = (−1, 0)` — chord addition -/

/-- The Cantor sum `(0,1) ⊕ (2,3)` on `y² = x³+1`, via `cantorAdd`; expected `(x+1, 0)`. -/
def cantorSum0123 : MumfordDivisor ℚ := cantorAdd hypRhoX3p1 1 hypPt01 hypPt23

/-- `(0,1) ⊕ (2,3) = (−1,0)` in the elliptic group: `cantorSum0123 = mumfordPoint (−1) 0` as polynomials
(`mumfordNormEq`). -/
theorem cantorSum0123_eq : mumfordNormEq cantorSum0123 (mumfordPoint (-1 : ℚ) 0) = true := by
  native_decide

/-- `(0,1) ⊕ (2,3)` is exactly the raw reduced Mumford pair `⟨[1, 1], []⟩` (`u = x + 1`, `v = 0`). -/
theorem cantorSum0123_raw : cantorSum0123 = (⟨[1, 1], []⟩ : MumfordDivisor ℚ) := by native_decide

/-- The Cantor sum `(0,1) ⊕ (2,3)` is a valid, reduced Mumford divisor (`deg u = 1 ≤ g = 1`). -/
theorem cantorSum0123_valid_reduced :
    mumfordValid hypRhoX3p1 cantorSum0123 = true
    ∧ mumfordIsReduced 1 cantorSum0123 = true := by native_decide

/-! ### `P ⊕ (−P) = O` — the inverse law -/

/-- The Cantor sum `(0,1) ⊕ (0,−1)` of `P = (0,1)` and `−P = mumfordOpposite P`; expected the identity
`(1, 0)`. -/
def cantorSumPoppP : MumfordDivisor ℚ :=
  cantorAdd hypRhoX3p1 1 hypPt01 (mumfordOpposite hypPt01)

/-- `P ⊕ (−P) = O`: `(0,1) ⊕ (0,−1) = mumfordIdentity` — a point and its opposite sum to the identity. -/
theorem cantorSumPoppP_eq : cantorSumPoppP = mumfordIdentity := by native_decide

/-- `P ⊕ (−P)` is valid and reduced: the identity `(1, 0)` is a valid reduced divisor. -/
theorem cantorSumPoppP_valid_reduced :
    mumfordValid hypRhoX3p1 cantorSumPoppP = true
    ∧ mumfordIsReduced 1 cantorSumPoppP = true := by native_decide

/-! ### Doubling `2·(0, 1)` — the tangent-line addition -/

/-- The doubling `2·(0,1) = (0,1) ⊕ (0,1)` on `y² = x³+1`, via `cantorAdd`; `(0,1)` is an inflection
point (3-torsion), so `2·(0,1) = (0, −1)`. -/
def cantorDouble01 : MumfordDivisor ℚ := cantorAdd hypRhoX3p1 1 hypPt01 hypPt01

/-- The doubling `2·(0,1)` is valid and reduced (`deg u ≤ g = 1`). -/
theorem cantorDouble01_valid_reduced :
    mumfordValid hypRhoX3p1 cantorDouble01 = true
    ∧ mumfordIsReduced 1 cantorDouble01 = true := by native_decide

/-- `2·(0,1) = (0, −1) = −(0,1)`: `(0,1)` is an inflection point, so its double is its own opposite. -/
theorem cantorDouble01_eq : cantorDouble01 = mumfordPoint (0 : ℚ) (-1) := by native_decide

/-! ### `(0,1)` is 3-torsion: `3·(0,1) = O` via `cantorMul` -/

/-- `(0,1)` is a 3-torsion point: `cantorMul 3 (0,1) = mumfordIdentity` while `2·(0,1)` and `1·(0,1)`
are not, so its order in the Jacobian is `3`. -/
theorem cantorMul_pt01_order3 :
    cantorMul hypRhoX3p1 1 3 hypPt01 = mumfordIdentity
    ∧ cantorMul hypRhoX3p1 1 2 hypPt01 ≠ mumfordIdentity
    ∧ cantorMul hypRhoX3p1 1 1 hypPt01 = hypPt01 := by native_decide

/-! ## The genus-2 stretch: `y² = x⁵ + 1`

A genuinely hyperelliptic example (`g = 2`), beyond the elliptic case. -/

/-- The radicand `ρ = x⁵ + 1 ∈ ℚ[x]`: the genus-2 hyperelliptic curve `y² = x⁵ + 1`. -/
def hypRhoX5p1 : DensePoly ℚ := [1, 0, 0, 0, 0, 1]

/-- `radGenus (x⁵+1) = 2`: `y² = x⁵ + 1` is a genus-2 hyperelliptic curve. -/
theorem cantorGenusX5p1_eq : radGenus hypRhoX5p1 = 2 := by native_decide

/-- The point `(0, 1)` on `y² = x⁵ + 1` (`1² = 0⁵ + 1`): Mumford `(x, 1)`. -/
def hypG2Pt01 : MumfordDivisor ℚ := mumfordPoint (0 : ℚ) 1

/-- The point `(−1, 0)` on `y² = x⁵ + 1`: a Weierstrass point, Mumford `(x + 1, 0)`. -/
def hypG2PtM10 : MumfordDivisor ℚ := mumfordPoint (-1 : ℚ) 0

/-- The genus-2 points `(0,1)` and `(−1,0)` on `y² = x⁵ + 1` are valid reduced Mumford divisors. -/
theorem hypG2_pts_valid :
    mumfordValid hypRhoX5p1 hypG2Pt01 = true
    ∧ mumfordValid hypRhoX5p1 hypG2PtM10 = true
    ∧ mumfordIsReduced 2 hypG2Pt01 = true
    ∧ mumfordIsReduced 2 hypG2PtM10 = true := by native_decide

/-- The genus-2 Cantor sum `(0,1) ⊕ (−1,0)` on `y² = x⁵ + 1`, a degree-2 divisor `u = x(x+1)`, already
reduced (`deg u = 2 ≤ g = 2`). -/
def cantorG2Sum : MumfordDivisor ℚ := cantorAdd hypRhoX5p1 2 hypG2Pt01 hypG2PtM10

/-- The genus-2 Cantor composition `(0,1) ⊕ (−1,0)` on `y² = x⁵ + 1` is valid and reduced
(`deg u ≤ 2`). -/
theorem cantorG2Sum_valid_reduced :
    mumfordValid hypRhoX5p1 cantorG2Sum = true
    ∧ mumfordIsReduced 2 cantorG2Sum = true := by native_decide

/-- The genus-2 sum `(0,1) ⊕ (−1,0)` has `u = x² + x` (support `{0, −1}`), a genus-2 reduced divisor of
degree `2`. -/
theorem cantorG2Sum_u :
    cantorG2Sum.u = ([0, 1, 1] : DensePoly ℚ) := by native_decide

/-! ## The Cantor-group-law milestone -/

/-- The hyperelliptic Jacobian group law validates: on `y² = x³ + 1`, chord addition
`(0,1) ⊕ (2,3) = (−1,0)`, the inverse law `P ⊕ (−P) = O`, doubling `2·(0,1) = (0,−1)`, and the order-3
torsion `3·(0,1) = O`; on the genus-2 curve `y² = x⁵ + 1`, `(0,1) ⊕ (−1,0)` composes to a valid reduced
degree-2 divisor `u = x² + x`. -/
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
    ∧ (cantorMul hypRhoX3p1 1 3 hypPt01 = mumfordIdentity
      ∧ cantorMul hypRhoX3p1 1 2 hypPt01 ≠ mumfordIdentity)
    -- genus-2 composition on y² = x⁵+1
    ∧ (mumfordValid hypRhoX5p1 cantorG2Sum = true
      ∧ mumfordIsReduced 2 cantorG2Sum = true
      ∧ cantorG2Sum.u = ([0, 1, 1] : DensePoly ℚ)) := by native_decide

/-! ### `#print axioms` for the Cantor group-law validations -/

#print axioms cantor_group_law_validates
#print axioms cantorSum0123_eq
#print axioms cantorMul_pt01_order3

end DeepWiki.SymbolicIntegration
