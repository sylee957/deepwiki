import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalIntegralBasis

/-! # The Mumford divisor representation on a hyperelliptic curve `y² = ρ(x)`

A semi-reduced divisor is encoded by a pair `(u, v)` of base-field polynomials with `u` monic,
`deg v < deg u`, and `u ∣ (v² − ρ)`; the support is the roots of `u` on sheet `v`. Provides the
validity test, the point/identity/opposite/reduced constructors, and the `residueDivisorMumford`
bridge from a residue pole set, validated by `native_decide` over `ℚ[x]`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### The Mumford representation `(u, v)` and its validity -/

/-- Mumford representation of a semi-reduced divisor on `y² = ρ(x)`: the pair `(u, v)` of base-field
polynomials, with support the roots `xᵢ` of `u` on sheet `yᵢ = v(xᵢ)`. -/
structure MumfordDivisor (α : Type*) where
  /-- The monic `u(x)`: its roots are the support `x`-coordinates (with multiplicity). -/
  u : CPolyG α
  /-- The sheet selector `v(x)` with `deg v < deg u`: `yᵢ = v(xᵢ)` picks the sheet at each `xᵢ`. -/
  v : CPolyG α
  deriving Repr, DecidableEq

/-- Mumford validity: `(D.u, D.v)` is a valid semi-reduced divisor on `y² = ρ` — `D.u` monic,
`deg D.v < deg D.u`, and `D.u ∣ (D.v² − ρ)` (the on-curve constraint). -/
def mumfordValid (ρ : CPolyG α) (D : MumfordDivisor α) : Bool :=
  cisMonicG D.u
    && (cdegG D.v < cdegG D.u || cisZeroG D.v)
    && cdvdG D.u (csubG (cmulG D.v D.v) ρ)

/-! ### The divisor of a single affine point, and the identity -/

/-- The identity divisor `mumfordIdentity = (1, 0)` — the zero element of the Jacobian. -/
def mumfordIdentity : MumfordDivisor α := ⟨[CField.one], []⟩

/-- The divisor of an affine point `mumfordPoint x0 y0 = (x − x₀, y₀)`: `u = [−x₀, 1]`, `v = [y₀]`. -/
def mumfordPoint (x0 y0 : α) : MumfordDivisor α := ⟨[CField.neg x0, CField.one], [y0]⟩

/-! ### The opposite (negation) `−D` -/

/-- The opposite `mumfordOpposite D = (u, (−v) mod u)` — the Jacobian inverse: same support,
opposite sheet `yᵢ ↦ −yᵢ`. -/
def mumfordOpposite (D : MumfordDivisor α) : MumfordDivisor α :=
  ⟨D.u, cmodWf (cnegG D.v) D.u⟩

/-! ### Reducedness `deg u ≤ g` -/

/-- Reducedness test `mumfordIsReduced g D`: `deg D.u ≤ g` (the genus). -/
def mumfordIsReduced (g : ℕ) (D : MumfordDivisor α) : Bool := cdegG D.u ≤ g

/-! ### The residue divisor as a Mumford pair

From support points `[(x₁, y₁), …]`: `u = ∏ᵢ (x − xᵢ)` monic, `v` the Lagrange interpolant through
`(xᵢ, yᵢ)`. Bridges a residue pole set to a Mumford divisor. -/

/-- Support polynomial `mumfordSupportPoly xs = ∏ᵢ (x − xᵢ)` (monic) for a support list `xs`. -/
def mumfordSupportPoly (xs : List α) : CPolyG α :=
  xs.foldl (fun acc xi => cmulG acc [CField.neg xi, CField.one]) [CField.one]

/-- The residue divisor as a Mumford pair `residueDivisorMumford pts = (u, v)`: from support points
`pts = [(x₁, y₁), …]`, `u = ∏ᵢ (x − xᵢ)` and `v` the Lagrange interpolant through `(xᵢ, yᵢ)`. -/
def residueDivisorMumford (pts : List (α × α)) : MumfordDivisor α :=
  ⟨mumfordSupportPoly (pts.map Prod.fst), cinterpolateG pts⟩

end CPolyG

/-! ## Validation over `ℚ[x]` (`native_decide`)

The flagship curve is the elliptic `y² = x³ + 1` (genus 1). -/

open CPolyG

/-! ### The elliptic curve `y² = x³ + 1` and three points -/

/-- The radicand `ρ = x³ + 1 ∈ ℚ[x]` (`[1,0,0,1]`): the elliptic curve `y² = x³ + 1` (genus 1). -/
def hypRhoX3p1 : CPolyG ℚ := [1, 0, 0, 1]

/-- The point `(0, 1)` on `y² = x³ + 1` (`1² = 0³ + 1`): Mumford `(x, 1)`. -/
def hypPt01 : MumfordDivisor ℚ := mumfordPoint (0 : ℚ) 1

/-- The point `(2, 3)` on `y² = x³ + 1` (`3² = 9 = 2³ + 1`): Mumford `(x − 2, 3)`. -/
def hypPt23 : MumfordDivisor ℚ := mumfordPoint (2 : ℚ) 3

/-- The point `(−1, 0)` on `y² = x³ + 1` (`0² = (−1)³ + 1 = 0`): a 2-torsion / Weierstrass point (its own
opposite, `y = 0`). Mumford `(x + 1, 0)`. -/
def hypPtM10 : MumfordDivisor ℚ := mumfordPoint (-1 : ℚ) 0

/-! ### The point divisors are valid Mumford pairs (`native_decide`) -/

/-- `(0, 1)` is a valid Mumford divisor on `y² = x³+1`. -/
theorem mumfordValid_pt01 : mumfordValid hypRhoX3p1 hypPt01 = true := by native_decide

/-- `(2, 3)` is a valid Mumford divisor on `y² = x³+1`. -/
theorem mumfordValid_pt23 : mumfordValid hypRhoX3p1 hypPt23 = true := by native_decide

/-- `(−1, 0)` is a valid Mumford divisor on `y² = x³+1` (a 2-torsion / Weierstrass point). -/
theorem mumfordValid_ptM10 : mumfordValid hypRhoX3p1 hypPtM10 = true := by native_decide

/-- A point not on the curve is rejected: `(0, 2)` (with `2² ≠ 0³+1`) gives `mumfordValid = false`. -/
theorem mumfordValid_offCurve_false :
    mumfordValid hypRhoX3p1 (mumfordPoint (0 : ℚ) 2) = false := by native_decide

/-! ### The opposite `−D` and reducedness (`native_decide`) -/

/-- The opposite of `(0, 1)`, computed: should be `(x, −1)` — the point `(0, −1)`. -/
def hypPt01opp : MumfordDivisor ℚ := mumfordOpposite hypPt01

/-- The opposite of `(0, 1)` is `(0, −1)`: `mumfordOpposite (x, 1) = (x, −1)`. -/
theorem mumfordOpposite_pt01_eq :
    hypPt01opp = mumfordPoint (0 : ℚ) (-1) := by native_decide

/-- The opposite `(0, −1)` is also a valid divisor. -/
theorem mumfordValid_pt01opp : mumfordValid hypRhoX3p1 hypPt01opp = true := by native_decide

/-- The point divisors are reduced: `deg u = 1 ≤ g = 1` for the genus-1 curve. -/
theorem mumfordIsReduced_pts :
    mumfordIsReduced (radGenus hypRhoX3p1) hypPt01 = true
    ∧ mumfordIsReduced (radGenus hypRhoX3p1) hypPt23 = true
    ∧ mumfordIsReduced (radGenus hypRhoX3p1) hypPtM10 = true := by native_decide

/-- The identity `(1, 0)`, the reduced form of `D + (−D)` (a point plus its opposite). -/
def hypIdentity : MumfordDivisor ℚ := mumfordIdentity

/-- The identity `(1, 0)` is valid and reduced. -/
theorem mumfordIdentity_valid_reduced :
    mumfordValid hypRhoX3p1 hypIdentity = true
    ∧ mumfordIsReduced (radGenus hypRhoX3p1) hypIdentity = true := by native_decide

/-! ### A two-point divisor on `y² = x³+1` (`native_decide`)

The sum `(0,1) + (2,3)`: `u = x² − 2x`, `v` the line through the two points. -/

/-- The two-point divisor `(0,1) + (2,3)`: support `{0, 2}`, `u = x² − 2x`, `v = x + 1`. -/
def hypSum0123 : MumfordDivisor ℚ := residueDivisorMumford [((0 : ℚ), 1), ((2 : ℚ), 3)]

/-- The interpolant of `(0,1) + (2,3)` is `(x² − 2x, x + 1)`. -/
theorem hypSum0123_eq :
    hypSum0123 = (⟨[0, -2, 1], [1, 1]⟩ : MumfordDivisor ℚ) := by native_decide

/-- The two-point divisor `(0,1) + (2,3)` is valid on `y² = x³+1`. -/
theorem mumfordValid_sum0123 : mumfordValid hypRhoX3p1 hypSum0123 = true := by native_decide

/-! ### The residue divisor from a residue resultant (`native_decide`)

`∫ dx/((x−1)√x)` on `y² = x`: residues `±1` at the pole `x = 1`, giving Mumford divisors
`(x − 1, ±1)`. -/

/-- The radicand `ρ = x ∈ ℚ[x]` (`[0,1]`): the curve `y² = x` of the residue example (`√x`). -/
def hypRhoX : CPolyG ℚ := [0, 1]

/-- The residue divisor of `r = +1` of `∫ dx/((x−1)√x)`: support `{x = 1}`, sheet `y = +1`. -/
def hypResDivP1 : MumfordDivisor ℚ := residueDivisorMumford [((1 : ℚ), 1)]

/-- The residue divisor of the residue `r = −1`: same support `{x = 1}`, the other sheet `y = −1`. -/
def hypResDivM1 : MumfordDivisor ℚ := residueDivisorMumford [((1 : ℚ), -1)]

/-- The `r = +1` residue divisor is `(x − 1, 1)`. -/
theorem hypResDivP1_eq :
    hypResDivP1 = (⟨[-1, 1], [1]⟩ : MumfordDivisor ℚ) := by native_decide

/-- The residue divisor `(x − 1, 1)` is valid on `y² = x`. -/
theorem mumfordValid_resDivP1 : mumfordValid hypRhoX hypResDivP1 = true := by native_decide

/-- The `r = −1` residue divisor `(x − 1, −1)` is valid and is the opposite of the `r = +1` one. -/
theorem mumfordOpposite_resDiv :
    mumfordOpposite hypResDivP1 = hypResDivM1
    ∧ mumfordValid hypRhoX hypResDivM1 = true := by native_decide

/-! ### The end-to-end Mumford-representation milestone (`native_decide`) -/

/-- The Mumford divisor representation and residue-divisor construction, computed and validated:
on `y² = x³+1` the point divisors `(0,1)`, `(2,3)`, `(−1,0)` are valid and reduced, `(0,1)`'s
opposite is `(0,−1)`, and `(0,1)+(2,3) = (x²−2x, x+1)` is valid; on `y² = x` the residue divisor of
`r = +1` is `(x−1, 1)` with opposite `(x−1, −1)`. -/
theorem mumford_representation_validates :
    -- point divisors on the elliptic curve `y² = x³+1`, valid and reduced
    (mumfordValid hypRhoX3p1 hypPt01 = true
      ∧ mumfordValid hypRhoX3p1 hypPt23 = true
      ∧ mumfordValid hypRhoX3p1 hypPtM10 = true)
    ∧ (mumfordIsReduced (radGenus hypRhoX3p1) hypPt01 = true
      ∧ mumfordIsReduced (radGenus hypRhoX3p1) hypPt23 = true)
    -- opposite and identity
    ∧ (hypPt01opp = mumfordPoint (0 : ℚ) (-1)
      ∧ mumfordValid hypRhoX3p1 hypIdentity = true)
    -- two-point divisor (the Cantor-composition output shape)
    ∧ (hypSum0123 = (⟨[0, -2, 1], [1, 1]⟩ : MumfordDivisor ℚ)
      ∧ mumfordValid hypRhoX3p1 hypSum0123 = true)
    -- residue divisor from `ComputableAlgebraicResidues`
    ∧ (hypResDivP1 = (⟨[-1, 1], [1]⟩ : MumfordDivisor ℚ)
      ∧ mumfordValid hypRhoX hypResDivP1 = true
      ∧ mumfordOpposite hypResDivP1 = hypResDivM1) := by native_decide

/-! ## The remaining pieces of the torsion sub-arc

Building on this representation: Cantor composition and reduction (the Jacobian group law on
Mumford pairs), the divisor order (smallest `m` with `m·D` principal) with a good-reduction torsion
bound to make the search terminate, and wiring the resulting `(1/m)·log` term into the integrator's
non-principal branch. -/

end DeepWiki.SymbolicIntegration
