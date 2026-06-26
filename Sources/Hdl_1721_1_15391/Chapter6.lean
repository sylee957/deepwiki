import DeepWiki.SymbolicIntegration.ComputableHyperellipticDivisor
import Sources.Hdl_1721_1_15391.Source

/-! # Trager catalog — Chapter 5 §3 + Chapter 6 §1: Divisors and Points of Finite Order
After the residue resultant (catalog `Sources.Hdl_1721_1_15391.Chapter5`) yields the candidate log
coefficients, Trager Chapter 5 §3 ("Constructing Divisors", thesis p.59–63) turns each residue into a
**divisor** on the curve, and Chapter 6 ("Principal Divisors and Points of Finite Order", p.64–65) tests
whether some multiple of that divisor is principal — the multiple `m` scaling the candidate coefficient,
giving a `(1/m)·log` term in the genuinely **non-principal** (points-of-finite-order) case the
principal-case linear solve (`ch5_logArgSolve`) defers.

The data structure the Jacobian arithmetic (Cantor's algorithm) runs on is the **Mumford
representation** of a semi-reduced divisor on the hyperelliptic curve `y² = ρ(x)`: a pair `(u, v)` of
base-field polynomials with `u` monic, `deg v < deg u`, and `u ∣ (v² − ρ)`. The
`DeepWiki.SymbolicIntegration` library renders this computationally
(`ComputableHyperellipticDivisor`) — Mathlib has the abstract `ClassGroup` and the elliptic group law
but no general hyperelliptic Cantor/Mumford — validated by `native_decide` on the **elliptic** curve
`y² = x³+1` (genus 1) and on the residue example `∫ dx/((x−1)√x)` (`y² = x`, from Chapter 5 §2).

**Computable-vs-abstract.** The Mumford representation, its validity test, the point/identity/opposite/
reduced constructors, and the residue-divisor construction are computable functions over `K`,
`native_decide`-validated. The abstract correctness (that `mumfordValid` characterizes effective divisor
classes, that `residueDivisorMumford` is the divisor of Trager's residue `rⱼ`) is validated by the
examples, not proved in general.

**The MILESTONE delivered here is the divisor REPRESENTATION + RESIDUE-DIVISOR CONSTRUCTION** (Ch. 5 §3,
the foundation Cantor's algorithm runs on). The remaining Jacobian arithmetic and the principal/torsion
test are deferred (see the block below).

## NOT YET FORMALIZED (audit 2026-06-26)
Ch. 5 §3 Cantor composition `D₁ + D₂`: the Jacobian group law on Mumford pairs (the three-gcd
  `d = gcd(u₁, u₂, v₁ + v₂)` composite `u = u₁u₂/d²`, `v = (s₁u₁v₂ + s₂u₂v₁ + s₃(v₁v₂ + ρ))/d mod u`),
  producing a semi-reduced divisor `[infra]`.
Ch. 5 §3 Cantor reduction: bringing a semi-reduced `(u, v)` to `deg u ≤ g` by the repeated step
  `u' = (ρ − v²)/u` monic-normalized, `v' = (−v) mod u'` `[infra]`.
Ch. 6 §1 The principal-divisor test: deciding whether a degree-0 divisor with no places at infinity is
  principal — a normal basis for the ideal of its multiples-except-at-infinity has an element regular at
  infinity (the Proposition + Corollary + Theorem, p.64–65) `[research]`.
Ch. 6 The order (points of finite order): the smallest `m ≥ 1` with `m·D` principal (= identity after
  reduction), iterating the principal-divisor test on `D, 2D, 3D, …` `[research]`.
Ch. 6 The torsion BOUND via good reduction mod `p`: bounding `m` by `|Jac(𝔽_p)|` (the reduced curve
  `y² = ρ mod p`) so the order search terminates `[research]`.
Ch. 5 §3 → integrator: wiring the order `m` into the non-principal branch
  (`radLogArgSolve`/`radLogArgSolveG` returns `none` ⇒ the candidate coefficient scales by `1/m`,
  the `(1/m)·log` term) `[infra]`. -/

open DeepWiki.SymbolicIntegration
open DeepWiki.SymbolicIntegration.CPolyG

namespace DeepWiki.Tiaf

/-! ## The Mumford representation (Ch. 5 §3 / Ch. 6 §1) -/

/-- **Mumford representation** of a divisor on `y² = ρ(x)` (Trager, Chapter 5 §3, p.59–63):
`MumfordDivisor` is the pair `(u, v)` of base-field polynomials — `u` monic with the support
`x`-coordinates as roots, `v` the sheet selector (`yᵢ = v(xᵢ)`, `deg v < deg u`). The data structure
Cantor's Jacobian arithmetic runs on. -/
abbrev ch6_mumfordDivisor := @MumfordDivisor

/-- **Mumford validity** `mumfordValid ρ (u, v)` (Trager, Chapter 5 §3): `u` monic, `deg v < deg u`, and
`u ∣ (v² − ρ)` — the on-curve constraint `v(xᵢ)² = ρ(xᵢ)` at every root `xᵢ` of `u`. The boolean test for
a valid semi-reduced divisor. -/
abbrev ch6_mumfordValid := @mumfordValid

/-- **The divisor of an affine point** `mumfordPoint x₀ y₀ = (x − x₀, y₀)` (Trager, Chapter 5 §3, the
basic building block: "for each root … a divisor of order one at that place"): the order-one divisor of
`(x₀, y₀)` on the curve. -/
abbrev ch6_mumfordPoint := @mumfordPoint

/-- **The identity divisor** `mumfordIdentity = (1, 0)` (Trager, Chapter 5 §3 / Ch. 6): the zero element
of the Jacobian (empty support). -/
abbrev ch6_mumfordIdentity := @mumfordIdentity

/-- **The opposite (negation)** `mumfordOpposite (u, v) = (u, (−v) mod u)` (Trager, Chapter 5 §3, divisor
inverse): the Jacobian inverse — same support, opposite sheet `yᵢ ↦ −yᵢ` (`y² = ρ` is `y ↦ −y`
symmetric). -/
abbrev ch6_mumfordOpposite := @mumfordOpposite

/-- **Reducedness** `mumfordIsReduced g (u, v)` (Trager, Chapter 5 §3): `deg u ≤ g` — the unique reduced
representative of the divisor's Jacobian class (`g = radGenus ρ`). -/
abbrev ch6_mumfordIsReduced := @mumfordIsReduced

/-- **The residue divisor as a Mumford pair** `residueDivisorMumford pts = (u, v)` (Trager, Chapter 5 §3):
from the support points `(xᵢ, yᵢ)` of a residue `rⱼ` (the `xᵢ` are roots of the residue-resultant
denominator `D` from Chapter 5 §2, the `yᵢ` the sheet values), `u = ∏ᵢ (x − xᵢ)` and `v` = the Lagrange
interpolant through `(xᵢ, yᵢ)`. The bridge from `cAlgResidueResultant`'s pole set to a Mumford divisor
Cantor's algorithm can act on. -/
abbrev ch6_residueDivisorMumford := @residueDivisorMumford

/-! ## Validation on the elliptic curve `y² = x³+1` (Ch. 5 §3 / Ch. 6 §1) -/

/-- **★ Point divisors on the elliptic curve `y² = x³+1` are valid** (Trager, Chapter 5 §3,
`native_decide`): `(0,1)`, `(2,3)`, `(−1,0)` give valid Mumford pairs `(u, v)` (`u` monic, `deg v < deg u`,
`u ∣ (v² − ρ)`). The order-one building blocks of every divisor on the genus-1 curve. -/
abbrev ch6_validates_points :=
  @mumfordValid_pt01

/-- **★ The opposite of `(0,1)` is `(0,−1)`** (Trager, Chapter 5 §3, `native_decide`):
`mumfordOpposite (x, 1) = (x, −1)` — the Jacobian inverse flips the sheet, and the result is again a valid
divisor. -/
abbrev ch6_opposite_eq := @mumfordOpposite_pt01_eq

/-- **★ The two-point divisor `(0,1)+(2,3)` is `(x²−2x, x+1)`, valid** (Trager, Chapter 5 §3,
`native_decide`): the support `{0,2}` with sheets `{1,3}` interpolates to `(u, v) = (x²−2x, x+1)`, a
semi-reduced degree-2 divisor — the shape a Cantor composition outputs, here built straight from
`residueDivisorMumford`. -/
abbrev ch6_twoPoint_valid := @mumfordValid_sum0123

/-- **★ The residue divisor of `∫ dx/((x−1)√x)` is `(x−1, 1)`, valid on `y² = x`** (Trager, Chapter 5 §3,
`native_decide`): the residue `r = +1` (Chapter 5 §2) occurs at the place `(1, 1)`, whose Mumford pair
`(x−1, 1)` is valid (`1² = ρ(1) = 1`); its opposite `(x−1, −1)` is the `r = −1` divisor. The bridge from
the residue resultant `R(Z) = Z⁴ − Z²` to a divisor Cantor's algorithm acts on. -/
abbrev ch6_residueDivisor_valid := @mumfordValid_resDivP1

/-- **★★ THE HYPERELLIPTIC MUMFORD DIVISOR REPRESENTATION + RESIDUE-DIVISOR CONSTRUCTION COMPUTE AND
VALIDATE** (Trager, Chapter 5 §3 / Chapter 6 §1, `native_decide`): the end-to-end milestone — on the
elliptic curve `y² = x³+1` the point/opposite/identity/two-point divisors are valid and reduced, and on
`y² = x` the residue divisor of `∫ dx/((x−1)√x)`'s residue `r = +1` is `(x−1, 1)` with opposite the `r = −1`
divisor. The engine has the Mumford representation, the on-curve validity test, the
point/identity/opposite/reduced constructors, and the `residueDivisorMumford` bridge from
`cAlgResidueResultant`'s pole set — the foundation Cantor's algorithm (composition + reduction → order →
torsion bound) runs on. -/
abbrev ch6_mumford_representation := @mumford_representation_validates

end DeepWiki.Tiaf
