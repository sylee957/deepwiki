import DeepWiki.SymbolicIntegration.ComputableHyperellipticDivisor
import DeepWiki.SymbolicIntegration.ComputableCantorComposition
import DeepWiki.SymbolicIntegration.ComputableDivisorOrder
import DeepWiki.SymbolicIntegration.ComputablePrincipalGenerator
import Sources.Hdl_1721_1_15391.Source

/-! # Trager catalog — Chapter 5 §3 + Chapter 6: Divisors and Points of Finite Order
After the residue resultant (catalog `Sources.Hdl_1721_1_15391.Chapter5`) yields the candidate log
coefficients, Trager Chapter 5 §3 ("Constructing Divisors", thesis p.59–63) turns each residue into a
**divisor** on the curve, and Chapter 6 ("Principal Divisors and Points of Finite Order", p.64–65) tests
whether some multiple of that divisor is principal — the multiple `m` scaling the candidate coefficient,
giving a `(1/m)·log` term in the genuinely **non-principal** (points-of-finite-order) case the
principal-case linear solve (`ch5_logArgSolve`) defers.

**The torsion sub-arc (Ch. 6) is delivered for the order-3 flex.** Three library files render Cantor's
Jacobian group law on Mumford pairs and the resulting elementarity decision computationally,
`native_decide`-validated: `ComputableCantorComposition` (the group law `cantorCompose`/`cantorReduce`/
`cantorAdd`/`cantorMul`), `ComputableDivisorOrder` (the DECISION — `cantorOrder` + the good-reduction
torsion test `isTorsionDivisor`/`elementarityViaTorsion` over `Jac(𝔽_p)`), and `ComputablePrincipalGenerator`
(the CONSTRUCTION — `principalGenerator` recovering `g` with `div(g) = m·D`, the `(1/m)·log g` argument).
On `y² = x³+1` the flex `(0,1)` is decided 3-torsion ⟹ elementary with generator `g = y − 1`; on the
rank-1 `y² = x³−2` the point `(3,5)` is decided **non-torsion** (orders `2,7,12` mod `5,7,11`, `gcd = 1`)
⟹ the integral is **not elementary**.

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

**The MILESTONE is the divisor REPRESENTATION + RESIDUE-DIVISOR CONSTRUCTION** (Ch. 5 §3) **plus the full
torsion sub-arc for the order-3 flex** (Ch. 6): the Jacobian group law, the elementarity DECISION (order +
good-reduction torsion test, both answers), and the principal-generator CONSTRUCTION `g = y − 1` are now
`native_decide`-validated. What remains (the fully general generator, the higher-genus/non-radical cases,
and the integrator wiring) is in the block below.

## NOT YET FORMALIZED (audit 2026-06-26)
Ch. 6 §1 The FULLY GENERAL principal generator: for genus `g > 1` (non-constant Cantor step `v`, so a
  non-constant factor `y − v(x)`) and for composition-step gcd cofactors (the cancelled `(y − v)` parts of
  `cantorCompose`, the ideal-quotient bookkeeping) — `principalGenerator` recovers `g = y − 1` exactly for
  the order-3 flex (where the cofactors are trivial), but the general-`v` / composition-cofactor product is
  the next `native_decide` target (the genus-2 `y² = x⁵+1` examples) `[deferred]`.
Ch. 5 §3 → integrator: wiring `(c/m, g)` into the non-principal branch — `principalGenerator` returns the
  generator `g`; packaging `(c/m, g)` as an `AlgIntegralResult` log term (the `cIntegrateAlgebraic` branch
  where `radLogArgSolve`/`radLogArgSolveG` returns `none`) closes the simple-radical log part end-to-end
  `[infra]`.
Ch. 2–4 General algebraic curves (non-radical): the divisor/torsion machinery here is on simple radicals
  `y² = ρ(x)` (hyperelliptic); the general algebraic-function-field integral basis and normal-basis
  principal test (Chs. 2–4) are not yet rendered `[infra]`.
Ch. 6 `n ≥ 3` radicals and odd-degree Puiseux: the Cantor/Mumford layer is genus-from-`y² = ρ`; cube and
  higher roots (`n ≥ 3`) and the odd-degree-place Puiseux expansions at infinity are out of scope here
  `[research]`. -/

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

/-! ## Cantor's Jacobian group law (`ComputableCantorComposition`, Trager Ch. 6 §2-3)

The hyperelliptic group law on Mumford pairs `(u, v)`. `cantor*` live in `namespace
DeepWiki.SymbolicIntegration.CPolyG`, referenced here as `CPolyG.<name>`. -/

/-- **Cantor composition** `CPolyG.cantorCompose ρ D₁ D₂` (Trager, Chapter 6 §2-3): the Jacobian
semi-reduced sum of two Mumford divisors — the three-gcd composite `d = gcd(u₁, u₂, v₁ + v₂)`,
`u = u₁u₂/d²`, `v = (s₁u₁v₂ + s₂u₂v₁ + s₃(v₁v₂ + ρ))/d mod u`. The "addition" half of the group law. -/
abbrev ch6_cantor_compose := @CPolyG.cantorCompose

/-- **Cantor reduction** `CPolyG.cantorReduce ρ g D` (Trager, Chapter 6 §2-3): brings a semi-reduced
`(u, v)` to the unique reduced representative `deg u ≤ g` by iterating `u' = (ρ − v²)/u` monic-normalized,
`v' = (−v) mod u'`. The "reduce to canonical form" half. -/
abbrev ch6_cantor_reduce := @CPolyG.cantorReduce

/-- **The Jacobian sum** `CPolyG.cantorAdd ρ g D₁ D₂ = cantorReduce (cantorCompose D₁ D₂)` (Trager,
Chapter 6 §2-3): the full group law `D₁ ⊕ D₂` on Mumford divisors (compose then reduce). -/
abbrev ch6_cantor_add := @CPolyG.cantorAdd

/-- **The scalar multiple** `CPolyG.cantorMul ρ g n D = n·D` (Trager, Chapter 6 §2-3): `n`-fold Jacobian
addition `D ⊕ ⋯ ⊕ D`. The iterate whose first identity hit gives the **order** (points of finite order). -/
abbrev ch6_cantor_mul := @CPolyG.cantorMul

/-- **★★ The hyperelliptic Jacobian group law (Cantor's algorithm) computes and validates** (Trager,
Chapter 6 §2-3, `native_decide`): on `y² = x³+1` the chord law `(0,1) ⊕ (2,3) = (−1,0)`, the inverse law
`P ⊕ (−P) = O`, and doubling `2·(0,1) = (0,−1)` all land in valid reduced divisors; on the genus-2
`y² = x⁵+1` (beyond Mathlib's elliptic group law) `(0,1) ⊕ (−1,0)` composes to a valid reduced degree-2
divisor. The engine computes the hyperelliptic group law Trager's torsion test runs on. -/
abbrev ch6_cantor_group_law := @cantor_group_law_validates

/-- **★ `(0,1)` is a 3-torsion point: `3·(0,1) = O`** (Trager, Chapter 6, `native_decide`):
`cantorMul 3 (0,1) = mumfordIdentity` while `2·(0,1) ≠ O` and `1·(0,1) = (0,1)` — the order of the
inflection point of `y² = x³+1` is 3. The order / point-of-finite-order computation, run by `cantorMul`. -/
abbrev ch6_cantor_order3 := @cantorMul_pt01_order3

/-! ## The elementarity DECISION (`ComputableDivisorOrder`, Trager Ch. 6 §2-3)

The order of a divisor and the good-reduction torsion test — deciding whether the simple-radical integral
is elementary. `cantorOrder` lives in `namespace …CPolyG`; the rest in `namespace …SymbolicIntegration`. -/

/-- **The divisor order** `CPolyG.cantorOrder fuel cfuel ρ g D` (Trager, Chapter 6 §2-3, "Points of Finite
Order"): the smallest `m ≥ 1` with `m·D = O` (identity after reduction), found by iterating `cantorMul` —
`some m` if a torsion order `≤ fuel` exists, else `none`. The order whose existence is the torsion test. -/
abbrev ch6_divisor_order := @CPolyG.cantorOrder

/-- **Reduction of a divisor mod `p`** `mumfordReduceModP p D` (Trager, Chapter 6 §2-3): pushes a Mumford
divisor over `ℚ` to one over `ZMod p` (coefficient-wise `ℚ → 𝔽_p`), so Cantor runs in the finite Jacobian
`Jac(𝔽_p)` of the reduced curve `y² = ρ mod p`. The good-reduction bridge bounding the order search.
(`instCFieldZMod` supplies the `CField (ZMod p)` the finite-field Cantor arithmetic needs.) -/
abbrev ch6_reduce_mod_p := @mumfordReduceModP

/-- **The torsion decision** `isTorsionDivisor p cfuel ρ g D` (Trager, Chapter 6 §2-3, the elementarity
test): `some m` iff `D` is `m`-torsion — the order mod `p` (good reduction) caps the ℚ-search, so the
decision TERMINATES (`none` ⟹ infinite order). The smallest-multiple-is-principal test, made decidable by
the good-reduction bound `m ∣ |Jac(𝔽_p)|`. (`elementarityViaTorsion` is its Boolean face: `true` ⟹ the
simple-radical integral is elementary with a `(1/m)·log` term, `false` ⟹ not elementary.) -/
abbrev ch6_torsion_decision := @isTorsionDivisor

/-- **★★ The reduction-mod-`p` NON-TORSION certificate for `(3,5)` on `y² = x³−2`** (Trager, Chapter 6 §2,
`native_decide`): the orders of `(3,5)` mod `5, 7, 11` are the DISTINCT `2, 7, 12` (`gcd = 1`), so any
torsion order `m` would divide each, forcing `m = 1` (`(3,5) = O`, false) — `(3,5)` is **non-torsion**.
With the good-reduction ceiling, `isTorsionDivisor` then decides `none` ⟹ the integral over `y² = x³−2` is
**NOT elementary**. The negative answer of the famous "points of finite order" decision, with a
terminating certificate. -/
abbrev ch6_nontorsion_witness := @cantorOrder_pt35_modp

/-- **★★ The divisor order + good-reduction torsion decision compute and validate** (Trager, Chapter 6
§2-3, `native_decide`): on `y² = x³+1` the orders of `(0,1)`/`(−1,0)`/`O` are `3`/`2`/`1`, torsion is
preserved mod `5, 7`, and `(0,1)` decides torsion of order 3 ⟹ **elementary** with a `(1/3)·log` term; on
the rank-1 `y² = x³−2` the point `(3,5)` decides **non-torsion** (orders `2,7,12` mod `5,7,11`) ⟹ **NOT
elementary**. Trager's elementarity decision via Cantor + good reduction, both answers, with terminating
certificates. -/
abbrev ch6_divisor_order_decision := @divisor_order_torsion_decision_validates

/-! ## The principal-generator CONSTRUCTION (`ComputablePrincipalGenerator`, Trager Ch. 6 §1)

For a torsion divisor `D` of order `m`, the function `g` with `div(g) = m·D` (the `(1/m)·log g` argument).
`cantorReduceTracked`/`cantorMulTracked` live in `namespace …CPolyG`; `principalGenerator` and the
`(0,1)` validations in `namespace …SymbolicIntegration`. -/

/-- **The principal generator** `principalGenerator fuel ρ ρq g m D` (Trager, Chapter 6 §1, the
constructive half): for a torsion divisor `D` of order `m` on `y² = ρ`, recover the function `g` with
`div(g) = m·D` — so the log term is `(1/m)·log g`. Runs `cantorMulTracked` (`= cantorMul` instrumented to
emit the `y − v` reduction step-functions) and multiplies the tracked factors into a `RadElem` over the
radical extension. The `g` the principal-case linear solve cannot supply for points of finite order. -/
abbrev ch6_principal_generator := @principalGenerator

/-- **★★ The principal generator of `3·(0,1)` on `y² = x³+1` is `g = y − 1`** (Trager, Chapter 6 §1,
`native_decide`): `principalGenerator … (0,1) 3` recovers the flex tangent line `y = 1` (`= [−1, 1]`), so
`div(y − 1) = 3·(0,1) − 3·∞ = 3·D` and the algebraic integral's log term is `(1/3)·log(y − 1)`. The engine
recovers the torsion log argument. -/
abbrev ch6_generator_pt01 := @principalGenerator_pt01_eq

/-- **★ The `(1/3)·log(y − 1)` differential passes the log-derivative certificate** (Trager, Chapter 6 §1,
`native_decide`): with `g = y − 1` and `ι = (1/3)·g'/g`, the cleared certificate `radDeriv g =
radMul g (3·ι)` holds (`3·ι = g'/g`, i.e. `g' = g·(g'/g)`) — confirming `(1/3)·log(y − 1)` is the torsion
log term of the `(0,1)` residue divisor. The logarithmic-derivative check on the recovered generator. -/
abbrev ch6_generator_logderiv := @principalGenerator_pt01_logderiv

/-- **★★ The principal generator of a torsion divisor computes and validates** (Trager, Chapter 6 §1,
`native_decide`): for the order-3 flex `D = (0,1)` on `y² = x³+1`, `principalGenerator` recovers `g = y − 1`
with `div(g) = 3·D`, the order is `3` (the decision feeding the construction), and the `(1/3)·log(y − 1)`
differential passes the log-derivative certificate. The engine now both DECIDES torsion and CONSTRUCTS the
`(1/m)·log g` argument — the two halves of Trager's "points of finite order", completing the
algebraic-integration decision procedure for simple radicals on this example. -/
abbrev ch6_principal_generator_validates := @principal_generator_validates

end DeepWiki.Tiaf
