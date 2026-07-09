import DeepWiki.SymbolicIntegration.Engine.Algebraic.HyperellipticDivisor
import DeepWiki.SymbolicIntegration.Engine.Algebraic.CantorComposition
import DeepWiki.SymbolicIntegration.Engine.Algebraic.DivisorOrder
import DeepWiki.SymbolicIntegration.Engine.Algebraic.PrincipalGenerator
import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralTorsionLight
import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralPicardGroupLaw
import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralPicardNonHyperelliptic
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
`native_decide`-validated.

**The general-torsion DECISION now reaches beyond hyperelliptic genus 1** (the `## GENERAL torsion` section
below). Three lightweight `𝔽_p` engines beat the fractional-ideal HNF compilation wall: (i) the
good-reduction **point-count torsion ceiling** `gcd_p N_p = gcd_p |Pic⁰(C)(𝔽_p)|` for an *arbitrary* plane
curve (pure `ZMod p` ring arithmetic), validated on the non-hyperelliptic Fermat cubic (ceiling 3); (ii) the
light **point-list Picard group law** + individual-class order `picOrder`, reading a *specific* class's order
on the GENUS-2 curve `y² = x⁵+1` (= 5, matching Cantor); (iii) the **non-hyperelliptic `L(D)` `𝔽_p`-linear
solve** group law + `picOrderNH`, reading the order on the genuinely non-hyperelliptic Fermat cubic (= 3).
So the "points of finite order" *order/elementarity decision* is now `native_decide`-readable on genus-2 and
non-hyperelliptic curves — what the genus-1 hyperelliptic ceiling could not reach.

What remains (the fully general *principal generator* for those higher cases, a self-contained
non-Mumford reduction, the non-radical *integral basis*, and the integrator wiring) is in the block below.

## NOT YET FORMALIZED (audit 2026-06-26)
Ch. 6 §1 The FULLY GENERAL principal generator `g` with `div(g) = m·D`: for genus `g > 1` (non-constant
  Cantor step `v`, so a non-constant factor `y − v(x)`) and for composition-step gcd cofactors (the
  cancelled `(y − v)` parts of `cantorCompose`, the ideal-quotient bookkeeping) — `principalGenerator`
  recovers `g = y − 1` exactly for the order-3 flex (where the cofactors are trivial), but the general-`v` /
  composition-cofactor product is the next `native_decide` target `[deferred]`. (The individual-class
  *order* on the genus-2 `y² = x⁵+1` is now read by the light point-list `picOrder` — `ch6_general_picOrder`
  below; only the *generator* construction remains in those higher cases.)
Ch. 6 §1 A self-contained non-Mumford point-list reduction: `pdivReduce` reduces by round-tripping through
  the proven Cantor compose/reduce (`ptToMum`/`mumToPts`); a fully self-contained point-list reduction
  (Hermite/CRT interpolation handling repeated points without the Mumford round-trip) is the natural
  follow-up `[deferred]`.
Ch. 5 §3 → integrator: wiring `(c/m, g)` into the non-principal branch — `principalGenerator` returns the
  generator `g`; packaging `(c/m, g)` as an `AlgIntegralResult (CFrac ℚ)` log term (the `cIntegrateAlgebraicWf` branch
  where `radLogArgSolveQ`/`radLogArgSolve` returns `none`) closes the simple-radical log part end-to-end
  `[infra]`.
Ch. 2–4 General algebraic curves (non-radical) — the *integral basis*: the divisor-class *order* for a
  non-hyperelliptic plane curve is now decided (the `L(D)` `𝔽_p`-linear-solve `picOrderNH`, validated on
  the Fermat cubic — `ch6_nonhyp_picOrder` below); what remains is the general algebraic-function-field
  *integral basis* and normal-basis principal test (Chs. 2–4), and the higher-genus `L((g+1)·∞ − D)`
  reduction with a multi-point residual divisor (degree-`g > 1` reduced class), not yet rendered `[infra]`.
Ch. 6 `n ≥ 3` radicals and odd-degree Puiseux: the Cantor/Mumford layer is genus-from-`y² = ρ`; cube and
  higher roots (`n ≥ 3`) and the odd-degree-place Puiseux expansions at infinity are out of scope here
  `[research]`. -/

open DeepWiki.SymbolicIntegration
open DeepWiki.SymbolicIntegration.CPoly

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
DeepWiki.SymbolicIntegration.CPoly`, referenced here as `CPoly.<name>`. -/

/-- **Cantor composition** `CPoly.cantorCompose ρ D₁ D₂` (Trager, Chapter 6 §2-3): the Jacobian
semi-reduced sum of two Mumford divisors — the three-gcd composite `d = gcd(u₁, u₂, v₁ + v₂)`,
`u = u₁u₂/d²`, `v = (s₁u₁v₂ + s₂u₂v₁ + s₃(v₁v₂ + ρ))/d mod u`. The "addition" half of the group law. -/
abbrev ch6_cantor_compose := @CPoly.cantorCompose

/-- **Cantor reduction** `CPoly.cantorReduce ρ g D` (Trager, Chapter 6 §2-3): brings a semi-reduced
`(u, v)` to the unique reduced representative `deg u ≤ g` by iterating `u' = (ρ − v²)/u` monic-normalized,
`v' = (−v) mod u'`. The "reduce to canonical form" half. -/
abbrev ch6_cantor_reduce := @CPoly.cantorReduce

/-- **The Jacobian sum** `CPoly.cantorAdd ρ g D₁ D₂ = cantorReduce (cantorCompose D₁ D₂)` (Trager,
Chapter 6 §2-3): the full group law `D₁ ⊕ D₂` on Mumford divisors (compose then reduce). -/
abbrev ch6_cantor_add := @CPoly.cantorAdd

/-- **The scalar multiple** `CPoly.cantorMul ρ g n D = n·D` (Trager, Chapter 6 §2-3): `n`-fold Jacobian
addition `D ⊕ ⋯ ⊕ D`. The iterate whose first identity hit gives the **order** (points of finite order). -/
abbrev ch6_cantor_mul := @CPoly.cantorMul

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
is elementary. `cantorOrder` lives in `namespace …CPoly`; the rest in `namespace …SymbolicIntegration`. -/

/-- **The divisor order** `CPoly.cantorOrder fuel ρ g D` (Trager, Chapter 6 §2-3, "Points of Finite
Order"): the smallest `m ≥ 1` with `m·D = O` (identity after reduction), found by iterating `cantorMul` —
`some m` if a torsion order `≤ fuel` exists, else `none`. The order whose existence is the torsion test. -/
abbrev ch6_divisor_order := @CPoly.cantorOrder

/-- **Reduction of a divisor mod `p`** `mumfordReduceModP p D` (Trager, Chapter 6 §2-3): pushes a Mumford
divisor over `ℚ` to one over `ZMod p` (coefficient-wise `ℚ → 𝔽_p`), so Cantor runs in the finite Jacobian
`Jac(𝔽_p)` of the reduced curve `y² = ρ mod p`. The good-reduction bridge bounding the order search.
(`instCFieldZMod` supplies the `CField (ZMod p)` the finite-field Cantor arithmetic needs.) -/
abbrev ch6_reduce_mod_p := @mumfordReduceModP

/-- **The torsion decision** `isTorsionDivisor p ρ g D` (Trager, Chapter 6 §2-3, the elementarity
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
`cantorReduceTracked`/`cantorMulTracked` live in `namespace …CPoly`; `principalGenerator` and the
`(0,1)` validations in `namespace …SymbolicIntegration`. -/

/-- **The principal generator** `principalGenerator ρ ρq g m D` (Trager, Chapter 6 §1, the
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

/-! ## GENERAL torsion — beyond hyperelliptic genus 1 (Trager Ch. 6 §2 / good reduction; computational AG)

The elementarity DECISION ("points of finite order") extended past the genus-1 hyperelliptic ceiling, in
**lightweight `𝔽_p` arithmetic** that `native_decide`-compiles where the general fractional-ideal HNF order
hits the compilation wall. Three engines: the good-reduction **point-count torsion ceiling** for an
arbitrary plane curve, the light **point-list Picard group law** reading an individual class's order on a
genus-2 curve, and the **non-hyperelliptic `L(D)` `𝔽_p`-linear solve** group law on the Fermat cubic. -/

/-- **The good-reduction torsion ceiling** `torsionCeiling nps = gcd_p N_p` (Trager, Chapter 6 §2 / Davenport
good reduction): the `ℚ`-torsion order of a divisor class divides `|Pic⁰(C)(𝔽_p)|` at every good prime, hence
divides `gcd_p N_p` over the supplied point counts `N_p = |Pic⁰(C)(𝔽_p)|`. The lightweight ceiling pinning the
torsion order without any ideal arithmetic — pure `ℕ`-gcd over the point counts. -/
abbrev ch6_torsion_ceiling := @torsionCeiling

/-- **`N_p = |Pic⁰(C)(𝔽_p)|` by `𝔽_p`-point counting** `npFermatCubic`/`countAffinePoints` (Trager, Chapter
6 §2): the good-reduction group order of a genus-1 plane curve as the affine `𝔽_p`-grid point count plus the
points at infinity, in pure `ZMod p` ring arithmetic (no field inverse, no `𝔽_p[x]`, no HNF — the lightest
curve computation, the wall the fractional-ideal `genDivisorOrder` mod `p` hits). -/
abbrev ch6_point_count := @npFermatCubic

/-- **★ The non-hyperelliptic Fermat-cubic torsion ceiling is 3** `fermatCubic_torsionCeiling_eq3` (Trager,
Chapter 6 §2, `native_decide`): for the genuinely **non-hyperelliptic** Fermat cubic `x³ + y³ = 1` (NOT a
`y² = ρ(x)` model, so Cantor/Mumford does not apply), `gcd(N₅, N₇, N₁₁, N₁₃) = gcd(6, 9, 12, 9) = 3` pins
the `ℚ`-torsion order to its rational `ℤ/3` (the flex differences) — the torsion-order ceiling decided on a
non-hyperelliptic curve in lightweight `ZMod p` point-count arithmetic. -/
abbrev ch6_general_torsion_ceiling := @fermatCubic_torsionCeiling_eq3

/-- **★★ The lightweight general-torsion ceiling computes and beats the fractional-ideal wall**
`lightweight_general_torsion_validates` (Trager, Chapter 6 §2 / Davenport, `native_decide`): the `𝔽_p`
point-count ceiling `gcd_p N_p` decides the torsion order for an arbitrary plane curve where the fractional-
ideal HNF order cannot compile — `3` on the non-hyperelliptic Fermat cubic `x³ + y³ = 1`, and conservatively
`6`/`1` on the hyperelliptic `y² = x³+1` (torsion `ℤ/6`) / `y² = x³−2` (trivial), reproducing the Cantor
torsion data. The good-reduction *ceiling* — the piece that makes the order search terminate — in pure
`ZMod p` ring arithmetic. -/
abbrev ch6_general_torsion_validates := @lightweight_general_torsion_validates

/-- **The light point-list Picard group law + individual-class order** `picOrder`/`pdivAdd` (Trager, Chapter
6 §2 / computational AG): a reduced divisor class as an `𝔽_p`-point list `RedDiv p`, the group law
`pdivAdd = pdivReduce ∘ pdivCompose` (compose by `++`, reduce by a faithful Cantor compose/reduce
**round-trip** `ptToMum`/`mumToPts` on the point list), and `picOrder` reading a *specific* class's order —
the general analogue of `cantorOrder`, beyond the genus-1 point-count ceiling, in light `𝔽_p[x]` arithmetic
(no `𝔽_p[x]` HNF). -/
abbrev ch6_general_picOrder := @picOrder

/-- **★★ The light point-list group law reads an individual class's order on a GENUS-2 curve, matching
Cantor** `light_picard_group_law_validates` (Trager, Chapter 6 §2, `native_decide`): on `y² = x⁵+1` (genus 2,
where `|Pic⁰| ≠ N_p` and Cantor's Mumford engine was the only prior group law) the light `picOrder` reads the
order of the class `(0,1) − ∞` as **5** and it **equals the Cantor `cantorOrder`** for the same class — the
individual-class order now `native_decide`-readable on a non-genus-1 curve, cross-validated against Cantor
(and, on genus-1 `y² = x³+1`, against the point count `N_p`). -/
abbrev ch6_general_picard_validates := @light_picard_group_law_validates

/-- **The non-hyperelliptic `L(D)` `𝔽_p`-linear-solve group law + order** `picOrderNH`/`nhAdd`/`kernelMat`
(Trager, Chapter 6 §2 / computational Brill–Noether): for a genuinely **non-hyperelliptic** plane curve
`f(x, y) = 0` (no `y² = ρ` involution, so Cantor/Mumford does not apply), the group law is the
`L((g+1)·∞ − D)` Riemann–Roch space solve — a line `h ∈ L(D)` as a nonzero kernel vector of the homogeneous
`ZMod p` matrix (`kernelMat`, a small Gauss–Jordan elimination over `𝔽_p` — the `native_decide`-LIGHT linear
algebra, NOT the `𝔽_p[x]` HNF wall), residual zero via the binary cubic (`pgThird`, chord-and-tangent),
folded into `nhAdd`/`picOrderNH`. The general (non-`y²=ρ`) individual-class-order reader. -/
abbrev ch6_nonhyp_picOrder := @picOrderNH

/-- **★★ The non-hyperelliptic `L(D)`-solve group law reads an individual class's order on the Fermat cubic**
`nonhyperelliptic_picard_group_law_validates` (Trager, Chapter 6 §2, `native_decide`): on the genuinely
non-hyperelliptic Fermat cubic `x³ + y³ = 1` over `𝔽₁₁`/`𝔽₅` (Cantor inapplicable), the `L(D)`-solve
`picOrderNH` reads the order of the flex class `(1,0) − ∞` as **3** (a genuine `ℤ/3`-torsion class) and a
higher class `(2,5) − ∞` as **4**, each dividing the point count `N_p` — the individual-class order on a
curve where the hyperelliptic Cantor round-trip could not reach, via the `𝔽_p`-linear `L(D)` solve. -/
abbrev ch6_nonhyp_picard_validates := @nonhyperelliptic_picard_group_law_validates

end DeepWiki.Tiaf
