import DeepWiki.SymbolicIntegration.RationalIntegrationLiouville
import DeepWiki.SymbolicIntegration.LiouvilleLog
import DeepWiki.SymbolicIntegration.Engine.LiouvilleExpBridge
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Liouville's Theorem (the completeness direction)
**Liouville's theorem** is the structural foundation of the whole integration decision: it constrains
the *shape* an elementary antiderivative can take. Bronstein develops it in two layers — the **rational
case** (§2.4/§2.5, behind `IntegrateRationalFunction`: `∫ f` for `f ∈ K(x)` is always `g + ∑ cᵢ log uᵢ`)
and the **general transcendental theorem** (§5.5, Theorems 5.5.1/5.5.2/5.5.3), itself resting on
Rosenlicht's *Integration in finite terms* (1972, §9.2). This catalog records the **completeness** results
the `DeepWiki.SymbolicIntegration` library now proves — the *converse* companion to the algorithmic
soundness cataloged in `Chapter2`/`Chapter5`: not "the algorithm's output is an antiderivative", but
"*every* integrand of the given class has an antiderivative of the Liouville shape, and a logarithm is
detectable from the residues".

**Two faithfully-proved layers** (axiom-clean `[propext, Classical.choice, Quot.sound]` — no
`native_decide`, no `sorry`):
* **Rational case** (§2.4/§2.5) — *unconditional*. `ratFunc_liouville` constructs the Liouville
  decomposition for *every* `f ∈ K(x)` over an algebraically closed char-`0` field (Hermite + polynomial
  part + Rothstein–Trager log grouping), and `ratFunc_logarithmFree_of_residues_zero` is the affirmative
  logarithm-detection decision (vanishing residues ⟹ rational antiderivative).
* **Transcendental-log case** (§5.5 / Rosenlicht §9.2) — *conditional on the new-monomial condition*.
  `isLiouville_logExtension_uncond` shows a simple transcendental logarithmic extension `F(log u)` is a
  Liouville extension of `F` **whenever `log u ∉ F`** (`NondegenerateLog u`, the Risch new-monomial
  condition — the necessary transcendence hypothesis, NOT removable). It is "unconditional" only in the
  sense that *every other* ingredient — the corrected `v`-reduction, the pole-matching, the simple-pole
  separation — is discharged; the one input is the new-monomial condition itself.

**The enabling Mathlib infrastructure.** The transcendental-log keystone rests on `fracDeriv`: a
derivation on `F[X]` extends to its fraction field by the quotient rule, as a self-`Derivation ℤ K K`
(Mathlib has only the Kähler-module-valued localization, no self-derivation extension). It is built from
scratch in the library and is Mathlib-contributable on its own — recorded here as the load-bearing
derivation-extension lemma.

This catalog does **not** introduce new book numbers beyond the §§ in the docstrings; the corresponding
`## NOT YET FORMALIZED` blocks are updated subtractively in `Chapter2` (§2.4 rational converse residue
gap), `Chapter5` (§5.5 Liouville's Theorem), and `Chapter9` (§9.2 Rosenlicht). -/

open scoped Differential
open DeepWiki.SymbolicIntegration

namespace DeepWiki.Si

/-! ## Liouville's theorem, rational case (§2.4/§2.5) — completeness of `IntegrateRationalFunction` -/

/-- **Liouville's theorem, rational case** (§2.4/§2.5, p.35–55, the constructive completeness behind
`IntegrateRationalFunction`): over an algebraically closed field of characteristic `0`, *every* `f ∈ K(x)`
has a closed Liouville integral `∫ f = g + ∑ᵢ cᵢ·log(uᵢ)` — i.e. `f = g′ + ∑ᵢ cᵢ·logDeriv(uᵢ)` with
`g ∈ K(x)`, `cᵢ ∈ K` constants. `ratFunc_liouville` produces the decomposition (Hermite + polynomial part +
Rothstein–Trager log grouping over the distinct denominator roots), not merely asserts it. The *converse*
companion to the rational-integration soundness capstone (`Chapter2`). -/
abbrev liouville_ratFunc := @ratFunc_liouville

/-- **Liouville's theorem, rational case — list shape** (§2.4/§2.5): the same theorem with the polynomial
part folded into the rational part and the logarithmic part presented as a `List (K × K(x))` of
(constant, argument) pairs — `f = g′ + ∑_(c,u) c·logDeriv(u)`. The clean "rational part + finite list of
logarithms" reading of `∫ f`. -/
abbrev liouville_ratFunc_list := @ratFunc_liouville_list

/-- **Logarithm detection — affirmative decision** (§2.4/§2.5, the algorithmically meaningful half of
Liouville's theorem for `K(x)`): if all the Rothstein–Trager residues vanish, then `∫ f` is
*logarithm-free* — `f = G′` for a rational `G ∈ K(x)`. The vanishing-residues ⟹ rational-antiderivative
direction (the algorithm's complete affirmative logarithm-detection). -/
abbrev liouville_logarithmFree_of_residues := @ratFunc_logarithmFree_of_residues_zero

/-- **Liouville's theorem, rational case — packaged with the residues exposed** (§2.4/§2.5): *every*
`f ∈ K(x)` comes with computed residues plus the flat Liouville form *and* the affirmative decision rule —
vanishing residues ⟹ logarithm-free. The decision content in one statement. (The full converse
`f = G′ ⟹ residues vanish` — that a rational derivative has no simple-pole residue — is the Laurent-
coefficient gap recorded in the `Chapter2` `## NOT YET FORMALIZED` block.) -/
abbrev liouville_ratFunc_with_residues := @ratFunc_liouville_form_with_residues

/-! ## Liouville's theorem, transcendental logarithmic case (§5.5 / Rosenlicht §9.2)

The structural keystone of the transcendental Risch *completeness* direction: that a simple transcendental
logarithmic extension `F(log u)` is a Liouville extension of `F`. Mathlib's differential-Liouville
framework (`IsLiouville F K`, `IsLiouville.trans`, `isLiouville_of_finiteDimensional`) covers the algebraic
case; the transcendental-log instance is exactly what is supplied here. -/

/-- **★ Liouville's theorem, transcendental logarithmic case** (§5.5, Thm 5.5.1/5.5.2/5.5.3; Rosenlicht
1972, §9.2): a simple transcendental logarithmic extension `F(log u) = RatFunc F` (with `t' = u'/u`,
`t = log u`) is a **Liouville extension** of `F` (`IsLiouville F (RatFunc F)`) **whenever the log is a
genuine new monomial** — `NondegenerateLog u`, i.e. `log u ∉ F`, the Risch *new-monomial* condition. This is
the completeness keystone of the transcendental Risch algorithm: every other ingredient (the corrected
`v`-reduction `v′ ∈ F ⟹ v = v₀ + b·t`, the UFD/partial-fraction pole-matching, the simple-pole separation
`v′` has no order-`1` `t`-pole) is discharged; the lone hypothesis is the necessary transcendence
`NondegenerateLog u` (when `u' = 0` the log is a new *constant*, not a new transcendental, and the statement
genuinely fails). -/
abbrev liouville_logExtension := @LiouvilleLog.isLiouville_logExtension_uncond

/-- **The new-monomial condition `NondegenerateLog u`** (§5.5 / §9.2, the Risch new-monomial hypothesis):
`∀ monic irreducible π ∈ F[t], D π ≠ 0` — equivalently `log u ∉ F` (no `s ∈ F` with `s′ = u'/u`). The exact
transcendence input `liouville_logExtension` is conditional on: it is precisely "the log is a genuine new
transcendental monomial over `F`", which the §9.3 Risch structure-theorem decision certifies. The library
proves it forbids an `F`-antiderivative of `u'/u` and forces `logDeriv u ≠ 0`. -/
abbrev liouville_newMonomial_condition := @LiouvilleLog.NondegenerateLog

/-- **★ Liouville's transcendental-log keystone, conditional-residual form** (§5.5 / §9.2): `F(log u)` is
Liouville over `F` given the new-monomial condition `NondegenerateLog u` and the simple-pole separation
residual `DerivSimplePoleSeparation u` (the twisted derivative `v′` has no simple `t`-pole). The residual is
itself a theorem from `NondegenerateLog` (`derivSimplePoleSeparation_of_nondegenerateLog`), which is what
upgrades this to the unconditional-modulo-new-monomial `liouville_logExtension`. -/
abbrev liouville_logExtension_of_separation := @LiouvilleLog.isLiouville_logExtension

/-- **★ Liouville's transcendental-exp keystone** (§5.5 / §9.2): `F(exp u)` is Liouville over `F` given the
new-monomial condition `NondegenerateExp u` (`exp u ∉ F`, i.e. `u' ≠ 0`). The exponential sibling of
`liouville_logExtension`, discharged unconditionally-modulo-new-monomial from the pole-matching over
`expDerivPoly` (the special factor `t = exp u` is a unit, so `logDeriv t = u'` is `F`-valued and folds into
the polynomial part; the genuine pole-matching runs over `π ≠ t`). This is the transcendental-exp
`IsLiouville` instance Mathlib lacked, completing the log+exp Liouville pair. -/
abbrev liouville_expExtension := @LiouvilleExpBridge.isLiouville_expExtension_uncond

/-- **The fraction-field derivation extension `fracDeriv`** (Mathlib-infra, the enabling lemma): a
derivation `d` on `F[X]` extends to a fraction field `K` of `F[X]` by the quotient rule, as a
self-`Derivation ℤ K K`, with `fracDeriv d ∘ algebraMap = algebraMap ∘ d` (`fracDeriv_algebraMap`). This is
the load-bearing piece making `F(log u) = RatFunc F` a genuine differential field extension (Mathlib has
only the Kähler-module-valued localization, not a self-derivation extension) — a standalone
Mathlib-contributable derivation-extension lemma, recorded here as the enabler of the transcendental-log
Liouville keystone. -/
noncomputable abbrev fracField_deriv_extension := @PolynomialFractionDeriv.fracDeriv

end DeepWiki.Si
