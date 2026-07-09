import DeepWiki.SymbolicIntegration.Engine.Structure
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 9: Structure Theorems
The module of differentials, Rosenlicht's theorem, and the Risch / Rothstein–Caviness structure
theorems — the algebraic-independence results deciding whether a candidate `log(u)` / `exp(u)` is a
*new transcendental monomial* over the field already built. The §9.3 Risch structure decision
(Corollary 9.3.1) is now rendered as a **computable** test over the reachable base `k = ℚ(x)`
(`DeepWiki.SymbolicIntegration.Engine.Structure`): for a logarithmic tower, (9.8)/(9.9) collapse to a
ℚ-linear-dependence test among the logarithmic derivatives `wᵢ = Duᵢ/uᵢ ∈ ℚ(x)`, decided by the §7.1
nullspace solver `cNullspaceBasisQ` (`crref` over ℚ), with the detected relation verified against the
rational-function identity. Validated on `log(x²) = 2 log(x)` (dependent) vs `log(x), log(x+1)`
(independent).

**Computable-vs-abstract.** Each decision below is a computable function over the generic `QFunNZG ℚ`
(= ℚ(x)) / `CPoly ℚ` validated by `native_decide` on the worked relations (checking the detected ℚ-coefficients
`rᵢ` *actually satisfy* `w = Σ rᵢ (Duᵢ/uᵢ)` over ℚ(x) via the cleared difference); the *abstract*
correctness (the structure theorem `Dv = Du/u ↔ …`, Theorem 9.3.1) is **NOT** proved. The full nested
tower (both index sets `E`, `L` over `C(x)(t₁,…,tₙ)` with level-by-level recursion), the §9.1 module of
differentials, §9.2 Rosenlicht, and §9.4 Rothstein–Caviness proof machinery remain deferred.

## NOT YET FORMALIZED (audit 2026-06-24)
§9.1 The Module of Differentials: Def 9.1.1; Thm 9.1.1, Thm 9.1.2; Cor 9.1.1, Cor 9.1.2;
  Lemma 9.1.3. (Mathlib `KaehlerDifferential` is the candidate foundation.)
§9.2 Rosenlicht's Theorem: Thm 9.2.1; Cor 9.2.1, Cor 9.2.2; Lemma 9.2.1, Lemma 9.2.2, Lemma 9.2.3,
  Lemma 9.2.4, Lemma 9.2.5 (the abstract module-of-differentials statement `[research]`). (The
  *operational* transcendental-logarithmic consequence — that `F(log u)` is a Liouville extension of `F`
  whenever `log u ∉ F` — is formalized as `liouville_logExtension`, catalog
  `Sources.Doi_10_1007_b138171.Liouville`, with its full pole-matching/`v`-reduction engine discharged from
  the new-monomial condition; the abstract Rosenlicht differential-form theorem itself stays deferred.)
§9.3 The Risch Structure Theorems: Thm 9.3.1, Thm 9.3.2; Cor 9.3.2; Lemma 9.3.1, Lemma 9.3.2,
  Lemma 9.3.3 (abstract correctness; the decision criterion Corollary 9.3.1(i)/(ii) is now computable +
  native_decide-validated over the reachable base `k = ℚ(x)`, the new-log / new-exp tests for a single
  level of logarithmic monomials over ℚ(x), see `alg_9_3_logIsNewMonomial`/`alg_9_3_expIsNewMonomial`/
  `alg_9_3_logRelationCoeffs`/`ex_9_3_1_log`/`ex_9_3_1_exp`/`ex_9_3_1_multi`). The general nested tower
  (matrix entries in the upper field `C(x)(t₁,…,t_{i-1})`, the level-by-level recursion threading the
  §5.1 result `Dv = Du/u`), the `exp`-of-radical witness (§5.12), and the √−1 / arc-tangent tower of
  Lemmas 9.3.2/9.3.3 are deferred.
§9.4 The Rothstein–Caviness Structure Theorem: Cor 9.4.1 (the *same* decision corollary as 9.3.1,
  eq. 9.21/9.22 ≡ 9.8/9.9, lifted onto log-explicit Liouvillian extensions — the computable test above
  serves it identically; abstract correctness deferred).
Exercises: Ex 9.1, Ex 9.2, Ex 9.3. -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.CPoly

namespace DeepWiki.Si

/-! ## §9.3 The Risch Structure Theorem — the new-monomial decision, computable + validated -/

/-- **The new-logarithm structure decision** (§9.3, Corollary 9.3.1(i), eq. 9.8, book p.284/285): the
computable `cLogIsNewMonomial fuel logDerivs w` over the logarithmic tower `C(x)(log u₁,…,log uₘ)`,
`k = ℚ(x)`, `Const = ℚ`. Given the existing logarithmic derivatives `[Du₁/u₁,…,Duₘ/uₘ] ∈ ℚ(x)` and a
candidate `log(u)`'s `w = Du/u`, returns `true` iff `log(u)` is a **new transcendental monomial** — iff
`Du/u ∉ span_ℚ{Duᵢ/uᵢ}` (no `rᵢ ∈ ℚ` with `Du/u = Σ rᵢ Duᵢ/uᵢ`, eq. 9.8 with `E` empty), decided by the
§7.1 ℚ-nullspace solver `cNullspaceBasisQ`. Computable + `native_decide`-validated; abstract correctness
(Thm 9.3.1) deferred. -/
def alg_9_3_logIsNewMonomial := @cLogIsNewMonomial

/-- **The new-exponential structure decision** (§9.3, Corollary 9.3.1(ii), eq. 9.9, book p.284/285): the
computable `cExpIsNewMonomial fuel logDerivs b` over `k = ℚ(x)`. Given a candidate `exp(b)`'s exponent
derivative `Db ∈ ℚ(x)` and the existing logarithmic derivatives, returns `true` iff `exp(b)` is a **new
transcendental monomial** — iff `Db` is not the logarithmic derivative of a `K`-radical, i.e. (at the
base, `E`-part empty) `Db ∉ span_ℚ{Duᵢ/uᵢ}` — the *same* ℚ-linear-dependence engine as the logarithm
case, applied to `Db`. Computable + `native_decide`-validated; abstract correctness deferred. -/
def alg_9_3_expIsNewMonomial := @cExpIsNewMonomial

/-- **The ℚ-relation coefficients** (§9.3, the explicit `rᵢ ∈ ℚ` of eq. 9.8): the computable
`cLogRelationCoeffs fuel logDerivs w`, returning `some [r₁,…,rₘ]` with `Du/u = Σ rᵢ (Duᵢ/uᵢ)` when a
single relation pins them (the kernel is one-dimensional with nonzero `w`-coordinate), else `none` —
e.g. `[2]` for `log(x²) = 2 log(x)`. Computable + `native_decide`-validated; abstract correctness
deferred. -/
def alg_9_3_logRelationCoeffs := @cLogRelationCoeffs

/-- **Example (§9.3, Corollary 9.3.1(i), book p.284/285)**, the logarithmic-monomial decision: over the
tower `C(x)(log x)` (logarithmic derivative `D(x)/x = 1/x`), `cLogIsNewMonomial` returns `false` for the
candidate `log(x²)` (`w = 2/x ∈ span_ℚ{1/x}`, the relation `log(x²) = 2 log(x)`) with detected
`cLogRelationCoeffs = some [2]` verified to **actually satisfy** `D(x²)/x² = 2·D(x)/x` over ℚ(x), and
`true` for `log(x+1)` (`1/(x+1) ∉ span_ℚ{1/x}`, a new transcendental monomial), `native_decide`. -/
abbrev ex_9_3_1_log := @structureTheorem_example

/-- **Example (§9.3, Corollary 9.3.1(ii), book p.284/285)**, the exponential analogue: over `C(x)(log x)`,
`cExpIsNewMonomial` returns `false` for a candidate `exp(b)` with `Db = 2/x ∈ span_ℚ{1/x}` (so `Db` is
the logarithmic derivative of the radical `x²`, `exp(b)` already in the field), relation `[2]` verified,
and `true` for `Db = 1/(x+1) ∉ span_ℚ{1/x}` (a new transcendental exponential monomial), `native_decide`.
The exponential decision shares the *same* ℚ-linear-dependence engine as the logarithm case. -/
abbrev ex_9_3_1_exp := @expStructureTheorem_example

/-- **Example (§9.3, Corollary 9.3.1, book p.284/285)**, the multi-monomial decision: over the genuine
2-element logarithmic tower `C(x)(log x, log(x+1))` (the ℚ-independent `1/x` and `1/(x+1)`),
`cLogIsNewMonomial` returns `false` for `log(x²+x) = log(x(x+1))` (`(2x+1)/(x²+x) = 1/x + 1/(x+1)`,
relation `[1, 1]` verified) and `true` for each generator relative to the other (the tower is a genuine
transcendence-degree-2 extension), `native_decide` — confirming the ℚ-linear-relation engine scales past
the single-generator base. -/
abbrev ex_9_3_1_multi := @multiStructureTheorem_example

end DeepWiki.Si
