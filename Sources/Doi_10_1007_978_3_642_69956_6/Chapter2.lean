import DeepWiki.RelationalDatabases.RelationalAlgebra
import Sources.Doi_10_1007_978_3_642_69956_6.Source

/-! # Relational Database Model catalog — Chapter 2: Query Systems
Chapter 2 introduces three query systems — the relational algebra (§2.1), the tuple calculus
(§2.2) and SQL (§2.3) — and proves them equivalent in expressive power by mutual reduction
(§2.4–2.6, a generalization of Codd's theorem). The `DeepWiki.RelationalDatabases` library
formalizes the relational-algebra operators at the row level and the first generating-part
reduction (intersection from difference).

## NOT YET FORMALIZED (audit 2026-06-23; subtractive — delete each item once it is formalized)
The query-language reductions are to be built as functional translation `def`s + correctness
lemmas (not operational semantics); they need syntax/semantics layers not yet present.
§2.1: the renaming operator `ρ` of Example 2.4 [infra: an attribute bijection on the subtype
  row representation].
§2.1: the division operator `÷` of Example 2.6 and its generating-part expansion
  `r ÷ s = Π(r;…) − Π((Π(r;…) ⋈ s) − r;…)` [infra].
§2.1.5: generating-part completeness for `DOM(A)`, the comparative instances `[A θ B]`/`[A θ a]`,
  the computable instances `{x₁:A₁;…|f}`, and the selection-as-join expansions
  `σ(r; A θ B) = r ⋈ [A θ B]`, `σ(r; A θ a) = r ⋈ [A θ a]`, `σ(r; f(A₁,…,Aₙ)) = r ⋈ {…|f}`
  [infra: needs the comparative/computable-instance layer].
§2.1.2 / Fig 2.9: the syntax of algebraic expressions [infra: an `AlgExpr` syntax type].
§2.1.4: the scheme-level operators (view schemes `Π(V;Ω₁)`, `ρ(V;f)`, `V ⋈ V'`, `V ∪ V'`,
  `V − V'`) with domain/`SC` bookkeeping [infra].
§2.2: the tuple calculus — syntax (2.2.2), generating part (2.2.3), views (2.2.4), expressive
  power (2.2.5) [infra: a first-order formula syntax + semantics over tuples].
§2.3: SQL — syntax (2.3.2), generating part (2.3.3), views (2.3.4), expressive power (2.3.5)
  [infra: an SQL syntax type].
§2.4: the reduction of the tuple calculus to the relational algebra [research: the translation
  plus safety/domain-independence].
§2.5: the reduction of the relational algebra to SQL [infra].
§2.6: the reduction of SQL to the tuple calculus [infra].
Expressive equivalence of the three systems (Codd's theorem, the chapter's main result) [research].
§2.7: Exercises [deferred: not yet transcribed]. -/

open DeepWiki

namespace DeepWiki.Rdb

/-! ## §2.1 The Relational Algebra -/

/-- **Row restriction `t[Ω₁]`** (§2.1.4, p.28): a row over `Ω` restricted to a subset `Ω₁ ⊆ Ω`. -/
abbrev algebra_restrict := @DeepWiki.Tuple.restrict

/-- **Projection `Π(v; Ω₁)`** (§2.1, Example 2.1, p.20): the rows of `v` restricted to `Ω₁`. -/
abbrev algebra_projection := @DeepWiki.project

/-- **Selection `σ(v; condition)`** (§2.1, Example 2.2, p.21): the rows of `v` satisfying the
condition. -/
abbrev algebra_selection := @DeepWiki.select

/-- **Join `v ⋈ v'`** (§2.1, Example 2.3, p.21): rows over `Ω ∪ Ω'` agreeing on the common
attributes; the cartesian product `v × v'` when `Ω`, `Ω'` are disjoint (Example 2.3). -/
abbrev algebra_join := @DeepWiki.join

/-- **Union `v ∪ v'`** (§2.1, Example 2.5, p.23): set union of tables over equal attributes. -/
abbrev algebra_union := @DeepWiki.union

/-- **Difference `v − v'`** (§2.1, Example 2.5, p.23): set difference of tables over equal
attributes. -/
abbrev algebra_difference := @DeepWiki.diff

/-- **Intersection `v ∩ v'`** (§2.1, Example 2.5, p.23): set intersection of tables over equal
attributes. -/
abbrev algebra_intersection := @DeepWiki.inter

/-- **Intersection from difference** (§2.1.3, p.28; §2.1.5): `r ∩ s = r − (r − s)` — the first
step in showing the generating part (instances, `Π`, `ρ`, `⋈`, `∪`, `−`, computable instances)
expresses the whole algebra. -/
abbrev algebra_inter_from_diff := @DeepWiki.inter_eq_diff_diff

end DeepWiki.Rdb
