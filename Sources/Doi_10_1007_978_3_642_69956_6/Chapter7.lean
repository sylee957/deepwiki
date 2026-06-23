import DeepWiki.RelationalDatabases.NestedRelationalModel
import Sources.Doi_10_1007_978_3_642_69956_6.Source

/-! # Relational Database Model catalog — Chapter 7: The Nested Relational Database Model
Chapter 7 drops the first-normal-form assumption: nested schemes and instances (§7.1), the
nested relational algebra with the nest/unnest operators (§7.2), constraints (§7.3),
expressiveness (§7.4) and hierarchical instances (§7.5). The `DeepWiki.RelationalDatabases`
library provides the recursive nested-value carrier (Def 7.4); the algebra and dependency theory
are layered on it later.

## NOT YET FORMALIZED (audit 2026-06-23; subtractive — delete each item once it is formalized)
The nested algebra and dependency theory need a richer development of the nested carrier
(scheme-indexed tuples, nest/unnest with grouping, decidable tuple equality).
§7.1: Def 7.1 (the attribute universe `𝒰` with composed attributes), Def 7.2 / 7.3 (primitive
  nested relation scheme and nested relation scheme), Def 7.5 (a nested relation constraint),
  Def 7.6 (a flat relation instance as a special nested one) [infra].
§7.2: Def 7.7 (the nested operators — union, difference, cartesian product, projection, the
  nest `ν` and unnest `μ`, renaming, selection), Def 7.8 (a nested algebra expression), and
  the fact that nest and unnest are not in general mutually inverse [infra].
§7.3: Def 7.9 / 7.10 (functional and multivalued dependencies on nested instances), Theorem 7.1
  (`ν(ω; X)` satisfies the fd `(Ω − X) → X`), and the non-commutativity of nesting (Example
  7.10) [infra].
§7.4: the expressiveness of the nested relational algebra [research].
§7.5: hierarchical instances [research].
§7.6: Exercises [deferred: not yet transcribed]. -/

open DeepWiki

namespace DeepWiki.Rdb

/-! ## §7.1 Nested Relation Schemes and Instances -/

/-- **Definition 7.4** (§7.1, p.182): a *nested value* — atomic, or a nested relation (a list of
tuples mapping attributes to nested values). The recursive carrier of the non-first-normal-form
model. -/
abbrev def_7_4_nested_value := @DeepWiki.NestedValue

/-- **Atomicity test** (§7.1): whether a nested value is atomic rather than a nested relation. -/
abbrev nested_value_isAtom := @DeepWiki.NestedValue.isAtom

end DeepWiki.Rdb
