import DeepWiki.RelationalDatabases.NestedRelationalModel
import Sources.Doi_10_1007_978_3_642_69956_6.Source

/-! # Relational Database Model catalog — Chapter 7: The Nested Relational Database Model
Chapter 7 drops the first-normal-form assumption: nested schemes and instances (§7.1), the
nested relational algebra with the nest/unnest operators (§7.2), constraints (§7.3),
expressiveness (§7.4) and hierarchical instances (§7.5). The `DeepWiki.RelationalDatabases`
library provides the recursive nested-value carrier (Def 7.4); the algebra and dependency theory
are layered on it later.

## NOT YET FORMALIZED (audit 2026-06-23; subtractive — delete each item once it is formalized)
The carrier was redesigned (2026-06-23) to assoc-list tuples (`NestedTuple = List (Att × NestedValue
…)`, `rel : List NestedTuple`) so recursion works via `mutual` blocks (`map`/`depth` defined); the
old function-valued tuple field could not be recursed through. The nested algebra and dependencies
are layered on this next.
§7.1: Def 7.1 (the attribute universe `𝒰` with composed attributes), Def 7.2 / 7.3 (primitive
  nested relation scheme and nested relation scheme), Def 7.5 (a nested relation constraint),
  Def 7.6 (a flat relation instance as a special nested one) [infra].
§7.2: Def 7.7 — unnest `μ` and renaming `ρ` are done; the remaining operators (union, difference,
  cartesian product, projection, the nest `ν`, selection) and Def 7.8 (a nested algebra expression)
  and the nest/unnest-not-inverse fact need a `DecidableEq (NestedValue …)` instance for grouping /
  set semantics — `deriving DecidableEq` does NOT apply to the recursive carrier, so a hand-written
  mutual `beq` + correctness (or `decEq`) is required first [infra].
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

/-- **§7.1 carrier**: a nested tuple — an association list of attribute–nested-value pairs. -/
abbrev nested_tuple := @DeepWiki.NestedTuple

/-- **§7.1 carrier**: a nested relation — a list of nested tuples. -/
abbrev nested_rel := @DeepWiki.NestedRel

/-- **§7.1**: functorial map over the atoms of a nested value (recurses into every nesting
level). -/
abbrev nested_value_map := @DeepWiki.NestedValue.map

/-- **§7.1**: the nesting depth of a nested value. -/
abbrev nested_value_depth := @DeepWiki.NestedValue.depth

/-- **§7.1**: functor identity law for `map`. -/
abbrev nested_value_map_id := @DeepWiki.NestedValue.map_id

/-- **§7.1**: functor composition law for `map`. -/
abbrev nested_value_map_map := @DeepWiki.NestedValue.map_map

/-- **§7.1**: `map` preserves nesting depth. -/
abbrev nested_value_depth_map := @DeepWiki.NestedValue.depth_map

/-- **Definition 7.6** (§7.1): a flat (first-normal-form) nested value — nesting depth at most
one. -/
abbrev def_7_6_isFlat := @DeepWiki.NestedValue.isFlat

/-! ## §7.2 The Nested Relational Algebra -/

/-- **Definition 7.7** (§7.2), the *unnest* operator `μ_a`: flatten a nested relation on the
relation-valued attribute `a` (one output row per inner sub-row). -/
abbrev def_7_7_unnest := @DeepWiki.NestedValue.unnest

/-- **Definition 7.7** (§7.2), the *renaming* operator `ρ_{a→b}`: rename a top-level attribute
throughout a nested relation. -/
abbrev def_7_7_rename := @DeepWiki.NestedValue.rename
