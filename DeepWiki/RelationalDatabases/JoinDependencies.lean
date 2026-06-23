import DeepWiki.RelationalDatabases.FunctionalDependencies

/-! # Join dependencies
A join dependency `⋈ᵢ Xᵢ` holds in a row set when any family of rows that pairwise agree on the
component intersections `Xᵢ ∩ Xⱼ` can be glued into a single row of the relation agreeing with
each on its component (Def 3.9) — equivalently, the relation equals the join of its projections
onto the components. Multivalued dependencies are exactly the two-component join dependencies.

The chase decision procedure (Algorithm 3.4), the NP-hardness of jd implication, acyclicity and
the Graham algorithm are layered on later; here we record the satisfaction definition. -/

namespace DeepWiki

universe u v w

variable {Att : Type u} [DecidableEq Att] {Val : Type v} {Ω : Finset Att}

/-- A row set satisfies the *join dependency* with components `comp i` (Def 3.9): for any family
of rows `t` pairwise agreeing on the intersections `comp i ∩ comp j`, there is a row of `r`
agreeing with each `t i` on its component `comp i`. (The components are intended to cover `Ω`.) -/
def SatisfiesJd {ι : Type w} (r : Table Ω Val) (comp : ι → Finset Att) : Prop :=
  ∀ t : ι → Tuple Ω Val, (∀ i, t i ∈ r) →
    (∀ i j, Agree (comp i ∩ comp j) (t i) (t j)) →
    ∃ v ∈ r, ∀ i, Agree (comp i) v (t i)

end DeepWiki
