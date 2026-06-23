import DeepWiki.RelationalDatabases.FunctionalDependencies

/-! # Horizontal decompositions and afunctional dependencies
A horizontal decomposition splits a relation into the tuples where a functional dependency holds
and the "exceptions" where it provably fails. The exception side is governed by an *afunctional
dependency* `X ↛ Y` (Def 5.4): every tuple has another tuple agreeing on `X` but differing on
`Y` (every `X`-value carries at least two `Y`-values). The sound mixed inference rules FA1, FA2
(turning a functional dependency and an ad into a new ad) and A1 are proved at the row-set level.

The conflict theory, the Armstrong-relation completeness proof (Thm 5.1/5.2), the membership
algorithm and the inheritance of dependencies under decomposition are layered on later. -/

namespace DeepWiki

universe u v

variable {Att : Type u} {Val : Type v} {Ω : Finset Att}

/-- A set of tuples `s ⊆ rs` is *X-complete* (Def 5.1): tuples of `s` have different `X`-values
from those outside `s`. -/
def IsXComplete (X : Finset Att) (s rs : Table Ω Val) : Prop :=
  s ⊆ rs ∧ ∀ t₁ ∈ s, ∀ t₂ ∈ rs \ s, ¬ Agree X t₁ t₂

/-- A set of tuples is *X-unique* (Def 5.1): all its tuples share one `X`-value. -/
def IsXUnique (X : Finset Att) (s : Table Ω Val) : Prop :=
  ∀ t₁ ∈ s, ∀ t₂ ∈ s, Agree X t₁ t₂

/-- A row set satisfies the *afunctional dependency* `X ↛ Y` (Def 5.4): every tuple has another
tuple agreeing on `X` but differing on `Y` — so every `X`-value carries at least two `Y`-values.
Holds vacuously on the empty instance. -/
def SatisfiesAd (r : Table Ω Val) (X Y : Finset Att) : Prop :=
  ∀ t ∈ r, ∃ t' ∈ r, Agree X t t' ∧ ¬ Agree Y t t'

variable {r : Table Ω Val} {X Y Z V W : Finset Att}

/-- Rule FA1 (Lemma 5.3): a functional dependency `X → Y` and an ad `X ↛ Z` give the ad
`Y ↛ Z`. -/
theorem satisfiesAd_fa1 (hfd : SatisfiesFd r X Y) (had : SatisfiesAd r X Z) :
    SatisfiesAd r Y Z := by
  intro t ht
  obtain ⟨t', ht', hX, hZ⟩ := had t ht
  exact ⟨t', ht', hfd t ht t' ht' hX, hZ⟩

/-- Rule FA2 (Lemma 5.3): a functional dependency `Y → Z` and an ad `X ↛ Z` give the ad
`X ↛ Y`. -/
theorem satisfiesAd_fa2 (hfd : SatisfiesFd r Y Z) (had : SatisfiesAd r X Z) :
    SatisfiesAd r X Y := by
  intro t ht
  obtain ⟨t', ht', hX, hZ⟩ := had t ht
  exact ⟨t', ht', hX, fun hY => hZ (hfd t ht t' ht' hY)⟩

/-- Rule A1 (Lemma 5.3): from the ad `X ∪ V ↛ Y ∪ W` with `W ⊆ V`, the ad `X ↛ Y`. -/
theorem satisfiesAd_a1 [DecidableEq Att] (hW : W ⊆ V)
    (had : SatisfiesAd r (X ∪ V) (Y ∪ W)) : SatisfiesAd r X Y := by
  intro t ht
  obtain ⟨t', ht', hXV, hYW⟩ := had t ht
  refine ⟨t', ht', Agree.mono Finset.subset_union_left hXV, fun hY => hYW ?_⟩
  exact agree_union.mpr ⟨hY, Agree.mono (hW.trans Finset.subset_union_right) hXV⟩

end DeepWiki
