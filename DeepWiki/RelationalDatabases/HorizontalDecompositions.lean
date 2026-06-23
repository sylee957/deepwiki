import DeepWiki.RelationalDatabases.FunctionalDependencies

/-! # Horizontal decompositions and afunctional dependencies
A horizontal decomposition splits a relation into the tuples where a functional dependency holds
and the "exceptions" where it provably fails. The exception side is governed by an *afunctional
dependency* `X ↛ Y` (Def 5.4): every tuple has another tuple agreeing on `X` but differing on
`Y` (every `X`-value carries at least two `Y`-values). The sound mixed inference rules FA1, FA2
(turning a functional dependency and an ad into a new ad) and A1 are proved at the row-set level.

The conflict notion (a constraint set whose only model is empty, with the canonical conflict
`{X → Y, X ↛ Y}`) and Armstrong / strong-Armstrong relations are defined, with strong-Armstrong ⟹
Armstrong on a nonempty instance. The existence proof (Thm 5.1/5.2, a direct-product construction),
the membership algorithm and the inheritance of dependencies under decomposition are layered on
later. -/

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

/-- A relation satisfying both the functional dependency `X → Y` and the afunctional dependency
`X ↛ Y` must be empty: a tuple would need a partner agreeing on `X` (hence on `Y`, by the fd) yet
differing on `Y`. So `{X → Y, X ↛ Y}` is the canonical conflicting set. -/
theorem eq_empty_of_satisfiesFd_satisfiesAd (h : SatisfiesFd r X Y) (had : SatisfiesAd r X Y) :
    r = ∅ := by
  ext t
  simp only [Set.mem_empty_iff_false, iff_false]
  intro ht
  obtain ⟨t', ht', hX, hnY⟩ := had t ht
  exact hnY (h t ht t' ht' hX)

/-- A set of functional dependencies `F` and afunctional dependencies `A` is *in conflict*
(Def 5.6): the empty instance is the only one satisfying all of them. -/
def InConflict (Ω : Finset Att) (Val : Type v) (F A : FdSet Att) : Prop :=
  ∀ r : Table Ω Val, (∀ fd ∈ F, SatisfiesFd r fd.1 fd.2) →
    (∀ ad ∈ A, SatisfiesAd r ad.1 ad.2) → r = ∅

/-- An instance is an *Armstrong relation* for `F` (Def 5.7): the functional dependencies holding
in it are exactly the consequences of `F`. -/
def IsArmstrongRelation (Ω : Finset Att) (Val : Type v) (F : FdSet Att) (r : Table Ω Val) : Prop :=
  ∀ X Y : Finset Att, SatisfiesFd r X Y ↔ Implies Ω Val F X Y

/-- An instance is a *strong Armstrong relation* for `F` (Def 5.8): every consequence fd of `F`
holds, and every non-consequence fd `X → Y` fails maximally — its afunctional dependency `X ↛ Y`
holds. -/
def IsStrongArmstrong (Ω : Finset Att) (Val : Type v) (F : FdSet Att) (r : Table Ω Val) : Prop :=
  (∀ X Y, Implies Ω Val F X Y → SatisfiesFd r X Y) ∧
    (∀ X Y, ¬ Implies Ω Val F X Y → SatisfiesAd r X Y)

/-- A nonempty strong Armstrong relation is an Armstrong relation: a non-consequence fd carries its
afunctional dependency, which (on a nonempty instance) forbids the fd from holding. -/
theorem isArmstrongRelation_of_isStrongArmstrong {F : FdSet Att} (hne : r.Nonempty)
    (h : IsStrongArmstrong Ω Val F r) : IsArmstrongRelation Ω Val F r := by
  refine fun X Y => ⟨fun hfd => ?_, h.1 X Y⟩
  by_contra hni
  exact (Set.nonempty_iff_ne_empty.mp hne)
    (eq_empty_of_satisfiesFd_satisfiesAd hfd (h.2 X Y hni))

end DeepWiki
