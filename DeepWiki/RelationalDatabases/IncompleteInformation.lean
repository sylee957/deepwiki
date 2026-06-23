import DeepWiki.RelationalDatabases.RelationalAlgebra

/-! # Incomplete information: updates on sets of instances
A database with incomplete information denotes a *set of possible instances*. Updates are then
maps on sets of instances (Def 6.4): the general insertion/deletion and integration are the
pairwise union/difference/intersection (combining one instance from each side), while subjection,
negative subjection and augmentation are the plain intersection, difference and union of the two
sets of possibilities.

The null-value representation systems themselves (Codd, V- and C-tables) and the expressiveness
results (Thm 6.1–6.9) require a null-extended carrier and are cataloged separately. -/

namespace DeepWiki

universe u v

variable {Att : Type u} {Val : Type v} {Ω : Finset Att}

/-- The *pairwise union* of two sets of instances: every union of an instance from each side. -/
def pairwiseUnion (X Y : Set (Table Ω Val)) : Set (Table Ω Val) :=
  {s | ∃ r ∈ X, ∃ r' ∈ Y, s = r ∪ r'}

/-- The *pairwise intersection* of two sets of instances. -/
def pairwiseInter (X Y : Set (Table Ω Val)) : Set (Table Ω Val) :=
  {s | ∃ r ∈ X, ∃ r' ∈ Y, s = r ∩ r'}

/-- The *pairwise difference* of two sets of instances. -/
def pairwiseDiff (X Y : Set (Table Ω Val)) : Set (Table Ω Val) :=
  {s | ∃ r ∈ X, ∃ r' ∈ Y, s = r \ r'}

/-- **General insertion** (Def 6.4): insert a (possibly incompletely specified) tuple set into
every possibility — the pairwise union. -/
def generalInsertion (X Y : Set (Table Ω Val)) : Set (Table Ω Val) := pairwiseUnion X Y

/-- **General deletion** (Def 6.4): the pairwise difference. -/
def generalDeletion (X Y : Set (Table Ω Val)) : Set (Table Ω Val) := pairwiseDiff X Y

/-- **Integration** (Def 6.4): combine the knowledge of two databases — the pairwise
intersection. -/
def integration (X Y : Set (Table Ω Val)) : Set (Table Ω Val) := pairwiseInter X Y

/-- **Subjection** (Def 6.4): keep only the possibilities of `X` that are also possibilities of
`Y` — the plain intersection. -/
def subjection (X Y : Set (Table Ω Val)) : Set (Table Ω Val) := X ∩ Y

/-- **Negative subjection** (Def 6.4): discard the possibilities of `X` that lie in `Y` — the
plain difference. -/
def negativeSubjection (X Y : Set (Table Ω Val)) : Set (Table Ω Val) := X \ Y

/-- **Augmentation** (Def 6.4): all possibilities of `X` or of `Y` — the plain union. -/
def augmentation (X Y : Set (Table Ω Val)) : Set (Table Ω Val) := X ∪ Y

/-- Subjection restricts the set of possibilities: the result is contained in `X`. -/
theorem subjection_subset (X Y : Set (Table Ω Val)) : subjection X Y ⊆ X :=
  Set.inter_subset_left

/-- Augmentation enlarges the set of possibilities: `X` is contained in the result. -/
theorem subset_augmentation (X Y : Set (Table Ω Val)) : X ⊆ augmentation X Y :=
  Set.subset_union_left

/-- Augmentation is commutative. -/
theorem augmentation_comm (X Y : Set (Table Ω Val)) : augmentation X Y = augmentation Y X :=
  Set.union_comm X Y

/-- Subjection is commutative. -/
theorem subjection_comm (X Y : Set (Table Ω Val)) : subjection X Y = subjection Y X :=
  Set.inter_comm X Y

/-- General insertion is commutative (pairwise union is symmetric). -/
theorem generalInsertion_comm (X Y : Set (Table Ω Val)) :
    generalInsertion X Y = generalInsertion Y X := by
  ext s
  constructor <;> rintro ⟨r, hr, r', hr', rfl⟩ <;> exact ⟨r', hr', r, hr, Set.union_comm r r'⟩

/-- Integration is commutative (pairwise intersection is symmetric). -/
theorem integration_comm (X Y : Set (Table Ω Val)) : integration X Y = integration Y X := by
  ext s
  constructor <;> rintro ⟨r, hr, r', hr', rfl⟩ <;> exact ⟨r', hr', r, hr, Set.inter_comm r r'⟩

end DeepWiki
