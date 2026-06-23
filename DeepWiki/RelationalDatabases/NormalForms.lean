import DeepWiki.RelationalDatabases.FunctionalDependencies

/-! # Normal forms (functional-dependency based)
Keys and the functional-dependency normal forms. A *superkey* functionally determines every
attribute; a *key* is a minimal superkey; an attribute is *prime* if it lies in some key
(Def 4.1). Third normal form forbids a determined non-prime attribute outside a non-superkey's
right side, Boyce–Codd normal form drops the prime escape hatch (Def 4.2, 4.5). The normal-form
hierarchy `BCNF ⟹ 3NF ⟹ 2NF` is proved.

The decomposition algorithms (Algorithms 4.1–4.3), the NP-completeness results, lossless-join /
constraint-preserving decompositions, and fourth/fifth normal form (which need multivalued- and
join-dependency implication) are layered on later. -/

namespace DeepWiki

universe u v

variable {Att : Type u} {Val : Type v} {Ω : Finset Att}

/-- `X` is a *superkey* (Def 4.1): `SC ⊨ X → Ω`, i.e. `X` functionally determines all
attributes. -/
def IsSuperkey (Ω : Finset Att) (Val : Type v) (SC : FdSet Att) (X : Finset Att) : Prop :=
  Implies Ω Val SC X Ω

/-- `X` is a *key* (Def 4.1): a superkey no proper subset of which is a superkey. -/
def IsKey (Ω : Finset Att) (Val : Type v) (SC : FdSet Att) (X : Finset Att) : Prop :=
  IsSuperkey Ω Val SC X ∧ ∀ Y ⊂ X, ¬ IsSuperkey Ω Val SC Y

/-- `A` is a *prime attribute* (Def 4.1): it belongs to some key. -/
def IsPrime (Ω : Finset Att) (Val : Type v) (SC : FdSet Att) (A : Att) : Prop :=
  ∃ X, IsKey Ω Val SC X ∧ A ∈ X

/-- A relation scheme is in *third normal form* (Def 4.2): for every implied `Y → A` (`A` an
attribute of `Ω`), `A ∈ Y`, or `A` is prime, or `Y` is a superkey. -/
def Is3NF (Ω : Finset Att) (Val : Type v) (SC : FdSet Att) : Prop :=
  ∀ (Y : Finset Att) (A : Att), A ∈ Ω → Implies Ω Val SC Y {A} →
    A ∈ Y ∨ IsPrime Ω Val SC A ∨ IsSuperkey Ω Val SC Y

/-- A relation scheme is in *second normal form* (Def 4.2): for every implied `Y → A` with `Y`
properly inside some key, `A ∈ Y` or `A` is prime (no partial dependencies). -/
def Is2NF (Ω : Finset Att) (Val : Type v) (SC : FdSet Att) : Prop :=
  ∀ (Y : Finset Att) (A : Att), A ∈ Ω → Implies Ω Val SC Y {A} →
    (∃ K, IsKey Ω Val SC K ∧ Y ⊂ K) → A ∈ Y ∨ IsPrime Ω Val SC A

/-- A relation scheme is in *Boyce–Codd normal form* (Def 4.5): for every implied `Y → A` (`A`
an attribute of `Ω`), `A ∈ Y` or `Y` is a superkey. -/
def IsBCNF (Ω : Finset Att) (Val : Type v) (SC : FdSet Att) : Prop :=
  ∀ (Y : Finset Att) (A : Att), A ∈ Ω → Implies Ω Val SC Y {A} →
    A ∈ Y ∨ IsSuperkey Ω Val SC Y

/-- A key has no proper subset that is a superkey. -/
theorem IsKey.not_superkey_of_ssubset {SC : FdSet Att} {K Y : Finset Att}
    (hK : IsKey Ω Val SC K) (h : Y ⊂ K) : ¬ IsSuperkey Ω Val SC Y :=
  hK.2 Y h

/-- Theorem 4.3: a relation scheme in Boyce–Codd normal form is in third normal form. -/
theorem is3NF_of_isBCNF {SC : FdSet Att} (h : IsBCNF Ω Val SC) : Is3NF Ω Val SC := by
  intro Y A hA hYA
  rcases h Y A hA hYA with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (Or.inr h2)

/-- A relation scheme in third normal form is in second normal form: a superkey `Y` cannot sit
properly inside a key, so the superkey escape hatch of 3NF is unavailable under the 2NF
hypothesis. -/
theorem is2NF_of_is3NF {SC : FdSet Att} (h : Is3NF Ω Val SC) : Is2NF Ω Val SC := by
  intro Y A hA hYA hpart
  rcases h Y A hA hYA with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr h2
  · obtain ⟨K, hK, hYK⟩ := hpart
    exact absurd h3 (hK.not_superkey_of_ssubset hYK)

end DeepWiki
