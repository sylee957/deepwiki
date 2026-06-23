import DeepWiki.RelationalDatabases.RelationalAlgebra

/-! # Functional dependencies
Functional dependencies `X → Y` over a relation scheme: a row set satisfies `X → Y` when any
two rows agreeing on `X` agree on `Y` (Def 3.5). Armstrong's axioms — triviality, augmentation
and transitivity — are proved sound at the row-set level, together with the derived union and
decomposition rules; a syntactic derivation `Derives` packages the axioms and is shown sound
against semantic implication.

The decision-theoretic heart is the attribute closure characterization: `SC ⊨ X → Y` iff every
attribute of `Y` lies in the fd-closure of `X`, reducing implication to membership. (The
completeness of Armstrong's axioms, the closure *algorithm*, and canonical covers are layered
on later.) -/

namespace DeepWiki

universe u v

variable {Att : Type u} {Val : Type v} {Ω : Finset Att}

/-- Two rows over `Ω` *agree on* an attribute set `X`: they share every value on attributes of
`X` (attributes outside `Ω` are ignored). -/
def Agree (X : Finset Att) (t₁ t₂ : Tuple Ω Val) : Prop :=
  ∀ a : {x // x ∈ Ω}, a.val ∈ X → t₁ a = t₂ a

/-- Agreement is antitone in the attribute set: agreeing on a larger set implies agreeing on a
smaller one. -/
theorem Agree.mono {X Y : Finset Att} {t₁ t₂ : Tuple Ω Val} (h : X ⊆ Y)
    (hag : Agree Y t₁ t₂) : Agree X t₁ t₂ :=
  fun a ha => hag a (h ha)

/-- Agreement on a union splits into agreement on each part. -/
theorem agree_union [DecidableEq Att] {X Y : Finset Att} {t₁ t₂ : Tuple Ω Val} :
    Agree (X ∪ Y) t₁ t₂ ↔ Agree X t₁ t₂ ∧ Agree Y t₁ t₂ := by
  constructor
  · intro h
    exact ⟨fun a ha => h a (Finset.mem_union_left _ ha),
           fun a ha => h a (Finset.mem_union_right _ ha)⟩
  · rintro ⟨hX, hY⟩ a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hX a ha
    · exact hY a ha

/-- A row set `r` *satisfies the functional dependency* `X → Y` (Def 3.5): any two rows of `r`
agreeing on `X` agree on `Y`. -/
def SatisfiesFd (r : Table Ω Val) (X Y : Finset Att) : Prop :=
  ∀ t₁ ∈ r, ∀ t₂ ∈ r, Agree X t₁ t₂ → Agree Y t₁ t₂

variable {r : Table Ω Val} {X Y Z : Finset Att}

/-- Armstrong's axiom F1 (triviality): `X → Y` holds whenever `Y ⊆ X`. -/
theorem satisfiesFd_trivial (h : Y ⊆ X) : SatisfiesFd r X Y :=
  fun _ _ _ _ hag => Agree.mono h hag

/-- Armstrong's axiom F2 (augmentation): `X → Y` gives `X → X ∪ Y`. -/
theorem satisfiesFd_augment [DecidableEq Att] (h : SatisfiesFd r X Y) :
    SatisfiesFd r X (X ∪ Y) := by
  intro t₁ h₁ t₂ h₂ hag
  exact agree_union.mpr ⟨hag, h t₁ h₁ t₂ h₂ hag⟩

/-- Armstrong's axiom F3 (transitivity): `X → Y` and `Y → Z` give `X → Z`. -/
theorem satisfiesFd_trans (hXY : SatisfiesFd r X Y) (hYZ : SatisfiesFd r Y Z) :
    SatisfiesFd r X Z :=
  fun t₁ h₁ t₂ h₂ hag => hYZ t₁ h₁ t₂ h₂ (hXY t₁ h₁ t₂ h₂ hag)

/-- Derived rule F4 (union): `X → Y` and `X → Z` give `X → Y ∪ Z`. -/
theorem satisfiesFd_unionRule [DecidableEq Att] (hXY : SatisfiesFd r X Y)
    (hXZ : SatisfiesFd r X Z) : SatisfiesFd r X (Y ∪ Z) :=
  fun t₁ h₁ t₂ h₂ hag => agree_union.mpr ⟨hXY t₁ h₁ t₂ h₂ hag, hXZ t₁ h₁ t₂ h₂ hag⟩

/-- Derived rule F8 (decomposition/fragmentation): `X → Y ∪ Z` gives `X → Y`. -/
theorem satisfiesFd_decompose [DecidableEq Att] (h : SatisfiesFd r X (Y ∪ Z)) :
    SatisfiesFd r X Y :=
  fun t₁ h₁ t₂ h₂ hag => Agree.mono Finset.subset_union_left (h t₁ h₁ t₂ h₂ hag)

/-- A set of functional dependencies (pairs `(X, Y)` of attribute sets). -/
abbrev FdSet (Att : Type u) : Type u := Set (Finset Att × Finset Att)

/-- `SC` *implies* `X → Y` (Def 3.1 for fds): every row set over `(Ω, Val)` satisfying every
dependency of `SC` also satisfies `X → Y`. -/
def Implies (Ω : Finset Att) (Val : Type v) (SC : FdSet Att) (X Y : Finset Att) : Prop :=
  ∀ r : Table Ω Val, (∀ fd ∈ SC, SatisfiesFd r fd.1 fd.2) → SatisfiesFd r X Y

/-- The *fd-closure* `X̄` of `X` under `SC`: the attributes `A` with `SC ⊨ X → A`. -/
def fdClosure (Ω : Finset Att) (Val : Type v) (SC : FdSet Att) (X : Finset Att) : Set Att :=
  {A | Implies Ω Val SC X {A}}

/-- A syntactic derivation of `X → Y` from `SC` via Armstrong's axioms (base, triviality,
augmentation, transitivity). -/
inductive Derives [DecidableEq Att] (SC : FdSet Att) : Finset Att → Finset Att → Prop where
  /-- A dependency of `SC` is derivable. -/
  | base {X Y : Finset Att} (h : (X, Y) ∈ SC) : Derives SC X Y
  /-- F1: a trivial dependency `Y ⊆ X` is derivable. -/
  | trivial {X Y : Finset Att} (h : Y ⊆ X) : Derives SC X Y
  /-- F2: augmentation. -/
  | augment {X Y : Finset Att} (h : Derives SC X Y) : Derives SC X (X ∪ Y)
  /-- F3: transitivity. -/
  | trans {X Y Z : Finset Att} (hXY : Derives SC X Y) (hYZ : Derives SC Y Z) : Derives SC X Z

/-- Soundness of Armstrong's axioms: every derivable dependency is semantically implied. -/
theorem derives_sound [DecidableEq Att] {SC : FdSet Att} {X Y : Finset Att}
    (h : Derives SC X Y) : Implies Ω Val SC X Y := by
  induction h with
  | base hmem => exact fun r hr => hr _ hmem
  | trivial hsub => exact fun _ _ => satisfiesFd_trivial hsub
  | augment _ ih => exact fun r hr => satisfiesFd_augment (ih r hr)
  | trans _ _ ihXY ihYZ => exact fun r hr => satisfiesFd_trans (ihXY r hr) (ihYZ r hr)

/-- Implication reduces to the fd-closure: `SC ⊨ X → Y` iff every attribute of `Y` lies in the
fd-closure of `X`. This is the characterization underlying the closure decision procedure. -/
theorem implies_iff_subset_fdClosure {SC : FdSet Att} {X Y : Finset Att} :
    Implies Ω Val SC X Y ↔ (↑Y : Set Att) ⊆ fdClosure Ω Val SC X := by
  constructor
  · intro h A hA
    have hAY : ({A} : Finset Att) ⊆ Y := Finset.singleton_subset_iff.mpr (Finset.mem_coe.mp hA)
    exact fun r hr => fun t₁ h₁ t₂ h₂ hag =>
      Agree.mono hAY (h r hr t₁ h₁ t₂ h₂ hag)
  · intro h r hr t₁ h₁ t₂ h₂ hag a ha
    have hmem : a.val ∈ fdClosure Ω Val SC X := h (Finset.mem_coe.mpr ha)
    have hsat : SatisfiesFd r X {a.val} := hmem r hr
    exact hsat t₁ h₁ t₂ h₂ hag a (Finset.mem_singleton_self a.val)

/-- Agreement is symmetric. -/
theorem Agree.symm {X : Finset Att} {t₁ t₂ : Tuple Ω Val} (h : Agree X t₁ t₂) :
    Agree X t₂ t₁ :=
  fun a ha => (h a ha).symm

/-- Syntactic union rule (derived F4): `X → Y` and `X → Z` derive `X → Y ∪ Z`. -/
theorem derives_union [DecidableEq Att] {SC : FdSet Att} {X Y Z : Finset Att}
    (hXY : Derives SC X Y) (hXZ : Derives SC X Z) : Derives SC X (Y ∪ Z) := by
  have h1 : Derives SC X (X ∪ Y) := hXY.augment
  have h2 : Derives SC (X ∪ Y) ((X ∪ Y) ∪ Z) :=
    ((Derives.trivial Finset.subset_union_left).trans hXZ).augment
  exact (h1.trans h2).trans
    (Derives.trivial (by intro a ha; simp only [Finset.mem_union] at *; tauto))

/-- From `X → {b}` for every `b ∈ U`, derive `X → U`. -/
theorem derives_of_forall_singleton [DecidableEq Att] {SC : FdSet Att} {X : Finset Att} :
    ∀ {U : Finset Att}, (∀ b ∈ U, Derives SC X {b}) → Derives SC X U := by
  intro U
  induction U using Finset.induction_on with
  | empty => intro _; exact Derives.trivial (Finset.empty_subset X)
  | @insert a s _ ih =>
    intro h
    rw [Finset.insert_eq]
    exact derives_union (h a (Finset.mem_insert_self a s))
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

/-- Completeness of Armstrong's axioms (Theorem 3.2): over a value type with at least two
elements, every functional dependency over `Ω` semantically implied by `SC` is derivable. The
witness is the two-tuple relation that is constant `v₀` except for value `v₁` off the fd-closure
of `X`. -/
theorem derives_complete [DecidableEq Att] [Nontrivial Val] {SC : FdSet Att} {X Y : Finset Att}
    (hSC : ∀ fd ∈ SC, fd.1 ⊆ Ω ∧ fd.2 ⊆ Ω) (hY : Y ⊆ Ω)
    (h : Implies Ω Val SC X Y) : Derives SC X Y := by
  classical
  obtain ⟨v₀, v₁, hv⟩ := exists_pair_ne Val
  let t₁ : Tuple Ω Val := fun _ => v₀
  let t₂ : Tuple Ω Val := fun a => if Derives SC X {a.val} then v₀ else v₁
  have e1 : ∀ a, t₁ a = v₀ := fun _ => rfl
  have e2pos : ∀ a : {x // x ∈ Ω}, Derives SC X {a.val} → t₂ a = v₀ := fun a hh => if_pos hh
  have e2neg : ∀ a : {x // x ∈ Ω}, ¬ Derives SC X {a.val} → t₂ a = v₁ := fun a hh => if_neg hh
  -- the two rows agree at `a` exactly when `X → {a}` is derivable
  have heq_imp : ∀ a : {x // x ∈ Ω}, t₁ a = t₂ a → Derives SC X {a.val} := by
    intro a hae
    by_contra hcon
    exact hv ((e1 a).symm.trans (hae.trans (e2neg a hcon)))
  have himp_eq : ∀ a : {x // x ∈ Ω}, Derives SC X {a.val} → t₁ a = t₂ a :=
    fun a hd => (e1 a).trans (e2pos a hd).symm
  have hsat : ∀ fd ∈ SC, SatisfiesFd ({t₁, t₂} : Table Ω Val) fd.1 fd.2 := by
    rintro ⟨U, V⟩ hUV s₁ hs₁ s₂ hs₂ hag
    obtain ⟨hU, _⟩ := hSC (U, V) hUV
    have key : Agree U t₁ t₂ → Agree V t₁ t₂ := by
      intro hagU
      have hUcl : ∀ b ∈ U, Derives SC X {b} :=
        fun b hb => heq_imp ⟨b, hU hb⟩ (hagU ⟨b, hU hb⟩ hb)
      have hXV : Derives SC X V :=
        (derives_of_forall_singleton hUcl).trans (Derives.base hUV)
      exact fun a ha =>
        himp_eq a (hXV.trans (Derives.trivial (Finset.singleton_subset_iff.mpr ha)))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs₁ hs₂
    rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl
    · exact fun a _ => rfl
    · exact key hag
    · exact (key hag.symm).symm
    · exact fun a _ => rfl
  have hagX : Agree X t₁ t₂ :=
    fun a ha => himp_eq a (Derives.trivial (Finset.singleton_subset_iff.mpr ha))
  have hagY : Agree Y t₁ t₂ :=
    h {t₁, t₂} hsat t₁ (Set.mem_insert _ _) t₂ (Set.mem_insert_iff.mpr (Or.inr rfl)) hagX
  exact derives_of_forall_singleton (fun b hb => heq_imp ⟨b, hY hb⟩ (hagY ⟨b, hY hb⟩ hb))

/-- Derived rule F5 (intersection): `X → Y` gives `X → Y ∩ Z` (in particular from `X → Y` and
`X → Z`). -/
theorem satisfiesFd_interRule [DecidableEq Att] (hXY : SatisfiesFd r X Y) :
    SatisfiesFd r X (Y ∩ Z) :=
  fun t₁ h₁ t₂ h₂ hag => Agree.mono Finset.inter_subset_left (hXY t₁ h₁ t₂ h₂ hag)

/-- Derived rule F6 (reduction): `X → Y` gives `X → Y − X`. -/
theorem satisfiesFd_reduction [DecidableEq Att] (hXY : SatisfiesFd r X Y) :
    SatisfiesFd r X (Y \ X) :=
  fun t₁ h₁ t₂ h₂ hag => Agree.mono Finset.sdiff_subset (hXY t₁ h₁ t₂ h₂ hag)

/-- Derived rule F7 (generalized augmentation): from `X → Y` with `X ⊆ U` and `V ⊆ X ∪ Y`, the
dependency `U → V`. -/
theorem satisfiesFd_genAugment [DecidableEq Att] {U V : Finset Att} (hXU : X ⊆ U)
    (hV : V ⊆ X ∪ Y) (hXY : SatisfiesFd r X Y) : SatisfiesFd r U V := by
  intro t₁ h₁ t₂ h₂ hag
  have hagX : Agree X t₁ t₂ := Agree.mono hXU hag
  exact Agree.mono hV (agree_union.mpr ⟨hagX, hXY t₁ h₁ t₂ h₂ hagX⟩)

/-- Derived rule F9 (generalized transitivity): from `X → Y` and `U → V` with `U ⊆ X ∪ Y`,
`X ⊆ W` and `Z ⊆ V ∪ W`, the dependency `W → Z`. -/
theorem satisfiesFd_genTrans [DecidableEq Att] {U V W : Finset Att} (hU : U ⊆ X ∪ Y)
    (hX : X ⊆ W) (hZ : Z ⊆ V ∪ W) (hXY : SatisfiesFd r X Y) (hUV : SatisfiesFd r U V) :
    SatisfiesFd r W Z := by
  intro t₁ h₁ t₂ h₂ hag
  have hagX : Agree X t₁ t₂ := Agree.mono hX hag
  have hagY : Agree Y t₁ t₂ := hXY t₁ h₁ t₂ h₂ hagX
  have hagU : Agree U t₁ t₂ := Agree.mono hU (agree_union.mpr ⟨hagX, hagY⟩)
  have hagV : Agree V t₁ t₂ := hUV t₁ h₁ t₂ h₂ hagU
  exact Agree.mono hZ (agree_union.mpr ⟨hagV, hag⟩)

end DeepWiki
