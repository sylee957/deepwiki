import DeepWiki.RelationalDatabases.RelationalAlgebra

/-! # Updates and transactions
The update operators on a relation instance: a *deletion* removes the tuples satisfying a
condition, an *insertion* adds them (Def 8.4). Conditions are modelled as predicates on tuples
(the book's elementary conditions `A = a` / `A ≠ a` and their conjunctions are particular cases).
Deletion and insertion distribute over union (Lemma 8.1), and several of the transaction
equivalence rules hold: inserting then deleting the same condition is a deletion (E2), deleting
then inserting is an insertion (E3), and deletions commute (a case of E9).

The modification operator, transactions, the polynomial equivalence-decision algorithm
(Algorithm 8.1), parameterized transactions and the specification results (Thm 8.2/8.3) are
layered on later. -/

namespace DeepWiki

universe u v

variable {Att : Type u} {Val : Type v} {Ω : Finset Att}

/-- A *condition* on tuples (Def 8.1/8.2): a predicate selecting the tuples it applies to. -/
abbrev Condition (Ω : Finset Att) (Val : Type v) : Type _ := Tuple Ω Val → Prop

/-- **Deletion** `Del(C, r)` (Def 8.4): the tuples of `r` not satisfying `C`. -/
def Del (C : Condition Ω Val) (r : Table Ω Val) : Table Ω Val := {t ∈ r | ¬ C t}

/-- **Insertion** `Ins(C, r)` (Def 8.4): `r` together with the tuples satisfying `C`. -/
def Ins (C : Condition Ω Val) (r : Table Ω Val) : Table Ω Val := r ∪ {t | C t}

@[simp] theorem mem_Del (C : Condition Ω Val) (r : Table Ω Val) (t : Tuple Ω Val) :
    t ∈ Del C r ↔ t ∈ r ∧ ¬ C t := Iff.rfl

@[simp] theorem mem_Ins (C : Condition Ω Val) (r : Table Ω Val) (t : Tuple Ω Val) :
    t ∈ Ins C r ↔ t ∈ r ∨ C t := Iff.rfl

/-- Lemma 8.1 (deletion): deletion distributes over union. -/
theorem Del_union (C : Condition Ω Val) (r₁ r₂ : Table Ω Val) :
    Del C (r₁ ∪ r₂) = Del C r₁ ∪ Del C r₂ := by
  ext t; simp only [mem_Del, Set.mem_union]; tauto

/-- Lemma 8.1 (insertion): insertion distributes over union. -/
theorem Ins_union (C : Condition Ω Val) (r₁ r₂ : Table Ω Val) :
    Ins C (r₁ ∪ r₂) = Ins C r₁ ∪ Ins C r₂ := by
  ext t; simp only [mem_Ins, Set.mem_union]; tauto

/-- Rule E2: inserting then deleting the same condition equals deleting. -/
theorem Del_Ins (C : Condition Ω Val) (r : Table Ω Val) : Del C (Ins C r) = Del C r := by
  ext t; simp only [mem_Del, mem_Ins]; tauto

/-- Rule E3: deleting then inserting the same condition equals inserting. -/
theorem Ins_Del (C : Condition Ω Val) (r : Table Ω Val) : Ins C (Del C r) = Ins C r := by
  ext t; simp only [mem_Ins, mem_Del]; tauto

/-- Rule E9 (deletion case): deletions commute. -/
theorem Del_Del_comm (C₁ C₂ : Condition Ω Val) (r : Table Ω Val) :
    Del C₁ (Del C₂ r) = Del C₂ (Del C₁ r) := by
  ext t; simp only [mem_Del]; tauto

/-- Rule E8: insertions commute. -/
theorem Ins_Ins_comm (C₁ C₂ : Condition Ω Val) (r : Table Ω Val) :
    Ins C₁ (Ins C₂ r) = Ins C₂ (Ins C₁ r) := by
  ext t; simp only [mem_Ins]; tauto

/-- Two conditions are *independent* (Def 8.10): no tuple satisfies both. -/
def Independent (C₁ C₂ : Condition Ω Val) : Prop := ∀ t, ¬ (C₁ t ∧ C₂ t)

/-- Rule E11: an insertion and a deletion of independent conditions commute. -/
theorem Ins_Del_comm_of_independent {C₁ C₂ : Condition Ω Val} (h : Independent C₁ C₂)
    (r : Table Ω Val) : Del C₂ (Ins C₁ r) = Ins C₁ (Del C₂ r) := by
  ext t
  simp only [mem_Del, mem_Ins]
  constructor
  · rintro ⟨ht | hC1, hnC2⟩
    · exact Or.inl ⟨ht, hnC2⟩
    · exact Or.inr hC1
  · rintro (⟨ht, hnC2⟩ | hC1)
    · exact ⟨Or.inl ht, hnC2⟩
    · exact ⟨Or.inr hC1, fun hC2 => h t ⟨hC1, hC2⟩⟩

end DeepWiki
