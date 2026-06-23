import DeepWiki.NetworkCalculus.TableauSchema
import DeepWiki.NetworkCalculus.BooleanConstraints

/-!
# Tableau consistency clauses and the assignment- and config-readback bridge

Layer 3b-i of a Cook- and Levin-style formalization: the **consistency clause family** of the
computation tableau together with the **assignment ↔ configuration sequence** bridge.

* `consistencyClauses tm T S` — for each slot (one fact at one position) the `exactlyOne`
  constraint forcing precisely one of its variables true; `Consistent assign` is its
  satisfaction, characterized by `consistent_iff`.
* `readLabel`/`readState`/`readCell` — the per-slot read of a Boolean assignment back into a
  configuration fact (total, via `Classical.choose`); under `Consistent` they invert the
  variable exactly (`readLabel_eq`, `readState_eq`, `readCell_eq`).
* `encodeSeq cfgs` — the assignment that sets each variable to the truth of its fact about a
  configuration sequence; its per-coordinate evaluation is `encodeSeq_labelCoord` etc.
* Round-trip: `encodeSeq_consistent`, `readLabel_encodeSeq`, `readState_encodeSeq`,
  `readCell_encodeSeq` — encoding a real configuration sequence is consistent and is read back
  to the original facts.

## Deferred

Only consistency, per-slot readback, encode, and the per-slot round-trip live here. Assembling
the per-cell readback over the position axis `i` into a `List` (the reconstructed stack), and the
init/accept/transition clause families plus reduction correctness, are **later** chunks.
-/

open Turing

namespace DeepWiki

namespace TableauSchema

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

open BooleanConstraints

variable {tm : FinTM2} {T S : ℕ} [∀ k, Fintype (tm.Γ k)]

/-! ## (1) Consistency clauses -/

variable (tm T S) in
/-- The **consistency clauses**: for every slot (a single fact at a single position) the
`exactlyOne` constraint forcing precisely one of its variables true. Label and state slots are
collected over the time axis; cell slots over time, stack, and position. -/
noncomputable def consistencyClauses : List (Clause (numVars tm T S)) :=
  ((Finset.univ : Finset (Fin (T + 1))).toList.flatMap
      (fun t => exactlyOne (labelSlot t) ++ exactlyOne (stateSlot t)))
    ++ ((Finset.univ : Finset (Fin (T + 1))).toList.flatMap
        (fun t => (Finset.univ : Finset tm.K).toList.flatMap
          (fun k => (Finset.univ : Finset (Fin S)).toList.flatMap
            (fun i => exactlyOne (cellSlot t k i)))))

/-- An assignment is **consistent** iff it satisfies every consistency clause. -/
def Consistent (assign : Fin (numVars tm T S) → Bool) : Prop :=
  satisfiesAll assign (consistencyClauses tm T S)

/-- `Consistent` decomposes slot-by-slot: every label/state/cell slot has exactly one true
variable. -/
theorem consistent_iff (assign : Fin (numVars tm T S) → Bool) :
    Consistent assign ↔
      (∀ t : Fin (T + 1), ((labelSlot t).filter (fun v => assign v)).length = 1) ∧
      (∀ t : Fin (T + 1), ((stateSlot t).filter (fun v => assign v)).length = 1) ∧
      (∀ (t : Fin (T + 1)) (k : tm.K) (i : Fin S),
        ((cellSlot t k i).filter (fun v => assign v)).length = 1) := by
  rw [Consistent, consistencyClauses, satisfiesAll_append]
  -- the label/state half
  have hLS :
      satisfiesAll assign ((Finset.univ : Finset (Fin (T + 1))).toList.flatMap
        (fun t => exactlyOne (labelSlot t) ++ exactlyOne (stateSlot t))) ↔
      (∀ t : Fin (T + 1), ((labelSlot t).filter (fun v => assign v)).length = 1) ∧
      (∀ t : Fin (T + 1), ((stateSlot t).filter (fun v => assign v)).length = 1) := by
    rw [List.flatMap_def, satisfiesAll_flatten]
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
      forall_exists_index]
    constructor
    · intro h
      refine ⟨fun t => ?_, fun t => ?_⟩
      · have := h _ t rfl
        rw [satisfiesAll_append, exactlyOne_sat_iff_length, exactlyOne_sat_iff_length] at this
        exact this.1
      · have := h _ t rfl
        rw [satisfiesAll_append, exactlyOne_sat_iff_length, exactlyOne_sat_iff_length] at this
        exact this.2
    · rintro ⟨hl, hs⟩ g t rfl
      rw [satisfiesAll_append, exactlyOne_sat_iff_length, exactlyOne_sat_iff_length]
      exact ⟨hl t, hs t⟩
  -- the cell half
  have hC :
      satisfiesAll assign ((Finset.univ : Finset (Fin (T + 1))).toList.flatMap
        (fun t => (Finset.univ : Finset tm.K).toList.flatMap
          (fun k => (Finset.univ : Finset (Fin S)).toList.flatMap
            (fun i => exactlyOne (cellSlot t k i))))) ↔
      (∀ (t : Fin (T + 1)) (k : tm.K) (i : Fin S),
        ((cellSlot t k i).filter (fun v => assign v)).length = 1) := by
    rw [List.flatMap_def, satisfiesAll_flatten]
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index]
    constructor
    · intro h t k i
      have ht := h _ t rfl
      rw [List.flatMap_def, satisfiesAll_flatten] at ht
      simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
        forall_exists_index] at ht
      have hk := ht _ k rfl
      rw [List.flatMap_def, satisfiesAll_flatten] at hk
      simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
        forall_exists_index] at hk
      have hi := hk _ i rfl
      rwa [exactlyOne_sat_iff_length] at hi
    · intro h g t rfl
      rw [List.flatMap_def, satisfiesAll_flatten]
      simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index]
      intro g' k rfl
      rw [List.flatMap_def, satisfiesAll_flatten]
      simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index]
      intro g'' i rfl
      rw [exactlyOne_sat_iff_length]
      exact h t k i
  rw [hLS, hC]
  tauto

/-! ## (2) Per-slot readback and its correctness under consistency

The crux is a uniqueness extraction: in a slot with exactly one true variable, any two true
variables coincide. From there `coordVar_inj` plus the `*Coord` injectivity recovers argument
equality. -/

/-- In a slot list with exactly one `true`-assigned entry, any two `true`-assigned members are
equal: a length-1 list is a singleton, so all its members coincide. -/
theorem eq_of_filter_length_one {n : ℕ} {assign : Fin n → Bool} {vars : List (Fin n)}
    (hlen : (vars.filter (fun v => assign v)).length = 1)
    {a b : Fin n} (ha : a ∈ vars) (hat : assign a = true) (hb : b ∈ vars) (hbt : assign b = true) :
    a = b := by
  have hmemA : a ∈ vars.filter (fun v => assign v) := by
    rw [List.mem_filter]; exact ⟨ha, by simpa using hat⟩
  have hmemB : b ∈ vars.filter (fun v => assign v) := by
    rw [List.mem_filter]; exact ⟨hb, by simpa using hbt⟩
  -- a length-1 list has a single element to which every member is equal
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hlen
  rw [hx] at hmemA hmemB
  rw [List.mem_singleton] at hmemA hmemB
  rw [hmemA, hmemB]

/-- **Label uniqueness.** Under consistency, two label values true at the same time coincide. -/
theorem label_unique {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin (T + 1)} {l l' : Option tm.Λ}
    (hl : assign (coordVar (labelCoord t l)) = true)
    (hl' : assign (coordVar (labelCoord t l')) = true) : l = l' := by
  have := eq_of_filter_length_one (((consistent_iff assign).1 hcons).1 t)
    (mem_labelSlot t l) hl (mem_labelSlot t l') hl'
  exact (labelCoord_inj (coordVar_injective this)).2

/-- **State uniqueness.** Under consistency, two states true at the same time coincide. -/
theorem state_unique {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin (T + 1)} {s s' : tm.σ}
    (hs : assign (coordVar (stateCoord t s)) = true)
    (hs' : assign (coordVar (stateCoord t s')) = true) : s = s' := by
  have := eq_of_filter_length_one (((consistent_iff assign).1 hcons).2.1 t)
    (mem_stateSlot t s) hs (mem_stateSlot t s') hs'
  exact (stateCoord_inj (coordVar_injective this)).2

/-- **Cell uniqueness.** Under consistency, two cell values true at the same position coincide. -/
theorem cell_unique {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin (T + 1)} {k : tm.K} {i : Fin S} {c c' : Option (tm.Γ k)}
    (hc : assign (coordVar (cellCoord t k i c)) = true)
    (hc' : assign (coordVar (cellCoord t k i c')) = true) : c = c' := by
  have := eq_of_filter_length_one (((consistent_iff assign).1 hcons).2.2 t k i)
    (mem_cellSlot t k i c) hc (mem_cellSlot t k i c') hc'
  -- `cellCoord` injective in `c` at fixed `(t,k,i)`
  have hco : (cellCoord t k i c : TableauCoord tm T S) = cellCoord t k i c' :=
    coordVar_injective this
  -- peel `Sum.inr`/`Sum.inr`, then the same-`k` `Sigma` and `Prod` to reach `c = c'`
  have hsig : (⟨t, k, i, c⟩ : Σ _ : Fin (T + 1), Σ k : tm.K, Fin S × Option (tm.Γ k))
      = ⟨t, k, i, c'⟩ := Sum.inr.inj (Sum.inr.inj hco)
  -- both first components match, so the nested `Sigma`/`Prod` equality collapses to `c = c'`
  simpa using hsig

/-- The **label read** of an assignment at time `t`: the label some true coordinate certifies,
or `none` by default. -/
noncomputable def readLabel (assign : Fin (numVars tm T S) → Bool) (t : Fin (T + 1)) :
    Option tm.Λ :=
  if h : ∃ l, assign (coordVar (labelCoord t l)) = true then Classical.choose h else none

/-- The **state read** of an assignment at time `t`: the state some true coordinate certifies,
or `tm.initialState` by default. -/
noncomputable def readState (assign : Fin (numVars tm T S) → Bool) (t : Fin (T + 1)) : tm.σ :=
  if h : ∃ s, assign (coordVar (stateCoord t s)) = true then Classical.choose h
  else tm.initialState

/-- The **cell read** of an assignment at `(t, k, i)`: the cell value some true coordinate
certifies, or `none` by default. -/
noncomputable def readCell (assign : Fin (numVars tm T S) → Bool)
    (t : Fin (T + 1)) (k : tm.K) (i : Fin S) : Option (tm.Γ k) :=
  if h : ∃ c, assign (coordVar (cellCoord t k i c)) = true then Classical.choose h else none

/-- **Label readback correctness.** Under consistency, a true label coordinate is read back. -/
theorem readLabel_eq {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin (T + 1)} {l : Option tm.Λ} (hl : assign (coordVar (labelCoord t l)) = true) :
    readLabel assign t = l := by
  have hex : ∃ l, assign (coordVar (labelCoord t l)) = true := ⟨l, hl⟩
  rw [readLabel, dif_pos hex]
  exact label_unique hcons (Classical.choose_spec hex) hl

/-- **State readback correctness.** Under consistency, a true state coordinate is read back. -/
theorem readState_eq {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin (T + 1)} {s : tm.σ} (hs : assign (coordVar (stateCoord t s)) = true) :
    readState assign t = s := by
  have hex : ∃ s, assign (coordVar (stateCoord t s)) = true := ⟨s, hs⟩
  rw [readState, dif_pos hex]
  exact state_unique hcons (Classical.choose_spec hex) hs

/-- **Cell readback correctness.** Under consistency, a true cell coordinate is read back. -/
theorem readCell_eq {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin (T + 1)} {k : tm.K} {i : Fin S} {c : Option (tm.Γ k)}
    (hc : assign (coordVar (cellCoord t k i c)) = true) :
    readCell assign t k i = c := by
  have hex : ∃ c, assign (coordVar (cellCoord t k i c)) = true := ⟨c, hc⟩
  rw [readCell, dif_pos hex]
  exact cell_unique hcons (Classical.choose_spec hex) hc

/-! ## (3) Encoding a configuration sequence as an assignment

`encodeSeq cfgs` sets each variable to the truth of the fact its coordinate names about `cfgs`.
The `DecidableEq` hypotheses are needed for the `==` equality tests in each fact. -/

section Encode

variable [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

/-- The truth value a coordinate names about a configuration sequence `cfgs`: the label/state/cell
fact of the indicated time, stack, and position. -/
def coordFact (cfgs : Fin (T + 1) → tm.Cfg) : TableauCoord tm T S → Bool
  | Sum.inl (t, l) => (cfgs t).l == l
  | Sum.inr (Sum.inl (t, s)) => (cfgs t).var == s
  | Sum.inr (Sum.inr ⟨t, _, i, c⟩) => ((cfgs t).stk _)[(i : ℕ)]? == c

/-- The **assignment encoding** a configuration sequence: each variable's truth is the fact its
coordinate names about `cfgs`. -/
noncomputable def encodeSeq (cfgs : Fin (T + 1) → tm.Cfg) :
    Fin (numVars tm T S) → Bool :=
  fun v => coordFact cfgs ((coordEquiv tm T S).symm v)

omit [∀ k, Fintype (tm.Γ k)] in
/-- `coordFact` on a `labelCoord` is the label equality test. -/
@[simp] theorem coordFact_labelCoord (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin (T + 1))
    (l : Option tm.Λ) :
    coordFact (S := S) cfgs (labelCoord t l) = ((cfgs t).l == l) := rfl

omit [∀ k, Fintype (tm.Γ k)] in
/-- `coordFact` on a `stateCoord` is the state equality test. -/
@[simp] theorem coordFact_stateCoord (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin (T + 1))
    (s : tm.σ) :
    coordFact (S := S) cfgs (stateCoord t s) = ((cfgs t).var == s) := rfl

omit [∀ k, Fintype (tm.Γ k)] in
/-- `coordFact` on a `cellCoord` is the `i`-th stack-element equality test. -/
@[simp] theorem coordFact_cellCoord (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin (T + 1))
    (k : tm.K) (i : Fin S) (c : Option (tm.Γ k)) :
    coordFact cfgs (cellCoord t k i c) = (((cfgs t).stk k)[(i : ℕ)]? == c) := rfl

/-- `encodeSeq` at a label variable evaluates to the label equality test. -/
theorem encodeSeq_labelCoord (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin (T + 1))
    (l : Option tm.Λ) :
    encodeSeq (S := S) cfgs (coordVar (labelCoord t l)) = ((cfgs t).l == l) := by
  rw [encodeSeq, coordVar, Equiv.symm_apply_apply, coordFact_labelCoord]

/-- `encodeSeq` at a state variable evaluates to the state equality test. -/
theorem encodeSeq_stateCoord (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin (T + 1))
    (s : tm.σ) :
    encodeSeq (S := S) cfgs (coordVar (stateCoord t s)) = ((cfgs t).var == s) := by
  rw [encodeSeq, coordVar, Equiv.symm_apply_apply, coordFact_stateCoord]

/-- `encodeSeq` at a cell variable evaluates to the `i`-th stack-element equality test. -/
theorem encodeSeq_cellCoord (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin (T + 1))
    (k : tm.K) (i : Fin S) (c : Option (tm.Γ k)) :
    encodeSeq cfgs (coordVar (cellCoord t k i c)) = (((cfgs t).stk k)[(i : ℕ)]? == c) := by
  rw [encodeSeq, coordVar, Equiv.symm_apply_apply, coordFact_cellCoord]

end Encode

/-! ## (4) Round-trip: encoding is consistent and reads back to the original facts -/

/-- **Slot-counting helper.** A slot `univ.toList.map g` whose assignment sends each `g x` to
`target == x` has exactly one true variable (the one at `target`). -/
theorem filter_map_univ_beq_length_one {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    [BEq α] [LawfulBEq α] {assign : Fin n → Bool} {g : α → Fin n} (target : α)
    (hval : ∀ x, assign (g x) = (target == x)) :
    (((Finset.univ : Finset α).toList.map g).filter (fun v => assign v)).length = 1 := by
  rw [List.filter_map, List.length_map]
  have hnd : (Finset.univ : Finset α).toList.Nodup := Finset.nodup_toList _
  -- the filter predicate `(assign ∘ g) ·` agrees pointwise with `· == target`
  have hpred : ((fun v => assign v) ∘ g) = (fun x => x == target) := by
    funext x
    simp only [Function.comp_apply, hval x]
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, eq_comm]
  -- length of the filter = `count target`, which is `1` in a nodup list containing `target`
  rw [hpred, ← List.countP_eq_length_filter, ← List.count_eq_countP]
  exact List.count_eq_one_of_mem hnd (Finset.mem_toList.2 (Finset.mem_univ target))

section Encode

variable [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

/-- **Encoding is consistent.** Encoding a real configuration sequence satisfies every consistency
clause: each slot has exactly the one matching value true. -/
theorem encodeSeq_consistent (cfgs : Fin (T + 1) → tm.Cfg) :
    Consistent (encodeSeq (S := S) cfgs) := by
  rw [consistent_iff]
  refine ⟨fun t => ?_, fun t => ?_, fun t k i => ?_⟩
  · exact filter_map_univ_beq_length_one (cfgs t).l (fun l => encodeSeq_labelCoord cfgs t l)
  · exact filter_map_univ_beq_length_one (cfgs t).var (fun s => encodeSeq_stateCoord cfgs t s)
  · exact filter_map_univ_beq_length_one (((cfgs t).stk k)[(i : ℕ)]?)
      (fun c => encodeSeq_cellCoord cfgs t k i c)

/-- **Label round-trip.** Reading back an encoded sequence recovers the label. -/
theorem readLabel_encodeSeq (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin (T + 1)) :
    readLabel (encodeSeq (S := S) cfgs) t = (cfgs t).l :=
  readLabel_eq (encodeSeq_consistent cfgs)
    (by rw [encodeSeq_labelCoord]; simp)

/-- **State round-trip.** Reading back an encoded sequence recovers the internal state. -/
theorem readState_encodeSeq (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin (T + 1)) :
    readState (encodeSeq (S := S) cfgs) t = (cfgs t).var :=
  readState_eq (encodeSeq_consistent cfgs)
    (by rw [encodeSeq_stateCoord]; simp)

/-- **Cell round-trip.** Reading back an encoded sequence recovers the `i`-th stack element. -/
theorem readCell_encodeSeq (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin (T + 1)) (k : tm.K)
    (i : Fin S) :
    readCell (encodeSeq cfgs) t k i = ((cfgs t).stk k)[(i : ℕ)]? :=
  readCell_eq (encodeSeq_consistent cfgs)
    (by rw [encodeSeq_cellCoord]; simp)

end Encode

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

variable [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- Encoding a real configuration sequence is consistent.
example (cfgs : Fin (T + 1) → tm.Cfg) : Consistent (encodeSeq (S := S) cfgs) :=
  encodeSeq_consistent cfgs

-- The encode-then-read round-trip recovers the label at each time.
example (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin (T + 1)) :
    readLabel (encodeSeq (S := S) cfgs) t = (cfgs t).l :=
  readLabel_encodeSeq cfgs t

-- The encode-then-read round-trip recovers the internal state at each time.
example (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin (T + 1)) :
    readState (encodeSeq (S := S) cfgs) t = (cfgs t).var :=
  readState_encodeSeq cfgs t

-- The encode-then-read round-trip recovers the `i`-th stack element of each stack at each time.
example (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin (T + 1)) (k : tm.K) (i : Fin S) :
    readCell (encodeSeq cfgs) t k i = ((cfgs t).stk k)[(i : ℕ)]? :=
  readCell_encodeSeq cfgs t k i

end Examples

end TableauSchema

end DeepWiki
