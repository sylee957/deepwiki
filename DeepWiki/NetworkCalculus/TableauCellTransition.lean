import DeepWiki.NetworkCalculus.TableauInit
import DeepWiki.NetworkCalculus.FiniteFunctionClauses

/-!
# Tableau per-stack cell-transition clauses (keep / pop / push)

Layer 3b-iii(c) of a Cook- and Levin-style formalization: the **per-stack cell-transition
clause families** relating the cells of one stack `k` at time `t` to its cells at time `t+1`,
each with correctness at the `readStack` level.  Three gadgets, indexed by `t : Fin T` (so
`Fin.castSucc t` and `Fin.succ t` are the consecutive time indices in `Fin (T+1)`):

* `keepCellClauses t k` — stack `k` is **unchanged**: `cell(t,k,i,c) ↔ cell(t+1,k,i,c)` for
  every `i`, `c`.  Correctness `keepCell_readStack` :
  `readStack (t+1) k = readStack t k`.
* `popCellClauses t k` — stack `k` at `t+1` is the **tail**: `cell(t+1,k,i,c) ↔ cell(t,k,i+1,c)`
  for `i+1 < S`, and the top cell `cell(t+1,k,S-1) = none`.  Correctness `popCell_readStack` :
  `readStack (t+1) k = (readStack t k).tail`.
* `pushCellClauses t k f` — stack `k` at `t+1` is `f(state@t) :: stack@t`: the new bottom
  `cell(t+1,k,0) = some (f (state@t))` (linked via `funClauses`) and a **shift up**
  `cell(t+1,k,i+1,c) ↔ cell(t,k,i,c)` for `i+1 < S`.  Correctness `pushCell_readStack` :
  with `(readStack t k).length < S`, `readStack (t+1) k = f (readState t) :: readStack t k`.

The pop and push correctness need the time-`t` cells to be in **none-terminated-prefix shape**
(`IsStackShape`: real values at the bottom, `none` padding above the top) — exactly the shape
`readback`/`encodeSeq` produces; it is supplied as a hypothesis here.

## Deferred

This chunk is **only** the three cell-transition gadgets and their `readStack`-level
correctness, decoupled from the time-axis dispatch.  The continuation-coordinate dispatch
(which gadget applies depends on the current `Turing.TM2.Stmt` head), the state-transition
clauses (load- and peek- and pop-`σ` update, which also need a `funClauses₂` on
`σ × Option (Γ k)`), the full per-`stmtStep` assembly, halt-padding, and reduction correctness
are **later** layers.
-/

open Turing

namespace DeepWiki

namespace TableauSchema

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

open BooleanConstraints

variable {tm : FinTM2} {T S : ℕ} [∀ k, Fintype (tm.Γ k)]

/-! ## (0) Abstract list lemmas: shifting `ofFn`/`reduceOption` cells

A column of cells over the position axis `Fin S` is **in stack shape** when it is the
`none`-terminated prefix `L.map some ++ replicate (S - L.length) none` of its underlying stack
`L`; `reduceOption` then recovers `L`.  These pure `List` lemmas are the heart of the pop/push
correctness — they show that shifting the column down by one yields `L.tail`, and prepending a
`some` and shifting up yields `x :: L`. -/

/-- The cell column `cells : Fin S → Option α` is **in stack shape** for `L`: it is `L`'s
elements as `some`, padded with `none` to length `S`. -/
def IsStackShape {α : Type*} {S : ℕ} (cells : Fin S → Option α) (L : List α) : Prop :=
  (List.ofFn cells) = L.map some ++ List.replicate (S - L.length) none

/-- A stack-shaped column has `reduceOption = L` (the padding `none`s drop out). -/
theorem IsStackShape.reduceOption {α : Type*} {S : ℕ} {cells : Fin S → Option α} {L : List α}
    (h : IsStackShape cells L) : (List.ofFn cells).reduceOption = L := by
  rw [h, reduceOption_map_some_append_replicate]

/-- **Head-peel.** If `g` over `Fin (m+1)` is stack-shaped for `L`, then `g ∘ Fin.succ` over
`Fin m` is stack-shaped for `L.tail` (dropping the bottom element). -/
theorem IsStackShape.succ {α : Type*} {m : ℕ} {g : Fin (m + 1) → Option α} {L : List α}
    (h : IsStackShape g L) : IsStackShape (fun i : Fin m => g i.succ) L.tail := by
  -- peel the head of `ofFn g` to read off `ofFn (g ∘ succ)`
  have hofFn : List.ofFn (fun i : Fin m => g i.succ) =
      (L.map some ++ List.replicate (m + 1 - L.length) none).tail := by
    have hsucc := List.ofFn_succ (f := g)
    rw [h] at hsucc
    -- `hsucc : L.map some ++ replicate (m+1-L.length) none = g 0 :: ofFn (g ∘ succ)`
    have h2 := congrArg List.tail hsucc
    rw [List.tail_cons] at h2
    exact h2.symm
  rw [IsStackShape, hofFn]
  cases L with
  | nil =>
    -- `([].map some ++ replicate (m+1) none).tail = replicate m none = [].map some ++ replicate m none`
    simp only [List.map_nil, List.nil_append, List.length_nil, Nat.sub_zero, List.tail_nil]
    rw [List.replicate_succ, List.tail_cons]
  | cons x xs =>
    -- `(some x :: (xs.map some ++ replicate r none)).tail = xs.map some ++ replicate r none`
    simp only [List.map_cons, List.cons_append, List.tail_cons, List.length_cons]
    congr 2
    omega

/-- **Top cell is `none`.** A stack-shaped column over `Fin (m+1)` with `L.length < m+1` has its
top position (`Fin.last m`) holding `none` (there is at least one `none` of padding). -/
theorem IsStackShape.last_eq_none {α : Type*} {m : ℕ} {g : Fin (m + 1) → Option α} {L : List α}
    (h : IsStackShape g L) (hlt : L.length < m + 1) : g (Fin.last m) = none := by
  -- read off position `m` of `ofFn g`; it lies in the `none` padding since `m ≥ L.length`
  have hget : (List.ofFn g)[m]? = some (g (Fin.last m)) := by
    rw [List.getElem?_ofFn]
    simp [Fin.last]
  rw [h] at hget
  -- index `m` of `L.map some ++ replicate r none` is in the replicate part (`m ≥ L.length`)
  rw [List.getElem?_append_right (by simpa using (by omega : L.length ≤ m))] at hget
  simp only [List.length_map, List.getElem?_replicate] at hget
  rw [if_pos (by omega)] at hget
  exact (Option.some.inj hget).symm

/-- **Pop list lemma.** Over `Fin (m+1)` with `g` stack-shaped for `L`, a column `f` shifted
*down* by one (`f i.castSucc = g i.succ`) and capped with `none` at the top has
`(ofFn f).reduceOption = L.tail`. -/
theorem reduceOption_ofFn_pop {α : Type*} {m : ℕ} {f g : Fin (m + 1) → Option α} {L : List α}
    (hg : IsStackShape g L)
    (hshift : ∀ i : Fin m, f i.castSucc = g i.succ) (htop : f (Fin.last m) = none) :
    (List.ofFn f).reduceOption = L.tail := by
  -- peel the last cell (`none`) of `ofFn f` via `ofFn_succ'`
  rw [List.ofFn_succ' (f := f), htop]
  rw [List.reduceOption_concat]
  simp only [Option.toList_none, List.append_nil]
  -- the truncated column is `g ∘ succ`, which is stack-shaped for `L.tail`
  have hfc : (fun i : Fin m => f i.castSucc) = (fun i : Fin m => g i.succ) := by
    funext i; exact hshift i
  rw [hfc]
  exact hg.succ.reduceOption

/-- **Push list lemma.** Over `Fin (m+1)` with `g` stack-shaped for `L` and `L.length < m+1`, a
column `f` with new bottom `f 0 = some x` and shifted *up* by one (`f i.succ = g i.castSucc`) has
`(ofFn f).reduceOption = x :: L`. -/
theorem reduceOption_ofFn_push {α : Type*} {m : ℕ} {f g : Fin (m + 1) → Option α} {L : List α}
    {x : α} (hg : IsStackShape g L) (hlt : L.length < m + 1)
    (hbot : f 0 = some x) (hshift : ∀ i : Fin m, f i.succ = g i.castSucc) :
    (List.ofFn f).reduceOption = x :: L := by
  -- peel the new bottom cell (`some x`) of `ofFn f` via `ofFn_succ`
  rw [List.ofFn_succ (f := f), hbot, List.reduceOption_cons_of_some]
  -- the shifted column is `g ∘ castSucc`; its `reduceOption` is `L` (the top `none` drops out)
  have hfc : (fun i : Fin m => f i.succ) = (fun i : Fin m => g i.castSucc) := by
    funext i; exact hshift i
  rw [hfc]
  -- relate `ofFn (g ∘ castSucc)` to `ofFn g` by appending back the top cell `g (last) = none`
  have hcast : (List.ofFn fun i : Fin m => g i.castSucc).reduceOption = L := by
    have hsplit := List.ofFn_succ' (f := g)
    rw [hg.last_eq_none hlt] at hsplit
    -- `ofFn g = (ofFn g∘castSucc).concat none`, so `reduceOption (ofFn g) = reduceOption (ofFn g∘castSucc)`
    have := congrArg List.reduceOption hsplit
    rw [hg.reduceOption, List.reduceOption_concat] at this
    simpa using this.symm
  rw [hcast]

/-- **Pop list lemma, `S`-general.** For `f g : Fin S → Option α` with `g` stack-shaped for `L`,
a shift *down* (`f i = g ⟨i+1⟩` for `i+1 < S`) capped with `none` at the top (`f i = none` when
`i+1 = S`) has `(ofFn f).reduceOption = L.tail`. -/
theorem reduceOption_ofFn_pop_gen {α : Type*} {S : ℕ} {f g : Fin S → Option α} {L : List α}
    (hg : IsStackShape g L)
    (hshift : ∀ (i : Fin S) (hi : (i : ℕ) + 1 < S), f i = g ⟨(i : ℕ) + 1, hi⟩)
    (htop : ∀ i : Fin S, (i : ℕ) + 1 = S → f i = none) :
    (List.ofFn f).reduceOption = L.tail := by
  cases S with
  | zero =>
    -- no positions: `ofFn g = []` forces `L = []`, and `[].tail = []`
    have hL : L = [] := by
      have := hg; rw [IsStackShape, List.ofFn_zero] at this
      simpa using (List.append_eq_nil_iff.1 this.symm).1
    rw [hL]; simp [List.ofFn_zero]
  | succ m =>
    refine reduceOption_ofFn_pop hg (fun i => ?_) ?_
    · -- shift-down at lower position `i.castSucc`, landing at `i.succ`
      have hi : ((i.castSucc : Fin (m + 1)) : ℕ) + 1 < m + 1 := by
        simp only [Fin.val_castSucc]; omega
      rw [hshift i.castSucc hi,
        show (⟨((i.castSucc : Fin (m + 1)) : ℕ) + 1, hi⟩ : Fin (m + 1)) = i.succ by
          apply Fin.ext; simp [Fin.val_succ, Fin.val_castSucc]]
    · exact htop (Fin.last m) (by simp [Fin.val_last])

/-- **Push list lemma, `S`-general.** For `f g : Fin S → Option α` with `g` stack-shaped for `L`
and `L.length < S`, a new bottom (`f 0 = some x`, given `0 < S`) plus a shift *up*
(`f ⟨i+1⟩ = g i` for `i+1 < S`) has `(ofFn f).reduceOption = x :: L`. -/
theorem reduceOption_ofFn_push_gen {α : Type*} {S : ℕ} {f g : Fin S → Option α} {L : List α}
    {x : α} (hg : IsStackShape g L) (hlt : L.length < S)
    (hbot : ∀ h : 0 < S, f ⟨0, h⟩ = some x)
    (hshift : ∀ (i : Fin S) (hi : (i : ℕ) + 1 < S), f ⟨(i : ℕ) + 1, hi⟩ = g i) :
    (List.ofFn f).reduceOption = x :: L := by
  cases S with
  | zero => exact absurd hlt (by omega)
  | succ m =>
    refine reduceOption_ofFn_push hg hlt (hbot (Nat.succ_pos m)) (fun i => ?_)
    · -- shift-up: new position `i.succ` carries the old value at `i.castSucc`
      have hi : ((i.castSucc : Fin (m + 1)) : ℕ) + 1 < m + 1 := by
        simp only [Fin.val_castSucc]; omega
      have hsh := hshift i.castSucc hi
      rw [show (⟨((i.castSucc : Fin (m + 1)) : ℕ) + 1, hi⟩ : Fin (m + 1)) = i.succ by
        apply Fin.ext; simp [Fin.val_succ, Fin.val_castSucc]] at hsh
      rw [hsh]

/-! ## (1) Readback helpers: the read cell value is the true one -/

/-- Under consistency, some cell value is `true` at `(t, k, i)` (its slot has a true variable). -/
theorem exists_cell_true {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    (t : Fin (T + 1)) (k : tm.K) (i : Fin S) :
    ∃ c : Option (tm.Γ k), assign (coordVar (cellCoord t k i c)) = true := by
  have hlen := ((consistent_iff assign).1 hcons).2.2 t k i
  -- a length-1 filter is nonempty: pull out a true member of the cell slot
  have hpos : 0 < ((cellSlot t k i).filter (fun v => assign v)).length := by omega
  rw [List.length_pos_iff_exists_mem] at hpos
  obtain ⟨v, hv⟩ := hpos
  rw [List.mem_filter] at hv
  -- the true variable is `coordVar (cellCoord t k i c)` for some `c`
  obtain ⟨c, _, hc⟩ := by simpa only [cellSlot, List.mem_map, Finset.mem_toList] using hv.1
  exact ⟨c, by rw [hc]; simpa using hv.2⟩

/-- Under consistency, the **read** cell value's own coordinate is `true`: the variable
`cellCoord t k i (readCell …)` is assigned `true`. -/
theorem readCell_self_true {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    (t : Fin (T + 1)) (k : tm.K) (i : Fin S) :
    assign (coordVar (cellCoord t k i (readCell assign t k i))) = true := by
  obtain ⟨c, hc⟩ := exists_cell_true hcons t k i
  rw [readCell_eq hcons hc]; exact hc

/-- Under consistency, some state is `true` at `t` (its slot has a true variable). -/
theorem exists_state_true {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    (t : Fin (T + 1)) : ∃ s : tm.σ, assign (coordVar (stateCoord t s)) = true := by
  have hlen := ((consistent_iff assign).1 hcons).2.1 t
  have hpos : 0 < ((stateSlot t).filter (fun v => assign v)).length := by omega
  rw [List.length_pos_iff_exists_mem] at hpos
  obtain ⟨v, hv⟩ := hpos
  rw [List.mem_filter] at hv
  obtain ⟨s, _, hs⟩ := by
    simpa only [stateSlot, List.mem_map, Finset.mem_toList] using hv.1
  exact ⟨s, by rw [hs]; simpa using hv.2⟩

/-- Under consistency, the **read** state's own coordinate is `true`. -/
theorem readState_self_true {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    (t : Fin (T + 1)) : assign (coordVar (stateCoord t (readState assign t))) = true := by
  obtain ⟨s, hs⟩ := exists_state_true hcons t
  rw [readState_eq hcons hs]; exact hs

/-- **Stack-shape bridge.** If the readback cell column at `(t, k)` is in stack shape for `L`,
then `readStack assign t k = L` (the column's `reduceOption`, by definition). -/
theorem readStack_eq_of_isStackShape {assign : Fin (numVars tm T S) → Bool} {t : Fin (T + 1)}
    {k : tm.K} {L : List (tm.Γ k)}
    (h : IsStackShape (fun i : Fin S => readCell assign t k i) L) :
    readStack assign t k = L :=
  h.reduceOption

/-! ## (2) Keep: stack `k` is unchanged from `t` to `t+1`

For each position `i`, a `funClauses` identity links the value at `(castSucc t, k, i)` to the
value at `(succ t, k, i)`: whichever cell value holds at time `t` also holds at `t+1`.  The
forward functional link is all the `readStack` correctness needs. -/

/-- The **keep clauses** for stack `k` over the step `t → t+1`: per position `i`, the
`funClauses` identity linking `cell(castSucc t, k, i, c)` to `cell(succ t, k, i, c)`. -/
noncomputable def keepCellClauses (t : Fin T) (k : tm.K) : List (Clause (numVars tm T S)) :=
  (Finset.univ : Finset (Fin S)).toList.flatMap
    (fun i => funClauses (fun c : Option (tm.Γ k) => coordVar (cellCoord (Fin.castSucc t) k i c))
      (fun c : Option (tm.Γ k) => coordVar (cellCoord (Fin.succ t) k i c)) id)

/-- Satisfying the keep clauses gives the per-position `funClauses` link at each `i`. -/
theorem satisfiesAll_keepCellClauses {assign : Fin (numVars tm T S) → Bool} {t : Fin T} {k : tm.K}
    (h : satisfiesAll assign (keepCellClauses (S := S) t k)) (i : Fin S) :
    satisfiesAll assign
      (funClauses (fun c : Option (tm.Γ k) => coordVar (cellCoord (Fin.castSucc t) k i c))
        (fun c : Option (tm.Γ k) => coordVar (cellCoord (Fin.succ t) k i c)) id) := by
  rw [keepCellClauses, List.flatMap_def, satisfiesAll_flatten] at h
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index] at h
  exact h _ i rfl

/-- **Keep, per-cell.** Under consistency, satisfying the keep clauses makes each cell at `t+1`
equal to the same cell at `t`. -/
theorem keepCell_readCell {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} (h : satisfiesAll assign (keepCellClauses (S := S) t k)) (i : Fin S) :
    readCell assign (Fin.succ t) k i = readCell assign (Fin.castSucc t) k i := by
  -- the read time-`t` value's coordinate is true; forward `funClauses` propagates it to `t+1`
  have hin := readCell_self_true hcons (Fin.castSucc t) k i
  have hout := funClauses_spec _ _ id assign (satisfiesAll_keepCellClauses h i)
    (readCell assign (Fin.castSucc t) k i) hin
  simpa using readCell_eq hcons hout

/-- **Keep, `readStack` correctness.** Under consistency, the keep clauses force stack `k` at
`t+1` to equal stack `k` at `t`. -/
theorem keepCell_readStack {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} (h : satisfiesAll assign (keepCellClauses (S := S) t k)) :
    readStack assign (Fin.succ t) k = readStack assign (Fin.castSucc t) k := by
  -- the two cell columns are literally equal (per-position), so their `readStack`s agree
  have hcell : (fun i : Fin S => readCell assign (Fin.succ t) k i)
      = (fun i : Fin S => readCell assign (Fin.castSucc t) k i) := by
    funext i; exact keepCell_readCell hcons h i
  rw [readStack, readStack, hcell]

/-! ## (3) Pop: stack `k` at `t+1` is the tail of stack `k` at `t`

For each non-top position `i` (with `i+1 < S`) a `funClauses` identity links the value at the
new position `(succ t, k, i)` to the value one step *higher* at the old time
`(castSucc t, k, i+1)` — a shift *down*.  The top position `(succ t, k, S-1)` is forced to
`none` (a unit clause), emptying the slot the tail vacates. -/

/-- The clauses for non-top position `i` (`i+1 < S`): the `funClauses` identity linking
`cell(succ t, k, i, c)` to `cell(castSucc t, k, ⟨i+1⟩, c)` — the shift *down*. -/
noncomputable def popShiftClauses (t : Fin T) (k : tm.K) (i : Fin S) (h : (i : ℕ) + 1 < S) :
    List (Clause (numVars tm T S)) :=
  funClauses (fun c : Option (tm.Γ k) => coordVar (cellCoord (Fin.succ t) k i c))
    (fun c : Option (tm.Γ k) => coordVar (cellCoord (Fin.castSucc t) k ⟨(i : ℕ) + 1, h⟩ c)) id

/-- The **pop clauses** for stack `k` over `t → t+1`: per position `i`, a shift-down
`funClauses` when `i+1 < S`, else (the top position) the unit clause forcing
`cell(succ t, k, i, none)`. -/
noncomputable def popCellClauses (t : Fin T) (k : tm.K) : List (Clause (numVars tm T S)) :=
  (Finset.univ : Finset (Fin S)).toList.flatMap
    (fun i : Fin S => if h : (i : ℕ) + 1 < S then popShiftClauses t k i h
      else [[(coordVar (cellCoord (Fin.succ t) k i none), true)]])

/-- Satisfying the pop clauses gives the per-position clause group at each `i`. -/
theorem satisfiesAll_popCellClauses {assign : Fin (numVars tm T S) → Bool} {t : Fin T} {k : tm.K}
    (h : satisfiesAll assign (popCellClauses (S := S) t k)) (i : Fin S) :
    satisfiesAll assign
      (if h : (i : ℕ) + 1 < S then popShiftClauses t k i h
        else [[(coordVar (cellCoord (Fin.succ t) k i none), true)]]) := by
  rw [popCellClauses, List.flatMap_def, satisfiesAll_flatten] at h
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index] at h
  exact h _ i rfl

/-- **Pop, non-top cell.** Under consistency, for `i+1 < S` the new cell at `(succ t, k, i)`
equals the old cell one step higher, `(castSucc t, k, ⟨i+1⟩)`. -/
theorem popCell_readCell_shift {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} (h : satisfiesAll assign (popCellClauses (S := S) t k))
    (i : Fin S) (hi : (i : ℕ) + 1 < S) :
    readCell assign (Fin.succ t) k i
      = readCell assign (Fin.castSucc t) k ⟨(i : ℕ) + 1, hi⟩ := by
  have hsat := satisfiesAll_popCellClauses h i
  rw [dif_pos hi, popShiftClauses] at hsat
  have hin := readCell_self_true hcons (Fin.succ t) k i
  have hout := funClauses_spec _ _ id assign hsat (readCell assign (Fin.succ t) k i) hin
  exact (readCell_eq hcons (by simpa using hout)).symm

/-- **Pop, top cell.** Under consistency, the new top cell `(succ t, k, last)` is `none`. -/
theorem popCell_readCell_top {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} (h : satisfiesAll assign (popCellClauses (S := S) t k))
    (i : Fin S) (hi : ¬ (i : ℕ) + 1 < S) :
    readCell assign (Fin.succ t) k i = none := by
  have hsat := satisfiesAll_popCellClauses h i
  rw [dif_neg hi] at hsat
  exact readCell_eq hcons (unitClause_sat hsat)

/-- **Pop, `readStack` correctness.** Under consistency, with the time-`t` cells in stack shape,
the pop clauses force stack `k` at `t+1` to be the **tail** of stack `k` at `t`. -/
theorem popCell_readStack {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} (h : satisfiesAll assign (popCellClauses (S := S) t k))
    (hshape : IsStackShape (fun i : Fin S => readCell assign (Fin.castSucc t) k i)
      (readStack assign (Fin.castSucc t) k)) :
    readStack assign (Fin.succ t) k = (readStack assign (Fin.castSucc t) k).tail := by
  -- `readStack t+1` is the `reduceOption` of the shifted-down/top-capped cell column
  rw [readStack]
  exact reduceOption_ofFn_pop_gen hshape
    (fun i hi => popCell_readCell_shift hcons h i hi)
    (fun i hi => popCell_readCell_top hcons h i (by omega))

/-! ## (5) Push: stack `k` at `t+1` is `f(state@t) :: stack@t`

A `funClauses` links the **state** at time `t` to the *new bottom* cell `(succ t, k, 0)`, set to
`some (f (state@t))`.  For each old position `i` (with `i+1 < S`) a `funClauses` identity links
the value at `(castSucc t, k, i)` to the value one step *higher* at the new time
`(succ t, k, i+1)` — a shift *up*.  Correctness needs `(stack@t).length < S` (the push fits). -/

/-- The new-bottom clauses (when `0 < S`): `funClauses` setting `cell(succ t, k, 0)` to
`some (f s)` where `s` is the state at time `t`. -/
noncomputable def pushBottomClauses (t : Fin T) (k : tm.K) (f : tm.σ → tm.Γ k) (h0 : 0 < S) :
    List (Clause (numVars tm T S)) :=
  funClauses (fun s : tm.σ => coordVar (stateCoord (Fin.castSucc t) s))
    (fun c : Option (tm.Γ k) => coordVar (cellCoord (Fin.succ t) k ⟨0, h0⟩ c))
    (fun s => some (f s))

/-- The shift-up clauses for old position `i` (`i+1 < S`): the `funClauses` identity linking
`cell(castSucc t, k, i, c)` to `cell(succ t, k, ⟨i+1⟩, c)` — the shift *up*. -/
noncomputable def pushShiftClauses (t : Fin T) (k : tm.K) (i : Fin S) (h : (i : ℕ) + 1 < S) :
    List (Clause (numVars tm T S)) :=
  funClauses (fun c : Option (tm.Γ k) => coordVar (cellCoord (Fin.castSucc t) k i c))
    (fun c : Option (tm.Γ k) => coordVar (cellCoord (Fin.succ t) k ⟨(i : ℕ) + 1, h⟩ c)) id

/-- The **push clauses** for stack `k` over `t → t+1` with new bottom value `f (state@t)`: the
new-bottom `funClauses` (when `0 < S`) together with the per-position shift-up clauses. -/
noncomputable def pushCellClauses (t : Fin T) (k : tm.K) (f : tm.σ → tm.Γ k) :
    List (Clause (numVars tm T S)) :=
  (if h0 : 0 < S then pushBottomClauses t k f h0 else []) ++
    (Finset.univ : Finset (Fin S)).toList.flatMap
      (fun i : Fin S => if h : (i : ℕ) + 1 < S then pushShiftClauses t k i h else [])

/-- Satisfying the push clauses gives the bottom group (when `0 < S`). -/
theorem satisfiesAll_pushCellClauses_bottom {assign : Fin (numVars tm T S) → Bool} {t : Fin T}
    {k : tm.K} {f : tm.σ → tm.Γ k} (h : satisfiesAll assign (pushCellClauses (S := S) t k f))
    (h0 : 0 < S) : satisfiesAll assign (pushBottomClauses t k f h0) := by
  rw [pushCellClauses, satisfiesAll_append] at h
  rw [dif_pos h0] at h
  exact h.1

/-- Satisfying the push clauses gives the shift-up clause group at each position `i`. -/
theorem satisfiesAll_pushCellClauses_shift {assign : Fin (numVars tm T S) → Bool} {t : Fin T}
    {k : tm.K} {f : tm.σ → tm.Γ k} (h : satisfiesAll assign (pushCellClauses (S := S) t k f))
    (i : Fin S) :
    satisfiesAll assign (if h : (i : ℕ) + 1 < S then pushShiftClauses t k i h else []) := by
  rw [pushCellClauses, satisfiesAll_append] at h
  rw [List.flatMap_def, satisfiesAll_flatten] at h
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_exists_index] at h
  exact h.2 _ i rfl

/-- **Push, bottom cell.** Under consistency, the new bottom cell `(succ t, k, 0)` is
`some (f (state@t))`. -/
theorem pushCell_readCell_bottom {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} {f : tm.σ → tm.Γ k}
    (h : satisfiesAll assign (pushCellClauses (S := S) t k f)) (h0 : 0 < S) :
    readCell assign (Fin.succ t) k ⟨0, h0⟩ = some (f (readState assign (Fin.castSucc t))) := by
  have hsat := satisfiesAll_pushCellClauses_bottom h h0
  rw [pushBottomClauses] at hsat
  have hin := readState_self_true hcons (Fin.castSucc t)
  have hout := funClauses_spec _ _ _ assign hsat (readState assign (Fin.castSucc t)) hin
  exact readCell_eq hcons hout

/-- **Push, shift cell.** Under consistency, for `i+1 < S` the new cell at `(succ t, k, ⟨i+1⟩)`
equals the old cell at `(castSucc t, k, i)`. -/
theorem pushCell_readCell_shift {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} {f : tm.σ → tm.Γ k}
    (h : satisfiesAll assign (pushCellClauses (S := S) t k f))
    (i : Fin S) (hi : (i : ℕ) + 1 < S) :
    readCell assign (Fin.succ t) k ⟨(i : ℕ) + 1, hi⟩ = readCell assign (Fin.castSucc t) k i := by
  have hsat := satisfiesAll_pushCellClauses_shift h i
  rw [dif_pos hi, pushShiftClauses] at hsat
  have hin := readCell_self_true hcons (Fin.castSucc t) k i
  have hout := funClauses_spec _ _ id assign hsat (readCell assign (Fin.castSucc t) k i) hin
  exact readCell_eq hcons (by simpa using hout)

/-- **Push, `readStack` correctness.** Under consistency, with the time-`t` cells in stack shape
and the pushed stack fitting (`(stack@t).length < S`), the push clauses force stack `k` at `t+1`
to be `f (state@t) :: stack@t`. -/
theorem pushCell_readStack {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} {f : tm.σ → tm.Γ k}
    (h : satisfiesAll assign (pushCellClauses (S := S) t k f))
    (hshape : IsStackShape (fun i : Fin S => readCell assign (Fin.castSucc t) k i)
      (readStack assign (Fin.castSucc t) k))
    (hfit : (readStack assign (Fin.castSucc t) k).length < S) :
    readStack assign (Fin.succ t) k
      = f (readState assign (Fin.castSucc t)) :: readStack assign (Fin.castSucc t) k := by
  -- `readStack t+1` is the `reduceOption` of the bottom-prepended/shifted-up cell column
  rw [readStack]
  exact reduceOption_ofFn_push_gen hshape hfit
    (fun h0 => pushCell_readCell_bottom hcons h h0)
    (fun i hi => pushCell_readCell_shift hcons h i hi)

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

-- Keep: stack `k` at `t+1` equals stack `k` at `t`.
example {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} (h : satisfiesAll assign (keepCellClauses (S := S) t k)) :
    readStack assign (Fin.succ t) k = readStack assign (Fin.castSucc t) k :=
  keepCell_readStack hcons h

-- Pop: stack `k` at `t+1` is the tail of stack `k` at `t`.
example {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} (h : satisfiesAll assign (popCellClauses (S := S) t k))
    (hshape : IsStackShape (fun i : Fin S => readCell assign (Fin.castSucc t) k i)
      (readStack assign (Fin.castSucc t) k)) :
    readStack assign (Fin.succ t) k = (readStack assign (Fin.castSucc t) k).tail :=
  popCell_readStack hcons h hshape

-- Push: stack `k` at `t+1` is `f(state@t) :: stack@t` (when it fits).
example {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} {f : tm.σ → tm.Γ k}
    (h : satisfiesAll assign (pushCellClauses (S := S) t k f))
    (hshape : IsStackShape (fun i : Fin S => readCell assign (Fin.castSucc t) k i)
      (readStack assign (Fin.castSucc t) k))
    (hfit : (readStack assign (Fin.castSucc t) k).length < S) :
    readStack assign (Fin.succ t) k
      = f (readState assign (Fin.castSucc t)) :: readStack assign (Fin.castSucc t) k :=
  pushCell_readStack hcons h hshape hfit

end Examples

end TableauSchema

end DeepWiki
