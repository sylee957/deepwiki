import DeepWiki.NetworkCalculus.CellTransitionAssembly

/-!
# `IsStackShape` invariant propagation for the Cook- and Levin-style tableau

Layer 3c-iii of a Cook- and Levin-style formalization: the **stack-shape invariant
propagation** across one time step.  The per-stack cell gadgets of `TableauCellTransition`
(`keepCellClauses`, `pushCellClauses`, `popCellClauses`) all preserve
`TableauSchema.IsStackShape` — the property that a stack's cell column is a `none`-terminated
prefix (real values at the bottom, `none` padding above the top).  Combined through the
continuation dispatch of `CellTransitionAssembly`, this gives the time-step propagation: if
every stack is in stack shape at time `t` (with room to spare), every stack is in stack shape
at `t+1`.  This is the invariant that lets the `readStack`-level per-time correctness of
`cellTransClauses_spec` chain across the whole time axis.

* Pure `List`/`ofFn` helpers (`IsStackShape.castSucc`, `isStackShape_ofFn_push`,
  `isStackShape_ofFn_pop`, and their `S`-general forms) strengthen the existing
  `reduceOption`-level helpers of `TableauCellTransition` to the full `IsStackShape` shape.
* `keepCell_isStackShape` / `pushCell_isStackShape` / `popCell_isStackShape` — each per-stack
  gadget preserves `IsStackShape` (with `cons`/`tail` of the read stack as the new list for
  push/pop).
* `isStackShape_propagate` — the combined-space propagation: from `IsStackShape` at every stack
  at `t` (and room `length < S`), `IsStackShape` at every stack at `t+1`, with the new list
  being `readStack (t+1) k` (so the invariant is self-perpetuating).

## Deferred

This chunk is **only** the one-step `IsStackShape` propagation.  The multi-step
`readUnif (t+1) = unifStep^[N] (readUnif 0)` induction (which combines this with
`cellTransClauses_spec` and `unifTransClauses_spec`), the init- and accept- clauses, and the
reduction's correctness are **later** layers.
-/

open Turing

namespace DeepWiki

namespace TableauSchema

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

open BooleanConstraints

variable {tm : FinTM2} {T S : ℕ} [∀ k, Fintype (tm.Γ k)]

/-! ## (0) `IsStackShape`-level `ofFn` helpers

The pop/push correctness of `TableauCellTransition` was proved at the `reduceOption` level
(`reduceOption_ofFn_pop_gen` / `reduceOption_ofFn_push_gen`).  For the *invariant* propagation
we need the full `IsStackShape` shape of the time-`t+1` column, so the same shifting arguments
are redone one level up — establishing `ofFn = L'.map some ++ replicate (S - L'.length) none`
rather than just `reduceOption = L'`. -/

/-- **Drop-top.** A stack-shaped column over `Fin (m+1)` with `L.length < m+1` restricts (drop
the top position) to a stack-shaped column over `Fin m` for the *same* `L`. -/
theorem IsStackShape.castSucc {α : Type*} {m : ℕ} {g : Fin (m + 1) → Option α} {L : List α}
    (h : IsStackShape g L) (hlt : L.length < m + 1) :
    IsStackShape (fun i : Fin m => g i.castSucc) L := by
  -- peel the last cell (`g (last) = none`) of `ofFn g` via `ofFn_succ'`
  have hsplit := List.ofFn_succ' (f := g)
  rw [h.last_eq_none hlt, List.concat_eq_append] at hsplit
  -- `ofFn g = (ofFn g∘castSucc) ++ [none]`; also `ofFn g = L.map some ++ replicate (m+1-|L|) none`
  rw [h] at hsplit
  -- so `ofFn (g∘castSucc) = (L.map some ++ replicate (m+1-|L|) none).dropLast`
  have hdrop : List.ofFn (fun i : Fin m => g i.castSucc) =
      (L.map some ++ List.replicate (m + 1 - L.length) none).dropLast := by
    have h2 := congrArg List.dropLast hsplit
    rw [List.dropLast_concat] at h2
    exact h2.symm
  rw [IsStackShape, hdrop]
  -- the dropped element is one of the `none` padding: `replicate (m+1-|L|) = replicate (m-|L|) ++ [none]`
  have hrep : m + 1 - L.length = (m - L.length) + 1 := by omega
  rw [hrep, List.replicate_succ', ← List.append_assoc, List.dropLast_concat]

/-- **Push, `ofFn` shape.** Over `Fin (m+1)` with `g` stack-shaped for `L` and `L.length < m+1`,
a column `f` with new bottom `f 0 = some x` and shifted *up* (`f i.succ = g i.castSucc`) is
stack-shaped for `x :: L`. -/
theorem isStackShape_ofFn_push {α : Type*} {m : ℕ} {f g : Fin (m + 1) → Option α} {L : List α}
    {x : α} (hg : IsStackShape g L) (hlt : L.length < m + 1)
    (hbot : f 0 = some x) (hshift : ∀ i : Fin m, f i.succ = g i.castSucc) :
    IsStackShape f (x :: L) := by
  -- peel the new bottom cell (`some x`) of `ofFn f` via `ofFn_succ`
  rw [IsStackShape, List.ofFn_succ (f := f), hbot]
  -- the shifted column `f ∘ succ = g ∘ castSucc` is stack-shaped for `L` (drop-top)
  have hfc : (fun i : Fin m => f i.succ) = (fun i : Fin m => g i.castSucc) := by
    funext i; exact hshift i
  rw [hfc, hg.castSucc hlt]
  -- assemble: `some x :: (L.map some ++ replicate (m-|L|) none) = (x::L).map some ++ replicate …`
  rw [List.map_cons, List.cons_append, List.length_cons,
    show m + 1 - (L.length + 1) = m - L.length from by omega]

/-- **Pop, `ofFn` shape.** Over `Fin (m+1)` with `g` stack-shaped for `L`, a column `f` shifted
*down* (`f i.castSucc = g i.succ`) and capped with `none` at the top is stack-shaped for
`L.tail`. -/
theorem isStackShape_ofFn_pop {α : Type*} {m : ℕ} {f g : Fin (m + 1) → Option α} {L : List α}
    (hg : IsStackShape g L)
    (hshift : ∀ i : Fin m, f i.castSucc = g i.succ) (htop : f (Fin.last m) = none) :
    IsStackShape f L.tail := by
  -- peel the last cell (`none`) of `ofFn f` via `ofFn_succ'`
  rw [IsStackShape, List.ofFn_succ' (f := f), htop]
  -- the truncated column `f ∘ castSucc = g ∘ succ` is stack-shaped for `L.tail` (head-peel)
  have hfc : (fun i : Fin m => f i.castSucc) = (fun i : Fin m => g i.succ) := by
    funext i; exact hshift i
  rw [hfc, hg.succ]
  -- `|L| ≤ m+1` (the column has length `m+1`), so `|L.tail| ≤ m`
  have hlen : L.length ≤ m + 1 := by
    have := congrArg List.length hg
    simp only [List.length_ofFn, List.length_append, List.length_map, List.length_replicate] at this
    omega
  have htl : L.tail.length ≤ m := by rw [List.length_tail]; omega
  -- assemble: `(L.tail.map some ++ replicate (m-|L.tail|) none).concat none = … ++ replicate (…+1)`
  rw [List.concat_eq_append, List.append_assoc,
    show [none] = List.replicate 1 (none : Option α) from rfl, List.replicate_append_replicate,
    show m - L.tail.length + 1 = m + 1 - L.tail.length from by omega]

/-- **Push, `ofFn` shape, `S`-general.** For `f g : Fin S → Option α` with `g` stack-shaped for
`L` and `L.length < S`, a new bottom (`f 0 = some x`, given `0 < S`) plus a shift *up*
(`f ⟨i+1⟩ = g i`) is stack-shaped for `x :: L`. -/
theorem isStackShape_ofFn_push_gen {α : Type*} {S : ℕ} {f g : Fin S → Option α} {L : List α}
    {x : α} (hg : IsStackShape g L) (hlt : L.length < S)
    (hbot : ∀ h : 0 < S, f ⟨0, h⟩ = some x)
    (hshift : ∀ (i : Fin S) (hi : (i : ℕ) + 1 < S), f ⟨(i : ℕ) + 1, hi⟩ = g i) :
    IsStackShape f (x :: L) := by
  cases S with
  | zero => exact absurd hlt (by omega)
  | succ m =>
    refine isStackShape_ofFn_push hg hlt (hbot (Nat.succ_pos m)) (fun i => ?_)
    -- shift-up: new position `i.succ` carries the old value at `i.castSucc`
    have hi : ((i.castSucc : Fin (m + 1)) : ℕ) + 1 < m + 1 := by
      simp only [Fin.val_castSucc]; omega
    have hsh := hshift i.castSucc hi
    rw [show (⟨((i.castSucc : Fin (m + 1)) : ℕ) + 1, hi⟩ : Fin (m + 1)) = i.succ by
      apply Fin.ext; simp [Fin.val_succ, Fin.val_castSucc]] at hsh
    rw [hsh]

/-- **Pop, `ofFn` shape, `S`-general.** For `f g : Fin S → Option α` with `g` stack-shaped for
`L`, a shift *down* (`f i = g ⟨i+1⟩` for `i+1 < S`) capped with `none` at the top (`f i = none`
when `i+1 = S`) is stack-shaped for `L.tail`. -/
theorem isStackShape_ofFn_pop_gen {α : Type*} {S : ℕ} {f g : Fin S → Option α} {L : List α}
    (hg : IsStackShape g L)
    (hshift : ∀ (i : Fin S) (hi : (i : ℕ) + 1 < S), f i = g ⟨(i : ℕ) + 1, hi⟩)
    (htop : ∀ i : Fin S, (i : ℕ) + 1 = S → f i = none) :
    IsStackShape f L.tail := by
  cases S with
  | zero =>
    -- no positions: `ofFn g = []` forces `L = []`, and `[].tail = []`
    have hL : L = [] := by
      have := hg; rw [IsStackShape, List.ofFn_zero] at this
      simpa using (List.append_eq_nil_iff.1 this.symm).1
    rw [hL]; rw [IsStackShape, List.ofFn_zero]; simp
  | succ m =>
    refine isStackShape_ofFn_pop hg (fun i => ?_) ?_
    · -- shift-down at lower position `i.castSucc`, landing at `i.succ`
      have hi : ((i.castSucc : Fin (m + 1)) : ℕ) + 1 < m + 1 := by
        simp only [Fin.val_castSucc]; omega
      rw [hshift i.castSucc hi,
        show (⟨((i.castSucc : Fin (m + 1)) : ℕ) + 1, hi⟩ : Fin (m + 1)) = i.succ by
          apply Fin.ext; simp [Fin.val_succ, Fin.val_castSucc]]
    · exact htop (Fin.last m) (by simp [Fin.val_last])

/-! ## (1) Per-gadget `IsStackShape` preservation -/

/-- **Keep preserves `IsStackShape`.** Under consistency, satisfying the keep clauses keeps the
time-`t` stack shape (for the same `L`) at `t+1` (the cell column is unchanged). -/
theorem keepCell_isStackShape {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} (hsat : satisfiesAll assign (keepCellClauses (S := S) t k))
    {L : List (tm.Γ k)}
    (hsh : IsStackShape (fun i : Fin S => readCell assign (Fin.castSucc t) k i) L) :
    IsStackShape (fun i : Fin S => readCell assign (Fin.succ t) k i) L := by
  -- the time-`t+1` cell column equals the time-`t` one (per-position keep), so the shape carries
  have hcell : (fun i : Fin S => readCell assign (Fin.succ t) k i)
      = (fun i : Fin S => readCell assign (Fin.castSucc t) k i) := by
    funext i; exact keepCell_readCell hcons hsat i
  rw [hcell]; exact hsh

/-- **Push preserves `IsStackShape`.** Under consistency, with the time-`t` stack shape and room
(`L.length < S`), satisfying the push clauses makes the time-`t+1` column stack-shaped for
`f (state@t) :: L`. -/
theorem pushCell_isStackShape {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} {f : tm.σ → tm.Γ k}
    (hsat : satisfiesAll assign (pushCellClauses (S := S) t k f)) {L : List (tm.Γ k)}
    (hsh : IsStackShape (fun i : Fin S => readCell assign (Fin.castSucc t) k i) L)
    (hlen : L.length < S) :
    IsStackShape (fun i : Fin S => readCell assign (Fin.succ t) k i)
      (f (readState assign (Fin.castSucc t)) :: L) :=
  isStackShape_ofFn_push_gen hsh hlen
    (fun h0 => pushCell_readCell_bottom hcons hsat h0)
    (fun i hi => pushCell_readCell_shift hcons hsat i hi)

/-- **Pop preserves `IsStackShape`.** Under consistency, with the time-`t` stack shape,
satisfying the pop clauses makes the time-`t+1` column stack-shaped for `L.tail`. -/
theorem popCell_isStackShape {assign : Fin (numVars tm T S) → Bool} (hcons : Consistent assign)
    {t : Fin T} {k : tm.K} (hsat : satisfiesAll assign (popCellClauses (S := S) t k))
    {L : List (tm.Γ k)}
    (hsh : IsStackShape (fun i : Fin S => readCell assign (Fin.castSucc t) k i) L) :
    IsStackShape (fun i : Fin S => readCell assign (Fin.succ t) k i) L.tail :=
  isStackShape_ofFn_pop_gen hsh
    (fun i hi => popCell_readCell_shift hcons hsat i hi)
    (fun i hi => popCell_readCell_top hcons hsat i (by omega))

end TableauSchema

/-! ## (2) The combined-space propagation -/

namespace CombinedTableau

open TableauSchema OneHotRegister BooleanConstraints ReachableCont UnifSmallStep
open Turing.TM2 Turing.TM2.Stmt

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

open scoped Classical

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **`IsStackShape` propagation.** Under full consistency, with every stack in stack shape and
fitting (`length < S`) at the time-`t` cells, the cell-transition clauses force, for *every*
stack `k'`, the time-`t+1` cell column to be in stack shape — for the list `readStack (t+1) k'`.
So the none-terminated-prefix invariant is self-perpetuating across one time step. -/
theorem isStackShape_propagate {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {t : Fin T}
    (h : satisfiesAll assign (cellTransClauses tm S t))
    (hsh : ∀ k, IsStackShape (fun i : Fin S => readCell (mainAssign assign) (Fin.castSucc t) k i)
      (readStack (mainAssign assign) (Fin.castSucc t) k))
    (hlen : ∀ k, (readStack (mainAssign assign) (Fin.castSucc t) k).length < S) (k' : tm.K) :
    IsStackShape (fun i : Fin S => readCell (mainAssign assign) (Fin.succ t) k' i)
      (readStack (mainAssign assign) (Fin.succ t) k') := by
  -- the main block is consistent and the active gadget holds on it
  have hmaincons : Consistent (mainAssign assign) := ((fullConsistent_iff assign).1 hcons).1
  have hgad := satisfiesAll_cellGadgetFor_active hcons h
  -- case on the active continuation token and its head statement; mirror `cellTransClauses_spec`
  set cont₀ := readContC assign (Fin.castSucc t) with hcont₀
  clear hcont₀
  match cont₀, hgad with
  | none, hgad =>
    rw [cellGadgetFor] at hgad
    have hkeep := satisfiesAll_keepCellClauses_of_univ hgad k'
    rw [keepCell_readStack hmaincons hkeep]
    exact keepCell_isStackShape hmaincons hkeep (hsh k')
  | some ⟨push k f q', hq⟩, hgad =>
    rw [cellGadgetFor, satisfiesAll_append] at hgad
    by_cases hk : k' = k
    · subst hk
      rw [pushCell_readStack hmaincons hgad.1 (hsh k') (hlen k')]
      exact pushCell_isStackShape hmaincons hgad.1 (hsh k') (hlen k')
    · have hkeep := satisfiesAll_keepCellClauses_of_erase hgad.2 hk
      rw [keepCell_readStack hmaincons hkeep]
      exact keepCell_isStackShape hmaincons hkeep (hsh k')
  | some ⟨pop k f q', hq⟩, hgad =>
    rw [cellGadgetFor, satisfiesAll_append] at hgad
    by_cases hk : k' = k
    · subst hk
      rw [popCell_readStack hmaincons hgad.1 (hsh k')]
      exact popCell_isStackShape hmaincons hgad.1 (hsh k')
    · have hkeep := satisfiesAll_keepCellClauses_of_erase hgad.2 hk
      rw [keepCell_readStack hmaincons hkeep]
      exact keepCell_isStackShape hmaincons hkeep (hsh k')
  | some ⟨peek k f q', hq⟩, hgad =>
    rw [cellGadgetFor] at hgad
    have hkeep := satisfiesAll_keepCellClauses_of_univ hgad k'
    rw [keepCell_readStack hmaincons hkeep]
    exact keepCell_isStackShape hmaincons hkeep (hsh k')
  | some ⟨load a q', hq⟩, hgad =>
    rw [cellGadgetFor] at hgad
    have hkeep := satisfiesAll_keepCellClauses_of_univ hgad k'
    rw [keepCell_readStack hmaincons hkeep]
    exact keepCell_isStackShape hmaincons hkeep (hsh k')
  | some ⟨branch g q₁ q₂, hq⟩, hgad =>
    rw [cellGadgetFor] at hgad
    have hkeep := satisfiesAll_keepCellClauses_of_univ hgad k'
    rw [keepCell_readStack hmaincons hkeep]
    exact keepCell_isStackShape hmaincons hkeep (hsh k')
  | some ⟨goto g, hq⟩, hgad =>
    rw [cellGadgetFor] at hgad
    have hkeep := satisfiesAll_keepCellClauses_of_univ hgad k'
    rw [keepCell_readStack hmaincons hkeep]
    exact keepCell_isStackShape hmaincons hkeep (hsh k')
  | some ⟨halt, hq⟩, hgad =>
    rw [cellGadgetFor] at hgad
    have hkeep := satisfiesAll_keepCellClauses_of_univ hgad k'
    rw [keepCell_readStack hmaincons hkeep]
    exact keepCell_isStackShape hmaincons hkeep (hsh k')

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- The cell-transition clauses propagate the stack-shape invariant one step in time.
example {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {t : Fin T}
    (h : satisfiesAll assign (cellTransClauses tm S t))
    (hsh : ∀ k, IsStackShape (fun i : Fin S => readCell (mainAssign assign) (Fin.castSucc t) k i)
      (readStack (mainAssign assign) (Fin.castSucc t) k))
    (hlen : ∀ k, (readStack (mainAssign assign) (Fin.castSucc t) k).length < S) (k' : tm.K) :
    IsStackShape (fun i : Fin S => readCell (mainAssign assign) (Fin.succ t) k' i)
      (readStack (mainAssign assign) (Fin.succ t) k') :=
  isStackShape_propagate hcons h hsh hlen k'

end Examples

end CombinedTableau

end DeepWiki
