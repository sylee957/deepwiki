import DeepWiki.NetworkCalculus.TableauReadback
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.ReduceOption

/-!
# Tableau stack reconstruction, config readback, and the init clauses

Layer 3b-ii of a Cook- and Levin-style formalization: the **full-stack reconstruction** of a
Boolean assignment back into a `Turing.FinTM2` configuration, and the **init clause family**
pinning the time-`0` configuration to `Turing.FinTM2.initList`.

* `readStack assign t k` — the stack `k` at time `t`, reconstructed from the per-cell
  `readCell` over the position axis `Fin S` via `List.reduceOption ∘ List.ofFn`.
* `readStack_encodeSeq` — **the crux round-trip**: with `((cfgs t).stk k).length ≤ S`,
  reconstructing the encoding of a real sequence recovers the stack. The genuine work is the
  `List` lemma `ofFn_getElem?_eq` (`List.ofFn` of `getElem?` over `Fin S` = `map some ++
  replicate none` when `length ≤ S`) plus the `reduceOption` recovery.
* `readConfig assign t` — the full configuration read (`l`, `var`, `stk`); its round-trip
  `readConfig_encodeSeq` follows from the three component round-trips.
* `initClauses tm T S input` — unit clauses pinning the time-`0` configuration to
  `initList tm input`; `initClauses_spec` reads it back, and `encodeSeq_satisfies_initClauses`
  is the converse for a sequence starting at `initList tm input`.

## Deferred

The **accept** and **transition** clause families (the latter needs a halt-padding decision and
`Turing.TM2.step` semantics) and the reduction's correctness are **later** chunks. Only stack
reconstruction, the config readback, its round-trip, and the init clauses live here.
-/

open Turing

namespace DeepWiki

namespace TableauSchema

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

open BooleanConstraints

variable {tm : FinTM2} {T S : ℕ} [∀ k, Fintype (tm.Γ k)]

/-! ## (0) The crux `List` lemma and its `reduceOption` recovery -/

/-- **The crux list lemma.** Over `Fin S` with `L.length ≤ S`, `List.ofFn` of `L`'s `getElem?`
is `L.map some` padded with `none`s: `L.map some ++ List.replicate (S - L.length) none`. -/
theorem ofFn_getElem?_eq {α : Type*} (L : List α) (S : ℕ) (hS : L.length ≤ S) :
    (List.ofFn (fun i : Fin S => L[(i : ℕ)]?)) =
      L.map some ++ List.replicate (S - L.length) none := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_map, List.length_replicate]
    omega
  · intro n h1 h2
    rw [List.getElem_ofFn]
    by_cases hn : n < L.length
    · rw [List.getElem_append_left (by simpa using hn)]
      simp [List.getElem?_eq_getElem hn]
    · rw [List.getElem_append_right (by simpa using hn)]
      simp only [List.getElem_replicate]
      rw [List.getElem?_eq_none (by omega)]

/-- `reduceOption` of `L.map some` recovers `L`. -/
theorem reduceOption_map_some {α : Type*} (L : List α) : (L.map some).reduceOption = L := by
  induction L with
  | nil => simp [List.reduceOption_nil]
  | cons hd tl ih => rw [List.map_cons, List.reduceOption_cons_of_some, ih]

/-- `reduceOption` of `L.map some ++ replicate none` recovers `L` (drops the `none` padding). -/
theorem reduceOption_map_some_append_replicate {α : Type*} (L : List α) (m : ℕ) :
    (L.map some ++ List.replicate m none).reduceOption = L := by
  rw [List.reduceOption_append, List.reduceOption_replicate_none, List.append_nil,
    reduceOption_map_some]

/-! ## (1) Stack reconstruction -/

/-- The **stack read** of an assignment at time `t`, stack `k`: the per-cell reads over the
position axis `Fin S`, with the `none`-padding above the stack top dropped (`reduceOption`). -/
noncomputable def readStack (assign : Fin (numVars tm T S) → Bool) (t : Fin (T + 1)) (k : tm.K) :
    List (tm.Γ k) :=
  (List.ofFn (fun i : Fin S => readCell assign t k i)).reduceOption

section Encode

variable [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

/-- **Stack round-trip (the crux).** With `((cfgs t).stk k).length ≤ S`, reconstructing the
encoding of a real configuration sequence recovers the whole stack. -/
theorem readStack_encodeSeq (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin (T + 1)) (k : tm.K)
    (hS : ((cfgs t).stk k).length ≤ S) :
    readStack (S := S) (encodeSeq cfgs) t k = (cfgs t).stk k := by
  -- the per-cell read along `Fin S` is exactly the stack's `getElem?`
  have hcell : (fun i : Fin S => readCell (encodeSeq (S := S) cfgs) t k i)
      = (fun i : Fin S => ((cfgs t).stk k)[(i : ℕ)]?) := by
    funext i; exact readCell_encodeSeq cfgs t k i
  rw [readStack, hcell, ofFn_getElem?_eq _ S hS, reduceOption_map_some_append_replicate]

end Encode

/-! ## (2) Configuration readback -/

/-- The **configuration read** of an assignment at time `t`: the label, internal state, and every
stack reconstructed from the per-slot/per-cell reads. -/
noncomputable def readConfig (assign : Fin (numVars tm T S) → Bool) (t : Fin (T + 1)) : tm.Cfg where
  l := readLabel assign t
  var := readState assign t
  stk k := readStack assign t k

section Encode

variable [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

/-- **Configuration round-trip.** With every stack of `cfgs t` fitting in `S`, reading back the
encoding of a real sequence recovers the whole configuration. -/
theorem readConfig_encodeSeq (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin (T + 1))
    (hS : ∀ k, ((cfgs t).stk k).length ≤ S) :
    readConfig (S := S) (encodeSeq cfgs) t = cfgs t := by
  -- `tm.Cfg` has no `@[ext]`; equate the three fields of the (structure-`mk`) `readConfig`
  show Turing.TM2.Cfg.mk (readLabel (encodeSeq cfgs) t) (readState (encodeSeq cfgs) t)
      (fun k => readStack (encodeSeq cfgs) t k) = cfgs t
  rw [readLabel_encodeSeq cfgs t, readState_encodeSeq cfgs t]
  have hstk : (fun k => readStack (S := S) (encodeSeq cfgs) t k) = (cfgs t).stk := by
    funext k; exact readStack_encodeSeq cfgs t k (hS k)
  rw [hstk]
  rfl

end Encode

/-! ## (3) Init clauses

The init clauses pin the time-`0` configuration to `initList tm input`: the label is
`some tm.main`, the internal state is `tm.initialState`, and each cell holds the input list's
`getElem?` value (so the input stack `k₀` is loaded, every other stack empty). Each is a unit
clause `[(coordVar …, true)]`. -/

variable (tm T S) in
/-- The **init clauses**: unit clauses pinning the time-`0` configuration to `initList tm input` —
label `some tm.main`, state `tm.initialState`, and every cell `((initList tm input).stk k)[i]?`. -/
noncomputable def initClauses (input : List (tm.Γ tm.k₀)) : List (Clause (numVars tm T S)) :=
  [(coordVar (labelCoord (0 : Fin (T + 1)) (some tm.main)), true)]
    :: [(coordVar (stateCoord (0 : Fin (T + 1)) tm.initialState), true)]
    :: ((Finset.univ : Finset tm.K).toList.flatMap
        (fun k => (Finset.univ : Finset (Fin S)).toList.map
          (fun i => [(coordVar
            (cellCoord (0 : Fin (T + 1)) k i (((initList tm input).stk k)[(i : ℕ)]?)), true)])))

/-- A unit clause `[(v, true)]` is satisfied iff `assign v = true`. -/
theorem unitClause_sat {n : ℕ} {assign : Fin n → Bool} {v : Fin n}
    (h : satisfiesAll assign [[(v, true)]]) : assign v = true := by
  have := h _ (List.mem_singleton.2 rfl)
  simpa only [CnfFormula.clauseSat, List.any_cons, List.any_nil, CnfFormula.litSat, Bool.or_false,
    beq_iff_eq] using this

/-- A satisfying assignment forces each cell coordinate of the init clauses to the `initList`
value at `(0, k, i)`. -/
theorem initClauses_cell_true {assign : Fin (numVars tm T S) → Bool} {input : List (tm.Γ tm.k₀)}
    (h : satisfiesAll assign (initClauses tm T S input)) (k : tm.K) (i : Fin S) :
    assign (coordVar (cellCoord (0 : Fin (T + 1)) k i (((initList tm input).stk k)[(i : ℕ)]?)))
      = true := by
  rw [initClauses, satisfiesAll_cons, satisfiesAll_cons] at h
  obtain ⟨_, _, hcells⟩ := h
  rw [List.flatMap_def, satisfiesAll_flatten] at hcells
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_exists_index] at hcells
  have hk := hcells _ k rfl
  simp only [satisfiesAll, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_exists_index] at hk
  have hi := hk _ i rfl
  exact unitClause_sat (by
    rw [satisfiesAll]; intro c hc; rw [List.mem_singleton] at hc; subst hc; exact hi)

section Encode

variable [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Init-clause correctness.** A consistent satisfying assignment reads its time-`0`
configuration back as `initList tm input`, provided the input fits in `S`. -/
theorem initClauses_spec {assign : Fin (numVars tm T S) → Bool} {input : List (tm.Γ tm.k₀)}
    (hsat : satisfiesAll assign (initClauses tm T S input)) (hcons : Consistent assign)
    (hSinit : input.length ≤ S) :
    readConfig assign (0 : Fin (T + 1)) = initList tm input := by
  -- the label and state unit clauses
  rw [initClauses, satisfiesAll_cons, satisfiesAll_cons] at hsat
  obtain ⟨hlabel, hstate, _⟩ := hsat
  have hl : assign (coordVar (labelCoord (0 : Fin (T + 1)) (some tm.main))) = true :=
    unitClause_sat (by rw [satisfiesAll]; intro c hc; rw [List.mem_singleton] at hc; subst hc
                       exact hlabel)
  have hs : assign (coordVar (stateCoord (0 : Fin (T + 1)) tm.initialState)) = true :=
    unitClause_sat (by rw [satisfiesAll]; intro c hc; rw [List.mem_singleton] at hc; subst hc
                       exact hstate)
  -- restore the full satisfaction for the cell extraction
  have hsat' : satisfiesAll assign (initClauses tm T S input) := by
    rw [initClauses, satisfiesAll_cons, satisfiesAll_cons]; exact ⟨hlabel, hstate, by assumption⟩
  -- per-stack length bound from the input bound (`initList` loads `input` on `k₀`, `[]` elsewhere)
  have hSk : ∀ k, ((initList tm input).stk k).length ≤ S := by
    intro k
    unfold initList
    dsimp only
    by_cases hk : k = tm.k₀
    · subst hk; simpa using hSinit
    · rw [dif_neg hk]; simp
  -- assemble the three readbacks: equate the three fields of the (structure-`mk`) `readConfig`
  show Turing.TM2.Cfg.mk (readLabel assign (0 : Fin (T + 1))) (readState assign (0 : Fin (T + 1)))
      (fun k => readStack assign (0 : Fin (T + 1)) k) = initList tm input
  rw [readLabel_eq hcons hl, readState_eq hcons hs]
  have hstk : (fun k => readStack (S := S) assign (0 : Fin (T + 1)) k)
      = (initList tm input).stk := by
    funext k
    -- reconstruct stack `k` from the per-cell readbacks forced by the init clauses
    have hcellread : (fun i : Fin S => readCell assign (0 : Fin (T + 1)) k i)
        = (fun i : Fin S => ((initList tm input).stk k)[(i : ℕ)]?) := by
      funext i
      exact readCell_eq hcons (initClauses_cell_true hsat' k i)
    rw [readStack, hcellread, ofFn_getElem?_eq _ S (hSk k),
      reduceOption_map_some_append_replicate]
  rw [hstk]
  -- the label and state fields of `initList` are `some tm.main` and `tm.initialState`
  rfl

/-- **Init-clause converse.** Encoding a sequence whose time-`0` configuration is
`initList tm input` satisfies the init clauses. -/
theorem encodeSeq_satisfies_initClauses (cfgs : Fin (T + 1) → tm.Cfg)
    (input : List (tm.Γ tm.k₀)) (h0 : cfgs (0 : Fin (T + 1)) = initList tm input) :
    satisfiesAll (encodeSeq (S := S) cfgs) (initClauses tm T S input) := by
  rw [initClauses, satisfiesAll_cons, satisfiesAll_cons]
  refine ⟨?_, ?_, ?_⟩
  · -- the label unit clause
    simp only [CnfFormula.clauseSat, List.any_cons, List.any_nil, CnfFormula.litSat, Bool.or_false,
      beq_iff_eq, encodeSeq_labelCoord, h0]
    simp [initList]
  · -- the state unit clause
    simp only [CnfFormula.clauseSat, List.any_cons, List.any_nil, CnfFormula.litSat, Bool.or_false,
      beq_iff_eq, encodeSeq_stateCoord, h0]
    simp [initList]
  · -- the cell unit clauses
    rw [List.flatMap_def, satisfiesAll_flatten]
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index]
    rintro g k rfl
    intro c hc
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hc
    obtain ⟨i, rfl⟩ := hc
    simp only [CnfFormula.clauseSat, List.any_cons, List.any_nil, CnfFormula.litSat, Bool.or_false,
      beq_iff_eq, encodeSeq_cellCoord, h0]

end Encode

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

variable [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- The config round-trip recovers the full configuration when every stack fits in `S`.
example (cfgs : Fin (T + 1) → tm.Cfg) (t : Fin (T + 1))
    (hS : ∀ k, ((cfgs t).stk k).length ≤ S) :
    readConfig (S := S) (encodeSeq cfgs) t = cfgs t :=
  readConfig_encodeSeq cfgs t hS

-- A consistent satisfying assignment reads its time-`0` configuration back as `initList`.
example {assign : Fin (numVars tm T S) → Bool} {input : List (tm.Γ tm.k₀)}
    (hsat : satisfiesAll assign (initClauses tm T S input)) (hcons : Consistent assign)
    (hSinit : input.length ≤ S) :
    readConfig assign (0 : Fin (T + 1)) = initList tm input :=
  initClauses_spec hsat hcons hSinit

end Examples

end TableauSchema

end DeepWiki
