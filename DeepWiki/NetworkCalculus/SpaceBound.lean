import DeepWiki.NetworkCalculus.MultiStepDecode
import DeepWiki.NetworkCalculus.CombinedInit

/-!
# Space-bounded multi-step decode: discharging `lenOk` by a joint space-bound induction

Layer 3c-v: the **space-bounded decode**.  The multi-step decode `readUnif_iterate`
(`MultiStepDecode`) consumes a *standalone* per-time room hypothesis
`(readStack … t k).length < S` at every time.  Here that hypothesis is **discharged**
by a joint induction with a linear space bound: each `unifStep` grows any one stack by
at most one cell (`unifStep_stack_length_le`), so along the decode the stack length at
time `t` is bounded by `initStk_k + t`.  With `S > initStk_k + T` (the `S ≥ init + T`
poly-size condition `hSpace`), this dominates `< S` at every reachable time, so the
decode holds with **no** `lenOk` hypothesis — only the structural `hSpace`.

* `unifStep_stack_length_le` — model length lemma: one `unifStep` grows a stack by `≤ 1`.
* `readUnif_iterate_spaceBounded` — joint `ℕ`-indexed induction carrying decode + stack
  shape + length bound `len@n ≤ initStk_k + n`, deriving `lenOk@n` internally from `hSpace`.
* `readUnif_last_spaceBounded` — the `Fin.last` corollary, with NO `lenOk` hypothesis.

## Deferred

This is the `lenOk`-discharge **only**.  The accept clauses, the full formula assembly
(consistency + init + transitions + accept as one `CnfFormula`), `Satisfiable ⟺ accepts`,
poly-size, verifier/certificate encoding, and the final `cookLevin` discharge are
**later** layers.
-/

open Turing Function

namespace DeepWiki

namespace CombinedTableau

open TableauSchema OneHotRegister BooleanConstraints ReachableCont UnifSmallStep
open Turing.TM2 Turing.TM2.Stmt

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

/-! ## (1) Model length lemma -/

/-- **Model length lemma.** A single `unifStep` grows any one stack by at most one cell:
`((unifStep M st).2.2 k).length ≤ (st.2.2 k).length + 1`.  By `cases` on the continuation
`st.1`: `push` prepends (length `+1`, via `update_self`/`List.length_cons`), `pop` takes
the tail (length `≤`, via `List.length_tail` and `update_self`/`update_of_ne`), every other
constructor leaves the stacks unchanged (`= S k ≤ +1`). -/
theorem unifStep_stack_length_le {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) (st : UnifSmallStep.UnifState Γ Λ σ) (k : K) :
    ((unifStep M st).2.2 k).length ≤ (st.2.2 k).length + 1 := by
  obtain ⟨cont, v, Stk⟩ := st
  match cont with
  | none => simp [unifStep]
  | some (push k' f q') =>
    simp only [unifStep]
    by_cases hk : k = k'
    · subst hk; rw [update_self]; simp [List.length_cons]
    · rw [update_of_ne hk]; exact Nat.le_succ _
  | some (peek k' f q') => simp [unifStep]
  | some (pop k' f q') =>
    simp only [unifStep]
    by_cases hk : k = k'
    · subst hk; rw [update_self, List.length_tail]; omega
    · rw [update_of_ne hk]; exact Nat.le_succ _
  | some (load a q') => simp [unifStep]
  | some (branch f q₁ q₂) => simp [unifStep]
  | some (goto f) => simp [unifStep]
  | some Turing.TM2.Stmt.halt => simp [unifStep]

/-! ## (2) The joint space-bounded decode -/

/-- The stack length at time `t`: `(readStack (mainAssign assign) t k).length`. -/
noncomputable def lenAt (assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool)
    (t : Fin (T + 1)) (k : tm.K) : ℕ :=
  (readStack (mainAssign assign) t k).length

/-- **Joint space-bounded decode (`ℕ`-indexed).**  Carrying the decode equality, the stack
shape, AND the length bound `len@n ≤ initStk_k + n` as a single three-way induction, the
length bound combined with the space bound `hSpace : initStk_k + T < S` discharges the room
hypothesis `lenOk@n` (`len < S`) internally at each step, feeding it into `step_decode`.  So
for every `n ≤ T` the readback at time `n` is the `n`-fold `unifStep` of the readback at time
`0`, the stack shape holds at `n`, and `len@n ≤ initStk_k + n` — with NO standalone `lenOk`
hypothesis.  The length branch at `n+1` uses the just-established decode equation to rewrite
`readUnif@(n+1)` and `unifStep_stack_length_le`. -/
theorem readUnif_iterate_spaceBounded
    {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {hS0 : 0 < S}
    (htrans : ∀ t : Fin T, satisfiesAll assign (unifTransClauses tm S t hS0))
    (hinit_unif : readUnif assign (0 : Fin (T + 1)) = unifOfCfg tm (initList tm input))
    (hinit_shape : ∀ k, IsStackShape
      (fun i : Fin S => readCell (mainAssign assign) (⟨0, by omega⟩ : Fin (T + 1)) k i)
      (readStack (mainAssign assign) (⟨0, by omega⟩ : Fin (T + 1)) k))
    (hSpace : ∀ k, ((initList tm input).stk k).length + T < S) :
    ∀ (n : ℕ), (hn : n ≤ T) →
      (readUnif assign ⟨n, by omega⟩ =
        (unifStep tm.m)^[n] (readUnif assign ⟨0, by omega⟩)) ∧
      (∀ k, IsStackShape (fun i : Fin S => readCell (mainAssign assign) ⟨n, by omega⟩ k i)
        (readStack (mainAssign assign) ⟨n, by omega⟩ k)) ∧
      (∀ k, lenAt assign ⟨n, by omega⟩ k ≤ ((initList tm input).stk k).length + n) := by
  -- `readStack … 0 k = (initList …).stk k`, from the stacks component of `hinit_unif`.
  have hstk0 : ∀ k, readStack (mainAssign assign) (⟨0, by omega⟩ : Fin (T + 1)) k
      = (initList tm input).stk k := by
    intro k
    have h := congrArg (fun st => st.2.2 k) hinit_unif
    rw [readUnif_snd_snd] at h
    rw [unifOfCfg_eq] at h
    simpa using h
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨by rw [Function.iterate_zero, id_eq], hinit_shape, fun k => ?_⟩
    -- length at `0` is exactly the initial stack length: `≤ initStk_k + 0`.
    show lenAt assign ⟨0, by omega⟩ k ≤ ((initList tm input).stk k).length + 0
    rw [lenAt, hstk0 k]; omega
  | succ m ih =>
    intro hle
    have hmlt : m < T := by omega
    obtain ⟨iheq, ihsh, ihlen⟩ := ih (by omega)
    -- Recast `castSucc`/`succ` of `⟨m, _⟩ : Fin T` to the plain `Fin (T+1)` indices.
    have hcs : (⟨m, hmlt⟩ : Fin T).castSucc = (⟨m, by omega⟩ : Fin (T + 1)) :=
      castSucc_mk_eq hmlt (by omega)
    have hsc : (⟨m, hmlt⟩ : Fin T).succ = (⟨m + 1, by omega⟩ : Fin (T + 1)) :=
      succ_mk_eq hmlt (by omega)
    -- The IH stack shape at `t.castSucc = ⟨m, _⟩`.
    have hshcs : ∀ k, IsStackShape
        (fun i : Fin S => readCell (mainAssign assign) (⟨m, hmlt⟩ : Fin T).castSucc k i)
        (readStack (mainAssign assign) (⟨m, hmlt⟩ : Fin T).castSucc k) := by
      rw [hcs]; exact ihsh
    -- DISCHARGE `lenOk@⟨m,_⟩`: `len ≤ initStk_k + m ≤ initStk_k + T < S`.
    have hlencs : ∀ k,
        (readStack (mainAssign assign) (⟨m, hmlt⟩ : Fin T).castSucc k).length < S := by
      intro k
      rw [hcs]
      have h1 : lenAt assign (⟨m, by omega⟩ : Fin (T + 1)) k
          ≤ ((initList tm input).stk k).length + m := ihlen k
      have h2 : ((initList tm input).stk k).length + T < S := hSpace k
      have : lenAt assign (⟨m, by omega⟩ : Fin (T + 1)) k < S := by omega
      simpa [lenAt] using this
    -- Single joint step (decode + shape) at `t := ⟨m, _⟩`.
    obtain ⟨steq, stsh⟩ := step_decode hcons (htrans ⟨m, hmlt⟩) hshcs hlencs
    rw [hsc, hcs] at steq
    rw [hsc] at stsh
    refine ⟨?_, stsh, fun k => ?_⟩
    · -- decode@(m+1): compose the step equation with the IH and `iterate_succ_apply'`.
      rw [steq, iheq, Function.iterate_succ_apply']
    · -- length@(m+1): `len@(m+1) = ((unifStep (readUnif@m)).2.2 k).length ≤ len@m + 1 ≤ …`.
      show lenAt assign (⟨m + 1, by omega⟩ : Fin (T + 1)) k
        ≤ ((initList tm input).stk k).length + (m + 1)
      have hlenstep :
          lenAt assign (⟨m + 1, by omega⟩ : Fin (T + 1)) k
            = ((unifStep tm.m (readUnif assign (⟨m, by omega⟩ : Fin (T + 1)))).2.2 k).length := by
        rw [lenAt]
        have hrw : readStack (mainAssign assign) (⟨m + 1, by omega⟩ : Fin (T + 1)) k
            = (readUnif assign (⟨m + 1, by omega⟩ : Fin (T + 1))).2.2 k := by
          rw [readUnif_snd_snd]
        rw [hrw, steq]
      rw [hlenstep]
      calc ((unifStep tm.m (readUnif assign (⟨m, by omega⟩ : Fin (T + 1)))).2.2 k).length
          ≤ ((readUnif assign (⟨m, by omega⟩ : Fin (T + 1))).2.2 k).length + 1 :=
            unifStep_stack_length_le tm.m _ k
        _ = lenAt assign (⟨m, by omega⟩ : Fin (T + 1)) k + 1 := by
            rw [lenAt, readUnif_snd_snd]
        _ ≤ (((initList tm input).stk k).length + m) + 1 := by
            have := ihlen k; omega
        _ = ((initList tm input).stk k).length + (m + 1) := by omega

/-- **Space-bounded decode at `Fin.last`.**  Instantiating `readUnif_iterate_spaceBounded`
at `n = T`: with only the structural space bound `hSpace : initStk_k + T < S` (no standalone
`lenOk` hypothesis), the readback at the final time is the `T`-fold `unifStep` of the initial
readback. -/
theorem readUnif_last_spaceBounded
    {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {hS0 : 0 < S}
    (htrans : ∀ t : Fin T, satisfiesAll assign (unifTransClauses tm S t hS0))
    (hinit_unif : readUnif assign (0 : Fin (T + 1)) = unifOfCfg tm (initList tm input))
    (hinit_shape : ∀ k, IsStackShape
      (fun i : Fin S => readCell (mainAssign assign) (⟨0, by omega⟩ : Fin (T + 1)) k i)
      (readStack (mainAssign assign) (⟨0, by omega⟩ : Fin (T + 1)) k))
    (hSpace : ∀ k, ((initList tm input).stk k).length + T < S) :
    readUnif assign (Fin.last T) =
      (unifStep tm.m)^[T] (readUnif assign 0) := by
  have h := (readUnif_iterate_spaceBounded hcons (hS0 := hS0) htrans
    hinit_unif hinit_shape hSpace T le_rfl).1
  rw [show (Fin.last T) = (⟨T, by omega⟩ : Fin (T + 1)) from rfl,
    show (0 : Fin (T + 1)) = (⟨0, by omega⟩ : Fin (T + 1)) from rfl]
  exact h

/-! ## Sanity restatement (intent check against the design) -/

section Examples

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- The final readback is the `T`-fold uniform step of the initial readback, derived from
-- the structural space bound alone (no standalone `lenOk` hypothesis).
example {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {hS0 : 0 < S}
    (htrans : ∀ t : Fin T, satisfiesAll assign (unifTransClauses tm S t hS0))
    (hinit_unif : readUnif assign (0 : Fin (T + 1)) = unifOfCfg tm (initList tm input))
    (hinit_shape : ∀ k, IsStackShape
      (fun i : Fin S => readCell (mainAssign assign) (⟨0, by omega⟩ : Fin (T + 1)) k i)
      (readStack (mainAssign assign) (⟨0, by omega⟩ : Fin (T + 1)) k))
    (hSpace : ∀ k, ((initList tm input).stk k).length + T < S) :
    readUnif assign (Fin.last T) =
      (unifStep tm.m)^[T] (readUnif assign 0) :=
  readUnif_last_spaceBounded hcons (hS0 := hS0) htrans hinit_unif hinit_shape hSpace

end Examples

end CombinedTableau

end DeepWiki
