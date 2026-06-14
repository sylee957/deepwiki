import Book.SchedulerSemantics
import Book.ServersWrr

/-! # WRR as an imperative program, and its soundness
Algorithm 2 (WRR) written in the operational-semantics framework: the
inner send loop `wrrInner` (lines 4-7), the per-flow turn `wrrTurn`
(lines 3-7, `k ← 1` then the loop), and one round `wrrRound` (the
`for` over flows). The soundness theorems pin the big-step execution to
the functional model `wrrServe` of `Book.ServersWrr` — a turn drops the
first `w` packets of flow `i`'s queue, leaving every other flow
untouched. `wrrServe` is the per-step building block of the `IsWrr`
round-count coupling derived at the curve level in
`Book.ServersResidualWrr`; the rounds-to-continuous-time bridge (`IsWrr`'s
abstraction boundary) and the output trace are not formalized here. -/

namespace DeepWiki

open scoped Classical NNReal

/-- The WRR inner-loop body (lines 5-6): `send(head(i)); removeHead(i)`
then `k ← k + 1`. -/
def wrrInnerBody {n : ℕ} (i : Fin n) : Stmt n := .seq (.serveHead i) .incK

/-- The WRR inner loop (lines 4-7): send head packets while the queue is
non-empty and the weight counter has not been spent. -/
def wrrInner {n : ℕ} (w : ℕ) (i : Fin n) : Stmt n :=
  .whileB (.and (.notEmpty i) (.kLe w)) (wrrInnerBody i)

/-- The WRR per-flow turn (lines 3-7): reset the counter to `1`, then run
the send loop. -/
def wrrTurn {n : ℕ} (w : ℕ) (i : Fin n) : Stmt n := .seq (.setK 1) (wrrInner w i)

variable {n : ℕ}

/-- On an empty queue the WRR guard is false. -/
theorem wrrGuard_eval_nil (w : ℕ) (i : Fin n) (σ : SchedState n)
    (hq : σ.queue i = []) :
    (BExp.and (BExp.notEmpty i) (BExp.kLe w)).eval σ = false := by
  simp [BExp.eval, hq]

/-- On a non-empty queue the WRR guard is the weight test `k ≤ w`. -/
theorem wrrGuard_eval_cons (w : ℕ) (i : Fin n) (σ : SchedState n) {p : ℝ≥0}
    {ps : List ℝ≥0} (hq : σ.queue i = p :: ps) :
    (BExp.and (BExp.notEmpty i) (BExp.kLe w)).eval σ = decide (σ.kvar ≤ w) := by
  simp [BExp.eval, hq]

/-- **Inner-loop soundness**: the WRR send loop drops from flow `i`'s
queue the `w + 1 − k` packets the weight counter `k` still allows
(saturating at the queue length), leaving the deficit counters untouched. -/
theorem bigStep_wrrInner (w : ℕ) (i : Fin n) {σ σ' : SchedState n}
    (h : BigStep (wrrInner w i) σ σ') :
    σ'.queue = Function.update σ.queue i ((σ.queue i).drop (w + 1 - σ.kvar))
      ∧ σ'.dc = σ.dc := by
  suffices H : ∀ (q : List ℝ≥0) (a a' : SchedState n), a.queue i = q →
      BigStep (wrrInner w i) a a' →
      a'.queue = Function.update a.queue i (q.drop (w + 1 - a.kvar))
        ∧ a'.dc = a.dc from H (σ.queue i) σ σ' rfl h
  intro q
  induction q with
  | nil =>
    intro a a' hq h
    rw [wrrInner, bigStep_whileB_iff] at h
    rcases h with ⟨_, heq⟩ | ⟨hc, _⟩
    · rw [heq]
      refine ⟨?_, rfl⟩
      rw [List.drop_nil, ← hq]; exact (Function.update_eq_self _ _).symm
    · rw [wrrGuard_eval_nil w i a hq] at hc; exact absurd hc (by simp)
  | cons p ps ih =>
    intro a a' hq h
    rw [wrrInner, bigStep_whileB_iff] at h
    rcases h with ⟨hc, heq⟩ | ⟨hc, σm, hbody, hrest⟩
    · -- guard false: the counter is spent, no send
      rw [wrrGuard_eval_cons w i a hq] at hc
      rw [heq]
      refine ⟨?_, rfl⟩
      have hkw : ¬ a.kvar ≤ w := of_decide_eq_false hc
      have hz : w + 1 - a.kvar = 0 := by omega
      rw [hz, List.drop_zero, ← hq]
      exact (Function.update_eq_self _ _).symm
    · -- guard true: send the head, increment, and recurse
      have hkw : a.kvar ≤ w :=
        of_decide_eq_true (by rw [← wrrGuard_eval_cons w i a hq]; exact hc)
      obtain ⟨σ1, h1, h2⟩ := bigStep_seq_iff.mp hbody
      rw [bigStep_serveHead_iff] at h1
      rw [bigStep_incK_iff] at h2
      have hσmq : σm.queue = Function.update a.queue i ps := by
        rw [h2]
        simp only [SchedState.setK_queue, h1, SchedState.setQueue_queue,
          SchedState.emit_queue]
        rw [hq, List.tail_cons]
      have hσmk : σm.kvar = a.kvar + 1 := by
        rw [h2]
        simp only [SchedState.setK_kvar, h1, SchedState.setQueue_kvar,
          SchedState.emit_kvar]
      have hσmdc : σm.dc = a.dc := by
        rw [h2]
        simp only [SchedState.setK_dc, h1, SchedState.setQueue_dc,
          SchedState.emit_dc]
      have hσmqi : σm.queue i = ps := by rw [hσmq, Function.update_self]
      obtain ⟨ihq, ihdc⟩ := ih σm a' hσmqi hrest
      refine ⟨?_, ?_⟩
      · rw [ihq, hσmq, hσmk, Function.update_idem]
        have e1 : w + 1 - (a.kvar + 1) = w - a.kvar := by omega
        have e2 : w + 1 - a.kvar = (w - a.kvar) + 1 := by omega
        rw [e1, e2, List.drop_succ_cons]
      · rw [ihdc, hσmdc]

/-- **Per-turn soundness**: the big-step execution of `wrrTurn w i` drops
the first `w` packets of flow `i`'s queue — exactly `(wrrServe w …).2` —
leaving the deficit counters untouched. The WRR program realizes the
functional model. -/
theorem bigStep_wrrTurn (w : ℕ) (i : Fin n) {σ σ' : SchedState n}
    (h : BigStep (wrrTurn w i) σ σ') :
    σ'.queue = Function.update σ.queue i ((σ.queue i).drop w) ∧ σ'.dc = σ.dc := by
  obtain ⟨σ1, h1, h2⟩ := bigStep_seq_iff.mp h
  rw [bigStep_setK_iff] at h1
  subst h1
  obtain ⟨hq, hdc⟩ := bigStep_wrrInner w i h2
  simp only [SchedState.setK_queue, SchedState.setK_dc, SchedState.setK_kvar]
    at hq hdc
  rw [Nat.add_sub_cancel] at hq
  exact ⟨hq, hdc⟩

/-- One WRR round (the `for` over flows): run every flow's turn once,
with its own weight `w i`. -/
def wrrRound (w : Fin n → ℕ) : Stmt n := roundStmt (fun i => wrrTurn (w i) i)

/-- **Round soundness**: one WRR round drops the first `w i` packets of
each flow `i`'s queue independently — turn `i` touches only flow `i`. -/
theorem bigStep_wrrRound (w : Fin n → ℕ) {σ σ' : SchedState n}
    (h : BigStep (wrrRound w) σ σ') (j : Fin n) :
    σ'.queue j = (σ.queue j).drop (w j) := by
  suffices H : ∀ (L : List (Fin n)), L.Nodup → ∀ {a a' : SchedState n},
      BigStep (L.foldr (fun i s => Stmt.seq (wrrTurn (w i) i) s) Stmt.skip) a a' →
      (∀ k ∈ L, a'.queue k = (a.queue k).drop (w k))
        ∧ (∀ k, k ∉ L → a'.queue k = a.queue k) by
    exact (H (List.finRange n) (List.nodup_finRange n) h).1 j (List.mem_finRange j)
  intro L
  induction L with
  | nil =>
    intro _ a a' h
    rw [List.foldr_nil, bigStep_skip_iff] at h
    subst h
    exact ⟨fun k hk => by simp at hk, fun k _ => rfl⟩
  | cons i rest ih =>
    intro hnd a a' h
    rw [List.foldr_cons, bigStep_seq_iff] at h
    obtain ⟨σm, hturn, hfold⟩ := h
    obtain ⟨hmq, _⟩ := bigStep_wrrTurn (w i) i hturn
    rw [List.nodup_cons] at hnd
    obtain ⟨hinotmem, hndrest⟩ := hnd
    obtain ⟨ihserved, ihframe⟩ := ih hndrest hfold
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [List.mem_cons] at hk
      rcases hk with rfl | hkrest
      · rw [ihframe k hinotmem, hmq, Function.update_self]
      · have hki : k ≠ i := fun he => hinotmem (he ▸ hkrest)
        rw [ihserved k hkrest, hmq, Function.update_of_ne hki]
    · rw [List.mem_cons, not_or] at hk
      obtain ⟨hkne, hkrest⟩ := hk
      rw [ihframe k hkrest, hmq, Function.update_of_ne hkne]

/-! ## Book restatement (WRR as an imperative program)
Running Algorithm 2's per-flow turn `wrrTurn w i` leaves flow `i`'s queue
as `wrrServe`'s — the first `w` packets sent, the rest retained
(`bigStep_wrrTurn`); one round `wrrRound` does so for every flow
(`bigStep_wrrRound`). So the operational semantics and the functional
model agree, and the per-step basis of the `IsWrr` round-count coupling
(`Book.ServersResidualWrr`) is realized by the genuine imperative
program. -/
example (w : ℕ) (i : Fin n) {σ σ' : SchedState n}
    (h : BigStep (wrrTurn w i) σ σ') :
    σ'.queue i = (wrrServe w (σ.queue i)).2 := by
  obtain ⟨hq, _⟩ := bigStep_wrrTurn w i h
  rw [hq, Function.update_self, wrrServe_snd]

end DeepWiki
