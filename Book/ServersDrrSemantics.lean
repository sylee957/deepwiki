import Book.SchedulerSemantics

/-! # DRR as an imperative program, and its soundness
Algorithm 1 (DRR) written in the operational-semantics framework: the
inner drain loop `drrInner` (lines 7-10), the per-flow turn `drrTurn`
(lines 5-12), and one round `drrRound` (the `for i = 1 to n` pass). The
soundness theorems pin the big-step execution of these programs to the
functional models of `Book.ServersDrr` — `drrInner` realizes `drrDrain`
and `drrTurn` realizes `drrServe` on flow `i`'s counter and queue — so the
round-count bounds (`IsDrr`) carry over to the genuine imperative program.
-/

namespace DeepWiki

open scoped Classical NNReal

/-- The DRR inner-loop guard `(not empty(i)) ∧ (size(head(i)) ≤ DC[i])`. -/
def drrGuard {n : ℕ} (i : Fin n) : BExp n :=
  .and (.notEmpty i) (.le (.headSize i) (.dc i))

/-- The DRR inner-loop body (lines 8-10): decrement the counter by the
head size, then `send(head(i)); removeHead(i)`. -/
def drrInnerBody {n : ℕ} (i : Fin n) : Stmt n :=
  .seq (.assignDc i (.sub (.dc i) (.headSize i))) (.serveHead i)

/-- The DRR inner loop (lines 7-10): drain head packets while the
counter covers them. -/
def drrInner {n : ℕ} (i : Fin n) : Stmt n :=
  .whileB (drrGuard i) (drrInnerBody i)

/-- The DRR per-flow turn (lines 5-12): if non-empty, add the quantum,
drain, and reset the counter to zero if the queue empties. -/
def drrTurn {n : ℕ} (Q : ℝ≥0) (i : Fin n) : Stmt n :=
  .ifte (.notEmpty i)
    (.seq (.assignDc i (.add (.dc i) (.lit Q)))
      (.seq (drrInner i)
        (.ifte (.notEmpty i) .skip (.assignDc i (.lit 0)))))
    .skip

variable {n : ℕ}

/-- `headSize` ignores a counter update. -/
@[simp] theorem headSize_setDc (σ : SchedState n) (i j : Fin n) (d : ℝ≥0) :
    headSize (σ.setDc i d) j = headSize σ j := rfl

/-- On an empty queue the DRR guard is false. -/
theorem drrGuard_eval_nil (i : Fin n) (σ : SchedState n)
    (hq : σ.queue i = []) : (drrGuard i).eval σ = false := by
  simp [drrGuard, BExp.eval, AExp.eval, headSize, hq]

/-- On a non-empty queue the DRR guard is the head-fits test. -/
theorem drrGuard_eval_cons (i : Fin n) (σ : SchedState n) {p : ℝ≥0}
    {ps : List ℝ≥0} (hq : σ.queue i = p :: ps) :
    (drrGuard i).eval σ = decide (p ≤ σ.dc i) := by
  simp [drrGuard, BExp.eval, AExp.eval, headSize, hq]

/-- **Inner-loop soundness**: the big-step execution of `drrInner i`
updates flow `i`'s counter and queue exactly as `drrDrain` does (and
leaves every other flow and the loop counter untouched). -/
theorem bigStep_drrInner (i : Fin n) {σ σ' : SchedState n}
    (h : BigStep (drrInner i) σ σ') :
    σ'.dc = Function.update σ.dc i (drrDrain (σ.dc i) (σ.queue i)).1
      ∧ σ'.queue = Function.update σ.queue i (drrDrain (σ.dc i) (σ.queue i)).2
      ∧ σ'.kvar = σ.kvar := by
  -- induct on the queue at `i`, threaded through the state
  suffices H : ∀ (q : List ℝ≥0) (a a' : SchedState n), a.queue i = q →
      BigStep (drrInner i) a a' →
      a'.dc = Function.update a.dc i (drrDrain (a.dc i) q).1
        ∧ a'.queue = Function.update a.queue i (drrDrain (a.dc i) q).2
        ∧ a'.kvar = a.kvar from H (σ.queue i) σ σ' rfl h
  intro q
  induction q with
  | nil =>
    intro a a' hq h
    rw [drrInner, bigStep_whileB_iff] at h
    rcases h with ⟨_, heq⟩ | ⟨hc, _⟩
    · rw [heq]
      refine ⟨?_, ?_, rfl⟩
      · rw [drrDrain_nil]; exact (Function.update_eq_self _ _).symm
      · rw [drrDrain_nil, ← hq]; exact (Function.update_eq_self _ _).symm
    · rw [drrGuard_eval_nil i _ hq] at hc; exact absurd hc (by simp)
  | cons p ps ih =>
    intro a a' hq h
    rw [drrInner, bigStep_whileB_iff] at h
    rcases h with ⟨hc, heq⟩ | ⟨hc, σm, hbody, hrest⟩
    · -- guard false: the head does not fit, `drrDrain` stops
      rw [drrGuard_eval_cons i _ hq] at hc
      rw [heq]
      refine ⟨?_, ?_, rfl⟩
      · rw [drrDrain_cons, if_neg (of_decide_eq_false hc)]
        exact (Function.update_eq_self _ _).symm
      · rw [drrDrain_cons, if_neg (of_decide_eq_false hc), ← hq]
        exact (Function.update_eq_self _ _).symm
    · -- guard true: `drrDrain`'s `if_pos`; the body drains the head, then recurse
      have hp : p ≤ a.dc i :=
        of_decide_eq_true (by rw [← drrGuard_eval_cons i a hq]; exact hc)
      have hhead : headSize a i = p := by simp only [headSize, hq, List.headI_cons]
      -- the body's effect on flow `i`
      obtain ⟨sm, h1, h2⟩ := bigStep_seq_iff.mp hbody
      rw [bigStep_assignDc_iff] at h1
      rw [bigStep_serveHead_iff] at h2
      have hσmdc : σm.dc = Function.update a.dc i (a.dc i - p) := by
        rw [h2]
        simp only [SchedState.setQueue_dc, SchedState.emit_dc, h1,
          SchedState.setDc_dc, AExp.eval, hhead]
      have hσmq : σm.queue = Function.update a.queue i ps := by
        rw [h2]
        simp only [SchedState.setQueue_queue, SchedState.emit_queue, h1,
          SchedState.setDc_queue]
        rw [hq, List.tail_cons]
      have hσmk : σm.kvar = a.kvar := by
        rw [h2]
        simp only [SchedState.setQueue_kvar, SchedState.emit_kvar, h1,
          SchedState.setDc_kvar]
      have hσmqi : σm.queue i = ps := by rw [hσmq, Function.update_self]
      have hσmdci : σm.dc i = a.dc i - p := by rw [hσmdc, Function.update_self]
      obtain ⟨ihdc, ihq, ihk⟩ := ih σm a' hσmqi hrest
      rw [drrDrain_cons, if_pos hp]
      refine ⟨?_, ?_, ?_⟩
      · rw [ihdc, hσmdci, hσmdc, Function.update_idem]
      · rw [ihq, hσmdci, hσmq, Function.update_idem]
      · rw [ihk, hσmk]

/-- The non-emptiness guard reads off the queue. -/
theorem notEmpty_eval (i : Fin n) (σ : SchedState n) :
    (BExp.notEmpty i).eval σ = !(σ.queue i).isEmpty := rfl

/-- **Per-turn soundness**: the big-step execution of `drrTurn Q i`
updates flow `i`'s counter and queue exactly as `drrServe` does — add the
quantum, drain, reset if the queue empties — leaving every other flow and
the loop counter untouched. The DRR program realizes the functional model. -/
theorem bigStep_drrTurn (Q : ℝ≥0) (i : Fin n) {σ σ' : SchedState n}
    (h : BigStep (drrTurn Q i) σ σ') :
    σ'.dc = Function.update σ.dc i (drrServe Q (σ.dc i) (σ.queue i)).1
      ∧ σ'.queue = Function.update σ.queue i (drrServe Q (σ.dc i) (σ.queue i)).2
      ∧ σ'.kvar = σ.kvar := by
  rw [drrTurn, bigStep_ifte_iff] at h
  rcases h with ⟨hne, hbody⟩ | ⟨hempty, hskip⟩
  · -- queue non-empty: add quantum, drain, reset if emptied
    have hqne : σ.queue i ≠ [] := by
      intro he; rw [notEmpty_eval, he] at hne; simp at hne
    obtain ⟨σ1, h1, h2⟩ := bigStep_seq_iff.mp hbody
    obtain ⟨σ2, hinner, hreset⟩ := bigStep_seq_iff.mp h2
    rw [bigStep_assignDc_iff] at h1
    subst h1
    obtain ⟨h2dc, h2q, h2k⟩ := bigStep_drrInner i hinner
    simp only [SchedState.setDc_dc, SchedState.setDc_queue,
      SchedState.setDc_kvar, AExp.eval, Function.update_self] at h2dc h2q h2k
    rw [Function.update_idem] at h2dc
    have hσ2qi : σ2.queue i = (drrDrain (σ.dc i + Q) (σ.queue i)).2 := by
      rw [h2q, Function.update_self]
    rw [bigStep_ifte_iff] at hreset
    rcases hreset with ⟨hne2, hsk⟩ | ⟨hne2, hass⟩
    · -- not drained: leftover queue is non-empty, no reset
      rw [bigStep_skip_iff] at hsk; subst hsk
      rw [notEmpty_eval, hσ2qi] at hne2
      have hnd : (drrDrain (σ.dc i + Q) (σ.queue i)).2 ≠ [] := by
        intro he; rw [he] at hne2; simp at hne2
      rw [drrServe_of_not_drained hqne hnd]
      exact ⟨h2dc, h2q, h2k⟩
    · -- drained: leftover queue empty, reset the counter to zero
      rw [bigStep_assignDc_iff] at hass; subst hass
      rw [notEmpty_eval, hσ2qi] at hne2
      have hd : (drrDrain (σ.dc i + Q) (σ.queue i)).2 = [] := by simpa using hne2
      rw [drrServe_drained hqne hd]
      refine ⟨?_, ?_, ?_⟩ <;>
        simp only [SchedState.setDc_dc, SchedState.setDc_queue,
          SchedState.setDc_kvar, AExp.eval, h2dc, h2q, h2k, hd,
          Function.update_idem]
  · -- queue empty: the turn is skipped
    rw [bigStep_skip_iff] at hskip
    rw [hskip]
    have hqe : σ.queue i = [] := by rw [notEmpty_eval] at hempty; simpa using hempty
    rw [hqe, drrServe_nil]
    refine ⟨(Function.update_eq_self _ _).symm, ?_, rfl⟩
    rw [← hqe]; exact (Function.update_eq_self _ _).symm

/-! ## Book restatement (DRR as an imperative program)
Running Algorithm 1's per-flow turn `drrTurn Q i` updates flow `i`'s
deficit counter and queue exactly as the functional model `drrServe` — the
basis of the `IsDrr` round-count bounds in `Book.ServersResidualDrr`. The
operational semantics and the functional model agree, so the round-count
guarantees hold of the genuine imperative program. -/
example (Q : ℝ≥0) (i : Fin n) {σ σ' : SchedState n}
    (h : BigStep (drrTurn Q i) σ σ') :
    σ'.dc i = (drrServe Q (σ.dc i) (σ.queue i)).1
      ∧ σ'.queue i = (drrServe Q (σ.dc i) (σ.queue i)).2 := by
  obtain ⟨hdc, hq, _⟩ := bigStep_drrTurn Q i h
  exact ⟨by rw [hdc, Function.update_self], by rw [hq, Function.update_self]⟩

end DeepWiki
