import DeepWiki.NetworkCalculus.SchedulerSemantics

/-! # DRR as an imperative program, and its soundness
DRR written in the operational-semantics framework: the
inner drain loop `drrInner` (lines 7-10), the per-flow turn `drrTurn`
(lines 5-12), and one round `drrRound` (the `for i = 1 to n` pass). The
soundness theorems pin the big-step execution of these programs to the
functional models of `Book.ServersDrr` — `drrInner` realizes `drrDrain`
and `drrTurn` realizes `drrServe` on flow `i`'s counter and queue, with the
output trace gaining exactly the packets sent (`drrDrainSent`,
`bigStep_drrTurn_out`). `drrServe` is the per-step building block of the
`IsDrr` round-count coupling derived at the curve level in
`Book.ServersResidualDrr`; the rounds-to-continuous-time bridge (`IsDrr`'s
abstraction boundary) is not formalized here.
-/

namespace DeepWiki

open scoped Classical NNReal

/-- The DRR inner-loop guard `(not empty(i)) ∧ (size(head(i)) ≤ DC[i])`. -/
def drrGuard {n : ℕ} (i : Fin n) : BExp n :=
  .and (.notEmpty i) (.le (.headSize i) (.dc i))

/-- The DRR inner-loop body (lines 8-10): `send(head(i))`, decrement the
counter by the head size, then `removeHead(i)`. -/
def drrInnerBody {n : ℕ} (i : Fin n) : Stmt n :=
  .seq (.send i) (.seq (.assignDc i (.sub (.dc i) (.headSize i))) (.removeHead i))

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
      -- the body's effect on flow `i`: send, then DC -= size, then removeHead
      obtain ⟨s1, hsend, hbody2⟩ := bigStep_seq_iff.mp hbody
      obtain ⟨s2, hassign, hrem⟩ := bigStep_seq_iff.mp hbody2
      rw [bigStep_send_iff] at hsend
      rw [bigStep_assignDc_iff] at hassign
      rw [bigStep_removeHead_iff] at hrem
      have hσmdc : σm.dc = Function.update a.dc i (a.dc i - p) := by
        simp only [hrem, SchedState.setQueue_dc, hassign, SchedState.setDc_dc,
          hsend, SchedState.emit_dc, AExp.eval, headSize_emit, hhead]
      have hσmq : σm.queue = Function.update a.queue i ps := by
        simp only [hrem, SchedState.setQueue_queue, hassign,
          SchedState.setDc_queue, hsend, SchedState.emit_queue]
        rw [hq, List.tail_cons]
      have hσmk : σm.kvar = a.kvar := by
        simp only [hrem, SchedState.setQueue_kvar, hassign,
          SchedState.setDc_kvar, hsend, SchedState.emit_kvar]
      have hσmqi : σm.queue i = ps := by rw [hσmq, Function.update_self]
      have hσmdci : σm.dc i = a.dc i - p := by rw [hσmdc, Function.update_self]
      obtain ⟨ihdc, ihq, ihk⟩ := ih σm a' hσmqi hrest
      rw [drrDrain_cons, if_pos hp]
      refine ⟨?_, ?_, ?_⟩
      · rw [ihdc, hσmdci, hσmdc, Function.update_idem]
      · rw [ihq, hσmdci, hσmq, Function.update_idem]
      · rw [ihk, hσmk]

/-- **Inner-loop output**: the drain loop appends to the output trace
exactly the packets it sends — the prefix `drrDrainSent (σ.dc i) (σ.queue i)`. -/
theorem bigStep_drrInner_out (i : Fin n) {σ σ' : SchedState n}
    (h : BigStep (drrInner i) σ σ') :
    σ'.out = σ.out ++ drrDrainSent (σ.dc i) (σ.queue i) := by
  suffices H : ∀ (q : List ℝ≥0) (a a' : SchedState n), a.queue i = q →
      BigStep (drrInner i) a a' →
      a'.out = a.out ++ drrDrainSent (a.dc i) q from H (σ.queue i) σ σ' rfl h
  intro q
  induction q with
  | nil =>
    intro a a' hq h
    rw [drrInner, bigStep_whileB_iff] at h
    rcases h with ⟨_, heq⟩ | ⟨hc, _⟩
    · rw [heq, drrDrainSent_nil, List.append_nil]
    · rw [drrGuard_eval_nil i a hq] at hc; exact absurd hc (by simp)
  | cons p ps ih =>
    intro a a' hq h
    rw [drrInner, bigStep_whileB_iff] at h
    rcases h with ⟨hc, heq⟩ | ⟨hc, σm, hbody, hrest⟩
    · rw [drrGuard_eval_cons i a hq] at hc
      rw [heq, drrDrainSent_cons, if_neg (of_decide_eq_false hc), List.append_nil]
    · have hp : p ≤ a.dc i :=
        of_decide_eq_true (by rw [← drrGuard_eval_cons i a hq]; exact hc)
      have hhead : headSize a i = p := by simp only [headSize, hq, List.headI_cons]
      obtain ⟨s1, hsend, hbody2⟩ := bigStep_seq_iff.mp hbody
      obtain ⟨s2, hassign, hrem⟩ := bigStep_seq_iff.mp hbody2
      rw [bigStep_send_iff] at hsend
      rw [bigStep_assignDc_iff] at hassign
      rw [bigStep_removeHead_iff] at hrem
      have hσmout : σm.out = a.out ++ [p] := by
        simp only [hrem, SchedState.setQueue_out, hassign, SchedState.setDc_out,
          hsend, SchedState.emit_out, hhead]
      have hσmdc : σm.dc = Function.update a.dc i (a.dc i - p) := by
        simp only [hrem, SchedState.setQueue_dc, hassign, SchedState.setDc_dc,
          hsend, SchedState.emit_dc, AExp.eval, headSize_emit, hhead]
      have hσmq : σm.queue = Function.update a.queue i ps := by
        simp only [hrem, SchedState.setQueue_queue, hassign,
          SchedState.setDc_queue, hsend, SchedState.emit_queue]
        rw [hq, List.tail_cons]
      have hσmqi : σm.queue i = ps := by rw [hσmq, Function.update_self]
      have hσmdci : σm.dc i = a.dc i - p := by rw [hσmdc, Function.update_self]
      rw [ih σm a' hσmqi hrest, hσmout, hσmdci, drrDrainSent_cons,
        if_pos hp, List.append_assoc, List.singleton_append]

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

/-- **Per-turn output**: a DRR turn appends to the output trace exactly the
packets it sends — `drrDrainSent (σ.dc i + Q) (σ.queue i)`, the prefix
drained after the quantum is added. -/
theorem bigStep_drrTurn_out (Q : ℝ≥0) (i : Fin n) {σ σ' : SchedState n}
    (h : BigStep (drrTurn Q i) σ σ') :
    σ'.out = σ.out ++ drrDrainSent (σ.dc i + Q) (σ.queue i) := by
  rw [drrTurn, bigStep_ifte_iff] at h
  rcases h with ⟨_, hbody⟩ | ⟨hempty, hskip⟩
  · obtain ⟨σ1, h1, h2⟩ := bigStep_seq_iff.mp hbody
    obtain ⟨σ2, hinner, hreset⟩ := bigStep_seq_iff.mp h2
    rw [bigStep_assignDc_iff] at h1
    subst h1
    have hout := bigStep_drrInner_out i hinner
    simp only [SchedState.setDc_out, SchedState.setDc_dc, SchedState.setDc_queue,
      AExp.eval, Function.update_self] at hout
    rw [bigStep_ifte_iff] at hreset
    rcases hreset with ⟨_, hsk⟩ | ⟨_, hass⟩
    · rw [bigStep_skip_iff] at hsk; subst hsk; exact hout
    · rw [bigStep_assignDc_iff] at hass; subst hass
      simpa only [SchedState.setDc_out] using hout
  · rw [bigStep_skip_iff] at hskip
    rw [hskip]
    have hqe : σ.queue i = [] := by rw [notEmpty_eval] at hempty; simpa using hempty
    rw [hqe, drrDrainSent_nil, List.append_nil]

/-- One DRR round (line 4, `for i = 1 to n`): run every flow's turn once,
with its own quantum `Q i`. -/
def drrRound (Q : Fin n → ℝ≥0) : Stmt n := roundStmt (fun i => drrTurn (Q i) i)

/-- **Round soundness** (the `for`-loop over flows): one round serves each
flow once, realizing `drrServe` on every flow independently — turn `i`
touches only flow `i`, so the serving order is immaterial. -/
theorem bigStep_drrRound (Q : Fin n → ℝ≥0) {σ σ' : SchedState n}
    (h : BigStep (drrRound Q) σ σ') (j : Fin n) :
    σ'.dc j = (drrServe (Q j) (σ.dc j) (σ.queue j)).1
      ∧ σ'.queue j = (drrServe (Q j) (σ.dc j) (σ.queue j)).2 := by
  suffices H : ∀ (L : List (Fin n)), L.Nodup → ∀ {a a' : SchedState n},
      BigStep (L.foldr (fun i s => Stmt.seq (drrTurn (Q i) i) s) Stmt.skip) a a' →
      (∀ k ∈ L, a'.dc k = (drrServe (Q k) (a.dc k) (a.queue k)).1
          ∧ a'.queue k = (drrServe (Q k) (a.dc k) (a.queue k)).2)
        ∧ (∀ k, k ∉ L → a'.dc k = a.dc k ∧ a'.queue k = a.queue k) by
    exact (H (List.finRange n) (List.nodup_finRange n) h).1 j (List.mem_finRange j)
  intro L
  induction L with
  | nil =>
    intro _ a a' h
    rw [List.foldr_nil, bigStep_skip_iff] at h
    subst h
    exact ⟨fun k hk => by simp at hk, fun k _ => ⟨rfl, rfl⟩⟩
  | cons i rest ih =>
    intro hnd a a' h
    rw [List.foldr_cons, bigStep_seq_iff] at h
    obtain ⟨σm, hturn, hfold⟩ := h
    obtain ⟨hmdc, hmq, _⟩ := bigStep_drrTurn (Q i) i hturn
    rw [List.nodup_cons] at hnd
    obtain ⟨hinotmem, hndrest⟩ := hnd
    obtain ⟨ihserved, ihframe⟩ := ih hndrest hfold
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [List.mem_cons] at hk
      rcases hk with rfl | hkrest
      · obtain ⟨fd, fq⟩ := ihframe k hinotmem
        exact ⟨by rw [fd, hmdc, Function.update_self],
          by rw [fq, hmq, Function.update_self]⟩
      · obtain ⟨sd, sq⟩ := ihserved k hkrest
        have hki : k ≠ i := fun he => hinotmem (he ▸ hkrest)
        exact ⟨by rw [sd, hmdc, hmq, Function.update_of_ne hki,
            Function.update_of_ne hki],
          by rw [sq, hmdc, hmq, Function.update_of_ne hki,
            Function.update_of_ne hki]⟩
    · rw [List.mem_cons, not_or] at hk
      obtain ⟨hkne, hkrest⟩ := hk
      obtain ⟨fd, fq⟩ := ihframe k hkrest
      exact ⟨by rw [fd, hmdc, Function.update_of_ne hkne],
        by rw [fq, hmq, Function.update_of_ne hkne]⟩

/-! ## Book restatement (DRR as an imperative program)
Running DRR's per-flow turn `drrTurn Q i` updates flow `i`'s
deficit counter and queue exactly as the functional model `drrServe`
(`bigStep_drrTurn`); one round `drrRound` does so for every flow
(`bigStep_drrRound`). `drrServe` is the per-step building block of the
`IsDrr` round-count coupling derived at the curve level in
`Book.ServersResidualDrr`; bridging this state-trajectory to the
continuous-time departure process `D` over a backlogged period (the
rounds-to-time correspondence) is `IsDrr`'s deliberate abstraction
boundary and is not formalized here. The output trace `out` and a
fuel-based executable evaluator are likewise deferred. -/
example (Q : ℝ≥0) (i : Fin n) {σ σ' : SchedState n}
    (h : BigStep (drrTurn Q i) σ σ') :
    σ'.dc i = (drrServe Q (σ.dc i) (σ.queue i)).1
      ∧ σ'.queue i = (drrServe Q (σ.dc i) (σ.queue i)).2
      ∧ σ'.out = σ.out ++ drrDrainSent (σ.dc i + Q) (σ.queue i) := by
  obtain ⟨hdc, hq, _⟩ := bigStep_drrTurn Q i h
  exact ⟨by rw [hdc, Function.update_self], by rw [hq, Function.update_self],
    bigStep_drrTurn_out Q i h⟩

end DeepWiki
