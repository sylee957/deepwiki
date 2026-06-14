import Book.ServersResidualDrr

/-! # Deficit-round-robin scheduling dynamics
The operational deficit-counter scheduler. Each flow holds a queue of
packet sizes; a turn (`drrServe`, lines 5-12) adds the
flow's quantum `Q` to its deficit counter, drains head packets while
the counter covers them (`drrDrain`, lines 7-10), and resets the
counter to zero when the queue empties (lines 11-12). The two
structural facts that drive the residual are derived here from the
dynamics: the counter stays below the maximal packet size after a turn
(`drrServe_fst_lt_of_backlogged`), and the data sent in a turn plus the
carried counter equals the entering counter plus the quantum
(`drrServed_add_fst_eq`). Telescoping these over a backlogged period
recovers exactly the round-count coupling that `IsDrr`
(`Book.ServersResidualDrr`) takes as its trajectory definition:
`drr_le_servedSum_add` (`p·Q ≤ served + ℓᵘ`, own flow) and
`drr_servedSum_le` (`served ≤ p·Q + ℓᵘ`, every flow). -/

namespace DeepWiki

open scoped Classical NNReal

/-- DRR inner loop (lines 7-10): send the head packet
while its size fits the deficit counter `d`, decrementing `d` by each
served size; stop at the first head the counter cannot cover. -/
noncomputable def drrDrain (d : ℝ≥0) : List ℝ≥0 → ℝ≥0 × List ℝ≥0
  | [] => (d, [])
  | p :: ps => if p ≤ d then drrDrain (d - p) ps else (d, p :: ps)

/-- `drrDrain d [] = (d, [])`. -/
@[simp] theorem drrDrain_nil (d : ℝ≥0) : drrDrain d [] = (d, []) := rfl

/-- `drrDrain` unfolds on a cons by the head-fits test. -/
theorem drrDrain_cons (d p : ℝ≥0) (ps : List ℝ≥0) :
    drrDrain d (p :: ps)
      = if p ≤ d then drrDrain (d - p) ps else (d, p :: ps) := rfl

/-- The packets left after draining are a suffix of the queue. -/
theorem drrDrain_snd_suffix (d : ℝ≥0) (q : List ℝ≥0) :
    (drrDrain d q).2 <:+ q := by
  induction q generalizing d with
  | nil => exact List.suffix_rfl
  | cons p ps ih =>
    rw [drrDrain_cons]
    split
    · exact (ih (d - p)).trans (List.suffix_cons p ps)
    · exact List.suffix_rfl

/-- Deficit conservation: the leftover counter plus the whole queue
equals the entering counter plus the leftover queue — every unit the
counter drops is a unit removed from the queue. -/
theorem drrDrain_fst_add_sum (d : ℝ≥0) (q : List ℝ≥0) :
    (drrDrain d q).1 + q.sum = d + (drrDrain d q).2.sum := by
  induction q generalizing d with
  | nil => simp
  | cons p ps ih =>
    rw [drrDrain_cons]
    split
    · rename_i hpd
      rw [List.sum_cons]
      calc (drrDrain (d - p) ps).1 + (p + ps.sum)
          = ((drrDrain (d - p) ps).1 + ps.sum) + p := by ring
        _ = ((d - p) + (drrDrain (d - p) ps).2.sum) + p := by rw [ih (d - p)]
        _ = ((d - p) + p) + (drrDrain (d - p) ps).2.sum := by ring
        _ = d + (drrDrain (d - p) ps).2.sum := by
              rw [tsub_add_cancel_of_le hpd]
    · simp

/-- Stopping bound: if draining leaves a non-empty queue, the leftover
counter is below the new head packet — the reason a turn ends with the
counter under the maximal packet size. -/
theorem drrDrain_fst_lt_of_snd_eq (d : ℝ≥0) (q : List ℝ≥0)
    {p : ℝ≥0} {ps : List ℝ≥0} (h : (drrDrain d q).2 = p :: ps) :
    (drrDrain d q).1 < p := by
  induction q generalizing d with
  | nil => simp at h
  | cons a as ih =>
    rw [drrDrain_cons] at h ⊢
    by_cases had : a ≤ d
    · rw [if_pos had] at h ⊢
      exact ih (d - a) h
    · rw [if_neg had] at h ⊢
      have hac : a :: as = p :: ps := h
      obtain ⟨ha, -⟩ := List.cons_eq_cons.mp hac
      exact ha ▸ not_le.mp had

/-- The packets `drrDrain` sends: the head prefix it removes while the
counter covers each head. -/
noncomputable def drrDrainSent (d : ℝ≥0) : List ℝ≥0 → List ℝ≥0
  | [] => []
  | p :: ps => if p ≤ d then p :: drrDrainSent (d - p) ps else []

/-- `drrDrainSent d [] = []`. -/
@[simp] theorem drrDrainSent_nil (d : ℝ≥0) : drrDrainSent d [] = [] := rfl

/-- `drrDrainSent` unfolds on a cons by the head-fits test. -/
theorem drrDrainSent_cons (d p : ℝ≥0) (ps : List ℝ≥0) :
    drrDrainSent d (p :: ps)
      = if p ≤ d then p :: drrDrainSent (d - p) ps else [] := rfl

/-- The sent prefix and the leftover queue reassemble the input:
`drrDrainSent d q ++ (drrDrain d q).2 = q`. -/
theorem drrDrainSent_append (d : ℝ≥0) (q : List ℝ≥0) :
    drrDrainSent d q ++ (drrDrain d q).2 = q := by
  induction q generalizing d with
  | nil => rfl
  | cons p ps ih =>
    rw [drrDrainSent_cons, drrDrain_cons]
    by_cases hpd : p ≤ d
    · rw [if_pos hpd, if_pos hpd, List.cons_append, ih (d - p)]
    · rw [if_neg hpd, if_neg hpd, List.nil_append]

/-- DRR per-flow turn (lines 5-12): a non-empty queue adds
the quantum to the counter, drains the head packets it covers, and
resets the counter to zero if the queue empties; an empty queue is
skipped, leaving the counter unchanged. -/
noncomputable def drrServe (Q d : ℝ≥0) (q : List ℝ≥0) : ℝ≥0 × List ℝ≥0 :=
  match q with
  | [] => (d, [])
  | a :: as =>
      if (drrDrain (d + Q) (a :: as)).2 = [] then (0, [])
      else drrDrain (d + Q) (a :: as)

/-- `drrServe Q d [] = (d, [])`: an empty queue is skipped. -/
@[simp] theorem drrServe_nil (Q d : ℝ≥0) : drrServe Q d [] = (d, []) := rfl

/-- `drrServe` unfolds on a non-empty queue by the empties-out test. -/
theorem drrServe_cons (Q d a : ℝ≥0) (as : List ℝ≥0) :
    drrServe Q d (a :: as)
      = if (drrDrain (d + Q) (a :: as)).2 = [] then (0, [])
        else drrDrain (d + Q) (a :: as) := rfl

/-- A turn that empties the queue resets the counter: `drrServe = (0, [])`. -/
theorem drrServe_drained {Q d : ℝ≥0} {q : List ℝ≥0} (hq : q ≠ [])
    (h : (drrDrain (d + Q) q).2 = []) : drrServe Q d q = (0, []) := by
  cases q with
  | nil => exact absurd rfl hq
  | cons a as => rw [drrServe_cons, if_pos h]

/-- A turn that leaves a backlog is exactly the drain (no reset). -/
theorem drrServe_of_not_drained {Q d : ℝ≥0} {q : List ℝ≥0} (hq : q ≠ [])
    (h : (drrDrain (d + Q) q).2 ≠ []) :
    drrServe Q d q = drrDrain (d + Q) q := by
  cases q with
  | nil => exact absurd rfl hq
  | cons a as => rw [drrServe_cons, if_neg h]

/-- The packets left after a turn are a suffix of the queue. -/
theorem drrServe_snd_suffix (Q d : ℝ≥0) (q : List ℝ≥0) :
    (drrServe Q d q).2 <:+ q := by
  cases q with
  | nil => exact List.suffix_rfl
  | cons a as =>
    rw [drrServe_cons]
    split
    · exact List.nil_suffix
    · exact drrDrain_snd_suffix (d + Q) (a :: as)

/-- The data left after a turn is at most the queue's data. -/
theorem drrServe_snd_sum_le (Q d : ℝ≥0) (q : List ℝ≥0) :
    (drrServe Q d q).2.sum ≤ q.sum := by
  obtain ⟨t, ht⟩ := drrServe_snd_suffix Q d q
  calc (drrServe Q d q).2.sum ≤ t.sum + (drrServe Q d q).2.sum := le_add_self
    _ = (t ++ (drrServe Q d q).2).sum := (List.sum_append).symm
    _ = q.sum := by rw [ht]

/-- The data flow `i` sends in one DRR turn: the queue mass removed
(`send(head)` applied to the served prefix). -/
noncomputable def drrServed (Q d : ℝ≥0) (q : List ℝ≥0) : ℝ≥0 :=
  q.sum - (drrServe Q d q).2.sum

/-- Sent data plus leftover data is the entering data. -/
theorem drrServed_add_snd_sum (Q d : ℝ≥0) (q : List ℝ≥0) :
    drrServed Q d q + (drrServe Q d q).2.sum = q.sum := by
  rw [drrServed, tsub_add_cancel_of_le (drrServe_snd_sum_le Q d q)]

/-- **Counter invariant**: after a turn that leaves a backlog the
deficit counter is below the maximal packet size — the leftover counter
is under the new head, and every packet is at most `lmax`. -/
theorem drrServe_fst_lt_of_backlogged {Q d lmax : ℝ≥0} {q : List ℝ≥0}
    (hq : q ≠ []) (hbl : (drrServe Q d q).2 ≠ [])
    (hpkt : ∀ x ∈ q, x ≤ lmax) : (drrServe Q d q).1 < lmax := by
  have hdr : (drrDrain (d + Q) q).2 ≠ [] := by
    intro h
    rw [drrServe_drained hq h] at hbl
    exact hbl rfl
  rw [drrServe_of_not_drained hq hdr]
  obtain ⟨p, ps, hps⟩ := List.exists_cons_of_ne_nil hdr
  have hlt := drrDrain_fst_lt_of_snd_eq (d + Q) q hps
  have hpmem : p ∈ q :=
    (drrDrain_snd_suffix (d + Q) q).subset
      (hps ▸ (List.mem_cons_self : p ∈ p :: ps))
  exact lt_of_lt_of_le hlt (hpkt p hpmem)

/-- Turn-level conservation (left side): sent data plus the whole queue
is at most the entering counter-plus-quantum plus the leftover. -/
theorem drrServe_fst_add_sum_le (Q d : ℝ≥0) (q : List ℝ≥0) :
    (drrServe Q d q).1 + q.sum ≤ (d + Q) + (drrServe Q d q).2.sum := by
  rcases eq_or_ne q [] with rfl | hq
  · rw [drrServe_nil]
    show d + (0 : ℝ≥0) ≤ (d + Q) + (0 : ℝ≥0)
    rw [add_zero, add_zero]; exact le_self_add
  · by_cases hdr : (drrDrain (d + Q) q).2 = []
    · rw [drrServe_drained hq hdr]
      have h2 := drrDrain_fst_add_sum (d + Q) q
      rw [hdr, List.sum_nil, add_zero] at h2
      show (0 : ℝ≥0) + q.sum ≤ (d + Q) + (0 : ℝ≥0)
      rw [zero_add, add_zero]
      calc q.sum ≤ (drrDrain (d + Q) q).1 + q.sum := le_add_self
        _ = d + Q := h2
    · rw [drrServe_of_not_drained hq hdr]
      exact le_of_eq (drrDrain_fst_add_sum (d + Q) q)

/-- Turn-level conservation (equality, backlogged): when the queue is
non-empty and not emptied, sent data plus the whole queue equals the
entering counter-plus-quantum plus the leftover. -/
theorem drrServe_fst_add_sum_eq {Q d : ℝ≥0} {q : List ℝ≥0}
    (hq : q ≠ []) (hbl : (drrServe Q d q).2 ≠ []) :
    (drrServe Q d q).1 + q.sum = (d + Q) + (drrServe Q d q).2.sum := by
  have hdr : (drrDrain (d + Q) q).2 ≠ [] := by
    intro h
    rw [drrServe_drained hq h] at hbl
    exact hbl rfl
  rw [drrServe_of_not_drained hq hdr]
  exact drrDrain_fst_add_sum (d + Q) q

/-- **Per-turn deficit accounting** (general): the data sent plus the
counter carried out is at most the entering counter plus the quantum. -/
theorem drrServed_add_fst_le (Q d : ℝ≥0) (q : List ℝ≥0) :
    drrServed Q d q + (drrServe Q d q).1 ≤ d + Q := by
  have hsum := drrServed_add_snd_sum Q d q
  have hle := drrServe_fst_add_sum_le Q d q
  have h : (drrServed Q d q + (drrServe Q d q).1) + (drrServe Q d q).2.sum
      ≤ (d + Q) + (drrServe Q d q).2.sum := by
    calc (drrServed Q d q + (drrServe Q d q).1) + (drrServe Q d q).2.sum
        = (drrServe Q d q).1 + (drrServed Q d q + (drrServe Q d q).2.sum) := by
            ring
      _ = (drrServe Q d q).1 + q.sum := by rw [hsum]
      _ ≤ (d + Q) + (drrServe Q d q).2.sum := hle
  exact le_of_add_le_add_right h

/-- **Per-turn deficit accounting** (equality, backlogged): the data
sent plus the counter carried out equals the entering counter plus the
quantum — no credit is lost while the flow stays backlogged. -/
theorem drrServed_add_fst_eq {Q d : ℝ≥0} {q : List ℝ≥0}
    (hq : q ≠ []) (hbl : (drrServe Q d q).2 ≠ []) :
    drrServed Q d q + (drrServe Q d q).1 = d + Q := by
  have hsum := drrServed_add_snd_sum Q d q
  have heq := drrServe_fst_add_sum_eq hq hbl
  have h : (drrServed Q d q + (drrServe Q d q).1) + (drrServe Q d q).2.sum
      = (d + Q) + (drrServe Q d q).2.sum := by
    calc (drrServed Q d q + (drrServe Q d q).1) + (drrServe Q d q).2.sum
        = (drrServe Q d q).1 + (drrServed Q d q + (drrServe Q d q).2.sum) := by
            ring
      _ = (drrServe Q d q).1 + q.sum := by rw [hsum]
      _ = (d + Q) + (drrServe Q d q).2.sum := heq
  exact add_right_cancel h

/-! ## Telescoping over rounds -/

/-- Telescoping (upper): if each round's sent data plus the carried
counter is at most the entering counter plus `Q`, then over `m` rounds
the sent data plus the final counter is at most the initial counter
plus `m·Q`. -/
theorem sum_le_of_deficit_step {Q : ℝ≥0} {d σ : ℕ → ℝ≥0}
    (h : ∀ k, σ k + d (k + 1) ≤ d k + Q) (m : ℕ) :
    (∑ k ∈ Finset.range m, σ k) + d m ≤ d 0 + (m : ℝ≥0) * Q := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    calc (∑ k ∈ Finset.range m, σ k) + σ m + d (m + 1)
        = (∑ k ∈ Finset.range m, σ k) + (σ m + d (m + 1)) := by ring
      _ ≤ (∑ k ∈ Finset.range m, σ k) + (d m + Q) := add_le_add_right (h m) _
      _ = ((∑ k ∈ Finset.range m, σ k) + d m) + Q := by ring
      _ ≤ (d 0 + (m : ℝ≥0) * Q) + Q := add_le_add_left ih Q
      _ = d 0 + ((m : ℝ≥0) + 1) * Q := by ring

/-- Telescoping (equality): if each round's sent data plus the carried
counter equals the entering counter plus `Q`, then over `m` rounds the
sent data plus the final counter equals the initial counter plus
`m·Q`. -/
theorem sum_add_eq_of_deficit_step {Q : ℝ≥0} {d σ : ℕ → ℝ≥0}
    (h : ∀ k, σ k + d (k + 1) = d k + Q) (m : ℕ) :
    (∑ k ∈ Finset.range m, σ k) + d m = d 0 + (m : ℝ≥0) * Q := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    calc (∑ k ∈ Finset.range m, σ k) + σ m + d (m + 1)
        = (∑ k ∈ Finset.range m, σ k) + (σ m + d (m + 1)) := by ring
      _ = (∑ k ∈ Finset.range m, σ k) + (d m + Q) := by rw [h m]
      _ = ((∑ k ∈ Finset.range m, σ k) + d m) + Q := by ring
      _ = (d 0 + (m : ℝ≥0) * Q) + Q := by rw [ih]
      _ = d 0 + ((m : ℝ≥0) + 1) * Q := by ring

/-! ## The round-count coupling, derived

A DRR *round trajectory* of a flow with quantum `Q`: `q k` is its queue
at the start of round `k`, `d k` its deficit counter, and the counter
carried out of round `k` is the one entering round `k + 1`
(`hstep`); packets are bounded by `lmax` (`hpkt`); the flow is
backlogged each round — non-empty and not emptied (`hbl`); and the
counter enters below `lmax` (`hd0`, the line-5 invariant). -/

/-- Along a backlogged round trajectory the counter stays below the
maximal packet size at every round. -/
theorem drr_deficit_lt {Q lmax : ℝ≥0} {d : ℕ → ℝ≥0} {q : ℕ → List ℝ≥0}
    (hstep : ∀ k, d (k + 1) = (drrServe Q (d k) (q k)).1)
    (hbl : ∀ k, q k ≠ [] ∧ (drrServe Q (d k) (q k)).2 ≠ [])
    (hpkt : ∀ k, ∀ x ∈ q k, x ≤ lmax)
    (hd0 : d 0 < lmax) : ∀ k, d k < lmax := by
  intro k
  cases k with
  | zero => exact hd0
  | succ k =>
    rw [hstep k]
    exact drrServe_fst_lt_of_backlogged (hbl k).1 (hbl k).2 (hpkt k)

/-- **DRR own-flow guarantee** (the first `IsDrr` inequality, derived
from the dynamics): over `m` backlogged rounds flow `i` sends at least
`m·Q − ℓᵘ`, i.e. `m·Q ≤ served + ℓᵘ`. -/
theorem drr_le_servedSum_add {Q lmax : ℝ≥0} {d : ℕ → ℝ≥0}
    {q : ℕ → List ℝ≥0}
    (hstep : ∀ k, d (k + 1) = (drrServe Q (d k) (q k)).1)
    (hbl : ∀ k, q k ≠ [] ∧ (drrServe Q (d k) (q k)).2 ≠ [])
    (hpkt : ∀ k, ∀ x ∈ q k, x ≤ lmax)
    (hd0 : d 0 < lmax) (m : ℕ) :
    (m : ℝ≥0) * Q
      ≤ (∑ k ∈ Finset.range m, drrServed Q (d k) (q k)) + lmax := by
  have hstepσ : ∀ k, drrServed Q (d k) (q k) + d (k + 1) = d k + Q := by
    intro k
    rw [hstep k]
    exact drrServed_add_fst_eq (hbl k).1 (hbl k).2
  have htel := sum_add_eq_of_deficit_step hstepσ m
  have hdm : d m < lmax := drr_deficit_lt hstep hbl hpkt hd0 m
  calc (m : ℝ≥0) * Q ≤ d 0 + (m : ℝ≥0) * Q := le_add_self
    _ = (∑ k ∈ Finset.range m, drrServed Q (d k) (q k)) + d m := htel.symm
    _ ≤ (∑ k ∈ Finset.range m, drrServed Q (d k) (q k)) + lmax :=
        add_le_add_right hdm.le _

/-- **DRR per-flow bound** (the second `IsDrr` inequality, derived from
the dynamics): over `m` rounds any flow sends at most `m·Q + ℓᵘ` — no
backlog assumption, since a reset only discards credit. -/
theorem drr_servedSum_le {Q lmax : ℝ≥0} {d : ℕ → ℝ≥0} {q : ℕ → List ℝ≥0}
    (hstep : ∀ k, d (k + 1) = (drrServe Q (d k) (q k)).1)
    (hd0 : d 0 < lmax) (m : ℕ) :
    (∑ k ∈ Finset.range m, drrServed Q (d k) (q k))
      ≤ (m : ℝ≥0) * Q + lmax := by
  have hstepσ : ∀ k, drrServed Q (d k) (q k) + d (k + 1) ≤ d k + Q := by
    intro k
    rw [hstep k]
    exact drrServed_add_fst_le Q (d k) (q k)
  have htel := sum_le_of_deficit_step hstepσ m
  calc (∑ k ∈ Finset.range m, drrServed Q (d k) (q k))
      ≤ (∑ k ∈ Finset.range m, drrServed Q (d k) (q k)) + d m := le_self_add
    _ ≤ d 0 + (m : ℝ≥0) * Q := htel
    _ ≤ lmax + (m : ℝ≥0) * Q := add_le_add_left hd0.le _
    _ = (m : ℝ≥0) * Q + lmax := by ring

/-! ## The two inequalities of `IsDrr`, as departure increments
With departures `Dᵢ(t) = Dᵢ(s) + (data sent over the backlogged
period)`, the derived round-count bounds are exactly the two
inequalities `IsDrr` (`Book.ServersResidualDrr`) takes as the DRR
trajectory definition: flow `i` over `p` backlogged rounds, and any
other flow over at most `p + 1` rounds. -/

/-- Own flow: `Dᵢ(s) + p·Q ≤ Dᵢ(t) + ℓᵘ`. -/
example {Q lmax Dis Dit : ℝ≥0} {d : ℕ → ℝ≥0} {q : ℕ → List ℝ≥0} {p : ℕ}
    (hstep : ∀ k, d (k + 1) = (drrServe Q (d k) (q k)).1)
    (hbl : ∀ k, q k ≠ [] ∧ (drrServe Q (d k) (q k)).2 ≠ [])
    (hpkt : ∀ k, ∀ x ∈ q k, x ≤ lmax) (hd0 : d 0 < lmax)
    (hD : Dit = Dis + ∑ k ∈ Finset.range p, drrServed Q (d k) (q k)) :
    Dis + (p : ℝ≥0) * Q ≤ Dit + lmax := by
  rw [hD]
  calc Dis + (p : ℝ≥0) * Q
      ≤ Dis + ((∑ k ∈ Finset.range p, drrServed Q (d k) (q k)) + lmax) :=
        add_le_add_right (drr_le_servedSum_add hstep hbl hpkt hd0 p) _
    _ = (Dis + ∑ k ∈ Finset.range p, drrServed Q (d k) (q k)) + lmax := by ring

/-- Any other flow: `Dⱼ(t) ≤ Dⱼ(s) + (p + 1)·Q + ℓᵘ`. -/
example {Q lmax Djs Djt : ℝ≥0} {d : ℕ → ℝ≥0} {q : ℕ → List ℝ≥0} {p : ℕ}
    (hstep : ∀ k, d (k + 1) = (drrServe Q (d k) (q k)).1)
    (hd0 : d 0 < lmax)
    (hD : Djt = Djs + ∑ k ∈ Finset.range (p + 1), drrServed Q (d k) (q k)) :
    Djt ≤ Djs + (((p : ℝ≥0) + 1) * Q + lmax) := by
  rw [hD]
  calc Djs + ∑ k ∈ Finset.range (p + 1), drrServed Q (d k) (q k)
      ≤ Djs + (((p + 1 : ℕ) : ℝ≥0) * Q + lmax) :=
        add_le_add_right (drr_servedSum_le hstep hd0 (p + 1)) _
    _ = Djs + (((p : ℝ≥0) + 1) * Q + lmax) := by push_cast; ring

end DeepWiki
