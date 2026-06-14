import DeepWiki.NetworkCalculus.ServersResidualWrr

/-! # Weighted-round-robin scheduling dynamics
The operational weight-counter scheduler. Each flow holds a queue of
packet sizes; a turn (`wrrServe`, lines 3-7) sends up to the
flow's weight `w` head packets — exactly `w` while backlogged, fewer
only when the queue runs dry. A backlogged turn therefore sends exactly
`w` packets, of total length between `w·ℓˡ` and `w·ℓᵘ`. Summing over a
backlogged period recovers the round-count coupling that `IsWrr`
(`Book.ServersResidualWrr`) takes as its trajectory definition:
`wrr_le_servedSum` (`p·w·ℓˡ ≤ served`, own flow) and `wrr_servedSum_le`
(`served ≤ p·w·ℓᵘ`, every flow). -/

namespace DeepWiki

open scoped NNReal

/-- WRR per-flow turn (lines 3-7): send up to `w` head
packets of the flow, stopping early only if the queue empties. -/
def wrrServe : ℕ → List ℝ≥0 → List ℝ≥0 × List ℝ≥0
  | 0, q => ([], q)
  | _ + 1, [] => ([], [])
  | w + 1, p :: ps => (p :: (wrrServe w ps).1, (wrrServe w ps).2)

/-- A WRR turn sends the first `w` packets and keeps the rest. -/
theorem wrrServe_eq (w : ℕ) (q : List ℝ≥0) :
    wrrServe w q = (q.take w, q.drop w) := by
  induction w generalizing q with
  | zero => cases q <;> rfl
  | succ w ih =>
    cases q with
    | nil => rfl
    | cons p ps =>
      simp [wrrServe, ih ps, List.take_succ_cons, List.drop_succ_cons]

/-- The packets sent in a WRR turn are the first `w`. -/
@[simp] theorem wrrServe_fst (w : ℕ) (q : List ℝ≥0) :
    (wrrServe w q).1 = q.take w := by rw [wrrServe_eq]

/-- The packets left after a WRR turn are all but the first `w`. -/
@[simp] theorem wrrServe_snd (w : ℕ) (q : List ℝ≥0) :
    (wrrServe w q).2 = q.drop w := by rw [wrrServe_eq]

/-- The data flow `i` sends in one WRR turn: the served head packets. -/
def wrrServed (w : ℕ) (q : List ℝ≥0) : ℝ≥0 := (wrrServe w q).1.sum

/-- `wrrServed w q` is the total length of the first `w` packets. -/
@[simp] theorem wrrServed_eq (w : ℕ) (q : List ℝ≥0) :
    wrrServed w q = (q.take w).sum := by rw [wrrServed, wrrServe_fst]

/-- **Per-turn upper bound**: a WRR turn sends at most `w` packets, each
at most `ℓᵘ`, so at most `w·ℓᵘ` of data — no backlog assumption. -/
theorem wrrServed_le {w : ℕ} {lmax : ℝ≥0} {q : List ℝ≥0}
    (hpkt : ∀ x ∈ q, x ≤ lmax) : wrrServed w q ≤ (w : ℝ≥0) * lmax := by
  rw [wrrServed_eq]
  calc (q.take w).sum
      ≤ (q.take w).length • lmax :=
        List.sum_le_card_nsmul _ _ (fun x hx => hpkt x (List.take_subset w q hx))
    _ = ((q.take w).length : ℝ≥0) * lmax := nsmul_eq_mul _ _
    _ ≤ (w : ℝ≥0) * lmax :=
        mul_le_mul_left (by
          rw [List.length_take]; exact_mod_cast min_le_left w q.length) _

/-- **Per-turn lower bound**: while backlogged (at least `w` packets
waiting), a WRR turn sends exactly `w` packets, each at least `ℓˡ`, so
at least `w·ℓˡ` of data. -/
theorem wrrServed_ge {w : ℕ} {lmin : ℝ≥0} {q : List ℝ≥0}
    (hlen : w ≤ q.length) (hpkt : ∀ x ∈ q, lmin ≤ x) :
    (w : ℝ≥0) * lmin ≤ wrrServed w q := by
  rw [wrrServed_eq]
  have hlentake : (q.take w).length = w := by
    rw [List.length_take, min_eq_left hlen]
  calc (w : ℝ≥0) * lmin = ((q.take w).length : ℝ≥0) * lmin := by rw [hlentake]
    _ = (q.take w).length • lmin := (nsmul_eq_mul _ _).symm
    _ ≤ (q.take w).sum :=
        List.card_nsmul_le_sum _ _ (fun x hx => hpkt x (List.take_subset w q hx))

/-! ## The round-count coupling, derived

A WRR *round trajectory* of a flow with weight `w`: `q k` is its queue
at the start of round `k`. -/

/-- **WRR own-flow guarantee** (the first `IsWrr` inequality, derived
from the dynamics): over `m` backlogged rounds flow `i` sends at least
`m·w·ℓˡ` of data. -/
theorem wrr_le_servedSum {w : ℕ} {lmin : ℝ≥0} {q : ℕ → List ℝ≥0}
    (hlen : ∀ k, w ≤ (q k).length)
    (hpkt : ∀ k, ∀ x ∈ q k, lmin ≤ x) (m : ℕ) :
    (m : ℝ≥0) * ((w : ℝ≥0) * lmin)
      ≤ ∑ k ∈ Finset.range m, wrrServed w (q k) := by
  calc (m : ℝ≥0) * ((w : ℝ≥0) * lmin)
      = ∑ _k ∈ Finset.range m, (w : ℝ≥0) * lmin := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ k ∈ Finset.range m, wrrServed w (q k) :=
        Finset.sum_le_sum (fun k _ => wrrServed_ge (hlen k) (hpkt k))

/-- **WRR per-flow bound** (the second `IsWrr` inequality, derived from
the dynamics): over `m` rounds any flow sends at most `m·w·ℓᵘ` of
data — no backlog assumption. -/
theorem wrr_servedSum_le {w : ℕ} {lmax : ℝ≥0} {q : ℕ → List ℝ≥0}
    (hpkt : ∀ k, ∀ x ∈ q k, x ≤ lmax) (m : ℕ) :
    (∑ k ∈ Finset.range m, wrrServed w (q k))
      ≤ (m : ℝ≥0) * ((w : ℝ≥0) * lmax) := by
  calc (∑ k ∈ Finset.range m, wrrServed w (q k))
      ≤ ∑ _k ∈ Finset.range m, (w : ℝ≥0) * lmax :=
        Finset.sum_le_sum (fun k _ => wrrServed_le (hpkt k))
    _ = (m : ℝ≥0) * ((w : ℝ≥0) * lmax) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## The two inequalities of `IsWrr`, as departure increments
With departures `Dᵢ(t) = Dᵢ(s) + (data sent over the backlogged
period)`, the derived round-count bounds are exactly the two
inequalities `IsWrr` (`Book.ServersResidualWrr`) takes as the WRR
trajectory definition: flow `i` over `p` backlogged rounds, and any
other flow over at most `p + 1` rounds. -/

/-- Own flow: `Dᵢ(s) + p·(wᵢ·ℓᵢˡ) ≤ Dᵢ(t)`. -/
example {w : ℕ} {lmin Dis Dit : ℝ≥0} {q : ℕ → List ℝ≥0} {p : ℕ}
    (hlen : ∀ k, w ≤ (q k).length) (hpkt : ∀ k, ∀ x ∈ q k, lmin ≤ x)
    (hD : Dit = Dis + ∑ k ∈ Finset.range p, wrrServed w (q k)) :
    Dis + (p : ℝ≥0) * ((w : ℝ≥0) * lmin) ≤ Dit := by
  rw [hD]
  exact add_le_add_right (wrr_le_servedSum hlen hpkt p) _

/-- Any other flow: `Dⱼ(t) ≤ Dⱼ(s) + (p + 1)·(wⱼ·ℓⱼᵘ)`. -/
example {w : ℕ} {lmax Djs Djt : ℝ≥0} {q : ℕ → List ℝ≥0} {p : ℕ}
    (hpkt : ∀ k, ∀ x ∈ q k, x ≤ lmax)
    (hD : Djt = Djs + ∑ k ∈ Finset.range (p + 1), wrrServed w (q k)) :
    Djt ≤ Djs + ((p : ℝ≥0) + 1) * ((w : ℝ≥0) * lmax) := by
  rw [hD]
  calc Djs + ∑ k ∈ Finset.range (p + 1), wrrServed w (q k)
      ≤ Djs + ((p + 1 : ℕ) : ℝ≥0) * ((w : ℝ≥0) * lmax) :=
        add_le_add_right (wrr_servedSum_le hpkt (p + 1)) _
    _ = Djs + ((p : ℝ≥0) + 1) * ((w : ℝ≥0) * lmax) := by push_cast; ring

end DeepWiki
