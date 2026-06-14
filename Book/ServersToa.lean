import Book.DeviationsComposition
import Book.ServiceCurveStrict

/-! # Total output analysis (TOA)
TOA computes a worst-case end-to-end delay bound for a flow crossing a
path of servers, using only strict service curves. At each
server `h` the per-server delay is the maximal backlogged-period length
`d^(h) = inf{t > 0 | α^(h)(t) ≤ β^(h)(t)} = firstCrossing α^(h) β^(h)`
(line 4, `length_le_firstCrossing_of_isBacklogged`), where `α^(h)` is the
aggregate arrival curve at `h` (line 3, the sum of the deconvolved
upstream outputs `α^(ℓ) ⊘ β^(ℓ)` and the source arrivals). The per-flow
bound is `d_i = ∑_{h∈p_i} d^(h)` (line 6): the end-to-end delay composes
additively over the path, the `n`-server form of the delay triangle
inequality `Deviation.delay_triangle`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **`n`-server delay composition**: the end-to-end delay through a path
of cumulative processes `A 0, A 1, …, A n` (each `A (k+1)` the output of
the server fed by `A k`) is at most the sum of the per-hop delays,
`d(A 0, A n) ≤ ∑_{k<n} d(A k, A (k+1))` — the `n`-fold delay triangle
inequality. -/
theorem delay_le_sum_delay (A : ℕ → ℝ≥0 → ℝ≥0) (n : ℕ) :
    Deviation.delay (A 0) (A n)
      ≤ ∑ k ∈ Finset.range n, Deviation.delay (A k) (A (k + 1)) := by
  induction n with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty]
    show Deviation.delay (A 0) (A 0) ≤ 0
    refine hDev_le fun t => le_trans (hDevAt_le (d := 0) ?_) ?_
    · exact le_of_eq (congrArg (A 0) (add_zero t).symm)
    · exact_mod_cast le_rfl
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc Deviation.delay (A 0) (A (n + 1))
        ≤ Deviation.delay (A 0) (A n) + Deviation.delay (A n) (A (n + 1)) :=
          Deviation.delay_triangle _ _ _
      _ ≤ (∑ k ∈ Finset.range n, Deviation.delay (A k) (A (k + 1)))
          + Deviation.delay (A n) (A (n + 1)) := add_le_add ih le_rfl

/-- **TOA per-flow delay bound** (line 6): if at each of the `n` servers
on flow `i`'s path the per-hop delay is bounded by `d^(h)` (line 4's
`firstCrossing α^(h) β^(h)`), the end-to-end delay is at most the sum
`∑_{h∈p_i} d^(h)`. -/
theorem delay_le_sum_of_perhop (A : ℕ → ℝ≥0 → ℝ≥0) (d : ℕ → ℝ≥0∞) (n : ℕ)
    (hd : ∀ k, k < n → Deviation.delay (A k) (A (k + 1)) ≤ d k) :
    Deviation.delay (A 0) (A n) ≤ ∑ k ∈ Finset.range n, d k :=
  le_trans (delay_le_sum_delay A n)
    (Finset.sum_le_sum fun k hk => hd k (Finset.mem_range.mp hk))

/-! ## Book restatement (total output analysis)
A flow crossing `n` servers, with per-server worst-case delays `d^(h)`
(each the maximal backlogged-period length at server `h`, computed from
the aggregate arrival curve and the strict service curve), has end-to-end
worst-case delay at most `∑_{h∈p_i} d^(h)` — the sum of the per-server
delays, the additive composition of TOA's line 6. -/
example (A : ℕ → ℝ≥0 → ℝ≥0) (d : ℕ → ℝ≥0∞) (n : ℕ)
    (hd : ∀ k, k < n → Deviation.delay (A k) (A (k + 1)) ≤ d k) :
    Deviation.delay (A 0) (A n) ≤ ∑ k ∈ Finset.range n, d k :=
  delay_le_sum_of_perhop A d n hd

/-! ## Book restatement (per-server delay is the first crossing)
The per-server delay used by TOA is the maximal backlogged-period length:
under a strict service curve `β` with aggregate arrival curve `α`, every
backlogged period has length at most `firstCrossing α β = inf{t > 0 |
α(t) ≤ β(t)}` (line 4). Combined with the additive composition above, this
gives the end-to-end bound `∑_{h} firstCrossing α^(h) β^(h)`. -/
example {S : Curve → Curve → Prop} {β α : ℝ≥0 → ℝ≥0}
    (hc : IsCausal S) (hβ : IsStrictMinimalServiceCurve β S)
    {A D : Curve} (hp : S A D) (harr : IsMaximalArrivalBound (⇑A) α) :
    maxBackloggedLength ⇑A ⇑D ≤ firstCrossing α β :=
  maxBackloggedLength_le_firstCrossing hc hβ hp harr

end DeepWiki
