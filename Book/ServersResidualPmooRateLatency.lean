import Book.ServersResidualPmooChain
import Book.RealCurves

/-! # The PMOO chain on rate-latency servers
The chain convolution of rate-latency service curves folds to a
single rate-latency curve `β_{⨅ Rₕ, ∑ Tₕ}` — the tandem of
rate-latency servers behaves like one rate-latency server, the
service-curve half of the book's Example 10.1 closed form. The
remaining half (folding the token-bucket cross-traffic into the
residual's effective rate and latency) is the arithmetic of
`pmooResidualChain` on this folded curve. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- Truncated subtraction is superadditive: `(a + c) − (b + d) ≤
(a − b) + (c − d)` on `ℝ≥0`. -/
theorem tsub_add_tsub_ge (a b c d : ℝ≥0) :
    (a + c) - (b + d) ≤ (a - b) + (c - d) := by
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_sub_def]
  refine max_le ?_ ?_
  · have h1 := le_max_left ((a : ℝ) - b) 0
    have h2 := le_max_left ((c : ℝ) - d) 0
    linarith
  · have h1 := le_max_right ((a : ℝ) - b) 0
    have h2 := le_max_right ((c : ℝ) - d) 0
    linarith

/-- **Rate-latency convolution**: `β_{R,T} ∗ β_{R',T'} = β_{R⊓R', T+T'}`
(projected `ℝ≥0` form) — the slower rate and the summed latencies, the
slack going on the smaller-rate side. -/
theorem minConvProj_rateLatency (R T R' T' : ℝ≥0) :
    minConvProj (rateLatency R T) (rateLatency R' T')
      = rateLatency (R ⊓ R') (T + T') := by
  funext t
  rw [minConvProj_eq]
  apply le_antisymm
  · rcases le_total t (T + T') with htle | htle
    · refine ciInf_le_of_le (OrderBot.bddBelow _)
        ⟨(min t T, t - min t T), add_tsub_cancel_of_le (min_le_left _ _)⟩ ?_
      show rateLatency R T (min t T) + rateLatency R' T' (t - min t T)
        ≤ rateLatency (R ⊓ R') (T + T') t
      have e1 : rateLatency R T (min t T) = 0 := by
        show R * (min t T - T) = 0
        rw [tsub_eq_zero_of_le (min_le_right _ _), mul_zero]
      have e2 : rateLatency R' T' (t - min t T) = 0 := by
        show R' * ((t - min t T) - T') = 0
        rw [tsub_eq_zero_of_le ?_, mul_zero]
        rcases le_total t T with h | h
        · rw [min_eq_left h, tsub_self]; exact zero_le'
        · rw [min_eq_right h, tsub_le_iff_left]; exact htle
      have e3 : rateLatency (R ⊓ R') (T + T') t = 0 := by
        show (R ⊓ R') * (t - (T + T')) = 0
        rw [tsub_eq_zero_of_le htle, mul_zero]
      rw [e1, e2, e3, add_zero]
    · have hsub : (t - T') - T = t - (T + T') := by
        rw [tsub_tsub, add_comm T' T]
      have hsub' : (t - T) - T' = t - (T + T') := by rw [tsub_tsub]
      rcases le_total R R' with hR | hR
      · refine ciInf_le_of_le (OrderBot.bddBelow _)
          ⟨(t - T', T'), tsub_add_cancel_of_le (le_trans le_add_self htle)⟩ ?_
        show rateLatency R T (t - T') + rateLatency R' T' T'
          ≤ rateLatency (R ⊓ R') (T + T') t
        have e2 : rateLatency R' T' T' = 0 := by
          show R' * (T' - T') = 0
          rw [tsub_self, mul_zero]
        rw [e2, add_zero]
        show R * ((t - T') - T) ≤ (R ⊓ R') * (t - (T + T'))
        rw [hsub, min_eq_left hR]
      · refine ciInf_le_of_le (OrderBot.bddBelow _)
          ⟨(T, t - T), add_tsub_cancel_of_le (le_trans le_self_add htle)⟩ ?_
        show rateLatency R T T + rateLatency R' T' (t - T)
          ≤ rateLatency (R ⊓ R') (T + T') t
        have e1 : rateLatency R T T = 0 := by
          show R * (T - T) = 0
          rw [tsub_self, mul_zero]
        rw [e1, zero_add]
        show R' * ((t - T) - T') ≤ (R ⊓ R') * (t - (T + T'))
        rw [hsub', min_eq_right hR]
  · refine le_ciInf fun p => ?_
    show rateLatency (R ⊓ R') (T + T') t
      ≤ rateLatency R T p.1.1 + rateLatency R' T' p.1.2
    show (R ⊓ R') * (t - (T + T'))
      ≤ R * (p.1.1 - T) + R' * (p.1.2 - T')
    have hge : t - (T + T') ≤ (p.1.1 - T) + (p.1.2 - T') := by
      have := tsub_add_tsub_ge p.1.1 T p.1.2 T'
      rwa [p.2] at this
    calc (R ⊓ R') * (t - (T + T'))
        ≤ (R ⊓ R') * ((p.1.1 - T) + (p.1.2 - T')) := by gcongr
      _ = (R ⊓ R') * (p.1.1 - T) + (R ⊓ R') * (p.1.2 - T') := by rw [mul_add]
      _ ≤ R * (p.1.1 - T) + R' * (p.1.2 - T') := by
          gcongr
          · exact min_le_left R R'
          · exact min_le_right R R'

/-- The folded rate of a chain of rate-latency hops: the slowest rate
across hops `0..n`. -/
noncomputable def chainRate (R : ℕ → ℝ≥0) : ℕ → ℝ≥0
  | 0 => R 0
  | n + 1 => chainRate R n ⊓ R (n + 1)

/-- The folded latency of a chain of rate-latency hops: the summed
latencies across hops `0..n`. -/
noncomputable def chainLatency (T : ℕ → ℝ≥0) : ℕ → ℝ≥0
  | 0 => T 0
  | n + 1 => chainLatency T n + T (n + 1)

/-- **The tandem of rate-latency servers is a rate-latency server**:
the chain convolution of `β_{Rₕ,Tₕ}` over hops `0..n` is
`β_{⨅ Rₕ, ∑ Tₕ}` — the service-curve closed form of Example 10.1. -/
theorem chainConv_rateLatency (R T : ℕ → ℝ≥0) (n : ℕ) :
    chainConv (fun h => rateLatency (R h) (T h)) n
      = rateLatency (chainRate R n) (chainLatency T n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [chainConv_succ, ih]
    exact minConvProj_rateLatency _ _ _ _

/-! ## Book restatement (Example 10.1, the service-curve fold)
A tandem of `n + 1` rate-latency servers crossed by every flow folds
to a single rate-latency server `β_{⨅ₕ Rₕ, ∑ₕ Tₕ}`: the chain PMOO
residual `(β₀ ∗ ⋯ ∗ βₙ − ∑_{j≠i} αⱼ)⁺` of the tagged flow is the
clamped difference against this folded curve. With token-bucket
cross-traffic the residual is itself rate-latency, recovering the
book's `R = ⨅ₕ(Rₕ − ∑ rⱼ)`, `T = ∑ₕ Tₕ(1 + ∑rⱼ/R) + ∑ bⱼ/R`; the
folding of the arrivals into that effective rate/latency is the
remaining arithmetic. -/
example (R T : ℕ → ℝ≥0) (n : ℕ) (α : ℝ≥0 → ℝ≥0) (v : ℝ≥0) :
    pmooResidualChain (fun h => rateLatency (R h) (T h)) n α v
      = rateLatency (chainRate R n) (chainLatency T n) v - α v := by
  rw [pmooResidualChain_apply, chainConv_rateLatency]

end DeepWiki
