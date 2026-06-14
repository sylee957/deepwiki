import Book.ServersResidualPmooChain
import Book.RealCurves
import Mathlib.Tactic.LinearCombination

/-! # The PMOO chain on rate-latency servers
The chain convolution of rate-latency service curves folds to a
single rate-latency curve `β_{⨅ Rₕ, ∑ Tₕ}` — a tandem of
rate-latency servers behaves like one rate-latency server (the
simple-tandem service-curve composition). Subtracting the summed
token-bucket cross-traffic then keeps the tagged flow's residual
itself rate-latency: this is the all-crossing case of the
multi-dimensional PMOO operator, where each cross arrival, applied
over the whole window, pulls out of the splitting infimum. -/

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

/-- `chainRate R 0 = R 0`. -/
theorem chainRate_zero (R : ℕ → ℝ≥0) : chainRate R 0 = R 0 := rfl

/-- `chainRate R (n+1) = chainRate R n ⊓ R (n+1)`. -/
theorem chainRate_succ (R : ℕ → ℝ≥0) (n : ℕ) :
    chainRate R (n + 1) = chainRate R n ⊓ R (n + 1) := rfl

/-- `chainLatency T 0 = T 0`. -/
theorem chainLatency_zero (T : ℕ → ℝ≥0) : chainLatency T 0 = T 0 := rfl

/-- `chainLatency T (n+1) = chainLatency T n + T (n+1)`. -/
theorem chainLatency_succ (T : ℕ → ℝ≥0) (n : ℕ) :
    chainLatency T (n + 1) = chainLatency T n + T (n + 1) := rfl

/-- The folded rate is the slowest among hops `0..n`: `chainRate R n
≤ R k` for every `k ≤ n`. -/
theorem chainRate_le (R : ℕ → ℝ≥0) {n k : ℕ} (hk : k ≤ n) :
    chainRate R n ≤ R k := by
  induction n with
  | zero => rw [Nat.le_zero.mp hk]; exact le_rfl
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hk) with h | h
    · exact le_trans (chainRate_succ R n ▸ inf_le_left)
        (ih (Nat.lt_succ_iff.mp h))
    · rw [h]; exact chainRate_succ R n ▸ inf_le_right

/-- The folded latency is the sum over hops `0..n`. -/
theorem chainLatency_eq_sum (T : ℕ → ℝ≥0) (n : ℕ) :
    chainLatency T n = ∑ h ∈ Finset.range (n + 1), T h := by
  induction n with
  | zero => rw [chainLatency_zero, Finset.sum_range_one]
  | succ n ih =>
    rw [chainLatency_succ, ih, Finset.sum_range_succ (f := T) (n + 1)]

/-- **The tandem of rate-latency servers is a rate-latency server**:
the chain convolution of `β_{Rₕ,Tₕ}` over hops `0..n` is
`β_{⨅ Rₕ, ∑ Tₕ}` (the slowest rate, the summed latencies) — the
simple-tandem service-curve composition. -/
theorem chainConv_rateLatency (R T : ℕ → ℝ≥0) (n : ℕ) :
    chainConv (fun h => rateLatency (R h) (T h)) n
      = rateLatency (chainRate R n) (chainLatency T n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [chainConv_succ, ih]
    exact minConvProj_rateLatency _ _ _ _

/-- **Residual of a rate-latency against an affine arrival**:
`[β_{R₀,T₀} − (ρ·t + b)]⁺ = β_{R₀−ρ, T'}` with the effective latency
`T' = T₀ + (ρ·T₀ + b)/(R₀−ρ)`, under stability `ρ < R₀` — the
clamped difference is again a rate-latency curve. -/
theorem rateLatency_sub_affine (R0 T0 rho b : ℝ≥0) (hR : rho < R0) :
    (fun t => rateLatency R0 T0 t - (rho * t + b))
      = rateLatency (R0 - rho) (T0 + (rho * T0 + b) / (R0 - rho)) := by
  have hRpos : 0 < R0 - rho := tsub_pos_of_lt hR
  have hRcoe : ((R0 - rho : ℝ≥0) : ℝ) = (R0 : ℝ) - rho :=
    NNReal.coe_sub (le_of_lt hR)
  have hRne : ((R0 : ℝ) - rho) ≠ 0 := by
    rw [← hRcoe]; exact_mod_cast hRpos.ne'
  have hRT' : ((R0 - rho : ℝ≥0) : ℝ)
      * ((T0 + (rho * T0 + b) / (R0 - rho) : ℝ≥0) : ℝ)
      = (R0 : ℝ) * T0 + b := by
    push_cast [hRcoe]
    field_simp
    ring
  funext t
  set R : ℝ≥0 := R0 - rho with hRdef
  set T' : ℝ≥0 := T0 + (rho * T0 + b) / (R0 - rho) with hT'def
  rcases le_total t T' with htle | htge
  · have hrhs : rateLatency R T' t = 0 := by
      show R * (t - T') = 0
      rw [tsub_eq_zero_of_le htle, mul_zero]
    have hlhs : rateLatency R0 T0 t - (rho * t + b) = 0 := by
      refine tsub_eq_zero_of_le ?_
      show R0 * (t - T0) ≤ rho * t + b
      rw [← NNReal.coe_le_coe]
      push_cast [NNReal.coe_sub_def]
      have htR : (t : ℝ) ≤ T' := by exact_mod_cast htle
      rcases le_total (t : ℝ) T0 with h0 | h0
      · rw [max_eq_right (by linarith), mul_zero]
        positivity
      · rw [max_eq_left (by linarith)]
        have hRtle : ((R0 : ℝ) - rho) * t ≤ (R0 : ℝ) * T0 + b := by
          have hle : ((R0 : ℝ) - rho) * t ≤ ((R0 : ℝ) - rho) * T' := by
            apply mul_le_mul_of_nonneg_left htR
            rw [← hRcoe]; exact (R0 - rho).coe_nonneg
          rw [hRcoe] at hRT'
          nlinarith [hle, hRT']
        nlinarith [hRtle]
    rw [hrhs, hlhs]
  · have hT0le : T0 ≤ T' := le_self_add
    have htT0 : T0 ≤ t := le_trans hT0le htge
    rw [← NNReal.coe_inj]
    show ((rateLatency R0 T0 t - (rho * t + b) : ℝ≥0) : ℝ)
      = ((rateLatency R T' t : ℝ≥0) : ℝ)
    have hRHS : ((rateLatency R T' t : ℝ≥0) : ℝ)
        = ((R0 : ℝ) - rho) * ((t : ℝ) - T') := by
      show ((R * (t - T') : ℝ≥0) : ℝ) = _
      rw [NNReal.coe_mul, NNReal.coe_sub htge, hRcoe]
    have htge' : (T' : ℝ) ≤ t := by exact_mod_cast htge
    have hge0 : rho * t + b ≤ rateLatency R0 T0 t := by
      show rho * t + b ≤ R0 * (t - T0)
      rw [← NNReal.coe_le_coe]
      push_cast [NNReal.coe_sub htT0]
      rw [hRcoe] at hRT'
      have hRtge : ((R0 : ℝ) - rho) * T' ≤ ((R0 : ℝ) - rho) * t := by
        apply mul_le_mul_of_nonneg_left htge'
        rw [← hRcoe]; exact (R0 - rho).coe_nonneg
      nlinarith [hRT', hRtge]
    rw [NNReal.coe_sub hge0, hRHS]
    show (((R0 * (t - T0) : ℝ≥0)) : ℝ) - ((rho * t + b : ℝ≥0) : ℝ)
      = ((R0 : ℝ) - rho) * ((t : ℝ) - T')
    push_cast [NNReal.coe_sub htT0]
    rw [hRcoe] at hRT'
    linear_combination hRT'

/-- **The all-crossing PMOO residual is rate-latency**: a tagged
flow crossing the rate-latency tandem, with summed cross-traffic
arrival `ρ·t + b` (the sum of the token buckets), is served the
rate-latency residual `β_{R, T}` with rate `R = (⨅ₕ Rₕ) − ρ` and
latency `T = (∑ₕ Tₕ) + (ρ·∑ₕ Tₕ + b)/R`, under stability
`ρ < ⨅ₕ Rₕ` — the chain fold less the cross-traffic. -/
theorem pmooResidualChain_rateLatency (R T : ℕ → ℝ≥0) (n : ℕ)
    (rho b : ℝ≥0) (hstab : rho < chainRate R n) :
    pmooResidualChain (fun h => rateLatency (R h) (T h)) n
        (fun v => rho * v + b)
      = rateLatency (chainRate R n - rho)
          (chainLatency T n
            + (rho * chainLatency T n + b) / (chainRate R n - rho)) := by
  funext v
  rw [pmooResidualChain_apply, chainConv_rateLatency]
  exact congrFun
    (rateLatency_sub_affine (chainRate R n) (chainLatency T n) rho b hstab) v

/-! ## Book restatement (all-crossing case)
A tandem of `n + 1` rate-latency servers crossed by every flow folds
to a single rate-latency server `β_{⨅ₕ Rₕ, ∑ₕ Tₕ}`, and the chain
PMOO residual of the tagged flow is the clamped difference against
it. For all-crossing flows each cross arrival applies over the whole
window, so it pulls out of the splitting infimum and the residual is
`(β₀ ∗ ⋯ ∗ βₙ − ∑_{j≠i} αⱼ)⁺` against the folded curve. With summed
token-bucket cross-traffic `ρ·t + b` this is the rate-latency curve
`β_{R, T}`, `R = (⨅ₕ Rₕ) − ρ`, `T = (∑ₕ Tₕ) + (ρ·∑ₕ Tₕ + b)/R` — the
book's effective rate `⨅ₕ(Rₕ − ρ)` and latency
`∑ₕ Tₕ(1 + ρ/R) + b/R`. -/
example (R T : ℕ → ℝ≥0) (n : ℕ) (α : ℝ≥0 → ℝ≥0) (v : ℝ≥0) :
    pmooResidualChain (fun h => rateLatency (R h) (T h)) n α v
      = rateLatency (chainRate R n) (chainLatency T n) v - α v := by
  rw [pmooResidualChain_apply, chainConv_rateLatency]
example (R T : ℕ → ℝ≥0) (n : ℕ) (rho b : ℝ≥0) (hstab : rho < chainRate R n) :
    pmooResidualChain (fun h => rateLatency (R h) (T h)) n
        (fun v => rho * v + b)
      = rateLatency (chainRate R n - rho)
          (chainLatency T n
            + (rho * chainLatency T n + b) / (chainRate R n - rho)) :=
  pmooResidualChain_rateLatency R T n rho b hstab

end DeepWiki
