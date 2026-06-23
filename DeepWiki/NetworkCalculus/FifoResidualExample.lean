import DeepWiki.NetworkCalculus.ServersResidualFifo
import DeepWiki.NetworkCalculus.ServersResidualPmooRateLatency
import DeepWiki.NetworkCalculus.RealCurvesDeconv
import DeepWiki.NetworkCalculus.RealCurvesRegularity

/-! # FIFO residual rate-latency example (two flows)
A FIFO server with rate-latency aggregate service curve `β_{R,T}`, crossed
by a flow whose cross-traffic is token-bucket `γ_{b,r}` (here the affine
`r·t + b`), with `r < R`. For each offset `θ ≤ b/R + T` the FIFO residual
service curve for the tagged flow is again a rate-latency curve
`β_{R−r, (b + R·T − r·θ)/(R−r)}`; the family is increasing on this range
and the greatest member is at `θ₀ = b/R + T`, giving `β_{R−r, b/R + T}`.
For `θ ≥ b/R + T` the residual is `δ_θ ∗ γ_{R(θ−T)−b, R−r}`. These are the
concrete curves of the worked example accompanying the FIFO θ-family
theorem (`minConv_fifoResidual_le_of_isFifo`). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The effective latency of the FIFO rate-latency residual at offset `θ`:
`(b + R·T − r·θ)/(R−r)`. -/
noncomputable def fifoLatency (R T r b θ : ℝ≥0) : ℝ≥0 :=
  (b + R * T - r * θ) / (R - r)

/-- At the optimal offset `θ₀ = b/R + T` the effective latency is `b/R + T`. -/
theorem fifoLatency_optimal (R T r b : ℝ≥0) (hR : r < R) (hRpos : 0 < R) :
    fifoLatency R T r b (b / R + T) = b / R + T := by
  have hRr : 0 < R - r := tsub_pos_of_lt hR
  rw [fifoLatency, ← NNReal.coe_inj]
  have hRrcoe : ((R - r : ℝ≥0) : ℝ) = (R : ℝ) - r := NNReal.coe_sub hR.le
  have hθ : ((b / R + T : ℝ≥0) : ℝ) = (b : ℝ) / R + T := by
    push_cast; ring
  have hnum : ((b + R * T - r * (b / R + T) : ℝ≥0) : ℝ)
      = (b : ℝ) + R * T - r * ((b : ℝ) / R + T) := by
    rw [NNReal.coe_sub]
    · push_cast; ring
    · -- `r * (b/R + T) ≤ b + R*T`
      rw [← NNReal.coe_le_coe]; push_cast
      have hRpos' : (0 : ℝ) < R := by exact_mod_cast hRpos
      have hrR : (r : ℝ) ≤ R := by exact_mod_cast hR.le
      have hbR : (r : ℝ) * (b / R) ≤ b := by
        rw [mul_div_assoc', div_le_iff₀ hRpos']
        nlinarith [r.coe_nonneg, b.coe_nonneg, hrR]
      have hT : (r : ℝ) * T ≤ R * T :=
        mul_le_mul_of_nonneg_right hrR T.coe_nonneg
      nlinarith [hbR, hT]
  rw [NNReal.coe_div, hnum, hRrcoe, hθ]
  have hRne : (R : ℝ) ≠ 0 := by exact_mod_cast hRpos.ne'
  have hRrne : (R : ℝ) - r ≠ 0 := by rw [← hRrcoe]; exact_mod_cast hRr.ne'
  field_simp

/-- On the comparison range `θ ≤ b/R + T` the effective latency dominates
the offset: `θ ≤ fifoLatency R T r b θ`. So the FIFO wedge `∧ δ_θ` is
inactive and the residual is the pure rate-latency. -/
theorem le_fifoLatency (R T r b θ : ℝ≥0) (hR : r < R) (hRpos : 0 < R)
    (hθ : θ ≤ b / R + T) :
    θ ≤ fifoLatency R T r b θ := by
  have hRr : 0 < R - r := tsub_pos_of_lt hR
  rw [fifoLatency, ← NNReal.coe_le_coe]
  have hRrcoe : ((R - r : ℝ≥0) : ℝ) = (R : ℝ) - r := NNReal.coe_sub hR.le
  have hRpos' : (0 : ℝ) < R := by exact_mod_cast hRpos
  have hrR : (r : ℝ) ≤ R := by exact_mod_cast hR.le
  -- `R·θ ≤ b + R·T`, from `θ ≤ b/R + T`
  have hRne : (R : ℝ) ≠ 0 := hRpos'.ne'
  have hRθ : (R : ℝ) * θ ≤ b + R * T := by
    have hθ' : (θ : ℝ) ≤ b / R + T := by
      have := hθ; rw [← NNReal.coe_le_coe] at this; push_cast at this; exact this
    have hmul := mul_le_mul_of_nonneg_left hθ' hRpos'.le
    rw [mul_add, mul_div_cancel₀ _ hRne] at hmul
    linarith [hmul]
  -- numerator nonneg and the division inequality
  have hnumnn : (0 : ℝ) ≤ (b : ℝ) + R * T - r * θ := by nlinarith [hRθ, hrR, θ.coe_nonneg]
  have hnum : ((b + R * T - r * θ : ℝ≥0) : ℝ) = (b : ℝ) + R * T - r * θ := by
    rw [NNReal.coe_sub]
    · push_cast; ring
    · rw [← NNReal.coe_le_coe]; push_cast; nlinarith [hnumnn]
  rw [NNReal.coe_div, hnum, hRrcoe, le_div_iff₀ (by rw [← hRrcoe]; exact_mod_cast hRr)]
  nlinarith [hRθ, hrR]

/-- **Active-region identity** (`ℝ≥0`): for `θ < v` the clamped difference
`R·(v−T) − (r·(v−θ) + b)` equals `(R−r)·(v − fifoLatency R T r b θ)`, on the
comparison range `θ ≤ b/R + T`. The pointwise core of the rate-latency form
of the FIFO residual. -/
theorem rateLatency_sub_shiftedAffine (R T r b θ v : ℝ≥0)
    (hR : r < R) (hRpos : 0 < R) (hθ : θ ≤ b / R + T) (hv : θ < v) :
    rateLatency R T v - (r * (v - θ) + b)
      = rateLatency (R - r) (fifoLatency R T r b θ) v := by
  have hRr : 0 < R - r := tsub_pos_of_lt hR
  have hRpos' : (0 : ℝ) < R := by exact_mod_cast hRpos
  have hRrcoe : ((R - r : ℝ≥0) : ℝ) = (R : ℝ) - r := NNReal.coe_sub hR.le
  have hRrne : ((R : ℝ) - r) ≠ 0 := by rw [← hRrcoe]; exact_mod_cast hRr.ne'
  have hrR : (r : ℝ) ≤ R := by exact_mod_cast hR.le
  have hθL : θ ≤ fifoLatency R T r b θ := le_fifoLatency R T r b θ hR hRpos hθ
  set L : ℝ≥0 := fifoLatency R T r b θ with hLdef
  -- the latency in real form: `(R−r)·L = b + R·T − r·θ`, with `R·θ ≤ b + R·T`
  have hRne : (R : ℝ) ≠ 0 := hRpos'.ne'
  have hRθ : (R : ℝ) * θ ≤ b + R * T := by
    have hθ' : (θ : ℝ) ≤ b / R + T := by
      have := hθ; rw [← NNReal.coe_le_coe] at this; push_cast at this; exact this
    have hmul := mul_le_mul_of_nonneg_left hθ' hRpos'.le
    rw [mul_add, mul_div_cancel₀ _ hRne] at hmul
    linarith [hmul]
  have hLeq : ((R : ℝ) - r) * (L : ℝ) = (b : ℝ) + R * T - r * θ := by
    rw [hLdef, fifoLatency]
    have hnumnn : (0 : ℝ) ≤ (b : ℝ) + R * T - r * θ := by
      nlinarith [hRθ, hrR, θ.coe_nonneg]
    have hnum : ((b + R * T - r * θ : ℝ≥0) : ℝ) = (b : ℝ) + R * T - r * θ := by
      rw [NNReal.coe_sub]
      · push_cast; ring
      · rw [← NNReal.coe_le_coe]; push_cast; nlinarith [hnumnn]
    rw [NNReal.coe_div, hnum, hRrcoe]
    field_simp
  have hRrpos : (0 : ℝ) < (R : ℝ) - r := by rw [← hRrcoe]; exact_mod_cast hRr
  have hRrnn : (0 : ℝ) ≤ (R : ℝ) - r := hRrpos.le
  -- `T ≤ L` and `θ ≤ v`, both used below
  -- `r(θ−T) ≤ b`, hence `T ≤ L`
  have hrθT : (r : ℝ) * ((θ : ℝ) - T) ≤ b := by
    rcases le_total (θ : ℝ) T with hθT | hTθ
    · have h1 : (r : ℝ) * ((θ : ℝ) - T) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos r.coe_nonneg (by linarith)
      linarith [b.coe_nonneg]
    · -- `R(θ−T) ≤ b` from hRθ, and `r ≤ R`
      have hRθT : (R : ℝ) * ((θ : ℝ) - T) ≤ b := by nlinarith [hRθ]
      have : (r : ℝ) * ((θ : ℝ) - T) ≤ (R : ℝ) * ((θ : ℝ) - T) :=
        mul_le_mul_of_nonneg_right hrR (by linarith)
      linarith
  have hTL : (T : ℝ) ≤ L := by
    have hp : (0 : ℝ) ≤ ((R : ℝ) - r) * ((L : ℝ) - T) := by
      have heq : ((R : ℝ) - r) * ((L : ℝ) - T)
          = ((R : ℝ) - r) * L - ((R : ℝ) - r) * T := by ring
      rw [heq, hLeq]; nlinarith [hrθT]
    rw [← sub_nonneg]
    exact nonneg_of_mul_nonneg_left (by rw [mul_comm]; exact hp) hRrpos
  have htge' : (θ : ℝ) ≤ v := by exact_mod_cast hv.le
  -- common real readings of each side
  have haff : ((r * (v - θ) + b : ℝ≥0) : ℝ) = (r : ℝ) * ((v : ℝ) - θ) + b := by
    rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_sub hv.le]
  have hrl : ((rateLatency R T v : ℝ≥0) : ℝ) = max ((R : ℝ) * ((v : ℝ) - T)) 0 := by
    show ((R * (v - T) : ℝ≥0) : ℝ) = _
    rw [NNReal.coe_mul, NNReal.coe_sub_def, mul_max_of_nonneg _ _ R.coe_nonneg, mul_zero]
  have hRHS : ((rateLatency (R - r) L v : ℝ≥0) : ℝ)
      = max (((R : ℝ) - r) * ((v : ℝ) - L)) 0 := by
    show ((((R - r) * (v - L) : ℝ≥0)) : ℝ) = _
    rw [NNReal.coe_mul, hRrcoe,
      show ((v - L : ℝ≥0) : ℝ) = max ((v : ℝ) - L) 0 from NNReal.coe_sub_def,
      mul_max_of_nonneg _ _ hRrnn, mul_zero]
  -- the equation in `ℝ`
  rw [← NNReal.coe_inj]
  rcases le_total (rateLatency R T v) (r * (v - θ) + b) with hle | hge
  · -- inactive: both sides `0`
    rw [tsub_eq_zero_of_le hle, NNReal.coe_zero, hRHS]
    have hle' : max ((R : ℝ) * ((v : ℝ) - T)) 0 ≤ (r : ℝ) * ((v : ℝ) - θ) + b := by
      rw [← hrl, ← haff]; exact_mod_cast hle
    have hRle : (R : ℝ) * ((v : ℝ) - T) ≤ (r : ℝ) * ((v : ℝ) - θ) + b :=
      le_trans (le_max_left _ _) hle'
    -- `(R−r)·v ≤ (R−r)·L`, so `(R−r)·(v−L) ≤ 0`
    have hvLle : ((R : ℝ) - r) * ((v : ℝ) - L) ≤ 0 := by nlinarith [hRle, hLeq]
    rw [max_eq_right hvLle]
  · -- active: `max (R(v−T)) 0 − (r(v−θ)+b) = max ((R−r)(v−L)) 0`
    rw [NNReal.coe_sub hge, hrl, haff, hRHS]
    have hge' : (r : ℝ) * ((v : ℝ) - θ) + b ≤ max ((R : ℝ) * ((v : ℝ) - T)) 0 := by
      rw [← haff, ← hrl]; exact_mod_cast hge
    have haffnn : (0 : ℝ) ≤ (r : ℝ) * ((v : ℝ) - θ) + b := by positivity
    have hRpos'' : (0 : ℝ) < R := hRpos'
    rcases le_total 0 ((R : ℝ) * ((v : ℝ) - T)) with hRvT | hRvT
    · -- genuine: rate-latency at active branch
      rw [max_eq_left hRvT] at hge' ⊢
      have hvLnn : (0 : ℝ) ≤ ((R : ℝ) - r) * ((v : ℝ) - L) := by nlinarith [hge', hLeq]
      rw [max_eq_left hvLnn]
      linear_combination hLeq
    · -- `R(v−T) ≤ 0` ⟹ `v ≤ T ≤ L`; both sides `0`
      rw [max_eq_right hRvT] at hge' ⊢
      have haff0 : (r : ℝ) * ((v : ℝ) - θ) + b = 0 := le_antisymm hge' haffnn
      have hvT : (v : ℝ) ≤ T := by
        by_contra hc
        rw [not_le] at hc
        exact absurd hRvT (not_le.mpr (mul_pos hRpos'' (by linarith)))
      have hvL : (v : ℝ) ≤ L := le_trans hvT hTL
      have hvLnp : ((R : ℝ) - r) * ((v : ℝ) - L) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hRrnn (by linarith)
      rw [max_eq_right hvLnp, haff0, sub_zero]

/-! ## The FIFO residual for the two-flow rate-latency / token-bucket example -/

/-- **FIFO residual is rate-latency (first case, `θ ≤ b/R + T`)**: a FIFO server
with rate-latency aggregate `β_{R,T}` crossed by a flow whose cross-traffic is the
affine token-bucket `α₂ = r·t + b` (`r < R`) gives the tagged flow the FIFO
residual `[β_{R,T} − α₂ ∗ δ_θ]⁺ ∧ δ_θ`, which on the comparison range is the
rate-latency curve `β_{R−r, (b + R·T − r·θ)/(R−r)}`. -/
theorem fifoResidual_rateLatencyNN_affine (R T r b θ : ℝ≥0)
    (hR : r < R) (hRpos : 0 < R) (hθ : θ ≤ b / R + T) :
    fifoResidual (rateLatencyNN R T) (affine r b) θ
      = rateLatencyNN (R - r) (fifoLatency R T r b θ) := by
  have hθL : θ ≤ fifoLatency R T r b θ := le_fifoLatency R T r b θ hR hRpos hθ
  set L : ℝ≥0 := fifoLatency R T r b θ with hLdef
  funext v
  rw [fifoResidual_apply]
  by_cases hv : v ≤ θ
  · -- inactive: residual `0`, and `rateLatencyNN (R−r) L v = 0` since `v ≤ θ ≤ L`
    rw [if_pos hv, rateLatencyNN_coe,
      tsub_eq_zero_of_le (le_trans hv hθL), mul_zero, ENNReal.coe_zero]
  · -- active: reduce the `ℝ≥0∞` difference to the `ℝ≥0` identity
    rw [if_neg hv]
    rw [not_le] at hv
    rw [show rateLatencyNN R T v = ((rateLatency R T v : ℝ≥0) : ℝ≥0∞) from
        rateLatencyNN_coe R T v,
      affine_coe,
      ← ENNReal.coe_sub,
      rateLatency_sub_shiftedAffine R T r b θ v hR hRpos hθ hv]
    rw [rateLatencyNN_coe]
    rfl

/-- **Optimal offset `θ₀ = b/R + T`**: the FIFO residual family attains its
greatest member, the rate-latency curve `β_{R−r, b/R + T}` — rate `R − r` and
latency `b/R + T`. -/
theorem fifoResidual_rateLatencyNN_affine_optimal (R T r b : ℝ≥0)
    (hR : r < R) (hRpos : 0 < R) :
    fifoResidual (rateLatencyNN R T) (affine r b) (b / R + T)
      = rateLatencyNN (R - r) (b / R + T) := by
  rw [fifoResidual_rateLatencyNN_affine R T r b (b / R + T) hR hRpos le_rfl,
    fifoLatency_optimal R T r b hR hRpos]

/-- **FIFO residual is a shifted token bucket (second case, `θ ≥ b/R + T`)**: for
offsets past `θ₀` the FIFO residual is `δ_θ ∗ γ_{R(θ−T)−b, R−r}` — burst
`R(θ−T) − b`, rate `R − r`, delayed by `θ`. The discontinuity `R(θ−T) − b` at
`θ` is the data the server may reserve for traffic that waited longer than `θ`. -/
theorem fifoResidual_rateLatencyNN_affine_late (R T r b θ : ℝ≥0)
    (hR : r < R) (hθ : b / R + T ≤ θ) (hRpos : 0 < R) :
    fifoResidual (rateLatencyNN R T) (affine r b) θ
      = minConv (tokenBucketNN (R - r) (R * (θ - T) - b)) (delayNN θ) := by
  rw [conv_delayNN _ (tokenBucketNN_mono _ _) θ]
  -- the burst `R(θ−T) − b` is genuine: `θ ≥ b/R + T`
  have hRpos' : (0 : ℝ) < R := by exact_mod_cast hRpos
  have hRne : (R : ℝ) ≠ 0 := hRpos'.ne'
  have hburst : (b : ℝ) ≤ R * ((θ : ℝ) - T) := by
    have hθ' : (b : ℝ) / R + T ≤ θ := by
      have := hθ; rw [← NNReal.coe_le_coe] at this; push_cast at this; exact this
    have := mul_le_mul_of_nonneg_left hθ' hRpos'.le
    rw [mul_add, mul_div_cancel₀ _ hRne] at this
    nlinarith [this]
  have hRrcoe : ((R - r : ℝ≥0) : ℝ) = (R : ℝ) - r := NNReal.coe_sub hR.le
  have hrR : (r : ℝ) ≤ R := by exact_mod_cast hR.le
  funext v
  rw [fifoResidual_apply]
  by_cases hv : v ≤ θ
  · -- inactive: residual `0`; shifted token bucket at `v − θ = 0` is `0`
    rw [if_pos hv, tsub_eq_zero_of_le hv, tokenBucketNN_zero_eq]
  · -- active: both sides the linear value `(R−r)v + r·θ − R·T − b`
    rw [if_neg hv, not_le] at *
    rw [tokenBucketNN_apply,
      show delayNN 0 (v - θ) = ⊤ from delay_eq_top 0 (tsub_pos_of_lt hv),
      min_eq_left le_top,
      show rateLatencyNN R T v = ((rateLatency R T v : ℝ≥0) : ℝ≥0∞) from
        rateLatencyNN_coe R T v,
      affine_coe, ← ENNReal.coe_sub]
    -- prove the `ℝ≥0` equation in `ℝ`
    rw [show (((R - r : ℝ≥0) : ℝ≥0∞) * ((v - θ : ℝ≥0) : ℝ≥0∞) + (R * (θ - T) - b : ℝ≥0))
        = (((R - r) * (v - θ) + (R * (θ - T) - b) : ℝ≥0) : ℝ≥0∞) by push_cast; ring]
    congr 1
    rw [← NNReal.coe_inj]
    have hvθ : (θ : ℝ) ≤ v := hv.le
    have hge : r * (v - θ) + b ≤ rateLatency R T v := by
      rw [← NNReal.coe_le_coe]
      show ((r * (v - θ) + b : ℝ≥0) : ℝ) ≤ ((R * (v - T) : ℝ≥0) : ℝ)
      rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_sub hv.le, NNReal.coe_mul,
        NNReal.coe_sub_def]
      have hvT : (T : ℝ) ≤ v := by
        have hb0 : (T : ℝ) ≤ b / R + T := le_add_of_nonneg_left (by positivity)
        have hθT : (b : ℝ) / R + T ≤ θ := by
          have := hθ; rw [← NNReal.coe_le_coe] at this; push_cast at this; exact this
        have hθv : (θ : ℝ) ≤ v := hvθ
        linarith
      rw [max_eq_left (by linarith)]
      nlinarith [hburst, hrR, hvθ, hvT]
    rw [NNReal.coe_sub hge]
    show ((R * (v - T) : ℝ≥0) : ℝ) - ((r * (v - θ) + b : ℝ≥0) : ℝ)
      = (((R - r) * (v - θ) + (R * (θ - T) - b) : ℝ≥0) : ℝ)
    have hvT : (T : ℝ) ≤ v := by
      have hθT : (b : ℝ) / R + T ≤ θ := by
        have := hθ; rw [← NNReal.coe_le_coe] at this; push_cast at this; exact this
      have hb0 : (T : ℝ) ≤ b / R + T := le_add_of_nonneg_left (by positivity)
      linarith [hvθ]
    rw [NNReal.coe_mul, NNReal.coe_sub hvT, NNReal.coe_add, NNReal.coe_mul,
      NNReal.coe_sub hv.le, NNReal.coe_add, NNReal.coe_mul, hRrcoe,
      NNReal.coe_sub hv.le, NNReal.coe_sub (by
        rw [← NNReal.coe_le_coe]; push_cast
        have hθT : (b : ℝ) / R + T ≤ θ := by
          have := hθ; rw [← NNReal.coe_le_coe] at this; push_cast at this; exact this
        rw [NNReal.coe_sub (by exact_mod_cast (show T ≤ θ by
          have : T ≤ b / R + T := le_add_self; exact le_trans this hθ))]
        nlinarith [hburst]),
      NNReal.coe_mul, NNReal.coe_sub (by
        exact_mod_cast (show T ≤ θ by
          have : T ≤ b / R + T := le_add_self; exact le_trans this hθ))]
    ring

/-! ## Served bound for the two-flow FIFO rate-latency / token-bucket example -/

/-- **Served form**: a two-flow FIFO server with rate-latency
aggregate `β_{R,T}` (non-decreasing, left-continuous) where flow `1` (the cross
flow) has token-bucket arrival curve `α₂ = r·t + b` and `r < R`, serves the
tagged flow `0` the rate-latency residual `β_{R−r, (b + R·T − r·θ)/(R−r)}` for
each offset `θ ≤ b/R + T`: `A₀ ∗ β_{R−r, L} ≤ D₀`. -/
theorem minConv_rateLatencyResidual_le_of_isFifo_two
    {As Ds : Fin 2 → Curve} {R T r b : ℝ≥0} (θ : ℝ≥0)
    (hfifo : IsFifo (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (hserv : ∀ x, minConv (Deviation.liftENN (fun y => ∑ j, (As j) y))
        (rateLatencyNN R T) x ≤ ((∑ j, (Ds j) x : ℝ≥0) : ℝ≥0∞))
    (harr : IsMaximalArrivalBound ⇑(As 1) (fun v => r * v + b))
    (hR : r < R) (hRpos : 0 < R) (hθ : θ ≤ b / R + T) (t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As 0))
        (rateLatencyNN (R - r) (fifoLatency R T r b θ)) t
      ≤ ((Ds 0) t : ℝ≥0∞) := by
  classical
  -- the cross-traffic family: only flow `1` matters for the tagged flow `0`
  have herase : Finset.univ.erase (0 : Fin 2) = {1} := by decide
  have harr' : ∀ j : Fin 2, j ≠ 0 →
      IsMaximalArrivalBound ⇑(As j) (fun v => r * v + b) := by
    intro j hj
    have hj1 : j = 1 := by
      have : j.val = 1 := by omega
      exact Fin.ext this
    subst hj1; exact harr
  have hkey := minConv_fifoResidual_le_of_isFifo (As := As) (Ds := Ds)
    (β := rateLatencyNN R T) (α := fun (_ : Fin 2) v => r * v + b)
    hfifo (rateLatencyNN_mono R T) (rateLatencyNN_leftCont R T) hserv
    (i := 0) harr' θ t
  -- identify the residual's cross-traffic with `affine r b`
  rw [← fifoResidual_rateLatencyNN_affine R T r b θ hR hRpos hθ]
  refine le_trans (le_of_eq ?_) hkey
  congr 2
  funext v
  rw [affine_coe]
  congr 1
  rw [Finset.sum_const]
  norm_num [Finset.card_erase_of_mem]

/-! ## Restatements against the worked-example wording
A FIFO server crossed by two flows, with rate-latency aggregate service curve
`β_{R,T}` and the cross flow's token-bucket arrival curve `γ_{b,r} = r·t + b`
(`R > r`): for every offset `θ ≤ b/R + T` the FIFO residual service curve for
the tagged flow is the rate-latency curve `β_{R−r, (b + R·T − r·θ)/(R−r)}`
(`fifoResidual_rateLatencyNN_affine`); the family is greatest at `θ₀ = b/R + T`,
giving `β_{R−r, b/R + T}` (`fifoResidual_rateLatencyNN_affine_optimal`); for
`θ ≥ b/R + T` it is the shifted token bucket `δ_θ ∗ γ_{R(θ−T)−b, R−r}`
(`fifoResidual_rateLatencyNN_affine_late`). -/
example (R T r b θ : ℝ≥0) (hR : r < R) (hRpos : 0 < R) (hθ : θ ≤ b / R + T) :
    fifoResidual (rateLatencyNN R T) (affine r b) θ
      = rateLatencyNN (R - r)
          ((b + R * T - r * θ) / (R - r)) :=
  fifoResidual_rateLatencyNN_affine R T r b θ hR hRpos hθ

/-- At `θ₀ = b/R + T` the residual is `β_{R−r, b/R + T}`. -/
example (R T r b : ℝ≥0) (hR : r < R) (hRpos : 0 < R) :
    fifoResidual (rateLatencyNN R T) (affine r b) (b / R + T)
      = rateLatencyNN (R - r) (b / R + T) :=
  fifoResidual_rateLatencyNN_affine_optimal R T r b hR hRpos

/-- For `θ ≥ b/R + T` the residual is the shifted token bucket
`δ_θ ∗ γ_{R(θ−T)−b, R−r}`. -/
example (R T r b θ : ℝ≥0) (hR : r < R) (hθ : b / R + T ≤ θ) (hRpos : 0 < R) :
    fifoResidual (rateLatencyNN R T) (affine r b) θ
      = minConv (tokenBucketNN (R - r) (R * (θ - T) - b)) (delayNN θ) :=
  fifoResidual_rateLatencyNN_affine_late R T r b θ hR hθ hRpos

end DeepWiki
