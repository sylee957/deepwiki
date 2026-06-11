import Book.PseudoInverse
import Book.RealCurves

/-! # Catalog of pseudo-inverses
The pseudo-inverses of the standard curves, computed over the complete domain
`ℝ≥0∞` (the `WithTop`-completion of the `ℝ≥0` time axis, where an unreached
level correctly inverts to `⊤`). Peak-rate `λ_R = R·t` inverts to `λ_{1/R}`;
pure delay `δ_d` inverts to the affine `γ_{0,d}`; rate-latency `β_{R,T}` inverts
to `γ_{1/R,T}`; and the affine/token-bucket `γ_{r,b}` inverts to `β_{1/r,b}`.
Each is a first-crossing `sInf` over the admissible set. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Set

/-! ## Peak-rate: `λ_R⁻¹ = λ_{1/R}` -/

/-- The admissible set `{t | x ≤ R·t}` is `[R⁻¹·x, ∞)` for `0 < R < ⊤`. -/
theorem levelGeSet_rateENN (R : ℝ≥0∞) (hR : 0 < R) (hRtop : R ≠ ⊤) (x : ℝ≥0∞) :
    levelGeSet (rateENN R) x = Ici (R⁻¹ * x) := by
  ext t
  rw [mem_levelGeSet, mem_Ici, ge_iff_le, rateENN, rateV,
    ENNReal.inv_mul_le_iff hR.ne' hRtop]

/-- `λ_R⁻¹ = λ_{1/R}`: the peak-rate inverse is peak-rate of reciprocal slope
(for `0 < R < ⊤`). -/
theorem pseudoInv_rateENN (R : ℝ≥0∞) (hR : 0 < R) (hRtop : R ≠ ⊤) (x : ℝ≥0∞) :
    pseudoInv (rateENN R) x = rateENN R⁻¹ x := by
  rw [pseudoInv, levelGeSet_rateENN R hR hRtop, csInf_Ici, rateENN, rateV]

/-! ## Rate-latency: `β_{R,T}⁻¹ = γ_{1/R,T}` -/

/-- The admissible set `{t | x ≤ R·(t-T)}` is `[R⁻¹·x + T, ∞)` for `0 < x`,
`0 < R < ⊤`, `T < ⊤`. -/
theorem levelGeSet_rateLatencyENN (R T : ℝ≥0∞) (hR : 0 < R) (hRtop : R ≠ ⊤)
    (hT : T ≠ ⊤) (x : ℝ≥0∞) (hx : 0 < x) :
    levelGeSet (rateLatencyENN R T) x = Ici (R⁻¹ * x + T) := by
  ext t
  rw [mem_levelGeSet, mem_Ici, ge_iff_le, rateLatencyENN, rateLatencyV,
    ← ENNReal.inv_mul_le_iff hR.ne' hRtop]
  constructor
  · intro h
    have hTt : T ≤ t := by
      by_contra hlt
      rw [not_le] at hlt
      rw [tsub_eq_zero_of_le hlt.le, le_zero_iff] at h
      rcases mul_eq_zero.mp h with h1 | h2
      · exact absurd (ENNReal.inv_eq_zero.mp h1) hRtop
      · exact absurd h2 hx.ne'
    rwa [ENNReal.le_sub_iff_add_le_right hT hTt] at h
  · intro h
    have hTt : T ≤ t := le_trans le_add_self h
    rwa [ENNReal.le_sub_iff_add_le_right hT hTt]

/-- `tokenBucketENN r b x = r·x + b` for `0 < x` (the `delay 0` factor is `⊤`). -/
theorem tokenBucketENN_pos (r b : ℝ≥0∞) {x : ℝ≥0∞} (hx : 0 < x) :
    tokenBucketENN r b x = r * x + b := by
  rw [tokenBucketENN, tokenBucketV]
  simp only [Pi.inf_apply, delay_apply]
  rw [if_neg (by simp [hx.ne']), min_top_right]

/-- `β_{R,T}⁻¹ = γ_{1/R,T}`: rate-latency inverts to the token-bucket curve of
reciprocal rate `R⁻¹` and burst `T` (for `0 < x`, `0 < R < ⊤`, `T < ⊤`). -/
theorem pseudoInv_rateLatencyENN (R T : ℝ≥0∞) (hR : 0 < R) (hRtop : R ≠ ⊤)
    (hT : T ≠ ⊤) (x : ℝ≥0∞) (hx : 0 < x) :
    pseudoInv (rateLatencyENN R T) x = tokenBucketENN R⁻¹ T x := by
  rw [pseudoInv, levelGeSet_rateLatencyENN R T hR hRtop hT x hx, csInf_Ici,
    tokenBucketENN_pos R⁻¹ T hx]

/-! ## Affine / token-bucket: `γ_{r,b}⁻¹ = β_{1/r,b}` -/

/-- Pointwise form: `γ_{r,b} t = 0` at `t = 0`, else `r·t + b`. -/
theorem tokenBucketENN_apply (r b t : ℝ≥0∞) :
    tokenBucketENN r b t = if t = 0 then 0 else r * t + b := by
  rw [tokenBucketENN, tokenBucketV]
  simp only [Pi.inf_apply, delay_apply]
  by_cases h : t = 0
  · subst h; simp
  · rw [if_neg h, if_neg (show ¬ t ≤ 0 by simpa using h), min_top_right]

/-- `γ_{r,b}⁻¹ = β_{1/r,b}`: the affine/token-bucket inverse is the rate-latency
curve of reciprocal rate `r⁻¹` and latency `b` (for `0 < x`, `0 < r < ⊤`). The
`0`-at-`0` of `γ` excludes `t = 0` from the admissible set, so the value is
`rateLatencyENN r⁻¹ b x = r⁻¹·(x - b)` even when `x ≤ b`. -/
theorem pseudoInv_tokenBucketENN (r b : ℝ≥0∞) (hr : 0 < r) (hrtop : r ≠ ⊤)
    (x : ℝ≥0∞) (hx : 0 < x) :
    pseudoInv (tokenBucketENN r b) x = rateLatencyENN r⁻¹ b x := by
  show pseudoInv (tokenBucketENN r b) x = r⁻¹ * (x - b)
  have hr0 : r ≠ 0 := ne_of_gt hr
  apply le_antisymm
  · -- `≤`: exhibit an admissible time at the claimed value.
    by_cases hbx : b < x
    · -- `b < x`: the value `d = r⁻¹·(x-b) > 0` is itself admissible.
      apply pseudoInv_le_of_le_apply
      rw [tokenBucketENN_apply]
      have hd0 : r⁻¹ * (x - b) ≠ 0 := by
        rw [ne_eq, mul_eq_zero, not_or, ENNReal.inv_eq_zero]
        refine ⟨hrtop, ?_⟩
        rw [tsub_eq_zero_iff_le, not_le]; exact hbx
      rw [if_neg hd0, ← mul_assoc, ENNReal.mul_inv_cancel hr0 hrtop, one_mul,
        tsub_add_cancel_of_le hbx.le]
    · -- `x ≤ b`: value is `0`; every positive time is admissible.
      rw [not_lt] at hbx
      rw [tsub_eq_zero_of_le hbx, mul_zero]
      apply le_of_forall_gt_imp_ge_of_dense
      intro a ha
      apply pseudoInv_le_of_le_apply
      rw [tokenBucketENN_apply, if_neg (ne_of_gt ha)]
      exact le_trans hbx le_add_self
  · -- `≥`: every admissible time is `≥ r⁻¹·(x-b)`.
    apply le_pseudoInv
    intro t ht
    rw [tokenBucketENN_apply] at ht
    have htne : t ≠ 0 := by
      rintro rfl
      rw [if_pos rfl] at ht
      exact (lt_irrefl 0 (lt_of_lt_of_le hx ht))
    rw [if_neg htne] at ht
    rw [ENNReal.inv_mul_le_iff hr0 hrtop, tsub_le_iff_right]
    exact ht

/-- Degenerate rate `r = 0`: `γ_{0,b}⁻¹ = δ_b`. The token-bucket `tokenBucketENN 0 b`
is `0` at `0` and the constant burst `b` for `t > 0`, so a level `x` is reached
(at any positive time) iff `x ≤ b` — its inverse is the delay curve with
threshold `b`, for every `x` (no positivity needed). -/
theorem pseudoInv_tokenBucketENN_zero_rate (b x : ℝ≥0∞) :
    pseudoInv (tokenBucketENN 0 b) x = delayENN b x := by
  rw [delayENN, delay_apply]
  by_cases hxb : x ≤ b
  · -- `x ≤ b`: reached at every positive time, so the first crossing is `0`.
    rw [if_pos hxb]
    apply le_antisymm _ bot_le
    apply le_of_forall_gt_imp_ge_of_dense
    intro a ha
    have ha0 : a ≠ 0 := by simpa using ha.ne'
    apply pseudoInv_le_of_le_apply
    rw [tokenBucketENN_apply, if_neg ha0, zero_mul, zero_add]
    exact hxb
  · -- `x > b`: never reached, so the admissible set is empty and the inf is `⊤`.
    rw [if_neg hxb, pseudoInv,
      show levelGeSet (tokenBucketENN 0 b) x = ∅ from ?_, sInf_empty]
    ext t
    simp only [mem_levelGeSet, ge_iff_le, mem_empty_iff_false, iff_false, not_le]
    rw [tokenBucketENN_apply]
    rcases eq_or_ne t 0 with ht | ht
    · subst ht; rw [if_pos rfl]; exact lt_of_le_of_lt bot_le (not_le.mp hxb)
    · rw [if_neg ht, zero_mul, zero_add]; exact not_le.mp hxb

/-! ## Pure delay: `δ_d⁻¹ = γ_{0,d}`

The delay inverts to the rate-`0`, latency-`d` token-bucket `tokenBucketENN 0 d`:
the constant `d` for `x > 0`, and `0` at `x = 0` (the dual of
`pseudoInv_tokenBucketENN_zero_rate`). The two branches are `pseudoInv_delayENN_pos`
and `pseudoInv_delayENN_zero` in `PseudoInverse`. -/

/-- `δ_d⁻¹ = γ_{0,d}`: the delay inverts to the rate-`0` token-bucket
`tokenBucketENN 0 d`, for every `x`. -/
theorem pseudoInv_delayENN_eq_tokenBucket (d x : ℝ≥0∞) :
    pseudoInv (delayENN d) x = tokenBucketENN 0 d x := by
  rw [tokenBucketENN_apply, zero_mul, zero_add]
  rcases eq_or_ne x 0 with hx | hx
  · subst hx; rw [if_pos rfl]; exact pseudoInv_delayENN_zero d
  · rw [if_neg hx]; exact pseudoInv_delayENN_pos d (pos_iff_ne_zero.mpr hx)

end DeepWiki
