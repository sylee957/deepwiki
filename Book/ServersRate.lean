import Book.ServiceCurveStrictMinimal
import Book.DeviationsBoundsTight
import Book.RealCurvesRegularity

/-! # Rate servers
The guaranteed-rate server offers the strict service curve `λ_R`, hence
also the min-plus service curve `λ_R`. The constant-rate server moreover
caps its increments by the rate — the maximal service curve `λ_R` (stated
at the `ℝ≥0∞` level) — and a pair served at `λ_R` from both sides is
exactly a greedy `λ_R`-shaper pair, whose output is `A ∗ λ_R`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **A rate-capped server offers the maximal service curve `λ_R`**: if
the output never exceeds rate `R` — `D t ≤ D s + R·(t − s)` for `s ≤ t` —
then `D ≤ A ∗ λ_R` across every split. -/
theorem coe_le_minConv_rateNN_of_increment {A D : ℝ≥0 → ℝ≥0} {R : ℝ≥0}
    (hc : ∀ x, D x ≤ A x)
    (hinc : ∀ s t, s ≤ t → D t ≤ D s + R * (t - s)) (t : ℝ≥0) :
    (D t : ℝ≥0∞) ≤ minConv (Deviation.liftENN A) (rateNN R) t := by
  refine le_minConv fun u v huv => ?_
  have hut : u ≤ t := by rw [← huv]; exact le_self_add
  have hv : t - u = v := by rw [← huv, add_tsub_cancel_left]
  have h : D t ≤ A u + R * v := by
    calc D t ≤ D u + R * (t - u) := hinc u t hut
      _ ≤ A u + R * (t - u) := add_le_add_left (hc u) _
      _ = A u + R * v := by rw [hv]
  show (D t : ℝ≥0∞) ≤ (A u : ℝ≥0∞) + (R : ℝ≥0∞) * (v : ℝ≥0∞)
  rw [← ENNReal.coe_mul, ← ENNReal.coe_add]
  exact_mod_cast h

/-! ## Book restatement (guaranteed-rate and constant-rate servers)
A guaranteed-rate server serves at least `R` on every backlogged period —
the strict service curve `λ_R` — hence also offers the min-plus service
curve `λ_R`. -/
example {S : Curve → Curve → Prop} {R : ℝ≥0} (hSrv : IsServer S)
    (hβ : IsStrictMinimalServiceCurve (rate R) S) :
    IsMinimalServiceCurve (liftEReal (rate R)) S :=
  hβ.isMinimalServiceCurve hSrv.1

/-! A constant-rate server serves *exactly* at rate `R`: it offers `λ_R`
both as a min-plus service curve (it is strict `λ_R`) and as a maximal
one (its increments are rate-capped, `coe_le_minConv_rateNN_of_increment`
at the `ℝ≥0∞` level) — and a pair served at `λ_R` from both sides is
exactly a greedy `λ_R`-shaper pair. -/
example {R : ℝ≥0} {A D : Curve}
    (hmin : minimalServiceRel (rateEReal R) A D)
    (hmax : maximalServiceRel (rateEReal R) A D) :
    greedyShaperRel (rateEReal R) A D :=
  (mem_greedyShaperRel_iff_minimal_and_maximal
    (le_of_eq (rateEReal_zero_eq R))).mpr ⟨hmin, hmax⟩

/-! The greedy `λ_R`-output itself, packaged as a curve (the
piecewise-continuity witness is the price of `C`-membership). -/
example (A : Curve) {R : ℝ≥0}
    (hpwc : IsPiecewiseContinuous (greedyFun A (rateEReal R))) :
    greedyShaperRel (rateEReal R) A
      (greedyCurve A (rateEReal R) (rateEReal_mono R) (rateEReal_zero_eq R)
        (rateEReal_leftCont R) hpwc) :=
  Deviation.greedyShaperRel_greedyCurve A (rateEReal_mono R)
    (rateEReal_zero_eq R) (rateEReal_leftCont R) hpwc

/-- The rate input as a curve. -/
noncomputable def rateCurve (R : ℝ≥0) : Curve where
  toFun := rate R
  mono := rate_mono R
  zero := mul_zero R
  pwc := isPiecewiseContinuous_of_continuous _ (rate_continuous R)
  leftCont := isLeftContinuous_of_continuous _ (rate_continuous R)

/-- `rateCurve R t = R * t`. -/
@[simp] theorem rateCurve_apply (R t : ℝ≥0) :
    rateCurve R t = R * t := rfl

/-- The convolution against a rate obeys the rate's additive
Lipschitz bound: shift each split of the smaller time. -/
theorem minConvProj_rate_le_add {β : ℝ≥0 → ℝ≥0} {R : ℝ≥0} :
    ∀ v w, w ≤ v → minConvProj (rate R) β v
      ≤ minConvProj (rate R) β w + R * (v - w) := by
  intro v w hwv
  rw [← tsub_le_iff_right]
  refine le_minConvProj fun u x hux => ?_
  rw [tsub_le_iff_right]
  refine le_trans (minConvProj_le_add (u := u + (v - w)) (s := x) ?_) ?_
  · rw [add_right_comm, hux, add_tsub_cancel_of_le hwv]
  · refine le_of_eq ?_
    rw [rate_apply, rate_apply, mul_add]
    ring

/-- The rate convolution `λ_R ∗ β` as a curve, for monotone `β` null
at the origin: Lipschitz, hence continuous. -/
noncomputable def rateConvCurve (β : ℝ≥0 → ℝ≥0) (R : ℝ≥0)
    (hmono : Monotone β) (h0 : β 0 = 0) : Curve where
  toFun := minConvProj (rate R) β
  mono := minConvProj_mono (rate_mono R) hmono
  zero := by
    show minConvProj (rate R) β 0 = 0
    rw [minConvProj_zero_eq, rate_apply, mul_zero, zero_add, h0]
  pwc := isPiecewiseContinuous_of_continuous _
    (continuous_of_monotone_of_lipschitz_bound
      (minConvProj_mono (rate_mono R) hmono) minConvProj_rate_le_add)
  leftCont := isLeftContinuous_of_continuous _
    (continuous_of_monotone_of_lipschitz_bound
      (minConvProj_mono (rate_mono R) hmono) minConvProj_rate_le_add)

/-- `rateConvCurve β R … t` is the projected convolution at `t`. -/
theorem rateConvCurve_apply {β : ℝ≥0 → ℝ≥0} {R : ℝ≥0}
    (hmono : Monotone β) (h0 : β 0 = 0) (t : ℝ≥0) :
    rateConvCurve β R hmono h0 t = minConvProj (rate R) β t := rfl

end DeepWiki
