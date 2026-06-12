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

end DeepWiki
