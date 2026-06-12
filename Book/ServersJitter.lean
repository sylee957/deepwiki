import Book.Continuity
import Book.DeviationsBounds
import Book.RealCurvesDeconv

/-! # Servers as jitters
A server whose per-bit delay always lies between `dm` and `dM` is captured
by pure-delay service curves: the minimal delay gives the maximal service
curve `δ_dm` (`D ≤ A ∗ δ_dm`) and the maximal delay gives the min-plus
service curve `δ_dM` (`A ∗ δ_dM ≤ D`); a server offering a min-plus curve
`β` to an `α`-constrained arrival is in particular a jitter with
`dM = hDev α β`. The output is then constrained by
`(α ∗ δ_dm) ⊘ δ_dM = α ⊘ δ_(dM − dm)`; `dM − dm` is the jitter. -/

namespace DeepWiki

open Set Topology Filter
open scoped Classical NNReal ENNReal

namespace Deviation

/-- **A minimal per-bit delay caps the output**: if every bit waits at
least `dm` (`dm ≤ delayAt A D t` for all `t`), then for left-continuous
monotone `D` the output is below the `dm`-shifted input,
`D t ≤ A (t − dm)` — the maximal service curve `δ_dm`. -/
theorem le_apply_tsub_of_le_delayAt {A D : ℝ≥0 → ℝ≥0} {dm : ℝ≥0}
    (hDmono : Monotone D) (hDlc : IsLeftContinuous D)
    (hc : ∀ x, D x ≤ A x)
    (hmin : ∀ t, (dm : ℝ≥0∞) ≤ delayAt A D t) (t : ℝ≥0) :
    D t ≤ A (t - dm) := by
  rcases eq_zero_or_pos dm with rfl | hdm
  · rw [tsub_zero]
    exact hc t
  -- shifts below `dm` are inadmissible: `D < A u` on `[u, u + dm)`
  have key : ∀ u, D (u + dm) ≤ A u := by
    intro u
    have hlt : ∀ s, s < u + dm → u ≤ s → D s < A u := by
      intro s hs hus
      by_contra hcon
      rw [not_lt] at hcon
      have hadm : A u ≤ D (u + (s - u)) := by
        rwa [add_tsub_cancel_of_le hus]
      have := le_trans (hmin u) (hDevAt_le hadm)
      have hsd : s - u < dm := by
        have : s < dm + u := by rwa [add_comm u dm] at hs
        exact tsub_lt_iff_right hus |>.mpr (by rwa [add_comm])
      exact absurd this (not_le.mpr (ENNReal.coe_lt_coe.mpr hsd))
    -- pass to the left limit at `u + dm`
    have hne : (𝓝[<] (u + dm)).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨u, lt_add_of_pos_right u hdm⟩
    refine le_of_tendsto (hDlc (u + dm)).tendsto ?_
    filter_upwards [Ioo_mem_nhdsLT (lt_add_of_pos_right u hdm)] with s hs
    exact (hlt s hs.2 hs.1.le).le
  rcases le_or_gt t dm with htd | htd
  · -- nothing leaves before `dm`
    calc D t ≤ D (0 + dm) := hDmono (by rwa [zero_add])
      _ ≤ A 0 := key 0
      _ = A (t - dm) := by rw [tsub_eq_zero_of_le htd]
  · calc D t = D ((t - dm) + dm) := by rw [tsub_add_cancel_of_le htd.le]
      _ ≤ A (t - dm) := key (t - dm)

/-- **A maximal delay floors the output**: if `delay A D ≤ dM`, then for
monotone `D` (and `A 0 = 0`) every shift `d` beyond `dM` serves:
`A (t − d) ≤ D t` — the min-plus service curve `δ_d`. (The book states the
bound at `dM` itself, which fails for the infimum-based `delayAt` when the
shift is not attained — a right jump of `D` just after `t + dM`; the
strict-`d` form is sharp.) -/
theorem apply_tsub_le_of_delay_le {A D : ℝ≥0 → ℝ≥0} {dM : ℝ≥0∞}
    (hA0 : A 0 = 0) (hDmono : Monotone D)
    (hdel : delay A D ≤ dM) {d : ℝ≥0} (hd : dM < (d : ℝ≥0∞)) (t : ℝ≥0) :
    A (t - d) ≤ D t := by
  rcases le_or_gt t d with htd | htd
  · rw [tsub_eq_zero_of_le htd, hA0]
    exact zero_le'
  · have h := le_of_hDev_lt hDmono (lt_of_le_of_lt hdel hd) (t - d)
    rwa [tsub_add_cancel_of_le htd.le] at h

/-- **Service curve for a jitter**: a server offering the min-plus service
curve `β` to an `α`-constrained arrival is in particular a jitter — it
offers every pure-delay service curve beyond the horizontal deviation:
`hDev α β < d` gives `A (t − d) ≤ D t`. -/
theorem apply_tsub_le_of_hDev_lt {A D : ℝ≥0 → ℝ≥0} {α β : ℝ≥0 → ℝ≥0∞}
    (hA0 : A 0 = 0) (hA : Monotone A) (hβ : Monotone β)
    (hDmono : Monotone D)
    (harr : IsMaximalArrivalBound (liftENN A) α)
    (hserv : ∀ t, minConv (liftENN A) β t ≤ (D t : ℝ≥0∞))
    {d : ℝ≥0} (hd : (hDev α β : ℝ≥0∞) < d) (t : ℝ≥0) :
    A (t - d) ≤ D t :=
  apply_tsub_le_of_delay_le hA0 hDmono (delay_le_hDev hA hβ harr hserv) hd t

end Deviation

/-! ## Book restatement (server as a jitter)
A server whose per-bit delay always lies between `dm` and `dM` offers the
maximal service curve `δ_dm` and — in the sharp shifted form — the
min-plus service curve `δ_d` for every `d` beyond `dM`:
`dm ≤ inf_t d(A, D, t)` gives `D ≤ A ∗ δ_dm`, and `d(A, D) ≤ dM` gives
`A ∗ δ_d ≤ D` for `dM < d`. -/
example {A D : ℝ≥0 → ℝ≥0} {dm : ℝ≥0} {dM : ℝ≥0∞}
    (hA0 : A 0 = 0) (hAmono : Monotone A) (hDmono : Monotone D)
    (hDlc : IsLeftContinuous D) (hc : ∀ x, D x ≤ A x)
    (hmin : ∀ t, (dm : ℝ≥0∞) ≤ Deviation.delayAt A D t)
    (hdel : Deviation.delay A D ≤ dM)
    {d : ℝ≥0} (hd : dM < (d : ℝ≥0∞)) (t : ℝ≥0) :
    (D t : ℝ≥0∞) ≤ minConv (Deviation.liftENN A) (delayNN dm) t
      ∧ minConv (Deviation.liftENN A) (delayNN d) t ≤ (D t : ℝ≥0∞) := by
  have hAmonoE : Monotone (Deviation.liftENN A) :=
    fun u v huv => ENNReal.coe_le_coe.mpr (hAmono huv)
  constructor
  · rw [conv_delayNN _ hAmonoE dm]
    show (D t : ℝ≥0∞) ≤ (A (t - dm) : ℝ≥0∞)
    exact_mod_cast Deviation.le_apply_tsub_of_le_delayAt hDmono hDlc hc hmin t
  · rw [conv_delayNN _ hAmonoE d]
    show (A (t - d) : ℝ≥0∞) ≤ (D t : ℝ≥0∞)
    exact_mod_cast Deviation.apply_tsub_le_of_delay_le hA0 hDmono hdel hd t

/-! The output of a jitter is constrained by the jitter deconvolution:
with minimal and maximal delays `a ≤ b`, the output arrival curve
`(α ∗ δ_a) ⊘ δ_b` collapses to `α ⊘ δ_(b − a)` — only the jitter `b − a`
matters. -/
example {α : ℝ≥0 → ℝ≥0∞} (hmono : Monotone α) {a b : ℝ≥0} (hab : a ≤ b) :
    minDeconv (minConv α (delayNN a)) (delayNN b)
      = minDeconv α (delayNN (b - a)) :=
  minDeconv_conv_delayNN_delayNN hmono hab

end DeepWiki
