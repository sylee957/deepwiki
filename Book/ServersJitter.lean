import Book.Continuity
import Book.DeviationsBounds
import Book.RealCurvesDeconv

/-! # Servers as jitters
A server whose per-bit delay always lies between `dm` and `dM` is captured
by pure-delay service curves: the minimal delay gives the maximal service
curve `δ_dm` (`D ≤ A ∗ δ_dm`), and the maximal delay gives the min-plus
service curve `δ_dM` (`A ∗ δ_dM ≤ D`) — at `dM` itself for left-continuous
arrivals, and at every `d > dM` with no continuity at all (left-continuity
of `A` is necessary at the bound: `not_forall_apply_tsub_le_of_delay_le`).
A server offering a min-plus curve `β` to an `α`-constrained arrival is in
particular a jitter with `dM = hDev α β`. The output is then constrained
by `(α ∗ δ_dm) ⊘ δ_dM = α ⊘ δ_(dM − dm)`; `dM − dm` is the jitter. -/

namespace DeepWiki

open Set Topology Filter
open scoped Classical NNReal ENNReal

namespace Deviation

/-- **A minimal per-bit delay caps the output**: if every bit waits at
least `dm` (`dm ≤ delayAt A D t` for all `t`), then for left-continuous
monotone `D` the output is below the `dm`-shifted input,
`D t ≤ A (t − dm)` — the maximal service curve `δ_dm`. -/
theorem le_apply_tsub_of_le_delayAt {A D : ℝ≥0 → ℝ≥0} {dm : ℝ≥0}
    (hDlc : IsLeftContinuous D) (hc : ∀ x, D x ≤ A x)
    (hmin : ∀ t, (dm : ℝ≥0∞) ≤ delayAt A D t) (t : ℝ≥0) :
    D t ≤ A (t - dm) := by
  rcases eq_zero_or_pos dm with rfl | hdm
  · rw [tsub_zero]
    exact hc t
  -- shifts below `dm` are inadmissible: `D < A u` on `[u, u + dm)`
  have hlt : ∀ u s, s < u + dm → u ≤ s → D s < A u := by
    intro u s hs hus
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
  have key : ∀ u, D (u + dm) ≤ A u := by
    intro u
    have hne : (𝓝[<] (u + dm)).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨u, lt_add_of_pos_right u hdm⟩
    refine le_of_tendsto (hDlc (u + dm)).tendsto ?_
    filter_upwards [Ioo_mem_nhdsLT (lt_add_of_pos_right u hdm)] with s hs
    exact (hlt u s hs.2 hs.1.le).le
  rcases le_or_gt t dm with htd | htd
  · -- nothing beyond `A 0` leaves before `dm`
    rw [tsub_eq_zero_of_le htd]
    rcases eq_or_lt_of_le htd with heq | hlt'
    · have h := key 0
      rw [zero_add] at h
      rw [heq]
      exact h
    · exact (hlt 0 t (by rwa [zero_add]) zero_le').le
  · calc D t = D ((t - dm) + dm) := by rw [tsub_add_cancel_of_le htd.le]
      _ ≤ A (t - dm) := key (t - dm)

/-- **A maximal delay floors the output**, continuity-free form: if
`delay A D ≤ dM`, then for monotone `D` (and `A 0 = 0`) every shift `d`
beyond `dM` serves: `A (t − d) ≤ D t` — the min-plus service curve `δ_d`.
At `dM` itself the bound needs `A` left-continuous
(`apply_tsub_le_of_delay_le_of_leftCont`); without that it fails
(`not_forall_apply_tsub_le_of_delay_le`). -/
theorem apply_tsub_le_of_delay_le {A D : ℝ≥0 → ℝ≥0} {dM : ℝ≥0∞}
    (hA0 : A 0 = 0) (hDmono : Monotone D)
    (hdel : delay A D ≤ dM) {d : ℝ≥0} (hd : dM < (d : ℝ≥0∞)) (t : ℝ≥0) :
    A (t - d) ≤ D t := by
  rcases le_or_gt t d with htd | htd
  · rw [tsub_eq_zero_of_le htd, hA0]
    exact zero_le'
  · have h := le_of_hDev_lt hDmono (lt_of_le_of_lt hdel hd) (t - d)
    rwa [tsub_add_cancel_of_le htd.le] at h

/-- **A maximal delay floors the output**, at the bound itself: for
left-continuous `A`, `delay A D ≤ dM` gives `A (t − dM) ≤ D t` — the
min-plus service curve `δ_dM`. The book's contraposition concludes a
strict inequality from a non-attained infimum; the repair routes through
the left limit of `A` at `t − dM` instead. -/
theorem apply_tsub_le_of_delay_le_of_leftCont {A D : ℝ≥0 → ℝ≥0} {dM : ℝ≥0}
    (hA0 : A 0 = 0) (hAlc : IsLeftContinuous A) (hDmono : Monotone D)
    (hdel : delay A D ≤ (dM : ℝ≥0∞)) (t : ℝ≥0) :
    A (t - dM) ≤ D t := by
  rcases le_or_gt t dM with htd | htd
  · rw [tsub_eq_zero_of_le htd, hA0]
    exact zero_le'
  -- every `s` strictly before `t − dM` is served by `t`
  have key : ∀ s, s < t - dM → A s ≤ D t := by
    intro s hs
    have hst : (dM : ℝ≥0∞) < ((t - s : ℝ≥0) : ℝ≥0∞) := by
      refine ENNReal.coe_lt_coe.mpr ?_
      exact lt_tsub_iff_left.mpr (lt_tsub_iff_right.mp hs)
    have h := le_of_hDev_lt hDmono (lt_of_le_of_lt hdel hst) s
    rwa [add_tsub_cancel_of_le (le_trans hs.le (tsub_le_self))] at h
  -- pass to the left limit of `A` at `t − dM`
  have hpos : 0 < t - dM := tsub_pos_of_lt htd
  have hne : (𝓝[<] (t - dM)).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
  refine le_of_tendsto (hAlc (t - dM)).tendsto ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact key s hs

/-- Left-continuity of the arrival is necessary for the bound at `dM`:
the universally quantified statement without it is false — a step arrival
carrying its jump value on the right keeps `delay A D ≤ dM` while
exceeding `D` at the shift `dM` exactly. -/
theorem not_forall_apply_tsub_le_of_delay_le :
    ¬ ∀ (A D : ℝ≥0 → ℝ≥0) (dM : ℝ≥0), A 0 = 0 → Monotone A → Monotone D →
      delay A D ≤ (dM : ℝ≥0∞) → ∀ t, A (t - dM) ≤ D t := by
  intro h
  have hbad := h (fun t => if t < 1 then 0 else 1)
    (fun t => if t ≤ 2 then 0 else 1) 1
    (by simp)
    (fun a b hab => by
      dsimp only
      split_ifs with ha hb hb
      · exact le_rfl
      · exact zero_le'
      · exact absurd (lt_of_le_of_lt hab hb) ha
      · exact le_rfl)
    (fun a b hab => by
      dsimp only
      split_ifs with ha hb hb
      · exact le_rfl
      · exact zero_le'
      · exact absurd (le_trans hab hb) ha
      · exact le_rfl)
    ?_ 2
  · -- `A (2 − 1) = A 1 = 1` exceeds `D 2 = 0`
    have h21 : (2 : ℝ≥0) - 1 = 1 := tsub_eq_of_eq_add (by norm_num)
    rw [h21, if_neg (lt_irrefl (1 : ℝ≥0)), if_pos (le_refl (2 : ℝ≥0))] at hbad
    exact absurd hbad (by norm_num)
  · -- every shift `1 + ε` is admissible everywhere, so `delay ≤ 1`
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    refine hDev_le fun t => ?_
    refine le_trans (hDevAt_le (d := 1 + ε) ?_) ?_
    · dsimp only
      by_cases ht : t < 1
      · rw [if_pos ht]
        exact zero_le'
      · -- `t ≥ 1` forces `t + (1 + ε) > 2`
        have h2 : (2 : ℝ≥0) < t + (1 + ε) :=
          calc (2 : ℝ≥0) = 1 + 1 := by norm_num
            _ < t + (1 + ε) :=
              add_lt_add_of_le_of_lt (not_lt.mp ht)
                (lt_add_of_pos_right 1 hε)
        rw [if_neg ht, if_neg (not_le.mpr h2)]
    · show ((1 + ε : ℝ≥0) : ℝ≥0∞) ≤ ((1 : ℝ≥0) : ℝ≥0∞) + (ε : ℝ≥0∞)
      rw [ENNReal.coe_add]

/-- **Service curve for a jitter**: a server offering the min-plus service
curve `β` to an `α`-constrained arrival is in particular a jitter — it
offers every pure-delay service curve beyond the horizontal deviation:
`hDev α β < d` gives `A (t − d) ≤ D t`. -/
theorem apply_tsub_le_of_hDev_lt {A D : ℝ≥0 → ℝ≥0} {α β : ℝ≥0 → ℝ≥0∞}
    (hA0 : A 0 = 0) (hAmono : Monotone A) (hβmono : Monotone β)
    (hDmono : Monotone D)
    (harr : IsMaximalArrivalBound (liftENN A) α)
    (hserv : ∀ t, minConv (liftENN A) β t ≤ (D t : ℝ≥0∞))
    {d : ℝ≥0} (hd : (hDev α β : ℝ≥0∞) < d) (t : ℝ≥0) :
    A (t - d) ≤ D t :=
  apply_tsub_le_of_delay_le hA0 hDmono (delay_le_hDev hAmono hβmono harr hserv) hd t

/-- **Service curve for a jitter**, at the deviation itself: for a
left-continuous arrival, a `β`-server serving an `α`-constrained flow
offers the pure-delay min-plus curve at any `dM` above `hDev α β`:
`A (t − dM) ≤ D t`. -/
theorem apply_tsub_le_of_hDev_le_of_leftCont {A D : ℝ≥0 → ℝ≥0}
    {α β : ℝ≥0 → ℝ≥0∞} {dM : ℝ≥0}
    (hA0 : A 0 = 0) (hAmono : Monotone A) (hAlc : IsLeftContinuous A)
    (hβmono : Monotone β) (hDmono : Monotone D)
    (harr : IsMaximalArrivalBound (liftENN A) α)
    (hserv : ∀ t, minConv (liftENN A) β t ≤ (D t : ℝ≥0∞))
    (hd : (hDev α β : ℝ≥0∞) ≤ (dM : ℝ≥0∞)) (t : ℝ≥0) :
    A (t - dM) ≤ D t :=
  apply_tsub_le_of_delay_le_of_leftCont hA0 hAlc hDmono
    (le_trans (delay_le_hDev hAmono hβmono harr hserv) hd) t

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
    exact_mod_cast Deviation.le_apply_tsub_of_le_delayAt hDlc hc hmin t
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
