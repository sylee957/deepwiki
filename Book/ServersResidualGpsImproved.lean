import Book.ServersResidualGps

/-! # GPS residual service, improved
The GPS residual ignores the cross-traffic intensity. When a flow is
arrival-constrained, the aggregate of the *other* flows keeps a
strict curve that recovers the constrained flow's share past its
crossing time: `(β − α)·1_{[T,∞)}` — the stepping stone to the
improved per-flow GPS residual. The book routes the proof through a
variable-capacity witness; every window it inspects turns out to be
backlogged, so the strict aggregate bound suffices and the detour
dissolves. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The gated residual `(β − α)·1_{[T,∞)}`: the leftover after the
gate time `T`, null before it. -/
noncomputable def gatedResidual (β α : ℝ≥0 → ℝ≥0) (T : ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun v => if T ≤ v then β v - α v else 0

/-- Past the gate the gated residual is the clamped difference. -/
theorem gatedResidual_apply_of_le {β α : ℝ≥0 → ℝ≥0} {T v : ℝ≥0}
    (h : T ≤ v) : gatedResidual β α T v = β v - α v := if_pos h

/-- Before the gate the gated residual is null. -/
theorem gatedResidual_apply_of_lt {β α : ℝ≥0 → ℝ≥0} {T v : ℝ≥0}
    (h : v < T) : gatedResidual β α T v = 0 := if_neg (not_le.mpr h)

/-- The gated residual stays below the curve. -/
theorem gatedResidual_le_apply (β α : ℝ≥0 → ℝ≥0) (T v : ℝ≥0) :
    gatedResidual β α T v ≤ β v := by
  rcases le_or_gt T v with h | h
  · rw [gatedResidual_apply_of_le h]
    exact tsub_le_self
  · rw [gatedResidual_apply_of_lt h]
    exact zero_le'

/-- **The constrained flow releases its share past its crossing
time** — the improved-GPS aggregation step: in a GPS server with
strict aggregate `β` and flow `k` arrival-constrained by `α`, the
remaining flows' aggregate obeys the strict inequality for the gated
residual `(β − α)·1_{[T,∞)}`, provided that from `T` on the weighted
arrival curve sits below flow `k`'s share (`hcross`) and the
weighted gap grows (`hgrow`). Every window of the argument is
backlogged, so no variable-capacity witness is needed: the start `p`
of flow `k`'s backlogged period at `s` makes `(p, t]` backlogged for
the total aggregate, GPS grants flow `k` its share of the service on
`(p, s]`, and the arrivals over `(p, t]` cap what flow `k` can take
from the rest. -/
theorem add_gatedResidual_le_of_isGps {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    {φ : ι → ℝ≥0} {As Ds : ι → Curve} {β α : ℝ≥0 → ℝ≥0} {T : ℝ≥0}
    (hΦ : 0 < ∑ j, φ j)
    (hc : ∀ j, Ds j ≤ As j)
    (hgps : IsGps φ (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    {k : ι} (harr : IsMaximalArrivalBound ⇑(As k) α)
    (hcross : ∀ x, T ≤ x → (∑ j, φ j) * α x ≤ φ k * β x)
    (hgrow : ∀ x y, T ≤ x → x ≤ y →
      φ k * β x + (∑ j, φ j) * α y ≤ φ k * β y + (∑ j, φ j) * α x)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged
      (fun x => ∑ j ∈ Finset.univ.erase k, (As j) x)
      (fun x => ∑ j ∈ Finset.univ.erase k, (Ds j) x) (Set.Ioc s t)) :
    (∑ j ∈ Finset.univ.erase k, (Ds j) s)
      + gatedResidual β α T (t - s)
      ≤ ∑ j ∈ Finset.univ.erase k, (Ds j) t := by
  rcases lt_or_ge (t - s) T with hT | hT
  · rw [gatedResidual_apply_of_lt hT, add_zero]
    exact Finset.sum_le_sum fun j _ => (Ds j).mono hst
  rw [gatedResidual_apply_of_le hT]
  -- the start of flow `k`'s backlogged period at `s`
  set p := start ⇑(As k) ⇑(Ds k) s with hpdef
  have hps : p ≤ s := start_le _ _ s
  have hpt : p ≤ t := hps.trans hst
  have hblk : IsBacklogged ⇑(As k) ⇑(Ds k) (Set.Ioc p s) :=
    isBacklogged_Ioc_start (hc k) s
  have hblT1 : IsBacklogged (fun x => ∑ j, (As j) x)
      (fun x => ∑ j, (Ds j) x) (Set.Ioc p s) :=
    isBacklogged_sum_of_isBacklogged (fun j _ x => hc j x)
      (Finset.mem_univ k) hblk
  have hblT2 : IsBacklogged (fun x => ∑ j, (As j) x)
      (fun x => ∑ j, (Ds j) x) (Set.Ioc s t) :=
    isBacklogged_sum_of_isBacklogged_subset (fun j _ x => hc j x)
      (Finset.erase_subset k Finset.univ) hbl
  have hblT : IsBacklogged (fun x => ∑ j, (As j) x)
      (fun x => ∑ j, (Ds j) x) (Set.Ioc p t) := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc hps hst]
    exact hblT1.union hblT2
  -- the strict aggregate bounds on the two backlogged windows
  have ha := hstrict s t hst hblT2
  have hb := hstrict p t hpt hblT
  -- GPS grants flow `k` its share of the service on `(p, s]`
  have hshare := mul_sum_le_sum_mul_of_isGps (J := Finset.univ)
    hgps hps hblk
  -- equality at the start, the arrival cap, causality
  have hd : (As k) p = (Ds k) p :=
    (As k).apply_start_eq (Ds k) (fun x => hc k x) s
  have he : (As k) t ≤ (As k) p + α (t - p) := by
    have h := (isMaximalArrivalBound_iff_increment _ _).mp harr p (t - p)
    rwa [add_tsub_cancel_of_le hpt] at h
  have hf : (Ds k) t ≤ (As k) t := hc k t
  have hg := hgrow (t - s) (t - p) hT (tsub_le_tsub_left hps t)
  -- the arrival curve sits below the curve past the gate
  have hαβ : α (t - s) ≤ β (t - s) := by
    refine le_of_mul_le_mul_left (le_trans (hcross (t - s) hT) ?_) hΦ
    exact mul_le_mul_left
      (Finset.single_le_sum (fun j _ => zero_le') (Finset.mem_univ k))
      (β (t - s))
  -- totals split over `k` and the rest
  have hsplit : ∀ x, (∑ j, (Ds j) x)
      = (Ds k) x + ∑ j ∈ Finset.univ.erase k, (Ds j) x :=
    fun x => (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
  -- monotonicity guards for the truncated subtractions
  have hDmono : (∑ j, (Ds j) p) ≤ ∑ j, (Ds j) s :=
    Finset.sum_le_sum fun j _ => (Ds j).mono hps
  have hkmono : (Ds k) p ≤ (Ds k) s := (Ds k).mono hps
  -- assemble the chain over `ℝ`
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_sub hαβ]
  have haR := NNReal.coe_le_coe.mpr ha
  have hbR := NNReal.coe_le_coe.mpr hb
  have hshareR := NNReal.coe_le_coe.mpr hshare
  have hdR := congrArg NNReal.toReal hd
  have heR := NNReal.coe_le_coe.mpr he
  have hfR := NNReal.coe_le_coe.mpr hf
  have hgR := NNReal.coe_le_coe.mpr hg
  have hsR := congrArg NNReal.toReal (hsplit s)
  have htR := congrArg NNReal.toReal (hsplit t)
  have hpR := congrArg NNReal.toReal (hsplit p)
  push_cast [NNReal.coe_sub hDmono, NNReal.coe_sub hkmono]
    at haR hbR hshareR hdR heR hfR hgR hsR htR hpR
  have hφknn : (0 : ℝ) ≤ (φ k : ℝ) := (φ k).coe_nonneg
  have hΦR : (0 : ℝ) < ∑ j, ((φ j : ℝ≥0) : ℝ) := by
    exact_mod_cast hΦ
  have hΦknn : (0 : ℝ) ≤ (∑ j, ((φ j : ℝ≥0) : ℝ)) - (φ k : ℝ) := by
    have h := Finset.single_le_sum
      (f := fun j => ((φ j : ℝ≥0) : ℝ))
      (fun j _ => (φ j).coe_nonneg) (Finset.mem_univ k)
    linarith
  -- the Φ-weighted goal, then cancel the positive total weight
  have haΦ := mul_le_mul_of_nonneg_left haR hΦknn
  have hbφ := mul_le_mul_of_nonneg_left hbR hφknn
  have heΦ := mul_le_mul_of_nonneg_left heR hΦR.le
  have hfΦ := mul_le_mul_of_nonneg_left hfR hΦR.le
  have hdΦ : (∑ j, ((φ j : ℝ≥0) : ℝ)) * ((As k) p : ℝ)
      = (∑ j, ((φ j : ℝ≥0) : ℝ)) * ((Ds k) p : ℝ) := by rw [hdR]
  have hgoalΦ : (∑ j, ((φ j : ℝ≥0) : ℝ))
      * ((∑ j ∈ Finset.univ.erase k, ((Ds j) s : ℝ))
        + (β (t - s) : ℝ) - (α (t - s) : ℝ))
      ≤ (∑ j, ((φ j : ℝ≥0) : ℝ))
        * ∑ j ∈ Finset.univ.erase k, ((Ds j) t : ℝ) := by
    nlinarith [haΦ, hbφ, hshareR, hgR, heΦ, hfΦ, hdΦ, hsR, htR, hpR]
  have hcancel := le_of_mul_le_mul_left hgoalΦ hΦR
  linarith

end DeepWiki
