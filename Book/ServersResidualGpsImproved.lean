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

/-- **The improved per-flow GPS residual, one peel**: flow `i ≠ k`
keeps the better of its full-GPS share of `β` and its share, among
the remaining flows, of the gated residual the constrained flow `k`
releases. -/
theorem add_max_div_mul_le_of_isGps {ι : Type*} [Fintype ι]
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
    {i : ι} (hik : i ≠ k) {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t)) :
    (Ds i) s
      + max ((φ i / ∑ j, φ j) * β (t - s))
          ((φ i / ∑ j ∈ Finset.univ.erase k, φ j)
            * gatedResidual β α T (t - s))
      ≤ (Ds i) t := by
  have hfull : (Ds i) s + (φ i / ∑ j, φ j) * β (t - s) ≤ (Ds i) t :=
    add_div_mul_le_of_isGps (fun j _ => hc j) hgps
      (fun s t hst hbl => hstrict s t hst hbl)
      (Finset.mem_univ i) hst hbl
  have hgated : (Ds i) s
      + (φ i / ∑ j ∈ Finset.univ.erase k, φ j)
        * gatedResidual β α T (t - s) ≤ (Ds i) t :=
    add_div_mul_le_of_isGps (J := Finset.univ.erase k)
      (fun j _ => hc j) hgps
      (fun s t hst hbl => add_gatedResidual_le_of_isGps hΦ hc hgps
        hstrict harr hcross hgrow hst hbl)
      (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩) hst hbl
  rcases le_total ((φ i / ∑ j, φ j) * β (t - s))
      ((φ i / ∑ j ∈ Finset.univ.erase k, φ j)
        * gatedResidual β α T (t - s)) with hle | hle
  · rwa [max_eq_right hle]
  · rwa [max_eq_left hle]

/-- Relation form: a GPS `n`-server with positive total weight, a
strict aggregate `β`, and flow `k` arrival-constrained offers flow
`i ≠ k` the maximum of its two shares as a strict service curve on
the residual server. -/
theorem isStrictMinimalServiceCurve_max_residualServer_of_isGps
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : (ι → Curve) → (ι → Curve) → Prop}
    {φ : ι → ℝ≥0} {β α : ℝ≥0 → ℝ≥0} {T : ℝ≥0} {k i : ι}
    (hΦ : 0 < ∑ j, φ j) (hik : i ≠ k)
    (hcaus : IsCausalN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hgps : IsGpsServerN φ S)
    (hcross : ∀ x, T ≤ x → (∑ j, φ j) * α x ≤ φ k * β x)
    (hgrow : ∀ x y, T ≤ x → x ≤ y →
      φ k * β x + (∑ j, φ j) * α y ≤ φ k * β y + (∑ j, φ j) * α x) :
    IsStrictMinimalServiceCurve
      (fun v => max ((φ i / ∑ j, φ j) * β v)
        ((φ i / ∑ j ∈ Finset.univ.erase k, φ j)
          * gatedResidual β α T v))
      (residualServer (fun A D => S A D
        ∧ IsMaximalArrivalBound ⇑(A k) α) i) := by
  rintro Ai Di ⟨As, Ds, ⟨hp, harr⟩, rfl, rfl⟩ s t hst hbl
  exact add_max_div_mul_le_of_isGps hΦ
    (fun j => hcaus As Ds hp j) (hgps As Ds hp)
    (hβ.sum_strict hp) harr hcross hgrow hik hst hbl

/-! ## Book restatement (towards the improved GPS residual)
The two lemmas on the way to the improved GPS theorem: in a GPS
`n`-server offering a strict `β` whose flow `k` has a (concave)
arrival curve `α`, with `β` convex of finite asymptotic rate — here
the consequences past the crossing time `T` taken as hypotheses —
the other flows' aggregate keeps the strict gated residual
`(β − α)·1_{[T,∞)}`, and each flow `i ≠ k` keeps the maximum of its
full share `(φᵢ/Φ)β` and its remaining share of the gated residual.
The book proves the first through a variable-capacity witness;
every window of its argument is backlogged, so the strict bound
carries the proof by itself. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : (ι → Curve) → (ι → Curve) → Prop}
    {φ : ι → ℝ≥0} {β α : ℝ≥0 → ℝ≥0} {T : ℝ≥0} {k i : ι}
    (hΦ : 0 < ∑ j, φ j) (hik : i ≠ k)
    (hSrv : IsServerN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hgps : IsGpsServerN φ S)
    (hcross : ∀ x, T ≤ x → (∑ j, φ j) * α x ≤ φ k * β x)
    (hgrow : ∀ x y, T ≤ x → x ≤ y →
      φ k * β x + (∑ j, φ j) * α y ≤ φ k * β y + (∑ j, φ j) * α x) :
    IsStrictMinimalServiceCurve
      (fun v => max ((φ i / ∑ j, φ j) * β v)
        ((φ i / ∑ j ∈ Finset.univ.erase k, φ j)
          * gatedResidual β α T v))
      (residualServer (fun A D => S A D
        ∧ IsMaximalArrivalBound ⇑(A k) α) i) :=
  isStrictMinimalServiceCurve_max_residualServer_of_isGps
    hΦ hik hSrv.1 hβ hgps hcross hgrow

end DeepWiki
