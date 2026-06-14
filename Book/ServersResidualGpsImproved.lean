import Mathlib.Analysis.Convex.Function
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

/-- Peeling from an already-gated residual collapses to one gate:
for a later gate the subtractions merge,
`((β − γ)·1_{[T,∞)} − α)·1_{[T',∞)} = (β − (γ + α))·1_{[T',∞)}`. -/
theorem gatedResidual_gatedResidual {β γ α : ℝ≥0 → ℝ≥0} {T T' : ℝ≥0}
    (h : T ≤ T') :
    gatedResidual (gatedResidual β γ T) α T'
      = gatedResidual β (fun v => γ v + α v) T' := by
  funext v
  rcases le_or_gt T' v with hv | hv
  · rw [gatedResidual_apply_of_le hv, gatedResidual_apply_of_le hv,
      gatedResidual_apply_of_le (h.trans hv), tsub_tsub]
  · rw [gatedResidual_apply_of_lt hv, gatedResidual_apply_of_lt hv]

/-- With no gate and nothing subtracted the gated residual is the
curve itself. -/
theorem gatedResidual_zero (β : ℝ≥0 → ℝ≥0) :
    gatedResidual β (fun _ => 0) 0 = β := by
  funext v
  rw [gatedResidual_apply_of_le zero_le', tsub_zero]

/-- A convex function nonpositive at the origin and nonnegative at a
positive gate is nonnegative and non-decreasing past the gate: the
secant through the origin pins every later value. -/
theorem ConvexOn.nonneg_and_le_of_gate {g : ℝ → ℝ}
    (hg : ConvexOn ℝ (Set.Ici 0) g) (h0 : g 0 ≤ 0)
    {T : ℝ} (hT : 0 < T) (hgT : 0 ≤ g T) :
    ∀ ⦃x y : ℝ⦄, T ≤ x → x ≤ y → 0 ≤ g x ∧ g x ≤ g y := by
  have hsec : ∀ c z : ℝ, 0 < z → 0 ≤ c → c ≤ z →
      g c ≤ (1 - c / z) * g 0 + (c / z) * g z := by
    intro c z hz0 hc0 hcz
    have hw1 : (0 : ℝ) ≤ 1 - c / z := by
      have h1 : c / z ≤ 1 := (div_le_one hz0).mpr hcz
      linarith
    have hw2 : (0 : ℝ) ≤ c / z := div_nonneg hc0 hz0.le
    have hab : (1 - c / z) + c / z = 1 := by ring
    have hcomb := hg.2 (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr hz0.le) hw1 hw2 hab
    rwa [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      mul_zero, zero_add, div_mul_cancel₀ _ hz0.ne'] at hcomb
  have hnn : ∀ z, T ≤ z → 0 ≤ g z := by
    intro z hz
    rcases eq_or_lt_of_le hz with rfl | hz'
    · exact hgT
    have hz0 : 0 < z := lt_trans hT hz'
    have h := hsec T z hz0 hT.le hz
    have hw : (0 : ℝ) ≤ 1 - T / z := by
      have : T / z ≤ 1 := (div_le_one hz0).mpr hz
      linarith
    have hgz : 0 ≤ (T / z) * g z := by nlinarith
    exact nonneg_of_mul_nonneg_right hgz (div_pos hT hz0)
  intro x y hx hxy
  refine ⟨hnn x hx, ?_⟩
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · exact le_rfl
  have hx0 : 0 < x := lt_of_lt_of_le hT hx
  have hy0 : 0 < y := lt_trans hx0 hxy'
  have h := hsec x y hy0 hx0.le hxy
  have hw : (0 : ℝ) ≤ 1 - x / y := by
    have : x / y ≤ 1 := (div_le_one hy0).mpr hxy
    linarith
  have hgy := hnn y (le_trans hx hxy)
  have hxy1 : x / y ≤ 1 := (div_le_one hy0).mpr hxy
  nlinarith

/-- **The convexity bridge**: a convex weighted gap
`x ↦ c·β(x) − d·α(x)` (the book's convex `β` against a concave `α`)
that starts below zero and is nonnegative at a positive gate yields
both gate conditions of the improved-GPS aggregation — domination
(`hcross`) and growth (`hgrow`) past the gate. -/
theorem cross_and_grow_of_convexOn_gap {β α : ℝ≥0 → ℝ≥0}
    {c d T : ℝ≥0}
    (hg : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ =>
      (c : ℝ) * (β x.toNNReal : ℝ) - (d : ℝ) * (α x.toNNReal : ℝ)))
    (h0 : c * β 0 ≤ d * α 0) (hT : 0 < T)
    (hgate : d * α T ≤ c * β T) :
    (∀ x, T ≤ x → d * α x ≤ c * β x)
      ∧ ∀ x y, T ≤ x → x ≤ y →
          c * β x + d * α y ≤ c * β y + d * α x := by
  set g : ℝ → ℝ := fun x =>
    (c : ℝ) * (β x.toNNReal : ℝ) - (d : ℝ) * (α x.toNNReal : ℝ)
    with hgdef
  have hval : ∀ x : ℝ≥0, g (x : ℝ)
      = (c : ℝ) * (β x : ℝ) - (d : ℝ) * (α x : ℝ) := fun x => by
    simp only [hgdef, Real.toNNReal_coe]
  have hg0 : g 0 ≤ 0 := by
    have h := hval 0
    rw [NNReal.coe_zero] at h
    rw [h]
    have h0R : (c : ℝ) * (β 0 : ℝ) ≤ (d : ℝ) * (α 0 : ℝ) := by
      exact_mod_cast h0
    linarith
  have hgT : 0 ≤ g (T : ℝ) := by
    rw [hval T]
    have hR : (d : ℝ) * (α T : ℝ) ≤ (c : ℝ) * (β T : ℝ) := by
      exact_mod_cast hgate
    linarith
  have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hkey := ConvexOn.nonneg_and_le_of_gate hg hg0 hTR hgT
  constructor
  · intro x hx
    have h := (hkey (x := (x : ℝ)) (y := (x : ℝ))
      (by exact_mod_cast hx) le_rfl).1
    rw [hval x] at h
    have : (d : ℝ) * (α x : ℝ) ≤ (c : ℝ) * (β x : ℝ) := by linarith
    exact_mod_cast this
  · intro x y hx hxy
    have h := (hkey (x := (x : ℝ)) (y := (y : ℝ))
      (by exact_mod_cast hx) (by exact_mod_cast hxy)).2
    rw [hval x, hval y] at h
    have : (c : ℝ) * (β x : ℝ) + (d : ℝ) * (α y : ℝ)
        ≤ (c : ℝ) * (β y : ℝ) + (d : ℝ) * (α x : ℝ) := by linarith
    exact_mod_cast this

/-- **The constrained flow releases its share past its crossing
time** — the improved-GPS aggregation step: in a GPS server with
strict aggregate `β` and flow `k` arrival-constrained by `α`, the
remaining flows' aggregate obeys the strict inequality for the gated
residual `(β − α)·1_{[T,∞)}`, provided that from `T` on the weighted
arrival curve sits below flow `k`'s share (`hcross`) and the
weighted gap grows (`hgrow`). Stated over a sub-aggregate `J ∋ k`,
the shape the iterated peeling consumes. Every window of the
argument is backlogged, so no variable-capacity witness is needed:
the start `p` of flow `k`'s backlogged period at `s` makes `(p, t]`
backlogged for the `J`-aggregate, GPS grants flow `k` its share of
the service on `(p, s]`, and the arrivals over `(p, t]` cap what
flow `k` can take from the rest. -/
theorem add_gatedResidual_le_of_isGps {ι : Type*} [DecidableEq ι]
    {φ : ι → ℝ≥0} {As Ds : ι → Curve} {J : Finset ι}
    {β α : ℝ≥0 → ℝ≥0} {T : ℝ≥0}
    (hΦ : 0 < ∑ j ∈ J, φ j)
    (hc : ∀ j ∈ J, Ds j ≤ As j)
    (hgps : IsGps φ (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j ∈ J, (As j) x)
        (fun x => ∑ j ∈ J, (Ds j) x) (Set.Ioc s t) →
      (∑ j ∈ J, (Ds j) s) + β (t - s) ≤ ∑ j ∈ J, (Ds j) t)
    {k : ι} (hk : k ∈ J) (harr : IsMaximalArrivalBound ⇑(As k) α)
    (hcross : ∀ x, T ≤ x → (∑ j ∈ J, φ j) * α x ≤ φ k * β x)
    (hgrow : ∀ x y, T ≤ x → x ≤ y →
      φ k * β x + (∑ j ∈ J, φ j) * α y
        ≤ φ k * β y + (∑ j ∈ J, φ j) * α x)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged
      (fun x => ∑ j ∈ J.erase k, (As j) x)
      (fun x => ∑ j ∈ J.erase k, (Ds j) x) (Set.Ioc s t)) :
    (∑ j ∈ J.erase k, (Ds j) s)
      + gatedResidual β α T (t - s)
      ≤ ∑ j ∈ J.erase k, (Ds j) t := by
  rcases lt_or_ge (t - s) T with hT | hT
  · rw [gatedResidual_apply_of_lt hT, add_zero]
    exact Finset.sum_le_sum fun j _ => (Ds j).mono hst
  rw [gatedResidual_apply_of_le hT]
  -- the start of flow `k`'s backlogged period at `s`
  set p := start ⇑(As k) ⇑(Ds k) s with hpdef
  have hps : p ≤ s := start_le _ _ s
  have hpt : p ≤ t := hps.trans hst
  have hblk : IsBacklogged ⇑(As k) ⇑(Ds k) (Set.Ioc p s) :=
    isBacklogged_Ioc_start (hc k hk) s
  have hblT1 : IsBacklogged (fun x => ∑ j ∈ J, (As j) x)
      (fun x => ∑ j ∈ J, (Ds j) x) (Set.Ioc p s) :=
    isBacklogged_sum_of_isBacklogged (fun j hj x => hc j hj x)
      hk hblk
  have hblT2 : IsBacklogged (fun x => ∑ j ∈ J, (As j) x)
      (fun x => ∑ j ∈ J, (Ds j) x) (Set.Ioc s t) :=
    isBacklogged_sum_of_isBacklogged_subset (fun j hj x => hc j hj x)
      (Finset.erase_subset k J) hbl
  have hblT : IsBacklogged (fun x => ∑ j ∈ J, (As j) x)
      (fun x => ∑ j ∈ J, (Ds j) x) (Set.Ioc p t) := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc hps hst]
    exact hblT1.union hblT2
  -- the strict aggregate bounds on the two backlogged windows
  have ha := hstrict s t hst hblT2
  have hb := hstrict p t hpt hblT
  -- GPS grants flow `k` its share of the service on `(p, s]`
  have hshare := mul_sum_le_sum_mul_of_isGps (J := J)
    hgps hps hblk
  -- equality at the start, the arrival cap, causality
  have hd : (As k) p = (Ds k) p :=
    (As k).apply_start_eq (Ds k) (fun x => hc k hk x) s
  have he : (As k) t ≤ (As k) p + α (t - p) := by
    have h := (isMaximalArrivalBound_iff_increment _ _).mp harr p (t - p)
    rwa [add_tsub_cancel_of_le hpt] at h
  have hf : (Ds k) t ≤ (As k) t := hc k hk t
  have hg := hgrow (t - s) (t - p) hT (tsub_le_tsub_left hps t)
  -- the arrival curve sits below the curve past the gate
  have hαβ : α (t - s) ≤ β (t - s) := by
    refine le_of_mul_le_mul_left (le_trans (hcross (t - s) hT) ?_) hΦ
    exact mul_le_mul_left
      (Finset.single_le_sum (fun j _ => zero_le') hk) (β (t - s))
  -- totals split over `k` and the rest
  have hsplit : ∀ x, (∑ j ∈ J, (Ds j) x)
      = (Ds k) x + ∑ j ∈ J.erase k, (Ds j) x :=
    fun x => (Finset.add_sum_erase _ _ hk).symm
  -- monotonicity guards for the truncated subtractions
  have hDmono : (∑ j ∈ J, (Ds j) p) ≤ ∑ j ∈ J, (Ds j) s :=
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
  have hΦR : (0 : ℝ) < ∑ j ∈ J, ((φ j : ℝ≥0) : ℝ) := by
    exact_mod_cast hΦ
  have hΦknn : (0 : ℝ) ≤ (∑ j ∈ J, ((φ j : ℝ≥0) : ℝ)) - (φ k : ℝ) := by
    have h := Finset.single_le_sum
      (f := fun j => ((φ j : ℝ≥0) : ℝ))
      (fun j _ => (φ j).coe_nonneg) hk
    linarith
  -- the Φ-weighted goal, then cancel the positive total weight
  have haΦ := mul_le_mul_of_nonneg_left haR hΦknn
  have hbφ := mul_le_mul_of_nonneg_left hbR hφknn
  have heΦ := mul_le_mul_of_nonneg_left heR hΦR.le
  have hfΦ := mul_le_mul_of_nonneg_left hfR hΦR.le
  have hdΦ : (∑ j ∈ J, ((φ j : ℝ≥0) : ℝ)) * ((As k) p : ℝ)
      = (∑ j ∈ J, ((φ j : ℝ≥0) : ℝ)) * ((Ds k) p : ℝ) := by rw [hdR]
  have hgoalΦ : (∑ j ∈ J, ((φ j : ℝ≥0) : ℝ))
      * ((∑ j ∈ J.erase k, ((Ds j) s : ℝ))
        + (β (t - s) : ℝ) - (α (t - s) : ℝ))
      ≤ (∑ j ∈ J, ((φ j : ℝ≥0) : ℝ))
        * ∑ j ∈ J.erase k, ((Ds j) t : ℝ) := by
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
      (fun s t hst hbl => add_gatedResidual_le_of_isGps hΦ
        (fun j _ => hc j) hgps hstrict (Finset.mem_univ k) harr
        hcross hgrow hst hbl)
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

/-- **Aggregate-strict service**: the `J`-aggregate of an `n`-server
obeys the strict inequality for `β` on its own backlogged periods —
the hypothesis-and-conclusion shape that the per-flow peeling
transports. -/
def IsAggregateStrict {ι : Type*}
    (As Ds : ι → Curve) (J : Finset ι) (β : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ s t, s ≤ t →
    IsBacklogged (fun x => ∑ j ∈ J, (As j) x)
      (fun x => ∑ j ∈ J, (Ds j) x) (Set.Ioc s t) →
    (∑ j ∈ J, (Ds j) s) + β (t - s) ≤ ∑ j ∈ J, (Ds j) t

/-- **One peel of the improved-GPS chain**: removing an
arrival-constrained flow `k` from a `J`-aggregate-strict curve `β`
leaves the remaining `J ∖ {k}`-aggregate strict for the gated
residual `(β − α)·1_{[T,∞)}` — the inductive step that, iterated,
peels every cross flow. -/
theorem IsAggregateStrict.peel {ι : Type*} [DecidableEq ι]
    {φ : ι → ℝ≥0} {As Ds : ι → Curve} {J : Finset ι}
    {β α : ℝ≥0 → ℝ≥0} {T : ℝ≥0}
    (hΦ : 0 < ∑ j ∈ J, φ j) (hc : ∀ j ∈ J, Ds j ≤ As j)
    (hgps : IsGps φ (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    {k : ι} (hk : k ∈ J) (harr : IsMaximalArrivalBound ⇑(As k) α)
    (hcross : ∀ x, T ≤ x → (∑ j ∈ J, φ j) * α x ≤ φ k * β x)
    (hgrow : ∀ x y, T ≤ x → x ≤ y →
      φ k * β x + (∑ j ∈ J, φ j) * α y
        ≤ φ k * β y + (∑ j ∈ J, φ j) * α x)
    (h : IsAggregateStrict As Ds J β) :
    IsAggregateStrict As Ds (J.erase k) (gatedResidual β α T) :=
  fun s t hst hbl =>
    add_gatedResidual_le_of_isGps (s := s) (t := t) hΦ hc hgps h hk harr
      hcross hgrow hst hbl

/-- **Two peels collapse to one gate**: peeling flows `k₁` then `k₂`
(gates `T₁ ≤ T₂`) from an aggregate-strict `β` leaves the remaining
aggregate strict for the single-gated residual
`(β − (α₁ + α₂))·1_{[T₂,∞)}` — the gate-collapse in action, the
shape the `n`-fold improved-GPS residual takes. -/
theorem IsAggregateStrict.peel_two {ι : Type*} [DecidableEq ι]
    {φ : ι → ℝ≥0} {As Ds : ι → Curve} {J : Finset ι}
    {β α₁ α₂ : ℝ≥0 → ℝ≥0} {T₁ T₂ : ℝ≥0} (hT : T₁ ≤ T₂)
    (hgps : IsGps φ (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    {k₁ k₂ : ι} (hk₁ : k₁ ∈ J) (hk₂ : k₂ ∈ J.erase k₁)
    (hΦ₁ : 0 < ∑ j ∈ J, φ j) (hΦ₂ : 0 < ∑ j ∈ J.erase k₁, φ j)
    (hc : ∀ j ∈ J, Ds j ≤ As j)
    (harr₁ : IsMaximalArrivalBound ⇑(As k₁) α₁)
    (harr₂ : IsMaximalArrivalBound ⇑(As k₂) α₂)
    (hcross₁ : ∀ x, T₁ ≤ x → (∑ j ∈ J, φ j) * α₁ x ≤ φ k₁ * β x)
    (hgrow₁ : ∀ x y, T₁ ≤ x → x ≤ y →
      φ k₁ * β x + (∑ j ∈ J, φ j) * α₁ y
        ≤ φ k₁ * β y + (∑ j ∈ J, φ j) * α₁ x)
    (hcross₂ : ∀ x, T₂ ≤ x →
      (∑ j ∈ J.erase k₁, φ j) * α₂ x
        ≤ φ k₂ * gatedResidual β α₁ T₁ x)
    (hgrow₂ : ∀ x y, T₂ ≤ x → x ≤ y →
      φ k₂ * gatedResidual β α₁ T₁ x + (∑ j ∈ J.erase k₁, φ j) * α₂ y
        ≤ φ k₂ * gatedResidual β α₁ T₁ y
          + (∑ j ∈ J.erase k₁, φ j) * α₂ x)
    (h : IsAggregateStrict As Ds J β) :
    IsAggregateStrict As Ds ((J.erase k₁).erase k₂)
      (gatedResidual β (fun v => α₁ v + α₂ v) T₂) := by
  have hpeel₁ : IsAggregateStrict As Ds (J.erase k₁)
      (gatedResidual β α₁ T₁) :=
    h.peel hΦ₁ hc hgps hk₁ harr₁ hcross₁ hgrow₁
  have hpeel₂ : IsAggregateStrict As Ds ((J.erase k₁).erase k₂)
      (gatedResidual (gatedResidual β α₁ T₁) α₂ T₂) :=
    hpeel₁.peel hΦ₂ (fun j hj => hc j (Finset.mem_of_mem_erase hj))
      hgps hk₂ harr₂ hcross₂ hgrow₂
  rwa [gatedResidual_gatedResidual hT] at hpeel₂

/-! ## The `n`-flow fold: iterated peeling
The book's Theorem 7.8 is proved by induction — peel the arrival-constrained flows one at a
time, each peel gating the residual, until a single aggregate remains. `GpsPeelChain` records
one such peel sequence (from `(J, β)` down to `(J', β')`, threading the running residual
through each `peel`); `GpsPeelChain.isAggregateStrict` transports aggregate-strictness along
it. Iterating from the full aggregate down to a single flow recovers the book's
`β̃ᵢ = (β − ∑_{j<i} αⱼ)·1_{≥t_{i-1}}`. -/

/-- A valid sequence of improved-GPS peels: from the aggregate `J` carrying the strict curve
`β`, peel arrival-constrained flows one at a time — each past its gate `T`, with the two gate
conditions (`hcross` domination, `hgrow` growth) on the running residual — down to the
aggregate `J'` carrying the gated residual `β'`. -/
inductive GpsPeelChain {ι : Type*} [DecidableEq ι] (φ : ι → ℝ≥0) (As : ι → Curve) :
    Finset ι → (ℝ≥0 → ℝ≥0) → Finset ι → (ℝ≥0 → ℝ≥0) → Prop
  /-- The empty peel sequence: the aggregate and curve are unchanged. -/
  | nil (J : Finset ι) (β : ℝ≥0 → ℝ≥0) : GpsPeelChain φ As J β J β
  /-- Peel one arrival-constrained flow `k` (gate `T`, gate conditions `hcross`/`hgrow`),
  then continue from the smaller aggregate `J.erase k` with the gated residual. -/
  | cons {J : Finset ι} {β : ℝ≥0 → ℝ≥0} {k : ι} {α : ℝ≥0 → ℝ≥0} {T : ℝ≥0}
      {J' : Finset ι} {β' : ℝ≥0 → ℝ≥0}
      (hΦ : 0 < ∑ j ∈ J, φ j) (hk : k ∈ J)
      (harr : IsMaximalArrivalBound ⇑(As k) α)
      (hcross : ∀ x, T ≤ x → (∑ j ∈ J, φ j) * α x ≤ φ k * β x)
      (hgrow : ∀ x y, T ≤ x → x ≤ y →
        φ k * β x + (∑ j ∈ J, φ j) * α y ≤ φ k * β y + (∑ j ∈ J, φ j) * α x)
      (rest : GpsPeelChain φ As (J.erase k) (gatedResidual β α T) J' β') :
      GpsPeelChain φ As J β J' β'

/-- **The `n`-flow fold (Theorem 7.8's induction)**: aggregate-strictness transports along a
peel chain — if `β` is strict for the aggregate `J` and the chain peels flows down to `(J', β')`,
then `β'` is strict for the remaining aggregate `J'`. Each step is one `IsAggregateStrict.peel`;
the chain just iterates it. -/
theorem GpsPeelChain.isAggregateStrict {ι : Type*} [DecidableEq ι]
    {φ : ι → ℝ≥0} {As Ds : ι → Curve}
    (hgps : IsGps φ (fun j => ⇑(As j)) (fun j => ⇑(Ds j))) (hc : ∀ j, Ds j ≤ As j)
    {J : Finset ι} {β : ℝ≥0 → ℝ≥0} {J' : Finset ι} {β' : ℝ≥0 → ℝ≥0}
    (chain : GpsPeelChain φ As J β J' β') :
    IsAggregateStrict As Ds J β → IsAggregateStrict As Ds J' β' := by
  induction chain with
  | nil => exact id
  | cons hΦ hk harr hcross hgrow _ ih =>
    exact fun h => ih (h.peel hΦ (fun j _ => hc j) hgps hk harr hcross hgrow)

/-- A singleton aggregate is one flow: `IsAggregateStrict As Ds {k} γ` is exactly the
backlogged-period bound of `strictServiceRel γ (As k) (Ds k)`, so with causality it *is* a
strict service curve for flow `k`. -/
theorem strictServiceRel_of_isAggregateStrict_singleton {ι : Type*} {As Ds : ι → Curve}
    {γ : ℝ≥0 → ℝ≥0} {k : ι} (hc : Ds k ≤ As k)
    (h : IsAggregateStrict As Ds {k} γ) :
    strictServiceRel γ (As k) (Ds k) := by
  refine ⟨hc, fun s t hst hbl => ?_⟩
  have key := h s t hst
  simp only [Finset.sum_singleton] at key
  exact key hbl

/-- **Theorem 7.8 (the improved per-flow GPS residual)**: peel every other flow from the full
aggregate (strict for `β`) along a `GpsPeelChain` down to the single flow `k`; the residual `γ`
left at the end is a strict service curve for flow `k`. With the linear peel order this `γ` is
the book's `β̃ = (β − ∑_{j≠k} αⱼ)·1_{≥T}` (the nested gates collapse via
`gatedResidual_gatedResidual`). -/
theorem strictServiceRel_of_gpsPeelChain_singleton {ι : Type*} [Fintype ι] [DecidableEq ι]
    {φ : ι → ℝ≥0} {As Ds : ι → Curve}
    (hgps : IsGps φ (fun j => ⇑(As j)) (fun j => ⇑(Ds j))) (hc : ∀ j, Ds j ≤ As j)
    {β γ : ℝ≥0 → ℝ≥0} {k : ι}
    (chain : GpsPeelChain φ As Finset.univ β {k} γ)
    (h : IsAggregateStrict As Ds Finset.univ β) :
    strictServiceRel γ (As k) (Ds k) :=
  strictServiceRel_of_isAggregateStrict_singleton (hc k)
    (chain.isAggregateStrict hgps hc h)

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
