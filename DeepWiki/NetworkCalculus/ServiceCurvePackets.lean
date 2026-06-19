import DeepWiki.NetworkCalculus.RealCurves
import DeepWiki.NetworkCalculus.ServiceCurveStrict
import DeepWiki.NetworkCalculus.ServiceCurveMinimal

/-! # Packet service times: strict versus min-plus service
For the burst arrival `b·1_{>T}` (`n` packets of size `s`, `b = n·s`, all
arriving at `T`), a strict service curve `λ_C` bounds every packet's service
time (waiting excluded) by `s/C`, while a min-plus service curve bounds only
the total: a server may serve the first `n − 1` packets instantly and the last
one alone in `b/C` time. -/

namespace DeepWiki

open Set Topology Filter
open scoped Classical NNReal

/-! ## Piecewise-after curves -/

/-- A function that is `0` up to `T` and follows the branch `g` strictly
after. -/
noncomputable def afterFun (T : ℝ≥0) (g : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun u => if T < u then g u else 0

/-- `afterFun T g` is nondecreasing for nondecreasing `g`. -/
theorem afterFun_mono (T : ℝ≥0) {g : ℝ≥0 → ℝ≥0} (hg : Monotone g) :
    Monotone (afterFun T g) := by
  intro u v huv
  unfold afterFun
  by_cases hu : T < u
  · rw [if_pos hu, if_pos (lt_of_lt_of_le hu huv)]
    exact hg huv
  · rw [if_neg hu]
    exact zero_le

/-- `afterFun T g` vanishes at the origin. -/
theorem afterFun_zero (T : ℝ≥0) (g : ℝ≥0 → ℝ≥0) :
    IsNullAtOrigin (afterFun T g) := by
  simp [IsNullAtOrigin, afterFun]

/-- `afterFun T g` is continuous at every `u ≠ T` for continuous `g`. -/
theorem afterFun_continuousAt (T : ℝ≥0) {g : ℝ≥0 → ℝ≥0} (hg : Continuous g)
    {u : ℝ≥0} (h : u ≠ T) :
    ContinuousAt (afterFun T g) u := by
  rcases lt_or_gt_of_ne h with h | h
  · refine (continuousAt_const (y := (0 : ℝ≥0))).congr ?_
    filter_upwards [Iio_mem_nhds h] with s hs
    simp [afterFun, (Set.mem_Iio.mp hs).asymm]
  · refine hg.continuousAt.congr ?_
    filter_upwards [Ioi_mem_nhds h] with s hs
    simp [afterFun, Set.mem_Ioi.mp hs]

/-- `afterFun T g` is piecewise continuous (one jump at `T`). -/
theorem afterFun_pwc (T : ℝ≥0) {g : ℝ≥0 → ℝ≥0} (hg : Continuous g) :
    IsPiecewiseContinuous (afterFun T g) := by
  intro S
  apply Set.Finite.subset (Set.finite_singleton T)
  rintro t ⟨ht, _⟩
  by_contra hne
  exact ht (afterFun_continuousAt T hg hne)

/-- `afterFun T g` is left-continuous for continuous `g`. -/
theorem afterFun_leftCont (T : ℝ≥0) {g : ℝ≥0 → ℝ≥0} (hg : Continuous g) :
    IsLeftContinuous (afterFun T g) := by
  intro t
  rcases le_or_gt t T with h | h
  · refine ContinuousWithinAt.congr
      (f := fun _ => (0 : ℝ≥0)) continuousWithinAt_const
      (fun s hs => ?_) ?_
    · simp [afterFun, (lt_of_lt_of_le hs h).asymm]
    · simp [afterFun, not_lt.mpr h]
  · have hev : afterFun T g =ᶠ[𝓝[Iio t] t] g := by
      filter_upwards [Ioo_mem_nhdsLT h] with s hs
      simp [afterFun, hs.1]
    exact (hg.continuousAt.continuousWithinAt).congr_of_eventuallyEq hev
      (by simp [afterFun, h])

/-- The piecewise-after curve: `0` up to `T`, a continuous nondecreasing
branch `g` strictly after. -/
noncomputable def afterCurve (T : ℝ≥0) (g : ℝ≥0 → ℝ≥0)
    (hmono : Monotone g) (hcont : Continuous g) : Curve :=
  ⟨afterFun T g, afterFun_mono T hmono, afterFun_zero T g,
    afterFun_pwc T hcont, afterFun_leftCont T hcont⟩

/-- `afterCurve T g … u = g u` past `T`, `0` before. -/
@[simp] theorem afterCurve_apply (T : ℝ≥0) (g : ℝ≥0 → ℝ≥0)
    (hmono : Monotone g) (hcont : Continuous g) (u : ℝ≥0) :
    afterCurve T g hmono hcont u = if T < u then g u else 0 := rfl

/-! ## The burst arrival -/

/-- The burst arrival `b·1_{>T}` as a `Curve`: `n` packets totalling `b`
arrive together at time `T`. -/
noncomputable def stepCurve (T b : ℝ≥0) : Curve :=
  afterCurve T (fun _ => b) monotone_const continuous_const

/-- `stepCurve T b u = b·1_{T<u}`. -/
@[simp] theorem stepCurve_apply (T b u : ℝ≥0) :
    stepCurve T b u = if T < u then b else 0 := rfl

/-- A sum of unit steps evaluates to the number of steps already
passed. -/
theorem sum_stepCurve_apply (s : Finset ℕ) (u : ℝ≥0) :
    (∑ k ∈ s, stepCurve (k : ℝ≥0) 1) u
      = ((s.filter (fun k : ℕ => (k : ℝ≥0) < u)).card : ℝ≥0) := by
  rw [Curve.sum_apply, Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl fun k _ => stepCurve_apply _ _ _

/-! ## Strict service: a per-packet guarantee -/

/-- Strict `λ_C` drains a burst at rate `C` past `T`:
`min b (D u + C·d) ≤ D (u + d)`. Either `(u, u + d]` is backlogged and the
strict bound applies, or the whole burst has already departed. -/
theorem stepCurve_strict_drain {S : Curve → Curve → Prop} {C T b : ℝ≥0}
    (hβ : IsStrictMinimalServiceCurve (rate C) S)
    {D : Curve} (hp : S (stepCurve T b) D)
    {u : ℝ≥0} (hu : T ≤ u) (d : ℝ≥0) :
    min b (D u + C * d) ≤ D (u + d) := by
  by_cases hbl : IsBacklogged (⇑(stepCurve T b)) (⇑D) (Set.Ioc u (u + d))
  · have h := hβ _ _ hp u (u + d) le_self_add hbl
    simp only [rate] at h
    rw [add_tsub_cancel_left] at h
    exact le_trans (min_le_right _ _) h
  · simp only [IsBacklogged, not_forall, not_lt] at hbl
    obtain ⟨w, hw, hDw⟩ := hbl
    rw [stepCurve_apply, if_pos (lt_of_le_of_lt hu hw.1)] at hDw
    exact le_trans (min_le_left _ _) (le_trans hDw (D.mono hw.2))

/-- **Strict per-packet bound.** Once `x` of the burst has departed by `u ≥ T`,
the next packet of size `s` departs by `u + s/C`: each packet's service time —
waiting excluded — is at most `s/C`. -/
theorem stepCurve_strict_packet {S : Curve → Curve → Prop} {C T b s x : ℝ≥0}
    (hC : C ≠ 0) (hβ : IsStrictMinimalServiceCurve (rate C) S)
    {D : Curve} (hp : S (stepCurve T b) D)
    {u : ℝ≥0} (hu : T ≤ u) (hxb : x + s ≤ b) (hxD : x ≤ D u) :
    x + s ≤ D (u + s / C) := by
  have h := stepCurve_strict_drain hβ hp hu (s / C)
  rw [mul_div_cancel₀ _ hC] at h
  exact le_trans (le_min hxb (add_le_add hxD le_rfl)) h

/-! ## Min-plus service: a total guarantee only -/

/-- **Min-plus total bound.** Under a min-plus `λ_C`, the whole burst `b` has
departed by `T + b/C`: the total service time is at most `b/C`. -/
theorem stepCurve_minimalService_total {S : Curve → Curve → Prop} {C T b : ℝ≥0}
    (hC : C ≠ 0) (hβ : IsMinimalServiceCurve (rateEReal C) S)
    {D : Curve} (hp : S (stepCurve T b) D) :
    b ≤ D (T + b / C) := by
  have h := hβ _ _ hp (T + b / C)
  have hlb : ((b : ℝ) : EReal) ≤
      minConv (curveEReal (stepCurve T b)) (rateEReal C) (T + b / C) := by
    refine le_iInf ?_
    rintro ⟨⟨v, w⟩, hvw⟩
    have hvw' : v + w = T + b / C := hvw
    show ((b : ℝ) : EReal) ≤ curveEReal (stepCurve T b) v + rateEReal C w
    by_cases hv : T < v
    · have hA : curveEReal (stepCurve T b) v = ((b : ℝ) : EReal) := by
        simp [hv]
      rw [hA]
      refine le_add_of_nonneg_right ?_
      rw [rateEReal_apply]
      exact_mod_cast (C * w).coe_nonneg
    · rw [not_lt] at hv
      have hw : b / C ≤ w := by
        have hTw : T + b / C ≤ T + w := by
          rw [← hvw']
          exact add_le_add hv le_rfl
        exact le_of_add_le_add_left hTw
      have hb : b ≤ C * w := by
        have h1 : C * (b / C) ≤ C * w := mul_le_mul' le_rfl hw
        rwa [mul_div_cancel₀ _ hC] at h1
      calc ((b : ℝ) : EReal)
          ≤ rateEReal C w := by rw [rateEReal_apply]; exact_mod_cast hb
        _ ≤ curveEReal (stepCurve T b) v + rateEReal C w :=
            le_add_of_nonneg_left (curveEReal_nonneg _ v)
  have hbD := le_trans hlb h
  rw [curveEReal_apply] at hbD
  exact_mod_cast hbD

/-! ## No per-packet guarantee under min-plus service
The rush server releases `c` of the burst immediately and the remaining
`b − c` at the minimal rate `C`: with `c = (n−1)·s`, the first `n − 1` packets
are served within any `ε > 0`, the last one alone in `b/C − ε`. -/

/-- The rush branch `v ↦ max c (min b (C·(v−T)))` is continuous. -/
theorem rushBranch_continuous (T b c C : ℝ≥0) :
    Continuous (fun v : ℝ≥0 => max c (min b (C * (v - T)))) :=
  continuous_const.max (continuous_const.min
    (continuous_const.mul (continuous_id.sub continuous_const)))

/-- The rush branch is nondecreasing. -/
theorem rushBranch_mono (T b c C : ℝ≥0) :
    Monotone (fun v : ℝ≥0 => max c (min b (C * (v - T)))) :=
  fun _ _ huv => max_le_max le_rfl
    (min_le_min le_rfl (mul_le_mul' le_rfl (tsub_le_tsub_right huv T)))

/-- The rush output for the burst `b·1_{>T}`: `c` departs immediately at `T`,
the remainder at rate `C` — `max c (min b (C·(v−T)))` past `T`. -/
noncomputable def rushCurve (T b c C : ℝ≥0) : Curve :=
  afterCurve T (fun v => max c (min b (C * (v - T))))
    (rushBranch_mono T b c C) (rushBranch_continuous T b c C)

/-- `rushCurve T b c C v = max c (min b (C·(v−T)))·1_{T<v}`. -/
@[simp] theorem rushCurve_apply (T b c C v : ℝ≥0) :
    rushCurve T b c C v =
      if T < v then max c (min b (C * (v - T))) else 0 := rfl

/-- The rush server: the burst `b·1_{>T}` departs as `rushCurve T b c C`; every
other arrival is served instantly (`D = A`). -/
def rushServer (T b c C : ℝ≥0) : Curve → Curve → Prop :=
  fun A D =>
    (A = stepCurve T b ∧ D = rushCurve T b c C) ∨
      (A ≠ stepCurve T b ∧ D = A)

/-- For `c ≤ b` the rush output never exceeds the burst arrival. -/
theorem rushCurve_le_stepCurve {T b c C : ℝ≥0} (hcb : c ≤ b) :
    rushCurve T b c C ≤ stepCurve T b := by
  intro v
  rw [rushCurve_apply, stepCurve_apply]
  by_cases hv : T < v
  · rw [if_pos hv, if_pos hv]
    exact max_le hcb (min_le_left _ _)
  · rw [if_neg hv, if_neg hv]

/-- `rushServer` is a server when `c ≤ b`. -/
theorem isServer_rushServer {T b c C : ℝ≥0} (hcb : c ≤ b) :
    IsServer (rushServer T b c C) := by
  constructor
  · rintro A D (⟨rfl, rfl⟩ | ⟨_, rfl⟩)
    · exact rushCurve_le_stepCurve hcb
    · exact fun t => le_refl _
  · intro A
    by_cases hA : A = stepCurve T b
    · exact ⟨rushCurve T b c C, Or.inl ⟨hA, rfl⟩⟩
    · exact ⟨A, Or.inr ⟨hA, rfl⟩⟩

/-- `rushServer` offers `λ_C` as a min-plus service curve. -/
theorem isMinimalServiceCurve_rushServer (T b c C : ℝ≥0) :
    IsMinimalServiceCurve (rateEReal C) (rushServer T b c C) := by
  rintro A D (⟨rfl, rfl⟩ | ⟨_, rfl⟩)
  · intro v
    by_cases hTv : T < v
    · by_cases hCb : C * (v - T) ≤ b
      · refine ciInf_le_of_le (OrderBot.bddBelow _)
          ⟨(T, v - T), add_tsub_cancel_of_le hTv.le⟩ ?_
        show curveEReal (stepCurve T b) T + rateEReal C (v - T) ≤
          curveEReal (rushCurve T b c C) v
        have hAT : curveEReal (stepCurve T b) T = 0 := by
          simp
        rw [hAT, zero_add]
        have hle : C * (v - T) ≤ rushCurve T b c C v := by
          rw [rushCurve_apply, if_pos hTv, min_eq_right hCb]
          exact le_max_right _ _
        simp only [curveEReal_apply, rateEReal_apply]
        exact_mod_cast hle
      · refine ciInf_le_of_le (OrderBot.bddBelow _)
          ⟨(v, 0), add_zero v⟩ ?_
        show curveEReal (stepCurve T b) v + rateEReal C 0 ≤
          curveEReal (rushCurve T b c C) v
        rw [rateEReal_zero_eq, add_zero]
        have hle : stepCurve T b v ≤ rushCurve T b c C v := by
          rw [stepCurve_apply, if_pos hTv, rushCurve_apply, if_pos hTv,
            min_eq_left (not_le.mp hCb).le]
          exact le_max_right _ _
        simp only [curveEReal_apply]
        exact_mod_cast hle
    · refine ciInf_le_of_le (OrderBot.bddBelow _)
        ⟨(v, 0), add_zero v⟩ ?_
      show curveEReal (stepCurve T b) v + rateEReal C 0 ≤
        curveEReal (rushCurve T b c C) v
      rw [rateEReal_zero_eq, add_zero]
      have hAv : curveEReal (stepCurve T b) v = 0 := by
        simp [hTv]
      rw [hAv]
      exact curveEReal_nonneg _ v
  · exact minConv_self_le (rateEReal_zero_eq C).le _

/-- The first `c` of the burst departs within any `ε > 0`:
`c ≤ rushCurve (T + ε)`. -/
theorem le_rushCurve_of_pos {T b c C ε : ℝ≥0} (hε : 0 < ε) :
    c ≤ rushCurve T b c C (T + ε) := by
  rw [rushCurve_apply, if_pos (lt_add_of_pos_right T hε)]
  exact le_max_left _ _

/-- Before `T + b/C` the burst has not fully departed: `rushCurve v < b` when
`c < b` and `C ≠ 0`. -/
theorem rushCurve_lt_of_lt {T b c C v : ℝ≥0} (hcb : c < b) (hC : C ≠ 0)
    (hv : v < T + b / C) :
    rushCurve T b c C v < b := by
  rw [rushCurve_apply]
  by_cases hTv : T < v
  · rw [if_pos hTv]
    have hvT : v - T < b / C := by
      rw [tsub_lt_iff_left hTv.le]
      exact hv
    have hCvT : C * (v - T) < b := by
      have h1 : C * (v - T) < C * (b / C) :=
        mul_lt_mul_of_pos_left hvT (zero_lt_iff.mpr hC)
      rwa [mul_div_cancel₀ _ hC] at h1
    exact max_lt hcb (lt_of_le_of_lt (min_le_right _ _) hCvT)
  · rw [if_neg hTv]
    exact lt_of_le_of_lt zero_le hcb

/-- **No strict guarantee from min-plus service.** The rush server violates the
strict per-packet bound on the last packet, so it does not offer `λ_C` as a
strict service curve. -/
theorem not_isStrictMinimalServiceCurve_rushServer {T b c C : ℝ≥0}
    (hc : 0 < c) (hcb : c < b) (hC : C ≠ 0) :
    ¬ IsStrictMinimalServiceCurve (rate C) (rushServer T b c C) := by
  intro hβ
  have hp : rushServer T b c C (stepCurve T b) (rushCurve T b c C) :=
    Or.inl ⟨rfl, rfl⟩
  set ε := c / (2 * C) with hεdef
  have hε : 0 < ε :=
    div_pos hc (mul_pos two_pos (zero_lt_iff.mpr hC))
  have hlast := stepCurve_strict_packet (x := c) (s := b - c) hC hβ hp
    (le_self_add : T ≤ T + ε)
    (le_of_eq (add_tsub_cancel_of_le hcb.le))
    (le_rushCurve_of_pos hε)
  rw [add_tsub_cancel_of_le hcb.le] at hlast
  have hlt : T + ε + (b - c) / C < T + b / C := by
    rw [add_assoc]
    refine add_lt_add_of_le_of_lt le_rfl ?_
    have h2 : c / 2 + (b - c) < b := by
      calc c / 2 + (b - c)
          < c + (b - c) :=
            add_lt_add_of_lt_of_le (NNReal.half_lt_self hc.ne') le_rfl
        _ = b := add_tsub_cancel_of_le hcb.le
    calc ε + (b - c) / C
        = (c / 2 + (b - c)) / C := by
          rw [hεdef, ← div_div, ← add_div]
      _ < b / C := by
          have h3 := mul_lt_mul_of_pos_right h2
            (inv_pos.mpr (zero_lt_iff.mpr hC))
          rwa [← div_eq_mul_inv, ← div_eq_mul_inv] at h3
  exact absurd hlast (not_le.mpr (rushCurve_lt_of_lt hcb hC hlt))

/-- **Min-plus service does not imply strict service.** For any rate `C ≠ 0`
and burst levels `0 < c < b`, the rush server offers the min-plus service
curve `λ_C` but not the strict one. -/
theorem exists_minimalService_not_strictService {C : ℝ≥0} (hC : C ≠ 0)
    {b c : ℝ≥0} (hc : 0 < c) (hcb : c < b) :
    ∃ S : Curve → Curve → Prop,
      IsServer S ∧ IsMinimalServiceCurve (rateEReal C) S ∧
        ¬ IsStrictMinimalServiceCurve (rate C) S :=
  ⟨rushServer 0 b c C, isServer_rushServer hcb.le,
    isMinimalServiceCurve_rushServer 0 b c C,
    not_isStrictMinimalServiceCurve_rushServer hc hcb hC⟩

/-! ## The book's packet phrasing
The level lemmas above instantiated at `n` packets of size `s`: the burst is
`stepCurve T (n·s)`, packet `k + 1` is the level interval `(k·s, (k+1)·s]`,
and the rush server takes `c = (n−1)·s`, `b = n·s`. -/

/-- Packet count form of `stepCurve_strict_packet`: under strict `λ_C`, once
the first `k` of `n` packets of size `s` have departed by `u ≥ T`, packet
`k + 1` departs by `u + s/C`. -/
theorem stepCurve_strict_packet_count {S : Curve → Curve → Prop}
    {C T s : ℝ≥0} {n k : ℕ} (hC : C ≠ 0)
    (hβ : IsStrictMinimalServiceCurve (rate C) S)
    {D : Curve} (hp : S (stepCurve T ((n : ℝ≥0) * s)) D)
    {u : ℝ≥0} (hu : T ≤ u) (hk : k < n) (hxD : (k : ℝ≥0) * s ≤ D u) :
    ((k + 1 : ℕ) : ℝ≥0) * s ≤ D (u + s / C) := by
  have hcast : ((k + 1 : ℕ) : ℝ≥0) * s = (k : ℝ≥0) * s + s := by
    push_cast
    ring
  have hxb : (k : ℝ≥0) * s + s ≤ (n : ℝ≥0) * s := by
    rw [← hcast]
    exact mul_le_mul' (Nat.cast_le.mpr hk) le_rfl
  rw [hcast]
  exact stepCurve_strict_packet hC hβ hp hu hxb hxD

/-- Packet count form of `stepCurve_minimalService_total`: under min-plus `λ_C`, all
`n` packets of size `s` have departed by `T + n·s/C` — the total service time
is at most `n·s/C`. -/
theorem stepCurve_minimalService_total_count {S : Curve → Curve → Prop}
    {C T s : ℝ≥0} {n : ℕ} (hC : C ≠ 0)
    (hβ : IsMinimalServiceCurve (rateEReal C) S)
    {D : Curve} (hp : S (stepCurve T ((n : ℝ≥0) * s)) D) :
    (n : ℝ≥0) * s ≤ D (T + (n : ℝ≥0) * s / C) :=
  stepCurve_minimalService_total hC hβ hp

/-- Packet count form of `le_rushCurve_of_pos`: the rush server for `n`
packets of size `s` serves the first `n − 1` packets within any `ε > 0`. -/
theorem le_rushCurve_of_pos_count {T s C ε : ℝ≥0} {n : ℕ} (hε : 0 < ε) :
    ((n - 1 : ℕ) : ℝ≥0) * s ≤
      rushCurve T ((n : ℝ≥0) * s) (((n - 1 : ℕ) : ℝ≥0) * s) C (T + ε) :=
  le_rushCurve_of_pos hε

/-- Packet count form of `rushCurve_lt_of_lt`: the rush server for `n ≥ 1`
packets of size `s > 0` has not completed the last packet at any time before
`T + n·s/C` — together with `le_rushCurve_of_pos_count`, its service time
alone is `n·s/C − ε`. -/
theorem rushCurve_lt_of_lt_count {T s C v : ℝ≥0} {n : ℕ} (hn : 0 < n)
    (hs : 0 < s) (hC : C ≠ 0) (hv : v < T + (n : ℝ≥0) * s / C) :
    rushCurve T ((n : ℝ≥0) * s) (((n - 1 : ℕ) : ℝ≥0) * s) C v <
      (n : ℝ≥0) * s :=
  rushCurve_lt_of_lt
    (mul_lt_mul_of_pos_right
      (Nat.cast_lt.mpr (Nat.sub_lt hn one_pos)) hs)
    hC hv

/-- Packet count form of the separation: for `n ≥ 2` packets of size `s > 0`,
some server (the rush server with `c = (n−1)·s`, `b = n·s`) offers `λ_C`
min-plus but not strictly. -/
theorem exists_minimalService_not_strictService_count {C s : ℝ≥0} {n : ℕ}
    (hn : 2 ≤ n) (hs : 0 < s) (hC : C ≠ 0) :
    ∃ S : Curve → Curve → Prop,
      IsServer S ∧ IsMinimalServiceCurve (rateEReal C) S ∧
        ¬ IsStrictMinimalServiceCurve (rate C) S :=
  exists_minimalService_not_strictService hC
    (c := ((n - 1 : ℕ) : ℝ≥0) * s) (b := ((n : ℕ) : ℝ≥0) * s)
    (mul_pos
      (by exact_mod_cast Nat.sub_pos_of_lt (lt_of_lt_of_le one_lt_two hn)) hs)
    (mul_lt_mul_of_pos_right
      (by exact_mod_cast Nat.sub_lt (lt_of_lt_of_le two_pos hn) one_pos) hs)

end DeepWiki
