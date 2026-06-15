import DeepWiki.NetworkCalculus.RealCurvesDeconv
import DeepWiki.NetworkCalculus.Continuity
import DeepWiki.NetworkCalculus.Deviations

/-! Horizontal and vertical deviations specialized to `ℝ≥0 → ℝ≥0∞`: the
`delayNN`/`tokenBucketNN`/`affine`/`rateLatencyNN` deviation values (stable and unstable), and
the right-limit/right-continuity criteria for a positive horizontal deviation.
The general deviations live in `Book.Deviations`; here `hDevAtENN`/`hDevENN`
pin the shift-embedding to `(↑· : ℝ≥0 → ℝ≥0∞)`. Any curve's value at the
latency lower-bounds its `vDev` against `β_{R,T}`; for the staircase the
book's matching equality fails at jump points (`¬∀` refutation). -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
open Set Topology Filter

/-- `ℝ≥0∞`-valued horizontal deviation: `hDevAt` with shift-embedding `↑`. -/
noncomputable abbrev hDevAtENN (f g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) : ℝ≥0∞ :=
  hDevAt f g t

/-- `ℝ≥0∞`-valued horizontal deviation sup: `hDev` with shift-embedding `↑`. -/
noncomputable abbrev hDevENN (f g : ℝ≥0 → ℝ≥0∞) : ℝ≥0∞ :=
  hDev f g

/-- `hDevAtENN` as an explicit-coe infimum (collapses the generic `CoeTC.coe`). -/
theorem hDevAtENN_eq (f g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    hDevAtENN f g t
      = ⨅ d : {d : ℝ≥0 // f t ≤ g (t + d)}, (d.1 : ℝ≥0∞) := rfl

/-- Intro: `x ≤ d` over all admissible shifts `d` gives `↑x ≤ hDevAtENN f g t`
(the coercion crossing is absorbed). -/
theorem le_hDevAtENN {f g : ℝ≥0 → ℝ≥0∞} {t x : ℝ≥0}
    (h : ∀ d : ℝ≥0, f t ≤ g (t + d) → x ≤ d) :
    (x : ℝ≥0∞) ≤ hDevAtENN f g t := by
  rw [hDevAtENN_eq]
  exact le_iInf fun d => ENNReal.coe_le_coe.mpr (h d.1 d.2)

/-- `delayNN d (t + u) = ⊤` when `d < t + u`. -/
theorem delayNN_top_of_gt (d t u : ℝ≥0) (h : d < t + u) :
    delayNN d (t + u) = ⊤ := by
  simp only [delayNN, delay_apply, if_neg (not_le.mpr h)]

/-- `hDevAtENN f (delayNN d) t ≤ d`. -/
theorem hDevAtENN_delay_le (f : ℝ≥0 → ℝ≥0∞) (d t : ℝ≥0) :
    hDevAtENN f (delayNN d) t ≤ d := by
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  have hadm : f t ≤ delayNN d (t + (d + ε)) := by
    rw [delayNN_top_of_gt d t (d + ε) (by
      calc d < d + ε := by simpa using hε
        _ ≤ t + (d + ε) := le_add_self)]
    exact le_top
  rw [hDevAtENN_eq]
  refine iInf_le_of_le ⟨d + ε, hadm⟩ ?_
  push_cast; rfl

/-- `hDevENN f (delayNN d) ≤ d`. -/
theorem hDevENN_delay_le (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0) :
    hDevENN f (delayNN d) ≤ d := by
  unfold hDevENN hDev
  exact iSup_le (fun t => hDevAtENN_delay_le f d t)

/-- `(d - t) ≤ hDevAtENN f (delayNN d) t` when `f t > 0`. -/
theorem hDevAtENN_delay_ge (f : ℝ≥0 → ℝ≥0∞) (d t : ℝ≥0)
    (hft : 0 < f t) :
    ((d - t : ℝ≥0) : ℝ≥0∞) ≤ hDevAtENN f (delayNN d) t := by
  refine le_hDevAtENN fun d' hd' => ?_
  by_contra hlt
  rw [not_le] at hlt
  have htd : t + d' < d := by
    rwa [lt_tsub_iff_left] at hlt
  have h0 : delayNN d (t + d') = 0 := by
    simp only [delayNN, delay_apply, if_pos htd.le]
  rw [h0] at hd'
  exact absurd (le_antisymm hd' bot_le) hft.ne'

/-- `↑a ≤ ↑(a - e) + ↑e`: the truncated-sub split, lifted to `ℝ≥0∞`. -/
theorem coe_le_coe_tsub_add (a e : ℝ≥0) :
    (a : ℝ≥0∞) ≤ ((a - e : ℝ≥0) : ℝ≥0∞) + (e : ℝ≥0∞) :=
  ENNReal.coe_sub ▸ le_tsub_add

/-- `hDevENN f (delayNN d) = d` when `f > 0` on `(0, ∞)`. -/
theorem hDevENN_delay_eq (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0)
    (hf : ∀ t : ℝ≥0, 0 < t → 0 < f t) :
    hDevENN f (delayNN d) = d := by
  apply le_antisymm (hDevENN_delay_le f d)
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  have ht : (0:ℝ≥0) < ε := hε
  have hlb : ((d - ε : ℝ≥0):ℝ≥0∞) ≤ hDevENN f (delayNN d) := by
    refine le_trans (hDevAtENN_delay_ge f d ε (hf ε ht)) ?_
    unfold hDevENN hDev; exact le_iSup _ ε
  calc (d:ℝ≥0∞) ≤ ((d - ε : ℝ≥0):ℝ≥0∞) + ε :=
        coe_le_coe_tsub_add d ε
    _ ≤ hDevENN f (delayNN d) + ε := by gcongr

/-- `hDevENN f (delayNN d) = d` if `f > 0` on some right-window of `0`. -/
theorem hDevENN_delay_eq_of_pos_window
    (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0)
    (hw : ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ t : ℝ≥0, 0 < t → t < δ → 0 < f t) :
    hDevENN f (delayNN d) = d := by
  apply le_antisymm (hDevENN_delay_le f d)
  obtain ⟨δ, hδ, hpw⟩ := hw
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  set s : ℝ≥0 := min ε (δ / 2) with hs
  have hs_pos : 0 < s := lt_min hε (by positivity)
  have hs_ltδ : s < δ :=
    lt_of_le_of_lt (min_le_right _ _)
      (NNReal.half_lt_self hδ.ne')
  have hs_le_ε : (s:ℝ≥0∞) ≤ ε := by
    exact_mod_cast min_le_left _ _
  have hlb : ((d - s : ℝ≥0):ℝ≥0∞)
      ≤ hDevENN f (delayNN d) := by
    refine le_trans
      (hDevAtENN_delay_ge f d s (hpw s hs_pos hs_ltδ)) ?_
    unfold hDevENN hDev; exact le_iSup _ s
  calc (d:ℝ≥0∞) ≤ ((d - s : ℝ≥0):ℝ≥0∞) + s :=
        coe_le_coe_tsub_add d s
    _ ≤ hDevENN f (delayNN d) + ε := add_le_add hlb hs_le_ε

/-- `hDevENN f (delayNN d) = d` if `f(0⁺) = L > 0`. -/
theorem hDevENN_delay_eq_of_rightLimit_pos
    (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0) (L : ℝ≥0∞)
    (hL : TendstoRight f 0 L) (hL0 : 0 < L) :
    hDevENN f (delayNN d) = d :=
  hDevENN_delay_eq_of_pos_window f d
    (pos_near_zero_of_rightLimit_pos f L hL hL0)

/-- `hDevENN f (delayNN d) = d` if `f` is right-continuous with `f 0 > 0`. -/
theorem hDevENN_delay_eq_of_isRightContinuous
    (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0)
    (hrc : IsRightContinuous f) (h0 : 0 < f 0) :
    hDevENN f (delayNN d) = d :=
  hDevENN_delay_eq_of_rightLimit_pos f d (f 0)
    (hrc 0).tendsto h0

/-- `tokenBucketNN r b` has right limit `b` at `0`. -/
theorem tokenBucketNN_tendsto_right (r b : ℝ≥0) :
    Tendsto (tokenBucketNN r b) (𝓝[>] (0:ℝ≥0))
      (𝓝 (b:ℝ≥0∞)) := by
  have heq : (𝓝[>] (0:ℝ≥0)).EventuallyEq
      (tokenBucketNN r b)
      (fun t => ((r*t + b : ℝ≥0):ℝ≥0∞)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact tokenBucketNN_coe_of_ne r b (Set.mem_Ioi.mp ht).ne'
  rw [tendsto_congr' heq]
  have hcont : Tendsto
      (fun t : ℝ≥0 => ((r*t + b : ℝ≥0):ℝ≥0∞))
      (𝓝 (0:ℝ≥0)) (𝓝 ((r*0 + b : ℝ≥0):ℝ≥0∞)) := by
    apply (ENNReal.continuous_coe.tendsto _).comp
    exact (continuous_const.mul continuous_id).add
      continuous_const |>.tendsto 0
  simp only [mul_zero, zero_add] at hcont
  exact hcont.mono_left nhdsWithin_le_nhds

/-- `hDevENN (tokenBucketNN r b) (delayNN d) = d` when `b > 0`. -/
theorem hDevENN_tokenBucketNN_delay (r b d : ℝ≥0)
    (hb : 0 < b) :
    hDevENN (tokenBucketNN r b) (delayNN d) = d :=
  hDevENN_delay_eq_of_rightLimit_pos (tokenBucketNN r b) d
    (b:ℝ≥0∞) (tokenBucketNN_tendsto_right r b)
    (by exact_mod_cast hb)

/-- Real reading of admissibility: `tokenBucketNN r b t ≤ rateLatencyNN R T (t + d)`
gives `r*t + b ≤ R*(t + d - T)` over `ℝ` (`0 < b`, `t ≠ 0`). -/
theorem tokenBucketNN_le_rateLatencyNN_real
    (r b R T t d : ℝ≥0) (hb : 0 < b) (ht : t ≠ 0)
    (h : tokenBucketNN r b t ≤ rateLatencyNN R T (t+d)) :
    (r:ℝ)*t + b ≤ (R:ℝ)*((t:ℝ) + d - T) := by
  rw [tokenBucketNN_coe_of_ne r b ht, rateLatencyNN_coe,
    ENNReal.coe_le_coe, ← NNReal.coe_le_coe] at h
  push_cast [NNReal.coe_sub_def] at h
  rcases le_total ((t:ℝ)+d-T) 0 with hle|hle
  · rw [max_eq_right hle] at h
    have hbb : (0:ℝ) < b := by exact_mod_cast hb
    linarith [mul_nonneg r.coe_nonneg t.coe_nonneg]
  · rwa [max_eq_left hle] at h

/-- The shift `T + b/R` is admissible:
`tokenBucketNN r b t ≤ rateLatencyNN R T (t + (T + b/R))` when `0 < R`, `r ≤ R`. -/
theorem tokenBucketNN_le_rateLatencyNN_shift (r b R T t : ℝ≥0)
    (hR : 0 < R) (hrR : r ≤ R) :
    tokenBucketNN r b t
      ≤ rateLatencyNN R T (t + (T + b/R)) := by
  rcases eq_or_ne t 0 with ht | ht
  · subst ht; rw [tokenBucketNN_zero_eq]; exact bot_le
  · rw [tokenBucketNN_coe_of_ne r b ht, rateLatencyNN_coe,
      ENNReal.coe_le_coe]
    have hkey : (t + (T + b/R)) - T = t + b/R := by
      rw [show t + (T + b/R) = (t + b/R) + T by ring,
        add_tsub_cancel_right]
    rw [hkey]
    have hRbR : R * (b/R) = b := by
      rw [mul_div_assoc', mul_comm, mul_div_assoc,
        div_self hR.ne', mul_one]
    calc (r*t+b : ℝ≥0) ≤ R*t + b := by gcongr
      _ = R*(t + b/R) := by rw [mul_add, hRbR]

/-- `hDevENN (tokenBucketNN r b) βRT ≤ T + b/R` (`0 < R`, `r ≤ R`). -/
theorem hDevENN_tokenBucketNN_rateLatencyNN_le
    (r b R T : ℝ≥0) (hR : 0 < R) (hrR : r ≤ R) :
    hDevENN (tokenBucketNN r b) (rateLatencyNN R T)
      ≤ ((T + b/R : ℝ≥0):ℝ≥0∞) := by
  refine hDev_le fun t => ?_
  exact hDevAt_le (tokenBucketNN_le_rateLatencyNN_shift r b R T t hR hrR)

/-- Any admissible shift `d` obeys `R*T + b ≤ R*d + (R - r)*t`
(`0 < b`, `t ≠ 0`). -/
theorem tokenBucketNN_rateLatencyNN_shift_bound (r b R T t d : ℝ≥0)
    (hb : 0 < b) (ht : t ≠ 0)
    (h : tokenBucketNN r b t ≤ rateLatencyNN R T (t+d)) :
    R*T + b ≤ R*d + (R - r)*t := by
  have hreal := tokenBucketNN_le_rateLatencyNN_real r b R T t d hb ht h
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_sub_def]
  have htt : (0:ℝ) ≤ t := t.coe_nonneg
  have hmrt : ((R:ℝ)-r)*t ≤ max ((R:ℝ)-r) 0 * t := by
    rcases le_total ((R:ℝ)-r) 0 with hle|hle
    · rw [max_eq_right hle]; nlinarith
    · rw [max_eq_left hle]
  linarith [hreal, hmrt]

/-- Per-point lower bound on `hDevAtENN (tokenBucketNN r b) βRT`. -/
theorem hDevAtENN_rateLatencyNN_ge (r b R T t : ℝ≥0)
    (hR : 0 < R) (hb : 0 < b) (ht : t ≠ 0) :
    (((T + b/R) - ((R-r)/R)*t : ℝ≥0):ℝ≥0∞)
      ≤ hDevAtENN (tokenBucketNN r b)
          (rateLatencyNN R T) t := by
  refine le_hDevAtENN fun d hd => ?_
  rw [tsub_le_iff_right]
  have hbnd := tokenBucketNN_rateLatencyNN_shift_bound r b R T t d hb ht hd
  rw [← NNReal.coe_le_coe] at hbnd ⊢
  push_cast [NNReal.coe_sub_def] at hbnd ⊢
  have hRpos : (0:ℝ) < R := by exact_mod_cast hR
  refine le_of_mul_le_mul_right ?_ hRpos
  have e1 : ((T:ℝ) + b/R) * R = R*T + b := by
    field_simp
  have e2 : ((d:ℝ) + max ((R:ℝ)-r) 0 / R * t) * R
      = R*d + max ((R:ℝ)-r) 0 * t := by field_simp
  rw [e1, e2]; linarith [hbnd]

/-- **Deviation against a rate-latency is at least `T − t`** at any
point where the curve is positive: an admissible shift `d` must
push `t + d` past the latency `T`. -/
theorem hDevAtENN_rateLatencyNN_ge_latency (f : ℝ≥0 → ℝ≥0∞)
    (R T t : ℝ≥0) (hft : 0 < f t) :
    ((T - t : ℝ≥0) : ℝ≥0∞) ≤ hDevAtENN f (rateLatencyNN R T) t := by
  refine le_hDevAtENN fun d hd => ?_
  rcases le_total T t with hTt | hTt
  · rw [tsub_eq_zero_of_le hTt]; exact zero_le'
  · by_contra hlt
    rw [not_le] at hlt
    have htd : t + d < T := by
      have h := add_lt_add_right hlt t
      rwa [add_tsub_cancel_of_le hTt] at h
    have hz : rateLatencyNN R T (t + d) = 0 := by
      rw [rateLatencyNN_coe, tsub_eq_zero_of_le htd.le, mul_zero,
        ENNReal.coe_zero]
    rw [hz] at hd
    exact absurd (le_antisymm hd bot_le) hft.ne'

/-- **The latency lower-bounds the deviation**: against a rate-latency
`β_{R,T}`, any curve positive on a right-window of the origin has
`T ≤ hDev` — the deviation at small positive times approaches `T`
from below. -/
theorem le_hDevENN_rateLatencyNN (f : ℝ≥0 → ℝ≥0∞) (R T : ℝ≥0)
    (hpw : ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : ℝ≥0, 0 < t → t < δ → 0 < f t) :
    (T : ℝ≥0∞) ≤ hDevENN f (rateLatencyNN R T) := by
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  obtain ⟨δ, hδ, hpwf⟩ := hpw
  set t : ℝ≥0 := min ε (δ / 2) with ht
  have ht_pos : 0 < t := lt_min hε (by positivity)
  have ht_lt : t < δ :=
    lt_of_le_of_lt (min_le_right _ _) (NNReal.half_lt_self hδ.ne')
  have hft : 0 < f t := hpwf t ht_pos ht_lt
  have hlb : ((T - t : ℝ≥0) : ℝ≥0∞) ≤ hDevENN f (rateLatencyNN R T) := by
    refine le_trans (hDevAtENN_rateLatencyNN_ge_latency f R T t hft) ?_
    unfold hDevENN hDev; exact le_iSup _ t
  calc (T : ℝ≥0∞) ≤ ((T - t : ℝ≥0) : ℝ≥0∞) + t := coe_le_coe_tsub_add T t
    _ ≤ hDevENN f (rateLatencyNN R T) + ε := by
        gcongr
        exact min_le_left _ _

/-- `T + b/R ≤ hDevENN (tokenBucketNN r b) βRT` (`0 < R`, `0 < b`). -/
theorem hDevENN_tokenBucketNN_rateLatencyNN_ge
    (r b R T : ℝ≥0) (hR : 0 < R) (hb : 0 < b) :
    ((T + b/R : ℝ≥0):ℝ≥0∞)
      ≤ hDevENN (tokenBucketNN r b) (rateLatencyNN R T) := by
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  set c : ℝ≥0 := (R-r)/R with hc
  set s : ℝ≥0 := ε / (c + 1) with hs
  have hsne : s ≠ 0 := by rw [hs]; positivity
  have h1 : (((T + b/R) - c*s : ℝ≥0):ℝ≥0∞)
      ≤ hDevENN (tokenBucketNN r b) (rateLatencyNN R T) := by
    refine le_trans
      (hDevAtENN_rateLatencyNN_ge r b R T s hR hb hsne) ?_
    unfold hDevENN hDev; exact le_iSup _ s
  have hcs_le : ((c*s : ℝ≥0):ℝ≥0∞) ≤ (ε:ℝ≥0∞) := by
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    rw [hs]; push_cast
    have hd : (0:ℝ) < (c:ℝ) + 1 := by positivity
    rw [mul_div_assoc', div_le_iff₀ hd]
    nlinarith [c.coe_nonneg, ε.coe_nonneg]
  calc ((T + b/R : ℝ≥0):ℝ≥0∞)
      ≤ (((T+b/R) - c*s : ℝ≥0):ℝ≥0∞) + (c*s : ℝ≥0) :=
        coe_le_coe_tsub_add (T + b/R) (c*s)
    _ ≤ hDevENN (tokenBucketNN r b) (rateLatencyNN R T) + ε :=
        add_le_add h1 hcs_le

/-- `hDevENN (tokenBucketNN r b) βRT = T + b/R` (stable case). -/
theorem hDevENN_tokenBucketNN_rateLatencyNN (r b R T : ℝ≥0)
    (hR : 0 < R) (hb : 0 < b) (hrR : r ≤ R) :
    hDevENN (tokenBucketNN r b) (rateLatencyNN R T)
      = ((T + b/R : ℝ≥0):ℝ≥0∞) :=
  le_antisymm
    (hDevENN_tokenBucketNN_rateLatencyNN_le r b R T hR hrR)
    (hDevENN_tokenBucketNN_rateLatencyNN_ge r b R T hR hb)

/-- Unstable case `R < r`: any admissible shift `d` obeys `(r - R)*t ≤ R*d`
(`0 < b`, `t ≠ 0`). -/
theorem tokenBucketNN_rateLatencyNN_shift_bound_unstable (r b R T t d : ℝ≥0)
    (hb : 0 < b) (hRr : R < r) (ht : t ≠ 0)
    (h : tokenBucketNN r b t ≤ rateLatencyNN R T (t+d)) :
    (r - R)*t ≤ R*d := by
  have hreal := tokenBucketNN_le_rateLatencyNN_real r b R T t d hb ht h
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_sub_def]
  have hbb : (0:ℝ) < b := by exact_mod_cast hb
  have hRr' : (R:ℝ) < r := by exact_mod_cast hRr
  rw [max_eq_left (by linarith : (0:ℝ) ≤ (r:ℝ)-R)]
  linarith [hreal, mul_nonneg R.coe_nonneg T.coe_nonneg]

/-- Unstable per-point lower bound growing linearly in `t`. -/
theorem hDevAtENN_rateLatencyNN_ge_top (r b R T t : ℝ≥0)
    (hR : 0 < R) (hb : 0 < b) (hRr : R < r) (ht : t ≠ 0) :
    ((((r-R)/R)*t : ℝ≥0):ℝ≥0∞)
      ≤ hDevAtENN (tokenBucketNN r b)
          (rateLatencyNN R T) t := by
  refine le_hDevAtENN fun d hd => ?_
  have hbnd :=
    tokenBucketNN_rateLatencyNN_shift_bound_unstable r b R T t d hb hRr ht hd
  rw [div_mul_eq_mul_div, div_le_iff₀ hR, mul_comm d R]
  exact hbnd

/-- `hDevENN (tokenBucketNN r b) βRT = ⊤` when `R < r` (unstable). -/
theorem hDevENN_tokenBucketNN_rateLatencyNN_top
    (r b R T : ℝ≥0) (hR : 0 < R) (hb : 0 < b)
    (hRr : R < r) :
    hDevENN (tokenBucketNN r b) (rateLatencyNN R T) = ⊤ := by
  have hc : 0 < (r - R)/R := by
    have : 0 < r - R := tsub_pos_of_lt hRr
    positivity
  rw [eq_top_iff, ← iSup_coe_mul_eq_top ((r-R)/R) hc]
  refine iSup_le (fun s => ?_)
  rcases eq_or_ne s 0 with hs | hs
  · subst hs; simp
  · refine le_trans
      (hDevAtENN_rateLatencyNN_ge_top r b R T s hR hb hRr hs)
      ?_
    exact le_iSup
      (fun t => hDevAtENN (tokenBucketNN r b)
        (rateLatencyNN R T) t) s

/-- The shift `T + b/R` is admissible for the affine curve:
`affine r b t ≤ rateLatencyNN R T (t + (T + b/R))` when `0 < R`, `r ≤ R`. -/
theorem affine_le_rateLatencyNN_shift (r b R T t : ℝ≥0)
    (hR : 0 < R) (hrR : r ≤ R) :
    affine r b t ≤ rateLatencyNN R T (t + (T + b/R)) := by
  rw [affine_coe, rateLatencyNN_coe, ENNReal.coe_le_coe]
  have hkey : (t + (T + b/R)) - T = t + b/R := by
    rw [show t + (T + b/R) = (t + b/R) + T by ring,
      add_tsub_cancel_right]
  rw [hkey]
  have hRbR : R * (b/R) = b := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc,
      div_self hR.ne', mul_one]
  calc (r*t+b : ℝ≥0) ≤ R*t + b := by gcongr
    _ = R*(t + b/R) := by rw [mul_add, hRbR]

/-- `hDevENN (affine r b) βRT ≤ T + b/R` (`0 < R`, `r ≤ R`). -/
theorem hDevENN_affine_rateLatencyNN_le (r b R T : ℝ≥0)
    (hR : 0 < R) (hrR : r ≤ R) :
    hDevENN (affine r b) (rateLatencyNN R T)
      ≤ ((T + b/R : ℝ≥0):ℝ≥0∞) := by
  refine hDev_le fun t => ?_
  exact hDevAt_le (affine_le_rateLatencyNN_shift r b R T t hR hrR)

/-- `T + b/R ≤ hDevENN (affine r b) βRT` (`0 < R`, `0 < b`): the origin value
`b` already forces the full shift. -/
theorem hDevENN_affine_rateLatencyNN_ge (r b R T : ℝ≥0)
    (hR : 0 < R) (hb : 0 < b) :
    ((T + b/R : ℝ≥0):ℝ≥0∞)
      ≤ hDevENN (affine r b) (rateLatencyNN R T) := by
  have h0 : ((T + b/R : ℝ≥0):ℝ≥0∞)
      ≤ hDevAtENN (affine r b) (rateLatencyNN R T) 0 := by
    refine le_hDevAtENN fun d hd => ?_
    rw [affine_zero_eq, zero_add, rateLatencyNN_coe,
      ENNReal.coe_le_coe] at hd
    have hTd : T ≤ d := by
      by_contra hlt
      rw [not_le] at hlt
      rw [tsub_eq_zero_of_le hlt.le, mul_zero] at hd
      exact absurd hd (not_le.mpr hb)
    have hdiv : b/R ≤ d - T := by
      rw [div_le_iff₀ hR, mul_comm]; exact hd
    calc T + b/R ≤ T + (d - T) := add_le_add le_rfl hdiv
      _ = d := add_tsub_cancel_of_le hTd
  refine le_trans h0 ?_
  unfold hDevENN hDev
  exact le_iSup _ 0

/-- `hDevENN (affine r b) βRT = T + b/R` (stable case) — the affine curve's
deviation agrees with the token bucket's. -/
theorem hDevENN_affine_rateLatencyNN (r b R T : ℝ≥0)
    (hR : 0 < R) (hb : 0 < b) (hrR : r ≤ R) :
    hDevENN (affine r b) (rateLatencyNN R T)
      = ((T + b/R : ℝ≥0):ℝ≥0∞) :=
  le_antisymm
    (hDevENN_affine_rateLatencyNN_le r b R T hR hrR)
    (hDevENN_affine_rateLatencyNN_ge r b R T hR hb)

/-- `hDevENN (affine r b) βRT = ⊤` when `R < r` (unstable). -/
theorem hDevENN_affine_rateLatencyNN_top (r b R T : ℝ≥0)
    (hR : 0 < R) (hb : 0 < b) (hRr : R < r) :
    hDevENN (affine r b) (rateLatencyNN R T) = ⊤ := by
  rw [eq_top_iff,
    ← hDevENN_tokenBucketNN_rateLatencyNN_top r b R T hR hb hRr]
  exact hDev_mono (fun t => tokenBucketNN_le_affine r b t) le_rfl

/-- `vDev (tokenBucketNN r b) (delayNN d) = r*d + b` for `d > 0`. -/
theorem vDev_tokenBucketNN_delay (r b d : ℝ≥0)
    (hd : 0 < d) :
    vDev (tokenBucketNN r b) (delayNN d)
      = (r*d + b : ℝ≥0) := by
  rw [vDev_eq_deconv_zero,
    minDeconv_tokenBucketNN_delay r b d hd,
    affine_zero_eq, add_comm b (r*d)]

/-- `vDev (tokenBucketNN r b) βRT = r*T + b` (`r ≤ R`, `T > 0`). -/
theorem vDev_tokenBucketNN_rateLatencyNN (r b R T : ℝ≥0)
    (h : r ≤ R) (hT : 0 < T) :
    vDev (tokenBucketNN r b) (rateLatencyNN R T)
      = (r*T + b : ℝ≥0) := by
  rw [vDev_eq_deconv_zero,
    minDeconv_tokenBucketNN_rateLatencyNN r b R T h hT,
    affine_zero_eq, add_comm b (r*T)]

/-- `vDev (tokenBucketNN r b) βRT ≤ r*T + b` (`r ≤ R`), valid for every `T` including `T = 0`
(where the backlog bound is the burst `b`) — the latency-free `≤` companion of the equality, which
needs `0 < T`. Proved by the pointwise vertical bound `r*t ≤ R*(t-T) + r*T` (via `le_tsub_add`). -/
theorem vDev_tokenBucketNN_rateLatencyNN_le (r b R T : ℝ≥0) (h : r ≤ R) :
    vDev (tokenBucketNN r b) (rateLatencyNN R T) ≤ ((r * T + b : ℝ≥0) : ℝ≥0∞) := by
  refine vDev_le fun t => ?_
  show tokenBucketNN r b t - rateLatencyNN R T t ≤ ((r * T + b : ℝ≥0) : ℝ≥0∞)
  rw [tsub_le_iff_right, rateLatencyNN_coe]
  calc tokenBucketNN r b t
      ≤ ((r * t + b : ℝ≥0) : ℝ≥0∞) := by rw [tokenBucketNN_apply]; exact inf_le_left
    _ ≤ ((r * T + b : ℝ≥0) : ℝ≥0∞) + ((R * (t - T) : ℝ≥0) : ℝ≥0∞) := by
        rw [← ENNReal.coe_add]
        refine ENNReal.coe_le_coe.mpr ?_
        have hrt : r * t ≤ R * (t - T) + r * T := by
          calc r * t ≤ r * (t - T + T) := by gcongr; exact le_tsub_add
            _ = r * (t - T) + r * T := by rw [mul_add]
            _ ≤ R * (t - T) + r * T := by gcongr
        calc r * t + b ≤ (R * (t - T) + r * T) + b := by gcongr
          _ = r * T + b + R * (t - T) := by ring

/-- `vDev (tokenBucketNN r b) βRT = ⊤` when `R < r` (unstable). -/
theorem vDev_tokenBucketNN_rateLatencyNN_top
    (r b R T : ℝ≥0) (hRr : R < r) :
    vDev (tokenBucketNN r b) (rateLatencyNN R T) = ⊤ := by
  rw [vDev_eq_deconv_zero,
    minDeconv_tokenBucketNN_rateLatencyNN_top r b R T hRr]

/-- A curve's value at the latency lower-bounds its vertical deviation
against `β_{R,T}`: `α T ≤ vDev α (rateLatencyNN R T)` — the rate-latency
server is still null at its latency. -/
theorem apply_le_vDev_rateLatencyNN (α : ℝ≥0 → ℝ≥0∞) (R T : ℝ≥0) :
    α T ≤ vDev α (rateLatencyNN R T) := by
  refine le_trans (le_of_eq ?_) (vDevAt_le_vDev _ _ T)
  rw [vDevAt, rateLatencyNN, tsub_self, ENNReal.coe_zero, mul_zero,
    tsub_zero]

/-- The matching equality `vDev(ν_{P,s}, β_{R,T}) = ν_{P,s}(T)` fails in
general, even under stability `s/P < R`: a jump of the staircase just
past the latency pushes the supremum strictly above the value at `T`. -/
theorem not_forall_vDev_staircase_rateLatencyNN_eq :
    ¬ ∀ (P s R T : ℝ≥0), s / P < R →
      vDev (staircase P s 0) (rateLatencyNN R T) = staircase P s 0 T := by
  intro h
  have hbad := h 1 1 2 1 (by norm_num)
  -- `ν(1) = 1`, while the deviation at `t = 11/10` is `2 − 1/5 = 9/5`
  have hT : staircase 1 1 0 1 = 1 := by
    simp only [staircase, delayNN, delay_apply,
      if_neg (by norm_num : ¬ (1:ℝ≥0) ≤ 0), min_top_right]
    norm_num
  have hsval : staircase 1 1 0 (11 / 10) = ((2 : ℝ≥0) : ℝ≥0∞) := by
    simp only [staircase, delayNN, delay_apply,
      if_neg (by norm_num : ¬ (11 / 10 : ℝ≥0) ≤ 0), min_top_right]
    have hc : ⌈(((11 / 10 : ℝ≥0) : ℝ) + 0) / ((1 : ℝ≥0) : ℝ)⌉ = 2 := by
      rw [Int.ceil_eq_iff]
      push_cast
      norm_num
    rw [hc]
    norm_num
  have hβval : rateLatencyNN 2 1 (11 / 10) = ((1 / 5 : ℝ≥0) : ℝ≥0∞) := by
    rw [rateLatencyNN,
      show (11 / 10 - 1 : ℝ≥0) = 1 / 10 from by
        rw [← NNReal.coe_inj, NNReal.coe_sub (by
          rw [← NNReal.coe_le_coe]; push_cast; norm_num)]
        push_cast
        norm_num,
      ← ENNReal.coe_mul, ENNReal.coe_inj, ← NNReal.coe_inj]
    push_cast
    norm_num
  have hAt : ((9 / 5 : ℝ≥0) : ℝ≥0∞)
      ≤ vDev (staircase 1 1 0) (rateLatencyNN 2 1) := by
    refine le_trans (le_of_eq ?_) (vDevAt_le_vDev _ _ (11 / 10))
    rw [vDevAt, hsval, hβval, ← ENNReal.coe_sub, ENNReal.coe_inj,
      ← NNReal.coe_inj, NNReal.coe_sub (by
        rw [← NNReal.coe_le_coe]; push_cast; norm_num)]
    push_cast
    norm_num
  rw [hbad, hT, ← ENNReal.coe_one, ENNReal.coe_le_coe] at hAt
  have : ((9 / 5 : ℝ≥0) : ℝ) ≤ 1 := by exact_mod_cast hAt
  norm_num at this

end DeepWiki
