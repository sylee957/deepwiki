import Book.RealCurvesDeconv
import Book.Continuity
import Book.Deviations

/-! Horizontal and vertical deviations specialized to `ℝ≥0 → ℝ≥0∞`: the
`delay`/`tokenBucket`/`rateLatency` deviation values (stable and unstable), and
the right-limit/right-continuity criteria for a positive horizontal deviation.
The general deviations live in `Book.Deviations`; here `hDevAtE`/`hDevE`
pin the shift-embedding to `(↑· : ℝ≥0 → ℝ≥0∞)`. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
open Set Topology Filter

/-- `ℝ≥0∞`-valued horizontal deviation: `hDevAt` with shift-embedding `↑`. -/
noncomputable abbrev hDevAtE (f g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) : ℝ≥0∞ :=
  hDevAt f g t

/-- `ℝ≥0∞`-valued horizontal deviation sup: `hDev` with shift-embedding `↑`. -/
noncomputable abbrev hDevE (f g : ℝ≥0 → ℝ≥0∞) : ℝ≥0∞ :=
  hDev f g

/-- `hDevAtE` as an explicit-coe infimum (collapses the generic `CoeTC.coe`). -/
theorem hDevAtE_eq (f g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    hDevAtE f g t
      = ⨅ d : {d : ℝ≥0 // f t ≤ g (t + d)}, (d.1 : ℝ≥0∞) := rfl

/-- Intro: `x ≤ d` over all admissible shifts `d` gives `↑x ≤ hDevAtE f g t`
(the coercion crossing is absorbed). -/
theorem le_hDevAtE {f g : ℝ≥0 → ℝ≥0∞} {t x : ℝ≥0}
    (h : ∀ d : ℝ≥0, f t ≤ g (t + d) → x ≤ d) :
    (x : ℝ≥0∞) ≤ hDevAtE f g t := by
  rw [hDevAtE_eq]
  exact le_iInf fun d => ENNReal.coe_le_coe.mpr (h d.1 d.2)

/-- `delayNN d (t + u) = ⊤` when `d < t + u`. -/
theorem delayNN_top_of_gt (d t u : ℝ≥0) (h : d < t + u) :
    delayNN d (t + u) = ⊤ := by
  simp only [delayNN, delay_apply, if_neg (not_le.mpr h)]

/-- `hDevAtE f (delayNN d) t ≤ d`. -/
theorem hDevAtE_delay_le (f : ℝ≥0 → ℝ≥0∞) (d t : ℝ≥0) :
    hDevAtE f (delayNN d) t ≤ d := by
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  have hadm : f t ≤ delayNN d (t + (d + ε)) := by
    rw [delayNN_top_of_gt d t (d + ε) (by
      calc d < d + ε := by simpa using hε
        _ ≤ t + (d + ε) := le_add_self)]
    exact le_top
  rw [hDevAtE_eq]
  refine iInf_le_of_le ⟨d + ε, hadm⟩ ?_
  push_cast; rfl

/-- `hDevE f (delayNN d) ≤ d`. -/
theorem hDevE_delay_le (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0) :
    hDevE f (delayNN d) ≤ d := by
  unfold hDevE hDev
  exact iSup_le (fun t => hDevAtE_delay_le f d t)

/-- `(d - t) ≤ hDevAtE f (delayNN d) t` when `f t > 0`. -/
theorem hDevAtE_delay_ge (f : ℝ≥0 → ℝ≥0∞) (d t : ℝ≥0)
    (hft : 0 < f t) :
    ((d - t : ℝ≥0) : ℝ≥0∞) ≤ hDevAtE f (delayNN d) t := by
  refine le_hDevAtE fun d' hd' => ?_
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

/-- `hDevE f (delayNN d) = d` when `f > 0` on `(0, ∞)`. -/
theorem hDevE_delay_eq (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0)
    (hf : ∀ t : ℝ≥0, 0 < t → 0 < f t) :
    hDevE f (delayNN d) = d := by
  apply le_antisymm (hDevE_delay_le f d)
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  have ht : (0:ℝ≥0) < ε := hε
  have hlb : ((d - ε : ℝ≥0):ℝ≥0∞) ≤ hDevE f (delayNN d) := by
    refine le_trans (hDevAtE_delay_ge f d ε (hf ε ht)) ?_
    unfold hDevE hDev; exact le_iSup _ ε
  calc (d:ℝ≥0∞) ≤ ((d - ε : ℝ≥0):ℝ≥0∞) + ε :=
        coe_le_coe_tsub_add d ε
    _ ≤ hDevE f (delayNN d) + ε := by gcongr

/-- `hDevE f (delayNN d) = d` if `f > 0` on some right-window of `0`. -/
theorem hDevE_delay_eq_of_pos_window
    (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0)
    (hw : ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ t : ℝ≥0, 0 < t → t < δ → 0 < f t) :
    hDevE f (delayNN d) = d := by
  apply le_antisymm (hDevE_delay_le f d)
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
      ≤ hDevE f (delayNN d) := by
    refine le_trans
      (hDevAtE_delay_ge f d s (hpw s hs_pos hs_ltδ)) ?_
    unfold hDevE hDev; exact le_iSup _ s
  calc (d:ℝ≥0∞) ≤ ((d - s : ℝ≥0):ℝ≥0∞) + s :=
        coe_le_coe_tsub_add d s
    _ ≤ hDevE f (delayNN d) + ε := add_le_add hlb hs_le_ε

/-- `hDevE f (delayNN d) = d` if `f(0⁺) = L > 0`. -/
theorem hDevE_delay_eq_of_rightLimit_pos
    (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0) (L : ℝ≥0∞)
    (hL : TendstoRight f 0 L) (hL0 : 0 < L) :
    hDevE f (delayNN d) = d :=
  hDevE_delay_eq_of_pos_window f d
    (pos_near_zero_of_rightLimit_pos f L hL hL0)

/-- `hDevE f (delayNN d) = d` if `f` is right-continuous with `f 0 > 0`. -/
theorem hDevE_delay_eq_of_rightCont
    (f : ℝ≥0 → ℝ≥0∞) (d : ℝ≥0)
    (hrc : IsRightContinuous f) (h0 : 0 < f 0) :
    hDevE f (delayNN d) = d :=
  hDevE_delay_eq_of_rightLimit_pos f d (f 0)
    (hrc 0).tendsto h0

/-- `tokenBucket r b` has right limit `b` at `0`. -/
theorem tokenBucket_tendsto_right (r b : ℝ≥0) :
    Tendsto (tokenBucket r b) (𝓝[>] (0:ℝ≥0))
      (𝓝 (b:ℝ≥0∞)) := by
  have heq : (𝓝[>] (0:ℝ≥0)).EventuallyEq
      (tokenBucket r b)
      (fun t => ((r*t + b : ℝ≥0):ℝ≥0∞)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact tokenBucket_coe_of_ne r b (Set.mem_Ioi.mp ht).ne'
  rw [tendsto_congr' heq]
  have hcont : Tendsto
      (fun t : ℝ≥0 => ((r*t + b : ℝ≥0):ℝ≥0∞))
      (𝓝 (0:ℝ≥0)) (𝓝 ((r*0 + b : ℝ≥0):ℝ≥0∞)) := by
    apply (ENNReal.continuous_coe.tendsto _).comp
    exact (continuous_const.mul continuous_id).add
      continuous_const |>.tendsto 0
  simp only [mul_zero, zero_add] at hcont
  exact hcont.mono_left nhdsWithin_le_nhds

/-- `hDevE (tokenBucket r b) (delayNN d) = d` when `b > 0`. -/
theorem hDevE_tokenBucket_delay (r b d : ℝ≥0)
    (hb : 0 < b) :
    hDevE (tokenBucket r b) (delayNN d) = d :=
  hDevE_delay_eq_of_rightLimit_pos (tokenBucket r b) d
    (b:ℝ≥0∞) (tokenBucket_tendsto_right r b)
    (by exact_mod_cast hb)

/-- Admissibility `tb ≤ βRT(t+d)` gives `r*t+b ≤ R*((t+d)-T)`. -/
theorem beta_admissible_imp
    (r b R T t d : ℝ≥0) (ht : t ≠ 0)
    (h : tokenBucket r b t ≤ rateLatency R T (t+d)) :
    (r*t+b : ℝ≥0) ≤ R*((t+d)-T) := by
  rw [tokenBucket_coe_of_ne r b ht, rateLatency_coe,
    ENNReal.coe_le_coe] at h
  exact h

/-- Shift `d* = T + b/R` is admissible (`0 < R`, `r ≤ R`). -/
theorem dstar_admissible (r b R T t : ℝ≥0)
    (hR : 0 < R) (hrR : r ≤ R) :
    tokenBucket r b t
      ≤ rateLatency R T (t + (T + b/R)) := by
  rcases eq_or_ne t 0 with ht | ht
  · subst ht; rw [tokenBucket_zero_eq]; exact bot_le
  · rw [tokenBucket_coe_of_ne r b ht, rateLatency_coe,
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

/-- `hDevE (tokenBucket r b) βRT ≤ T + b/R` (`0 < R`, `r ≤ R`). -/
theorem hDevE_tokenBucket_rateLatency_le
    (r b R T : ℝ≥0) (hR : 0 < R) (hrR : r ≤ R) :
    hDevE (tokenBucket r b) (rateLatency R T)
      ≤ ((T + b/R : ℝ≥0):ℝ≥0∞) := by
  unfold hDevE hDev
  refine iSup_le (fun t => ?_)
  unfold hDevAt
  exact iInf_le_of_le
    ⟨T + b/R, dstar_admissible r b R T t hR hrR⟩
    (le_refl _)

/-- Admissible shift lower bound: `R*T + b ≤ R*d + (R-r)*t`. -/
theorem dlb (r b R T t d : ℝ≥0) (hb : 0 < b)
    (ht : t ≠ 0)
    (h : tokenBucket r b t ≤ rateLatency R T (t+d)) :
    R*T + b ≤ R*d + (R - r)*t := by
  have hreal := beta_admissible_imp r b R T t d ht h
  rw [← NNReal.coe_le_coe] at hreal ⊢
  push_cast [NNReal.coe_sub_def] at hreal ⊢
  have htt : (0:ℝ) ≤ t := by positivity
  have hbb : (0:ℝ) < b := by exact_mod_cast hb
  have hmrt : (R-r:ℝ)*t ≤ max ((R:ℝ)-r) 0 * t := by
    rcases le_total ((R:ℝ)-r) 0 with hle|hle
    · rw [max_eq_right hle]; nlinarith
    · rw [max_eq_left hle]
  rcases le_total ((t:ℝ)+d-T) 0 with hle|hle
  · rw [max_eq_right hle] at hreal
    nlinarith [hreal,
      mul_nonneg htt (by positivity : (0:ℝ) ≤ r)]
  · rw [max_eq_left hle] at hreal
    nlinarith [hreal, hmrt]

/-- Per-point lower bound on `hDevAtE (tokenBucket r b) βRT`. -/
theorem hDevAtE_rateLatency_ge (r b R T t : ℝ≥0)
    (hR : 0 < R) (hb : 0 < b) (ht : t ≠ 0) :
    (((T + b/R) - ((R-r)/R)*t : ℝ≥0):ℝ≥0∞)
      ≤ hDevAtE (tokenBucket r b)
          (rateLatency R T) t := by
  refine le_hDevAtE fun d hd => ?_
  rw [tsub_le_iff_right]
  have hbnd := dlb r b R T t d hb ht hd
  rw [← NNReal.coe_le_coe] at hbnd ⊢
  push_cast [NNReal.coe_sub_def] at hbnd ⊢
  have hRpos : (0:ℝ) < R := by exact_mod_cast hR
  refine le_of_mul_le_mul_right ?_ hRpos
  have e1 : ((T:ℝ) + b/R) * R = R*T + b := by
    field_simp
  have e2 : ((d:ℝ) + max ((R:ℝ)-r) 0 / R * t) * R
      = R*d + max ((R:ℝ)-r) 0 * t := by field_simp
  rw [e1, e2]; linarith [hbnd]

/-- `T + b/R ≤ hDevE (tokenBucket r b) βRT` (`0 < R`, `0 < b`). -/
theorem hDevE_tokenBucket_rateLatency_ge
    (r b R T : ℝ≥0) (hR : 0 < R) (hb : 0 < b) :
    ((T + b/R : ℝ≥0):ℝ≥0∞)
      ≤ hDevE (tokenBucket r b) (rateLatency R T) := by
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  set c : ℝ≥0 := (R-r)/R with hc
  set s : ℝ≥0 := ε / (c + 1) with hs
  have hsne : s ≠ 0 := by rw [hs]; positivity
  have h1 : (((T + b/R) - c*s : ℝ≥0):ℝ≥0∞)
      ≤ hDevE (tokenBucket r b) (rateLatency R T) := by
    refine le_trans
      (hDevAtE_rateLatency_ge r b R T s hR hb hsne) ?_
    unfold hDevE hDev; exact le_iSup _ s
  have hcs_le : ((c*s : ℝ≥0):ℝ≥0∞) ≤ (ε:ℝ≥0∞) := by
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    rw [hs]; push_cast
    have hd : (0:ℝ) < (c:ℝ) + 1 := by positivity
    rw [mul_div_assoc', div_le_iff₀ hd]
    nlinarith [c.coe_nonneg, ε.coe_nonneg]
  calc ((T + b/R : ℝ≥0):ℝ≥0∞)
      ≤ (((T+b/R) - c*s : ℝ≥0):ℝ≥0∞) + (c*s : ℝ≥0) :=
        coe_le_coe_tsub_add (T + b/R) (c*s)
    _ ≤ hDevE (tokenBucket r b) (rateLatency R T) + ε :=
        add_le_add h1 hcs_le

/-- `hDevE (tokenBucket r b) βRT = T + b/R` (stable case). -/
theorem hDevE_tokenBucket_rateLatency (r b R T : ℝ≥0)
    (hR : 0 < R) (hb : 0 < b) (hrR : r ≤ R) :
    hDevE (tokenBucket r b) (rateLatency R T)
      = ((T + b/R : ℝ≥0):ℝ≥0∞) :=
  le_antisymm
    (hDevE_tokenBucket_rateLatency_le r b R T hR hrR)
    (hDevE_tokenBucket_rateLatency_ge r b R T hR hb)

/-- Unstable admissible bound: `(r-R)*t ≤ R*d` when `R < r`. -/
theorem dlb_top (r b R T t d : ℝ≥0) (hR : 0 < R)
    (hb : 0 < b) (hRr : R < r) (ht : t ≠ 0)
    (h : tokenBucket r b t ≤ rateLatency R T (t+d)) :
    (r - R)*t ≤ R*d := by
  have hreal := beta_admissible_imp r b R T t d ht h
  rw [← NNReal.coe_le_coe] at hreal ⊢
  push_cast [NNReal.coe_sub_def] at hreal ⊢
  have hRpos : (0:ℝ) < R := by exact_mod_cast hR
  have hbb : (0:ℝ) < b := by exact_mod_cast hb
  have hRr' : (R:ℝ) < r := by exact_mod_cast hRr
  rw [max_eq_left (by linarith : (0:ℝ) ≤ (r:ℝ)-R)]
  rcases le_total ((t:ℝ)+d-T) 0 with hle|hle
  · rw [max_eq_right hle] at hreal
    nlinarith [hreal,
      mul_nonneg hRpos.le (by positivity:(0:ℝ)≤t)]
  · rw [max_eq_left hle] at hreal
    nlinarith [hreal, T.coe_nonneg, hbb,
      mul_nonneg hRpos.le T.coe_nonneg]

/-- Unstable per-point lower bound growing linearly in `t`. -/
theorem hDevAtE_rateLatency_ge_top (r b R T t : ℝ≥0)
    (hR : 0 < R) (hb : 0 < b) (hRr : R < r) (ht : t ≠ 0) :
    ((((r-R)/R)*t : ℝ≥0):ℝ≥0∞)
      ≤ hDevAtE (tokenBucket r b)
          (rateLatency R T) t := by
  refine le_hDevAtE fun d hd => ?_
  have hbnd := dlb_top r b R T t d hR hb hRr ht hd
  rw [div_mul_eq_mul_div, div_le_iff₀ hR, mul_comm d R]
  exact hbnd

/-- `hDevE (tokenBucket r b) βRT = ⊤` when `R < r` (unstable). -/
theorem hDevE_tokenBucket_rateLatency_top
    (r b R T : ℝ≥0) (hR : 0 < R) (hb : 0 < b)
    (hRr : R < r) :
    hDevE (tokenBucket r b) (rateLatency R T) = ⊤ := by
  have hc : 0 < (r - R)/R := by
    have : 0 < r - R := tsub_pos_of_lt hRr
    positivity
  rw [eq_top_iff, ← iSup_coe_mul_eq_top ((r-R)/R) hc]
  refine iSup_le (fun s => ?_)
  rcases eq_or_ne s 0 with hs | hs
  · subst hs; simp
  · refine le_trans
      (hDevAtE_rateLatency_ge_top r b R T s hR hb hRr hs)
      ?_
    exact le_iSup
      (fun t => hDevAtE (tokenBucket r b)
        (rateLatency R T) t) s

/-- `vDev (tokenBucket r b) (delayNN d) = r*d + b` for `d > 0`. -/
theorem vDev_tokenBucket_delay (r b d : ℝ≥0)
    (hd : 0 < d) :
    vDev (tokenBucket r b) (delayNN d)
      = (r*d + b : ℝ≥0) := by
  rw [vDev_eq_deconv_zero,
    minDeconv_tokenBucket_delay r b d hd,
    affine_zero_eq, add_comm b (r*d)]

/-- `vDev (tokenBucket r b) βRT = r*T + b` (`r ≤ R`, `T > 0`). -/
theorem vDev_tokenBucket_rateLatency (r b R T : ℝ≥0)
    (h : r ≤ R) (hT : 0 < T) :
    vDev (tokenBucket r b) (rateLatency R T)
      = (r*T + b : ℝ≥0) := by
  rw [vDev_eq_deconv_zero,
    minDeconv_tokenBucket_rateLatency r b R T h hT,
    affine_zero_eq, add_comm b (r*T)]

/-- `vDev (tokenBucket r b) βRT = ⊤` when `R < r` (unstable). -/
theorem vDev_tokenBucket_rateLatency_top
    (r b R T : ℝ≥0) (hRr : R < r) :
    vDev (tokenBucket r b) (rateLatency R T) = ⊤ := by
  rw [vDev_eq_deconv_zero,
    minDeconv_tokenBucket_rateLatency_top r b R T hRr]

end DeepWiki
