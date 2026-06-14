import Book.RealCurvesDeviations
import Book.ArrivalCurvesPeriodic

/-! # Delay of a shaped periodic flow
The shaping closed-form delay: a periodic flow of period `P`, packet size `s`,
crossing a constant-rate-`C` shaper `λ_C` and then a rate-latency server
`β_{R,T}`. The shaped arrival curve is the TSpec
`f = γ_{s/P,s} ⊓ λ_C` (`tokenBucketNN (s/P) s ⊓ rateNN C`), and under stability
`s/P < min(C,R)` the horizontal deviation has the closed form
`hDev(f, β_{R,T}) = T + [(C − R)/(C − s/P)]⁺ · (s/R)`.

This file lands the full equality in the `C ≥ R` stable case
(`hDevENN_shaped_rateLatencyNN`): the upper bound is the admissible fixed shift
through the kink of the two `min` lines (`hDevENN_shaped_rateLatencyNN_le`) and
the matching lower bound is the deviation at the kink witness
`t* = s/(C − s/P)` (`le_hDevAtENN_shaped_kinkTime`). It also records the
*shaping reduces delay* comparison `hDev(f, β) ≤ hDev(γ, β) = T + s/R`
(`hDevENN_shaped_le_tokenBucketNN`, by monotonicity in the first argument since
`f ≤ γ`). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The kink shift `δ = [(C − R)/(C − s/P)] · (s/R)`: the fixed horizontal shift
that makes `β_{R,T}` clear the shaped curve `γ_{s/P,s} ⊓ λ_C` everywhere. -/
noncomputable def shapedShift (P s C R : ℝ≥0) : ℝ≥0 :=
  (C - R) / (C - s / P) * (s / R)

/-- `R · δ = s·(C − R)/(C − s/P)` (the kink burst), under `0 < R`. -/
theorem rate_mul_shapedShift (P s C R : ℝ≥0) (hR : 0 < R) :
    R * shapedShift P s C R = (C - R) / (C - s / P) * s := by
  rw [shapedShift, mul_comm R _, mul_assoc]
  congr 1
  rw [div_mul_cancel₀ s hR.ne']

/-- The fixed shift `δ` is admissible at every time: the shaped curve
`γ_{s/P,s} ⊓ λ_C` is cleared by `β_{R,T}` shifted by `δ`, i.e.
`(γ_{s/P,s} ⊓ λ_C) t ≤ β_{R,T} (t + (T + δ))` under stability
`s/P < R ≤ C` with `0 < R`. -/
theorem shaped_le_rateLatencyNN_shift (P s C R T t : ℝ≥0)
    (hR : 0 < R) (hRC : R ≤ C) (hsPR : s / P < R) :
    (tokenBucketNN (s / P) s ⊓ rateNN C) t
      ≤ rateLatencyNN R T (t + (T + shapedShift P s C R)) := by
  have hsPC : s / P < C := lt_of_lt_of_le hsPR hRC
  set ρ : ℝ≥0 := s / P with hρ
  set δ : ℝ≥0 := shapedShift P s C R with hδ
  rw [rateLatencyNN_coe]
  have hkey : (t + (T + δ)) - T = t + δ := by
    rw [show t + (T + δ) = (t + δ) + T by ring, add_tsub_cancel_right]
  rw [hkey]
  -- The kink burst `R·δ = (C−R)·(s/(C−ρ))`, computed over `ℝ` after coercion.
  have hKdef : (R:ℝ) * δ = ((C:ℝ) - R) * ((s:ℝ) / ((C:ℝ) - ρ)) := by
    have h := rate_mul_shapedShift P s C R hR
    have hcoe : ((R * δ : ℝ≥0):ℝ) = (((C - R) / (C - ρ) * s : ℝ≥0):ℝ) := by
      rw [h]
    rw [NNReal.coe_mul] at hcoe
    rw [hcoe]
    rw [NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_sub hRC, NNReal.coe_sub (le_of_lt hsPC)]
    ring
  have hρR : (ρ:ℝ) ≤ R := le_of_lt (by exact_mod_cast hsPR)
  have hCρ : (0:ℝ) < (C:ℝ) - ρ := by
    have : (ρ:ℝ) < C := by exact_mod_cast hsPC
    linarith
  -- kink time `t* = s/(C−ρ)` as a real
  set rt : ℝ := (s:ℝ) / ((C:ℝ) - ρ) with hrt
  have hrt0 : 0 ≤ rt := div_nonneg s.coe_nonneg (le_of_lt hCρ)
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    rw [Pi.inf_apply, tokenBucketNN_zero_eq]; exact inf_le_left.trans bot_le
  -- t ≠ 0. Split on `(t:ℝ) ≤ t*` (use the rate branch) vs `t* ≤ t` (bucket branch).
  rcases le_total (t:ℝ) rt with hle | hge
  · -- rate branch: `λ_C t = C·t`, `f t ≤ C·t ≤ R·(t+δ)` (the `−T` cancelled)
    refine inf_le_right.trans ?_
    rw [rateNN_apply, ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    push_cast
    -- goal over `ℝ`: `C·t ≤ R·(t + δ)`, i.e. `(C−R)·t ≤ R·δ = (C−R)·t*`
    have hCR : (0:ℝ) ≤ (C:ℝ) - R := by
      have : (R:ℝ) ≤ C := by exact_mod_cast hRC
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hle hCR, hKdef, t.coe_nonneg]
  · -- bucket branch: `γ t = ρ·t + s`, `f t ≤ ρ·t + s ≤ R·(t+δ)` (the `−T` cancelled)
    refine inf_le_left.trans ?_
    rw [tokenBucketNN_coe_of_ne ρ s ht, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    push_cast
    -- the kink identity `s = (C − ρ)·t*`
    have hsstar : (s:ℝ) = ((C:ℝ) - ρ) * rt := by
      rw [hrt, mul_div_cancel₀ _ (ne_of_gt hCρ)]
    -- goal over `ℝ`: `ρ·t + s ≤ R·(t + δ)`, i.e. `(ρ−R)·t + s ≤ R·δ = (C−R)·t*`
    have hρRle : (ρ:ℝ) - R ≤ 0 := by linarith
    nlinarith [mul_le_mul_of_nonpos_left hge hρRle, hKdef, hsstar]

/-- **Shaping closed-form delay, upper bound** (`C ≥ R` stable case).
For the shaped periodic flow `f = γ_{s/P,s} ⊓ λ_C` crossing `β_{R,T}` under
stability `s/P < R ≤ C` (`0 < R`),
`hDev(f, β_{R,T}) ≤ T + [(C − R)/(C − s/P)] · (s/R)`. The bound is the kink
value of the two `min` lines; the matching lower bound is
`le_hDevAtENN_shaped_kinkTime`, and the equality `hDevENN_shaped_rateLatencyNN`. -/
theorem hDevENN_shaped_rateLatencyNN_le (P s C R T : ℝ≥0)
    (hR : 0 < R) (hRC : R ≤ C) (hsPR : s / P < R) :
    hDevENN (tokenBucketNN (s / P) s ⊓ rateNN C) (rateLatencyNN R T)
      ≤ ((T + shapedShift P s C R : ℝ≥0) : ℝ≥0∞) := by
  refine hDev_le fun t => ?_
  exact hDevAt_le (shaped_le_rateLatencyNN_shift P s C R T t hR hRC hsPR)

/-- The shaped curve `f = γ_{s/P,s} ⊓ λ_C` is pointwise below the token bucket
`γ_{s/P,s}` (the rate cap of `λ_C` only lowers it). -/
theorem shaped_le_tokenBucketNN (P s C : ℝ≥0) :
    (tokenBucketNN (s / P) s ⊓ rateNN C) ≤ tokenBucketNN (s / P) s :=
  inf_le_left

/-- **Shaping reduces delay**: the shaped flow's horizontal deviation is no
larger than the unshaped token bucket's, `hDev(f, β) ≤ hDev(γ, β) = T + s/R`
(`s/P ≤ R`, `0 < R`). The right-hand value is `hDevENN_tokenBucketNN_rateLatencyNN`;
the inequality is `hDev`-monotonicity in the first argument via `f ≤ γ`. -/
theorem hDevENN_shaped_le_tokenBucketNN (P s C R T : ℝ≥0)
    (hR : 0 < R) (hs : 0 < s) (hsPR : s / P ≤ R) :
    hDevENN (tokenBucketNN (s / P) s ⊓ rateNN C) (rateLatencyNN R T)
      ≤ ((T + s / R : ℝ≥0) : ℝ≥0∞) := by
  refine le_trans (hDev_mono (shaped_le_tokenBucketNN P s C) le_rfl) ?_
  exact le_of_eq (hDevENN_tokenBucketNN_rateLatencyNN (s / P) s R T hR hs hsPR)

/-- The kink time `t* = s/(C − s/P)` where the two `min` lines `γ_{s/P,s}` and
`λ_C` of the shaped curve cross. -/
noncomputable def kinkTime (P s C : ℝ≥0) : ℝ≥0 :=
  s / (C - s / P)

/-- At the kink time the two shaped lines agree: `γ_{s/P,s}(t*) = λ_C(t*)`, both
`= C · t*` (`s/P < C`, `0 < s`). -/
theorem tokenBucketNN_kinkTime_eq (P s C : ℝ≥0)
    (hs : 0 < s) (hsPC : s / P < C) :
    tokenBucketNN (s / P) s (kinkTime P s C) = rateNN C (kinkTime P s C) := by
  set ρ : ℝ≥0 := s / P with hρ
  have hCρpos : 0 < C - ρ := tsub_pos_of_lt hsPC
  have htne : kinkTime P s C ≠ 0 := by
    rw [kinkTime, ← hρ]
    exact (div_ne_zero hs.ne' hCρpos.ne')
  rw [tokenBucketNN_coe_of_ne ρ s htne, rateNN_apply, ← ENNReal.coe_mul,
    ENNReal.coe_inj, ← NNReal.coe_inj]
  push_cast
  have hCρ : (0:ℝ) < (C:ℝ) - ρ := by
    rw [← NNReal.coe_sub (le_of_lt hsPC)]; exact_mod_cast hCρpos
  have hkt : ((kinkTime P s C : ℝ≥0):ℝ) = (s:ℝ) / ((C:ℝ) - ρ) := by
    rw [kinkTime, ← hρ, NNReal.coe_div, NNReal.coe_sub (le_of_lt hsPC)]
  rw [hkt]; field_simp; ring

/-- Lower bound at the kink witness: `T + δ ≤ hDevAtENN(f, β_{R,T}, t*)`, where
`δ = shapedShift P s C R` and `f = γ_{s/P,s} ⊓ λ_C`. The kink burst makes
`f(t*)/R = t* + δ`, so any admissible shift `d` obeys `T + δ ≤ d` (`0 < R`,
`0 < s`, `s/P < R ≤ C`). -/
theorem le_hDevAtENN_shaped_kinkTime (P s C R T : ℝ≥0)
    (hR : 0 < R) (hRC : R ≤ C) (hs : 0 < s) (hsPR : s / P < R) :
    ((T + shapedShift P s C R : ℝ≥0) : ℝ≥0∞)
      ≤ hDevAtENN (tokenBucketNN (s / P) s ⊓ rateNN C)
          (rateLatencyNN R T) (kinkTime P s C) := by
  have hsPC : s / P < C := lt_of_lt_of_le hsPR hRC
  set ρ : ℝ≥0 := s / P with hρ
  set δ : ℝ≥0 := shapedShift P s C R with hδ
  set ts : ℝ≥0 := kinkTime P s C with hts
  have hCρpos : 0 < C - ρ := tsub_pos_of_lt hsPC
  have hCρ : (0:ℝ) < (C:ℝ) - ρ := by
    rw [← NNReal.coe_sub (le_of_lt hsPC)]; exact_mod_cast hCρpos
  have htne : ts ≠ 0 := by
    rw [hts, kinkTime, ← hρ]; exact div_ne_zero hs.ne' hCρpos.ne'
  -- the value `f(t*) = C·t*` as a real, and the kink identity `C·t* = R·t* + R·δ`
  have hts_real : (ts:ℝ) = (s:ℝ) / ((C:ℝ) - ρ) := by
    rw [hts, kinkTime, ← hρ, NNReal.coe_div, NNReal.coe_sub (le_of_lt hsPC)]
  have hKdef : (R:ℝ) * δ = ((C:ℝ) - R) * (s:ℝ) / ((C:ℝ) - ρ) := by
    have h := rate_mul_shapedShift P s C R hR
    have hcoe : ((R * δ : ℝ≥0):ℝ) = (((C - R) / (C - ρ) * s : ℝ≥0):ℝ) := by rw [h]
    rw [NNReal.coe_mul] at hcoe
    rw [hcoe, NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_sub hRC, NNReal.coe_sub (le_of_lt hsPC)]
    ring
  -- the identity `C·t* = R·(t* + δ)` over `ℝ`
  have hCstar : (C:ℝ) * ts = (R:ℝ) * ((ts:ℝ) + δ) := by
    rw [mul_add, hts_real, hKdef]; field_simp; ring
  refine le_hDevAtENN fun d hd => ?_
  -- admissibility: `f(t*) ≤ R·(t* + d − T)`; with `f(t*) = C·t*` and `C·t* > 0`
  rw [Pi.inf_apply, tokenBucketNN_kinkTime_eq P s C hs hsPC, min_self,
    rateNN_apply, rateLatencyNN_coe, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe, NNReal.coe_mul] at hd
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_sub_def] at hd ⊢
  -- `hd : C·t* ≤ R·max(t*+d−T, 0)`. Since `C·t* = R·(t*+δ) > 0`, the max is hit.
  have hRpos : (0:ℝ) < R := by exact_mod_cast hR
  have htspos : (0:ℝ) < ts := by
    rw [hts_real]; exact div_pos (by exact_mod_cast hs) hCρ
  have hCpos : (0:ℝ) < (C:ℝ) := lt_of_le_of_lt (NNReal.coe_nonneg ρ) (by exact_mod_cast hsPC)
  have hCtspos : (0:ℝ) < (C:ℝ) * ts := mul_pos hCpos htspos
  rcases le_or_gt ((ts:ℝ) + d - T) 0 with hmle | hmgt
  · rw [max_eq_right hmle] at hd
    nlinarith [hCstar, hCtspos, hd]
  · rw [max_eq_left (le_of_lt hmgt)] at hd
    -- `C·t* ≤ R·(t*+d−T)` and `C·t* = R·(t*+δ)` give `δ ≤ d−T`, i.e. `T+δ ≤ d`
    have : (R:ℝ) * ((ts:ℝ) + δ) ≤ (R:ℝ) * ((ts:ℝ) + d - T) := by
      rw [← hCstar]; exact hd
    nlinarith [this, hRpos]

/-- **Shaping closed-form delay** (`C ≥ R` stable case):
`hDev(γ_{s/P,s} ⊓ λ_C, β_{R,T}) = T + [(C − R)/(C − s/P)] · (s/R)`, under
stability `s/P < R ≤ C` with `0 < R`, `0 < s`. The upper bound is the kink
admissible shift; the matching lower bound is the kink-witness deviation. -/
theorem hDevENN_shaped_rateLatencyNN (P s C R T : ℝ≥0)
    (hR : 0 < R) (hRC : R ≤ C) (hs : 0 < s) (hsPR : s / P < R) :
    hDevENN (tokenBucketNN (s / P) s ⊓ rateNN C) (rateLatencyNN R T)
      = ((T + shapedShift P s C R : ℝ≥0) : ℝ≥0∞) := by
  refine le_antisymm (hDevENN_shaped_rateLatencyNN_le P s C R T hR hRC hsPR) ?_
  refine le_trans (le_hDevAtENN_shaped_kinkTime P s C R T hR hRC hs hsPR) ?_
  exact hDevAt_le_hDev _ _ (kinkTime P s C)

/-- **Shaping with a slow shaper caps the delay at the latency**: when
the shaper rate `C ≤ R`, the shaped flow `γ_{s/P,s} ⊓ λ_C` against
`β_{R,T}` has deviation exactly `T` — the rate cap kills the burst, so
the server adds only its latency (the `C < R` regime of the closed
form, where the shift `[(C−R)/(C−s/P)]⁺·(s/R)` vanishes). -/
theorem hDevENN_shaped_rateLatencyNN_of_le (P s C R T : ℝ≥0)
    (hC : 0 < C) (hCR : C ≤ R) (hs : 0 < s) :
    hDevENN (tokenBucketNN (s / P) s ⊓ rateNN C) (rateLatencyNN R T) = T := by
  apply le_antisymm
  · refine hDev_le fun t => ?_
    refine hDevAt_le (d := T) ?_
    refine inf_le_right.trans ?_
    rw [rateNN_apply, rateLatencyNN_coe, add_tsub_cancel_right,
      ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    gcongr
  · refine le_hDevENN_rateLatencyNN _ R T ⟨1, one_pos, fun t ht _ => ?_⟩
    rw [Pi.inf_apply, lt_inf_iff]
    refine ⟨?_, ?_⟩
    · rw [tokenBucketNN_coe_of_ne (s / P) s ht.ne']
      exact_mod_cast lt_of_lt_of_le hs le_add_self
    · rw [rateNN_apply, ← ENNReal.coe_mul]
      exact_mod_cast mul_pos hC ht

/-! ## Book restatement (shaping closed-form delay)
The shaped periodic flow's deviation
`hDev(γ_{s/P,s} ⊓ λ_C, β_{R,T}) = T + [(C − R)/(C − s/P)]·(s/R)`
under stability `s/P < R ≤ C`, and the *shaping reduces delay*
comparison `hDev(γ ⊓ λ_C, β) ≤ T + s/R` against the unshaped token
bucket. -/
example (P s C R T : ℝ≥0)
    (hR : 0 < R) (hRC : R ≤ C) (hs : 0 < s) (hsPR : s / P < R) :
    hDevENN (tokenBucketNN (s / P) s ⊓ rateNN C) (rateLatencyNN R T)
      = ((T + (C - R) / (C - s / P) * (s / R) : ℝ≥0) : ℝ≥0∞) :=
  hDevENN_shaped_rateLatencyNN P s C R T hR hRC hs hsPR
example (P s C R T : ℝ≥0) (hR : 0 < R) (hs : 0 < s) (hsPR : s / P ≤ R) :
    hDevENN (tokenBucketNN (s / P) s ⊓ rateNN C) (rateLatencyNN R T)
      ≤ ((T + s / R : ℝ≥0) : ℝ≥0∞) :=
  hDevENN_shaped_le_tokenBucketNN P s C R T hR hs hsPR
example (P s C R T : ℝ≥0) (hC : 0 < C) (hCR : C ≤ R) (hs : 0 < s) :
    hDevENN (tokenBucketNN (s / P) s ⊓ rateNN C) (rateLatencyNN R T) = T :=
  hDevENN_shaped_rateLatencyNN_of_le P s C R T hC hCR hs

end DeepWiki
