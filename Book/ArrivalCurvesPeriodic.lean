import Book.Deconvolution
import Book.RealCurvesAdditivity
import Book.RealCurvesDeviations

/-! # Arrival curves of periodic flows
A periodic flow (a packet of size `s` every `P`) has cumulative process
`ν_{P,s}`: its tightest maximal arrival curve is `ν ⊘ ν = ν_{P,s}` itself
and its tightest minimal arrival curve is `ν ⊘̄ ν`, the floor staircase
`t ↦ s⌊t/P⌋`. Both are approximated by quasi-linear curves: the
token-bucket `γ_{s/P,s(P+J)/P}` from above (`⌈x⌉ ≤ x + 1`) and the
rate-latency `β_{s/P,P+J}` from below (`x − 1 ≤ ⌊x⌋`), jitter `J`
included. A sporadic flow (pseudo-period `P`) keeps only the maximal
side. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **The jittered staircase is its own tightest maximal arrival curve**:
`ν_{P,s,J} ⊘ ν_{P,s,J} = ν_{P,s,J}` for `J ≥ 0` — sub-additivity and the
null origin collapse the self-deconvolution. -/
theorem minDeconv_staircase_self (P s : ℝ≥0) (hP : (0:ℝ) < P)
    {J : ℝ} (hJ : 0 ≤ J) :
    minDeconv (staircase P s J) (staircase P s J) = staircase P s J :=
  minDeconv_self_eq_of_isSubadditive (staircase_subadditive P s hP J hJ)
    (staircase_zero_eq P s J)

/-- **Token-bucket approximation of the jittered staircase**: since
`⌈x⌉ ≤ x + 1`, `ν_{P,s,J} ≤ γ_{s/P, s(P+J)/P}`. -/
theorem staircase_le_tokenBucketNN (P s : ℝ≥0) (hP : (0:ℝ) < P)
    (J : ℝ≥0) (t : ℝ≥0) :
    staircase P s J t ≤ tokenBucketNN (s / P) (s * (P + J) / P) t := by
  have hP' : (P:ℝ) ≠ 0 := ne_of_gt hP
  rcases eq_zero_or_pos t with rfl | ht
  · rw [staircase_zero_eq, tokenBucketNN_zero_eq]
  have ht0 : ¬ t ≤ 0 := not_le.mpr ht
  rw [tokenBucketNN_apply, show delayNN 0 t = ⊤ from delay_eq_top 0 ht,
    inf_top_eq]
  simp only [staircase, delayNN, delay_apply, if_neg ht0, min_top_right]
  have hcast : ((s / P : ℝ≥0) : ℝ≥0∞) * (t : ℝ≥0∞)
        + ((s * (P + J) / P : ℝ≥0) : ℝ≥0∞)
      = ENNReal.ofReal
          ((s:ℝ) / P * t + (s:ℝ) * ((P:ℝ) + J) / P) := by
    rw [← ENNReal.coe_mul, ← ENNReal.coe_add, ← ENNReal.ofReal_coe_nnreal]
    congr 1
  rw [hcast]
  refine ENNReal.ofReal_le_ofReal ?_
  refine max_le ?_ (by positivity)
  have hceil : (⌈((t:ℝ) + J) / P⌉ : ℝ) ≤ ((t:ℝ) + J) / P + 1 :=
    (Int.ceil_lt_add_one _).le
  calc (s:ℝ) * ⌈((t:ℝ) + J) / P⌉
      ≤ (s:ℝ) * (((t:ℝ) + J) / P + 1) :=
        mul_le_mul_of_nonneg_left hceil s.coe_nonneg
    _ = (s:ℝ) / P * t + (s:ℝ) * ((P:ℝ) + J) / P := by
        field_simp
        ring

/-- **Rate-latency approximation of the jittered floor staircase**: since
`x − 1 ≤ ⌊x⌋`, `β_{s/P, P+J} ≤ ν'_{P,s,J}`. -/
theorem rateLatencyNN_le_staircaseFloor (P s : ℝ≥0) (hP : (0:ℝ) < P)
    (J : ℝ≥0) (t : ℝ≥0) :
    rateLatencyNN (s / P) (P + J) t ≤ staircaseFloor P s J t := by
  have hP' : (P:ℝ) ≠ 0 := ne_of_gt hP
  rcases le_or_gt t (P + J) with htd | htd
  · rw [rateLatencyNN, tsub_eq_zero_of_le htd]
    simp
  · rw [rateLatencyNN, staircaseFloor_apply,
      ← ENNReal.coe_mul, ← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast [NNReal.coe_sub htd.le]
    have hfloor : ((t:ℝ) - J) / P - 1 ≤ (⌊((t:ℝ) - J) / P⌋ : ℝ) :=
      (Int.sub_one_lt_floor _).le
    calc (s:ℝ) / P * ((t:ℝ) - ((P:ℝ) + J))
        = (s:ℝ) * (((t:ℝ) - J) / P - 1) := by
          field_simp
          ring
      _ ≤ (s:ℝ) * ⌊((t:ℝ) - J) / P⌋ :=
          mul_le_mul_of_nonneg_left hfloor s.coe_nonneg

/-- **The floor staircase is the periodic flow's tightest minimal arrival
curve**: `ν_{P,s} ⊘̄ ν_{P,s} = ν'_{P,s}` — the infimum of
`ν(t + u) − ν(u)` is attained at the gap from `t` to the next multiple
of `P`. -/
theorem maxDeconv_staircase_self (P s : ℝ≥0) (hP : (0:ℝ) < P) :
    maxDeconv (staircase P s 0) (staircase P s 0) = staircaseFloor P s 0 := by
  have hP' : (P:ℝ) ≠ 0 := ne_of_gt hP
  funext t
  set q : ℤ := ⌊(t:ℝ) / (P:ℝ)⌋ with hq
  have hq0 : 0 ≤ q := Int.floor_nonneg.mpr (by positivity)
  have hfloor : staircaseFloor P s 0 t = ENNReal.ofReal ((s:ℝ) * q) := by
    rw [staircaseFloor_apply, sub_zero, ← hq]
  apply le_antisymm
  · -- the witness split: `u` is the gap to the next multiple of `P`
    have htq : (t:ℝ) < ((q:ℝ) + 1) * P := by
      have h1 := Int.lt_floor_add_one ((t:ℝ) / P)
      calc (t:ℝ) = (t:ℝ) / P * P := by field_simp
        _ < ((q:ℝ) + 1) * P := by
          exact mul_lt_mul_of_pos_right (by exact_mod_cast h1) hP
    have hqt : (q:ℝ) * P ≤ t := by
      have h1 := Int.floor_le ((t:ℝ) / P)
      calc (q:ℝ) * P ≤ (t:ℝ) / P * P :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast h1) P.coe_nonneg
        _ = t := by field_simp
    set u : ℝ≥0 := Real.toNNReal (((q:ℝ) + 1) * P - t) with hu
    have huval : (u:ℝ) = ((q:ℝ) + 1) * P - t :=
      Real.coe_toNNReal _ (by linarith)
    have hu_pos : 0 < u := by
      rw [← NNReal.coe_lt_coe, NNReal.coe_zero, huval]
      linarith
    have hu_le : (u:ℝ) ≤ P := by
      rw [huval]
      linarith
    have htu : ((t + u : ℝ≥0) : ℝ) = ((q:ℝ) + 1) * P := by
      push_cast [huval]
      ring
    have hu0 : ¬ u ≤ 0 := not_le.mpr hu_pos
    have htu0 : ¬ (t + u) ≤ 0 := by
      rw [not_le]
      exact lt_of_lt_of_le hu_pos le_add_self
    have hceil_tu : ⌈((t + u : ℝ≥0) : ℝ) / (P:ℝ)⌉ = q + 1 := by
      rw [htu, mul_div_cancel_right₀ _ hP',
        show ((q:ℝ) + 1) = ((q + 1 : ℤ) : ℝ) from by push_cast; ring]
      exact Int.ceil_intCast (q + 1)
    have hceil_u : ⌈((u : ℝ≥0) : ℝ) / (P:ℝ)⌉ = 1 := by
      rw [Int.ceil_eq_iff]
      constructor
      · push_cast
        simpa using div_pos (NNReal.coe_pos.mpr hu_pos) hP
      · push_cast
        rw [div_le_one hP]
        exact hu_le
    have hval : staircase P s 0 (t + u) - staircase P s 0 u
        = staircaseFloor P s 0 t := by
      simp only [staircase, delayNN, delay_apply, if_neg htu0, if_neg hu0,
        min_top_right, add_zero, hceil_tu, hceil_u]
      rw [hfloor,
        max_eq_left (mul_nonneg s.coe_nonneg
          (by exact_mod_cast Int.le_add_one hq0)),
        max_eq_left (mul_nonneg s.coe_nonneg (by norm_num)),
        ← ENNReal.ofReal_sub _ (mul_nonneg s.coe_nonneg (by norm_num))]
      congr 1
      push_cast
      ring
    exact (maxDeconv_le_sub _ _ t u).trans hval.le
  · -- every split dominates the floor: `⌊x⌋ + ⌈y⌉ ≤ ⌈x + y⌉`
    refine le_maxDeconv fun u => ?_
    rcases eq_zero_or_pos u with rfl | hu
    · rw [add_zero, staircase_zero_eq, tsub_zero, hfloor]
      rcases eq_zero_or_pos t with rfl | ht
      · simp [hq.symm ▸ (by norm_num : ⌊(0:ℝ) / (P:ℝ)⌋ = 0)]
      · have ht0 : ¬ t ≤ 0 := not_le.mpr ht
        simp only [staircase, delayNN, delay_apply, if_neg ht0,
          min_top_right, add_zero]
        refine ENNReal.ofReal_le_ofReal (le_max_of_le_left ?_)
        refine mul_le_mul_of_nonneg_left ?_ s.coe_nonneg
        exact_mod_cast hq ▸ Int.floor_le_ceil ((t:ℝ) / P)
    · have hu0 : ¬ u ≤ 0 := not_le.mpr hu
      have htu0 : ¬ (t + u) ≤ 0 := by
        rw [not_le]
        exact lt_of_lt_of_le hu le_add_self
      rw [hfloor]
      simp only [staircase, delayNN, delay_apply, if_neg hu0, if_neg htu0,
        min_top_right, add_zero]
      have h1 : (0:ℝ) ≤ (s:ℝ) * ⌈((t + u : ℝ≥0) : ℝ) / (P:ℝ)⌉ :=
        mul_nonneg s.coe_nonneg
          (by exact_mod_cast Int.ceil_nonneg (by positivity))
      have h2 : (0:ℝ) ≤ (s:ℝ) * ⌈((u : ℝ≥0) : ℝ) / (P:ℝ)⌉ :=
        mul_nonneg s.coe_nonneg
          (by exact_mod_cast Int.ceil_nonneg (by positivity))
      rw [max_eq_left h1, max_eq_left h2, ← ENNReal.ofReal_sub _ h2]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [le_sub_iff_add_le]
      have hkey : ⌊(t:ℝ) / P⌋ + ⌈((u : ℝ≥0) : ℝ) / (P:ℝ)⌉
          ≤ ⌈((t + u : ℝ≥0) : ℝ) / (P:ℝ)⌉ := by
        calc ⌊(t:ℝ) / P⌋ + ⌈((u:ℝ≥0):ℝ) / (P:ℝ)⌉
            = ⌈((u:ℝ≥0):ℝ) / P + (⌊(t:ℝ) / P⌋ : ℤ)⌉ := by
              rw [Int.ceil_add_intCast]
              ring
          _ ≤ ⌈((t + u : ℝ≥0) : ℝ) / (P:ℝ)⌉ := by
              refine Int.ceil_mono ?_
              push_cast
              rw [add_div]
              have := Int.floor_le ((t:ℝ) / P)
              linarith
      calc (s:ℝ) * (q:ℝ) + (s:ℝ) * ⌈((u:ℝ≥0):ℝ) / (P:ℝ)⌉
          = (s:ℝ) * ((q:ℝ) + ⌈((u:ℝ≥0):ℝ) / (P:ℝ)⌉) := by ring
        _ ≤ (s:ℝ) * ⌈((t + u : ℝ≥0) : ℝ) / (P:ℝ)⌉ := by
            refine mul_le_mul_of_nonneg_left ?_ s.coe_nonneg
            exact_mod_cast hq ▸ hkey

/-! ## Book restatement (periodic and sporadic flows)
A packet of size `s` arrives every `P` units of time, so the cumulative
process is `A(t) = s⌈t/P⌉ = ν_{P,s}(t)`. As `A ⊘ A = A`, the tightest
maximal and minimal arrival curves for `A` are `α : t ↦ s⌈t/P⌉` and
`α' : t ↦ s⌊t/P⌋`. These are often approximated by quasi-linear curves:
as `x + 1 ≥ ⌈x⌉` the maximal curve is upper-bounded by `γ_{s/P,s}`, and
as `x − 1 ≤ ⌊x⌋`, `β_{s/P,P} ≤ α'` is a minimal arrival curve. With
jitter `J` the maximal curve is `ν_{P,s,J}`, approximated by
`γ_{s/P,s(P+J)/P}` and `β_{s/P,P+J}`. A *sporadic* flow with
pseudo-period `P` (minimal inter-arrival time `P`) admits only the
maximal arrival curve `ν_{P,s,0}`. -/
example (P s : ℝ≥0) (hP : (0:ℝ) < P) :
    minDeconv (staircase P s 0) (staircase P s 0) = staircase P s 0 :=
  minDeconv_staircase_self P s hP le_rfl

example (P s : ℝ≥0) (hP : (0:ℝ) < P) :
    maxDeconv (staircase P s 0) (staircase P s 0) = staircaseFloor P s 0 :=
  maxDeconv_staircase_self P s hP

example (P s : ℝ≥0) (hP : (0:ℝ) < P) (t : ℝ≥0) :
    staircase P s 0 t ≤ tokenBucketNN (s / P) s t := by
  have h := staircase_le_tokenBucketNN P s hP 0 t
  rwa [NNReal.coe_zero, add_zero, mul_div_assoc,
    div_self (by exact_mod_cast hP.ne' : P ≠ 0), mul_one] at h

example (P s : ℝ≥0) (hP : (0:ℝ) < P) (t : ℝ≥0) :
    rateLatencyNN (s / P) P t ≤ staircaseFloor P s 0 t := by
  have h := rateLatencyNN_le_staircaseFloor P s hP 0 t
  rwa [NNReal.coe_zero, add_zero] at h

/-! ## Book restatement (propagation and performance bounds)
A periodic flow with jitter crossing a server that offers the min-plus
service curve `β_{R,T}`, under stability `s/P < R`. With the linear
approximation `α₂ = γ_{s/P, s(P+J)/P}` the bounds are closed-form:
`hDev(α₂, β_{R,T}) = T + s(P+J)/(RP)` and
`vDev(α₂, β_{R,T}) = s(P+T+J)/P`. With the staircase `α₁ = ν_{P,s,J}`
itself, `vDev(α₁, β_{R,T})` dominates `α₁(T)` — the value the book
reports; the supremum can exceed it at a jump just past `T`
(`not_forall_vDev_staircase_rateLatencyNN_eq`). -/
example {P s R T J : ℝ≥0} (hP : 0 < P) (hs : 0 < s) (hst : s / P < R) :
    hDevENN (tokenBucketNN (s / P) (s * (P + J) / P)) (rateLatencyNN R T)
      = ((T + s * (P + J) / (R * P) : ℝ≥0) : ℝ≥0∞) := by
  rw [hDevENN_tokenBucketNN_rateLatencyNN _ _ _ _
      (lt_of_le_of_lt zero_le' hst)
      (div_pos (mul_pos hs (lt_of_lt_of_le hP le_self_add)) hP) hst.le,
    ENNReal.coe_inj, div_div, mul_comm P R]

example {P s R T J : ℝ≥0} (hst : s / P < R) (hT : 0 < T) :
    vDev (tokenBucketNN (s / P) (s * (P + J) / P)) (rateLatencyNN R T)
      = ((s * (P + T + J) / P : ℝ≥0) : ℝ≥0∞) := by
  rw [vDev_tokenBucketNN_rateLatencyNN _ _ _ _ hst.le hT, ENNReal.coe_inj,
    div_mul_eq_mul_div, ← add_div]
  congr 1
  ring

example (P s R T : ℝ≥0) (J : ℝ) :
    staircase P s J T ≤ vDev (staircase P s J) (rateLatencyNN R T) :=
  apply_le_vDev_rateLatencyNN (staircase P s J) R T

/-- **The shaped staircase arrival curve**: the closure of the minimum
`λ_C ⊓ ν_{P,s,0}` is the convolution `λ_C ∗ ν_{P,s,0}`
(`rateNN C ∗ staircase P s 0`) — both factors are their own closures, so the
star-of-meet identity collapses to the plain convolution. -/
theorem subadditiveClosureENN_min_rateNN_staircase (C P s : ℝ≥0) (hP : (0:ℝ) < P) :
    subadditiveClosureENN (fun t => min (rateNN C t) (staircase P s 0 t))
      = minConv (rateNN C) (staircase P s 0) := by
  rw [subadditiveClosureENN_min (rateNN C) (staircase P s 0),
    subadditiveClosureENN_eq_self (rateNN C) (rateNN_subadditive C) (rateNN_zero_eq C),
    staircase_closure P s hP 0 le_rfl]

/-! ## Book restatement (shaping and periodic flows)
A periodic flow crossing a constant-rate server `λ_C` (a shaper) under
stability `s/P < C`: with the token-bucket approximation `γ_{s/P,s}`,
the arrival curve at the next server is
`(γ_{s/P,s} ⊘ λ_C) ∧ λ_C = γ_{s/P,s} ∧ λ_C` — the TSpec shape, whose
rate cap is what reduces the downstream burst (the *shaping effect*).
(The identity needs no stability at all.) -/
example (P s C : ℝ≥0) :
    minDeconv (tokenBucketNN (s / P) s) (rateNN C) ⊓ rateNN C
      = tokenBucketNN (s / P) s ⊓ rateNN C :=
  minDeconv_tokenBucketNN_rateNN_inf (s / P) s C

/-! With the tighter periodic staircase `ν_{P,s,0}` in place of the
token-bucket, the arrival curve at the next server is `λ_C ∧ ν_{P,s,0}`;
the sub-additive closure sharpens it to `(λ_C ∧ ν_{P,s,0})⋆ = λ_C ∗ ν_{P,s,0}`. -/
example (P s C : ℝ≥0) (hP : (0:ℝ) < P) :
    subadditiveClosureENN (fun t => min (rateNN C t) (staircase P s 0 t))
      = minConv (rateNN C) (staircase P s 0) :=
  subadditiveClosureENN_min_rateNN_staircase C P s hP

end DeepWiki
