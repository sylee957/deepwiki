import DeepWiki.NetworkCalculus.LegendreFenchel
import DeepWiki.NetworkCalculus.RealCurves

/-! # Legendre–Fenchel transforms of the catalog curves
Closed forms of `𝓛` on the basic curves (Proposition 3.14): the burst-delay
`δ_d` transforms to the rate curve `λ_d`, and the rate curve `λ_R` transforms
back to the burst-delay `δ_R`. Each is a supremum of affine slices computed by
`le_antisymm` — the witness slice is at `u = d` (resp. `u = 0`). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Filter

/-- **𝓛(λ_R) = δ_R** (Proposition 3.14): the rate curve's Legendre–Fenchel
transform is the burst-delay. For `t ≤ R` every slice `↑((t−R)·u)` is `≤ 0`
(supremum `0` at `u = 0`); for `t > R` the slices `↑((t−R)·u)` are unbounded
(supremum `⊤`). -/
theorem legendre_rateEReal (R : ℝ≥0) : legendre (rateEReal R) = delayEReal R := by
  funext t
  rw [legendre_apply]
  rcases le_or_gt t R with ht | ht
  · rw [show delayEReal R t = 0 from delay_eq_zero R ht]
    apply le_antisymm
    · refine iSup_le fun u => ?_
      rw [rateEReal_apply, ← EReal.coe_sub, EReal.coe_nonpos]
      have h : ((t * u : ℝ≥0) : ℝ) ≤ ((R * u : ℝ≥0) : ℝ) := by
        exact_mod_cast mul_le_mul' ht (le_refl u)
      linarith
    · refine le_trans (le_of_eq ?_) (le_iSup _ (0 : ℝ≥0))
      rw [rateEReal_apply]; simp
  · rw [show delayEReal R t = ⊤ from delay_eq_top R ht, iSup_eq_top]
    intro b hb
    rcases eq_or_ne b ⊥ with hbot | hbot
    · refine ⟨0, ?_⟩
      rw [hbot, rateEReal_apply]; simp
    · obtain ⟨M, rfl⟩ : ∃ M : ℝ, b = (M : EReal) :=
        ⟨b.toReal, (EReal.coe_toReal hb.ne hbot).symm⟩
      have hδ : (0 : ℝ) < (t : ℝ) - (R : ℝ) := by
        have : (R : ℝ) < (t : ℝ) := by exact_mod_cast ht
        linarith
      refine ⟨Real.toNNReal (M / ((t : ℝ) - (R : ℝ))) + 1, ?_⟩
      rw [rateEReal_apply, ← EReal.coe_sub, EReal.coe_lt_coe_iff]
      have hM : M ≤ ((t : ℝ) - (R : ℝ)) * (Real.toNNReal (M / ((t : ℝ) - (R : ℝ))) : ℝ) := by
        rw [mul_comm]
        exact (div_le_iff₀ hδ).mp (Real.le_coe_toNNReal _)
      push_cast
      nlinarith [hM, hδ]

/-- **𝓛(δ_d) = λ_d** (Proposition 3.14): the burst-delay's Legendre–Fenchel
transform is the rate curve. The slices `↑(t·u) − δ_d(u)` are `↑(t·u)` for
`u ≤ d` (supremum `↑(t·d)` at `u = d`) and `⊥` for `u > d`. -/
theorem legendre_delayEReal (d : ℝ≥0) : legendre (delayEReal d) = rateEReal d := by
  funext t
  rw [legendre_apply, rateEReal_apply]
  apply le_antisymm
  · refine iSup_le fun u => ?_
    rcases le_or_gt u d with hu | hu
    · rw [show delayEReal d u = 0 from delay_eq_zero d hu, sub_zero]
      exact_mod_cast (mul_le_mul' (le_refl t) hu).trans (le_of_eq (mul_comm t d))
    · rw [show delayEReal d u = ⊤ from delay_eq_top d hu, EReal.sub_top]
      exact bot_le
  · refine le_trans (le_of_eq ?_)
      (le_iSup (fun u => (((t * u : ℝ≥0) : ℝ) : EReal) - delayEReal d u) d)
    rw [show delayEReal d d = 0 from delay_eq_zero d (le_refl d), sub_zero]
    exact_mod_cast (mul_comm d t)

/-- **𝓛(β_{R,T}) = λ_T ∨ δ_R** (Proposition 3.14): the rate-latency curve's
Legendre–Fenchel transform is the max of the rate curve `λ_T` and the
burst-delay `δ_R`. For `s ≤ R` the supremum is `↑(s·T)` (witness `u = T`); for
`s > R` it is unbounded (`⊤`). -/
theorem legendre_rateLatencyEReal (R T : ℝ≥0) :
    legendre (rateLatencyEReal R T) = rateEReal T ⊔ delayEReal R := by
  funext s
  rw [legendre_apply, Pi.sup_apply, rateEReal_apply]
  rcases le_or_gt s R with hs | hs
  · -- `s ≤ R`: `δ_R s = 0`, so the join is `↑(T·s)`, the supremum at `u = T`
    rw [show delayEReal R s = 0 from delay_eq_zero R hs,
      sup_eq_left.mpr (show (0 : EReal) ≤ (((T * s : ℝ≥0) : ℝ) : EReal) by
        exact_mod_cast (T * s).coe_nonneg)]
    apply le_antisymm
    · refine iSup_le fun u => ?_
      rw [rateLatencyEReal_apply, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      rcases le_or_gt u T with hu | hu
      · rw [tsub_eq_zero_of_le hu]
        push_cast
        nlinarith [mul_nonneg s.coe_nonneg (sub_nonneg.mpr (show (u : ℝ) ≤ T by exact_mod_cast hu))]
      · push_cast [NNReal.coe_sub hu.le]
        nlinarith [mul_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ R by exact_mod_cast hs))
          (sub_nonneg.mpr (show (T : ℝ) ≤ u by exact_mod_cast hu.le))]
    · refine le_trans (le_of_eq ?_) (le_iSup _ T)
      rw [rateLatencyEReal_apply, tsub_self, mul_zero, NNReal.coe_zero, EReal.coe_zero, sub_zero]
      norm_cast; ring
  · -- `s > R`: `δ_R s = ⊤`, so the join is `⊤`; the supremum is unbounded
    rw [show delayEReal R s = ⊤ from delay_eq_top R hs, sup_top_eq, iSup_eq_top]
    intro b hb
    rcases eq_or_ne b ⊥ with hbot | hbot
    · refine ⟨T, ?_⟩
      rw [hbot, rateLatencyEReal_apply, tsub_self, mul_zero, NNReal.coe_zero,
        EReal.coe_zero, sub_zero]
      exact EReal.bot_lt_coe _
    · obtain ⟨M, rfl⟩ : ∃ M : ℝ, b = (M : EReal) :=
        ⟨b.toReal, (EReal.coe_toReal hb.ne hbot).symm⟩
      have hδ : (0 : ℝ) < (s : ℝ) - (R : ℝ) := by
        have : (R : ℝ) < (s : ℝ) := by exact_mod_cast hs
        linarith
      refine ⟨Real.toNNReal ((M - (s : ℝ) * (T : ℝ)) / ((s : ℝ) - (R : ℝ))) + 1 + T, ?_⟩
      rw [rateLatencyEReal_apply, add_tsub_cancel_right, ← EReal.coe_sub, EReal.coe_lt_coe_iff]
      have hn : (M - (s : ℝ) * (T : ℝ)) / ((s : ℝ) - (R : ℝ))
          ≤ (Real.toNNReal ((M - (s : ℝ) * (T : ℝ)) / ((s : ℝ) - (R : ℝ))) : ℝ) :=
        Real.le_coe_toNNReal _
      have hbig : M - (s : ℝ) * (T : ℝ)
          ≤ (Real.toNNReal ((M - (s : ℝ) * (T : ℝ)) / ((s : ℝ) - (R : ℝ))) : ℝ)
            * ((s : ℝ) - (R : ℝ)) :=
        (div_le_iff₀ hδ).mp hn
      push_cast
      nlinarith [hbig, hδ]

/-- **The Fenchel–Moreau involution on the burst-delay**: `𝓛(𝓛(δ_d)) = δ_d` —
the biconjugate recovers `δ_d`, by composing the duality `𝓛(δ_d) = λ_d` and
`𝓛(λ_d) = δ_d`. (The general involution `𝓛(𝓛 f) = f` for convex non-decreasing
`f` is not formalized; here it is verified on the catalog curve.) -/
theorem legendre_legendre_delayEReal (d : ℝ≥0) :
    legendre (legendre (delayEReal d)) = delayEReal d := by
  rw [legendre_delayEReal, legendre_rateEReal]

/-- **The Fenchel–Moreau involution on the rate curve**: `𝓛(𝓛(λ_R)) = λ_R` —
the biconjugate recovers `λ_R`, by composing `𝓛(λ_R) = δ_R` and `𝓛(δ_R) = λ_R`. -/
theorem legendre_legendre_rateEReal (R : ℝ≥0) :
    legendre (legendre (rateEReal R)) = rateEReal R := by
  rw [legendre_rateEReal, legendre_delayEReal]

end DeepWiki
