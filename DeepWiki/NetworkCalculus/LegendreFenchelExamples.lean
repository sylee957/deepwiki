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

end DeepWiki
