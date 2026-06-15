import DeepWiki.NetworkCalculus.LegendreFenchel
import DeepWiki.NetworkCalculus.RealCurves

/-! # Legendre–Fenchel transforms of the catalog curves
Closed forms of `𝓛` on the basic curves (Proposition 3.14): the burst-delay
`δ_d` transforms to the rate curve `λ_d`, and the rate curve `λ_R` transforms
back to the burst-delay `δ_R`. Each is a supremum of affine slices computed by
`le_antisymm` — the witness slice is at `u = d` (resp. `u = 0`). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

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
