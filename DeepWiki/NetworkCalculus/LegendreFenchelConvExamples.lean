import DeepWiki.NetworkCalculus.LegendreFenchelConv
import DeepWiki.NetworkCalculus.LegendreFenchelExamples

/-! # The rate-latency curve as an inf-convolution
The rate-latency curve is the inf-convolution of the rate and burst-delay
curves, `β_{R,T} = λ_R ⊗ δ_T`. Feeding this through the convolution-to-sum
identity `𝓛(f ⊗ g) = 𝓛(f) + 𝓛(g)` recomputes `𝓛(β_{R,T})` as
`𝓛(λ_R) + 𝓛(δ_T) = δ_R + λ_T`, which the direct computation
(`legendre_rateLatencyEReal`) gives as `λ_T ⊔ δ_R` — so the two agree, forcing
the pointwise identity `δ_R + λ_T = λ_T ⊔ δ_R`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **The rate-latency curve is `λ_R ⊗ δ_T`**: `β_{R,T} = legendreConv (λ_R) (δ_T)`.
Each `u+v=t` split costs `R·u` from the rate part plus `0` (when `v ≤ T`) or
`⊤` (when `v > T`) from the delay; the infimum is `↑(R·(t−T))`, attained at the
split `(t−T, t−(t−T))`. -/
theorem rateLatencyEReal_eq_legendreConv (R T : ℝ≥0) :
    rateLatencyEReal R T = legendreConv (rateEReal R) (delayEReal T) := by
  funext u
  rw [rateLatencyEReal_apply, legendreConv_apply]
  apply le_antisymm
  · -- `↑(R(u−T))` is a lower bound for every split `a + b = u`
    refine le_iInf fun p => ?_
    obtain ⟨⟨a, b⟩, (hab : a + b = u)⟩ := p
    show (((R * (u - T) : ℝ≥0) : ℝ) : EReal) ≤ rateEReal R a + delayEReal T b
    rcases le_or_gt b T with hb | hb
    · rw [show delayEReal T b = 0 from delay_eq_zero T hb, add_zero, rateEReal_apply,
        EReal.coe_le_coe_iff]
      have hle : u - T ≤ a := by
        rw [← hab]; exact tsub_le_iff_right.mpr (add_le_add le_rfl hb)
      exact_mod_cast mul_le_mul' (le_refl R) hle
    · rw [show delayEReal T b = ⊤ from delay_eq_top T hb, rateEReal_apply,
        EReal.coe_add_top]
      exact le_top
  · -- the split `(u−T, u−(u−T))` attains `↑(R(u−T))`
    refine iInf_le_of_le ⟨(u - T, u - (u - T)), ?_⟩ ?_
    · show (u - T) + (u - (u - T)) = u
      exact add_tsub_cancel_of_le tsub_le_self
    · show rateEReal R (u - T) + delayEReal T (u - (u - T)) ≤ _
      have hb : u - (u - T) ≤ T := tsub_le_iff_right.mpr le_add_tsub
      rw [show delayEReal T (u - (u - T)) = 0 from delay_eq_zero T hb, add_zero,
        rateEReal_apply]

/-- **𝓛(β_{R,T}) = 𝓛(λ_R) + 𝓛(δ_T)**: the rate-latency transform computed via the
convolution-to-sum identity `legendre_legendreConv`, since `β_{R,T} = λ_R ⊗ δ_T`
and both factors are proper (never `⊥`). -/
theorem legendre_rateLatencyEReal_eq_add (R T : ℝ≥0) :
    legendre (rateLatencyEReal R T)
      = legendre (rateEReal R) + legendre (delayEReal T) := by
  have hf : ∀ u, rateEReal R u ≠ ⊥ := fun u => by
    rw [rateEReal_apply]; exact EReal.coe_ne_bot _
  have hg : ∀ v, delayEReal T v ≠ ⊥ := fun v => by
    rcases le_or_gt v T with hv | hv
    · rw [show delayEReal T v = 0 from delay_eq_zero T hv]; exact EReal.zero_ne_bot
    · rw [show delayEReal T v = ⊤ from delay_eq_top T hv]; exact top_ne_bot
  rw [rateLatencyEReal_eq_legendreConv, legendre_legendreConv hf hg]

/-- **Consistency of the two rate-latency transforms**: `δ_R + λ_T = λ_T ⊔ δ_R`.
The convolution route gives `𝓛(β_{R,T}) = 𝓛(λ_R) + 𝓛(δ_T) = δ_R + λ_T`
(`legendre_rateLatencyEReal_eq_add` with `legendre_rateEReal`, `legendre_delayEReal`),
while the direct computation `legendre_rateLatencyEReal` gives `λ_T ⊔ δ_R`; the two
must coincide. -/
theorem delayEReal_add_rateEReal_eq_sup (R T : ℝ≥0) :
    delayEReal R + rateEReal T = rateEReal T ⊔ delayEReal R := by
  have h := legendre_rateLatencyEReal_eq_add R T
  rw [legendre_rateEReal, legendre_delayEReal, legendre_rateLatencyEReal] at h
  exact h.symm

end DeepWiki
