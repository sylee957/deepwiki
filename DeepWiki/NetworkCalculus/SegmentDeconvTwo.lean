import DeepWiki.NetworkCalculus.SegmentDeconv
import Mathlib.Data.EReal.Operations

/-! # (min,plus) deconvolution of rate-latency curves (toward Lemma 4.6, §4.3)
Extends the affine base case (`SegmentDeconv`) to **rate-latency** curves
`β_{R,T}(u) = R·(u − T)₊` (with `ℝ≥0` truncated subtraction, so the curve is `0` before
the latency `T` and affine with slope `R` after). For the rate-ordering case `R₁ ≤ R₂` the
`(min,plus)` deconvolution `β_{R₁,T₁} ⊘ β_{R₂,T₂}` has the closed form
`t ↦ R₁·(t + T₂ − T₁)₊`: the supremum over the shift `s` is attained at `s = T₂`, where the
divisor vanishes and the dividend reads `R₁·(t + T₂ − T₁)₊`. This is the rate-latency content
of Lemma 4.6 (the affine pieces of a two-segment curve, deconvolved). -/

namespace DeepWiki

open scoped NNReal

/-- The `EReal`-valued rate-latency curve `u ↦ R·(u − T)₊` (the `ℝ≥0` truncated subtraction
`(u − T)` embedded through `ℝ`): `0` for `u ≤ T`, affine with slope `R` for `u ≥ T`. -/
noncomputable def rlE (R T : ℝ≥0) : ℝ≥0 → EReal :=
  fun u => (((R * (u - T) : ℝ≥0) : ℝ) : EReal)

/-- `rlE R T u = ↑(↑(R·(u − T)₊))`: the defining evaluation. -/
theorem rlE_apply (R T u : ℝ≥0) :
    rlE R T u = (((R * (u - T) : ℝ≥0) : ℝ) : EReal) := rfl

/-- `rlE R T 0 = ↑(↑(R·(0 − T)₊)) = 0` (the curve starts at the origin: `(0 − T)₊ = 0`). -/
@[simp] theorem rlE_zero (R T : ℝ≥0) : rlE R T 0 = (0 : EReal) := by
  simp [rlE]

/-- On the active region `u ≥ T`, the rate-latency curve is affine: `rlE R T u = ↑(↑(R·(u−T)))`
with `R·(u−T)` the *honest* (non-truncated, here non-negative) product. -/
theorem rlE_of_le {R T u : ℝ≥0} (h : T ≤ u) :
    rlE R T u = (((R * ((u : ℝ) - (T : ℝ)) : ℝ)) : EReal) := by
  rw [rlE_apply]
  norm_cast

/-- Below the latency (`u ≤ T`) the rate-latency curve vanishes: `rlE R T u = 0`. -/
theorem rlE_of_ge {R T u : ℝ≥0} (h : u ≤ T) : rlE R T u = (0 : EReal) := by
  rw [rlE_apply]
  have : u - T = 0 := tsub_eq_zero_of_le h
  rw [this]
  simp

/-- `rlE R T u` read as the `EReal` coe of the *real* product `R·max(↑u − ↑T, 0)`: the
`ℝ≥0` truncated subtraction `(u − T)` unfolds to the real `max` via `NNReal.coe_sub_def`. -/
theorem rlE_coe_max (R T u : ℝ≥0) :
    rlE R T u = (((R : ℝ) * max ((u : ℝ) - (T : ℝ)) 0 : ℝ) : EReal) := by
  rw [rlE_apply]
  push_cast [NNReal.coe_sub_def]
  norm_num

/-- Real-valued backbone of the rate-latency term bound: for `R₁ ≤ R₂` and arbitrary reals,
`R₁·max(a, 0) − R₂·max(b, 0) ≤ R₁·max(a − b, 0)` whenever the dividend/divisor arguments shift
by the same amount, here taken with `a − b` constant (`a = t+s−T₁`, `b = s−T₂`, so
`a − b = t + T₂ − T₁`). The supremum over the shift is realised when the divisor argument hits
its kink `b = 0`. -/
theorem rl_real_term_le {R₁ R₂ a b c : ℝ} (hR : R₁ ≤ R₂) (h0 : 0 ≤ R₁)
    (hc : c = a - b) :
    R₁ * max a 0 - R₂ * max b 0 ≤ R₁ * max c 0 := by
  subst hc
  rcases le_or_gt b 0 with hb | hb
  · -- divisor inactive: `max b 0 = 0`, and `a - b ≥ a`, so `max (a-b) 0 ≥ max a 0`
    rw [max_eq_right hb]
    have : max a 0 ≤ max (a - b) 0 := by
      apply max_le_max _ le_rfl
      · linarith
    nlinarith [this, h0]
  · -- divisor active: `max b 0 = b > 0`
    rw [max_eq_left hb.le]
    rcases le_or_gt a 0 with ha | ha
    · -- dividend inactive: LHS `= -R₂·b < 0 ≤ RHS`
      rw [max_eq_right ha]
      have : (0 : ℝ) ≤ R₁ * max (a - b) 0 := by positivity
      nlinarith [mul_nonneg (le_trans h0 hR) hb.le]
    · -- both active: `R₁·a − R₂·b = R₁·(a−b) + (R₁−R₂)·b ≤ R₁·(a−b) ≤ R₁·max(a−b,0)`
      rw [max_eq_left ha.le]
      have hle : R₁ * (a - b) ≤ R₁ * max (a - b) 0 := by
        apply mul_le_mul_of_nonneg_left (le_max_left _ _) h0
      nlinarith [mul_nonneg (sub_nonneg.mpr hR) hb.le, hle]

/-- The closed-form value of the rate-latency deconvolution (slow-divisor case), as the `EReal`
coe of the real `R₁·max(↑t + ↑T₂ − ↑T₁, 0)`. It equals `↑(↑(R₁·(t + T₂ − T₁)₊))` (the `ℝ≥0`
truncated value), realised at the shift `s = T₂`. -/
theorem rlDeconvValue_coe (R₁ T₁ T₂ t : ℝ≥0) :
    (((R₁ : ℝ) * max ((t : ℝ) + (T₂ : ℝ) - (T₁ : ℝ)) 0 : ℝ) : EReal)
      = (((R₁ * (t + T₂ - T₁) : ℝ≥0) : ℝ) : EReal) := by
  norm_cast

/-- Each deconvolution term of two rate-latency curves is bounded by the closed-form value when
the divisor rate dominates: for `R₁ ≤ R₂` and `s : ℝ≥0`,
`rlE R₁ T₁ (t + s) − rlE R₂ T₂ s ≤ ↑(↑(R₁·(t + T₂ − T₁)₊))`. -/
theorem rl_decon_term_le (R₁ T₁ R₂ T₂ t : ℝ≥0) (hR : R₁ ≤ R₂) (s : ℝ≥0) :
    rlE R₁ T₁ (t + s) - rlE R₂ T₂ s
      ≤ (((R₁ * (t + T₂ - T₁) : ℝ≥0) : ℝ) : EReal) := by
  rw [← rlDeconvValue_coe, rlE_coe_max, rlE_coe_max, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  refine rl_real_term_le (by exact_mod_cast hR) R₁.coe_nonneg ?_
  push_cast
  ring

/-- **Deconvolution of two rate-latency curves, slow-divisor case (Lemma 4.6).** When the divisor
rate dominates (`R₁ ≤ R₂`), the `(min,plus)` deconvolution of `β_{R₁,T₁}(u) = R₁·(u − T₁)₊` by
`β_{R₂,T₂}(u) = R₂·(u − T₂)₊` is the finite value `R₁·(t + T₂ − T₁)₊` (the supremum over the shift
`s` is attained at `s = T₂`, where the divisor vanishes). -/
theorem minDeconv_rl_le (R₁ T₁ R₂ T₂ t : ℝ≥0) (hR : R₁ ≤ R₂) :
    minDeconv (rlE R₁ T₁) (rlE R₂ T₂) t
      = (((R₁ * (t + T₂ - T₁) : ℝ≥0) : ℝ) : EReal) := by
  apply le_antisymm
  · -- upper bound: every term is `≤` the closed-form value
    exact minDeconv_le (fun s => rl_decon_term_le R₁ T₁ R₂ T₂ t hR s)
  · -- lower bound: the `s = T₂` term realises the value (divisor vanishes there)
    refine le_trans (le_of_eq ?_) (sub_le_minDeconv (rlE R₁ T₁) (rlE R₂ T₂) t T₂)
    rw [rlE_of_ge (le_refl T₂), sub_zero, rlE_coe_max, ← rlDeconvValue_coe]
    norm_num

/-! ## Distribution over `⊓` in the divisor (deconvolution by a min of curves) -/

/-- `EReal` subtraction turns a meet in the subtrahend into a join: `x − (a ⊓ b) = (x−a) ⊔ (x−b)`.
(Antitone in the second slot; `⊓` on the `EReal` linear order is `min`.) -/
theorem ereal_sub_inf (x a b : EReal) : x - (a ⊓ b) = (x - a) ⊔ (x - b) := by
  apply le_antisymm
  · rcases min_choice a b with h | h
    · rw [show a ⊓ b = min a b from rfl, h]; exact le_sup_left
    · rw [show a ⊓ b = min a b from rfl, h]; exact le_sup_right
  · refine sup_le ?_ ?_
    · exact EReal.sub_le_sub le_rfl inf_le_left
    · exact EReal.sub_le_sub le_rfl inf_le_right

/-- **Deconvolution distributes over `⊓` in the divisor:**
`minDeconv g (h₁ ⊓ h₂) = minDeconv g h₁ ⊔ minDeconv g h₂` (pointwise `⊓`/`⊔`). Each term splits as
`g (t+s) − (h₁ s ⊓ h₂ s) = (g (t+s) − h₁ s) ⊔ (g (t+s) − h₂ s)` and `⨆` distributes over `⊔`. -/
theorem minDeconv_inf_right {D : Type*} [Add D] (g h₁ h₂ : D → EReal) (t : D) :
    minDeconv g (h₁ ⊓ h₂) t = minDeconv g h₁ t ⊔ minDeconv g h₂ t := by
  unfold minDeconv
  simp only [Pi.inf_apply]
  rw [← iSup_sup_eq]
  exact iSup_congr (fun s => ereal_sub_inf (g (t + s)) (h₁ s) (h₂ s))

/-! ## Restatements (faithfulness checks against the book's wording) -/

/-- Slow-divisor rate-latency case, written out with explicit `EReal`-coerced rate-latency
functions: deconvolving `u ↦ R₁·(u − T₁)₊` by `u ↦ R₂·(u − T₂)₊` (`R₁ ≤ R₂`) gives
`R₁·(t + T₂ − T₁)₊`. -/
example (R₁ T₁ R₂ T₂ t : ℝ≥0) (hR : R₁ ≤ R₂) :
    minDeconv (fun u => (((R₁ * (u - T₁) : ℝ≥0) : ℝ) : EReal))
              (fun u => (((R₂ * (u - T₂) : ℝ≥0) : ℝ) : EReal)) t
      = (((R₁ * (t + T₂ - T₁) : ℝ≥0) : ℝ) : EReal) :=
  minDeconv_rl_le R₁ T₁ R₂ T₂ t hR

/-- Pure-rate specialization (`T₁ = T₂ = 0`, `R₁ ≤ R₂`): the deconvolution is the finite value
`R₁·t` — the latency-free shape recurring in Lemma 4.6's segment pieces. -/
example (R₁ R₂ t : ℝ≥0) (hR : R₁ ≤ R₂) :
    minDeconv (rlE R₁ 0) (rlE R₂ 0) t = (((R₁ * t : ℝ≥0) : ℝ) : EReal) := by
  rw [minDeconv_rl_le R₁ 0 R₂ 0 t hR]; simp

/-- Equal-rate, latency-only case (`R₁ = R₂ = R`): deconvolving `β_{R,T₁}` by `β_{R,T₂}` gives
`R·(t + T₂ − T₁)₊` — the deconvolution shifts the latency by `T₂ − T₁`. -/
example (R T₁ T₂ t : ℝ≥0) :
    minDeconv (rlE R T₁) (rlE R T₂) t = (((R * (t + T₂ - T₁) : ℝ≥0) : ℝ) : EReal) :=
  minDeconv_rl_le R T₁ R T₂ t le_rfl

end DeepWiki
