import DeepWiki.NetworkCalculus.SegmentDeconvTwo
import Mathlib.Data.EReal.Operations

/-! # (min,plus) deconvolution of composite rate-latency divisors (toward Lemma 4.6, §4.3)
Extends `SegmentDeconvTwo` (the two rate-latency curves) along two axes:
* the **fast-divisor `⊤` case** `minDeconv_rl_top` (mirror of `minDeconv_affine_top`): when the
  dividend rate strictly dominates (`R₂ < R₁`) the deconvolution diverges, because for large
  shifts `s` both curves are affine and the term has positive combined slope `R₁ − R₂`;
* **distribution of the deconvolution over a meet of divisors** — `minDeconv g (h₁ ⊓ h₂)` splits
  as a join (already `minDeconv_inf_right`), here packaged for the **min of two rate-latencies**
  (a concave/piecewise divisor) as a `⊔` of the two rate-latency closed forms, and generalized to
  a finite **list** of divisors (`minDeconv_inf_list_right`, the divisor-side analog of the
  convolution-distributes-over-min law). These are the composite-curve pieces of Lemma 4.6. -/

namespace DeepWiki

open scoped NNReal

/-! ## (a) Fast-divisor rate-latency case: the deconvolution is `⊤` -/

/-- Real-valued backbone of the unbounded rate-latency term: when the dividend rate strictly
dominates (`R₂ < R₁`) and both curves are active (`a = t+s−T₁ ≥ 0`, `b = s−T₂ ≥ 0` for `s` large),
the term `R₁·a − R₂·b` grows linearly in `s` with positive slope `R₁ − R₂`, exceeding any `M`. -/
theorem rl_real_term_unbounded {R₁ R₂ : ℝ} (hR : R₂ < R₁) (M : ℝ) :
    ∃ s : ℝ, 0 ≤ s ∧ M < R₁ * s - R₂ * s := by
  -- slope `R₁ - R₂ > 0`; pick `s ≥ (M+1)/(R₁-R₂)`, clamped to be nonnegative
  have hd : (0 : ℝ) < R₁ - R₂ := by linarith
  set c : ℝ := (M + 1) / (R₁ - R₂) with hc
  refine ⟨max c 0, le_max_right _ _, ?_⟩
  set s : ℝ := max c 0 with hsdef
  have hcs : c ≤ s := le_max_left _ _
  have key : (R₁ - R₂) * c = M + 1 := by rw [hc]; field_simp
  have hmul : (R₁ - R₂) * c ≤ (R₁ - R₂) * s := by
    apply mul_le_mul_of_nonneg_left hcs hd.le
  nlinarith [hmul, key]

/-- Each deconvolution term of two rate-latency curves, divergent case: when the dividend rate
strictly dominates (`R₂ < R₁`), for any real `M` a large shift `s` makes
`rlE R₁ T₁ (t + s) − rlE R₂ T₂ s > ↑M`. -/
theorem rl_decon_term_unbounded (R₁ T₁ R₂ T₂ t : ℝ≥0) (hR : R₂ < R₁) (M : ℝ) :
    ∃ s : ℝ≥0, ((M : ℝ) : EReal) < rlE R₁ T₁ (t + s) - rlE R₂ T₂ s := by
  -- it suffices to handle the active region; absorb the (finite, `s`-independent) offset into `M`
  set M' : ℝ := M - (R₁ : ℝ) * ((t : ℝ) - T₁) + R₂ * (- (T₂ : ℝ)) with hM'
  obtain ⟨s₀, hs₀, hgt⟩ := rl_real_term_unbounded (by exact_mod_cast hR) M'
  -- clamp `s₀` up to be `≥` both latencies, so both curves are active
  refine ⟨Real.toNNReal s₀ + T₁ + T₂, ?_⟩
  set s : ℝ≥0 := Real.toNNReal s₀ + T₁ + T₂ with hsdef
  -- both curves are active at `s`
  have hT₂s : T₂ ≤ s := by
    rw [hsdef]; exact le_add_self.trans (le_refl _)
  have hT₁ts : T₁ ≤ t + s := by
    rw [hsdef]; calc T₁ ≤ Real.toNNReal s₀ + T₁ + T₂ := by
                        rw [add_comm (Real.toNNReal s₀) T₁, add_assoc]; exact le_self_add
              _ ≤ t + (Real.toNNReal s₀ + T₁ + T₂) := le_add_self
  rw [rlE_of_le hT₁ts, rlE_of_le hT₂s, ← EReal.coe_sub, EReal.coe_lt_coe_iff]
  -- reduce to the real backbone, with `s₀ ≤ ↑s - ↑T₂ - ... ` slack
  have hs₀le : s₀ ≤ (Real.toNNReal s₀ : ℝ) := Real.le_coe_toNNReal _
  -- denote the active-region real shift quantities
  have hsR : (s : ℝ) = (Real.toNNReal s₀ : ℝ) + T₁ + T₂ := by rw [hsdef]; push_cast; ring
  -- want: M < R₁·((t+s) - T₁) - R₂·(s - T₂)
  -- = R₁·(t - T₁) + R₁·s - R₂·s + R₂·T₂  ; with R₁·s - R₂·s ≥ R₁·s₀ - R₂·s₀ > M'
  have hslope : (0 : ℝ) ≤ (R₁ : ℝ) - R₂ := by
    have : (R₂ : ℝ) < R₁ := by exact_mod_cast hR
    linarith
  have hsbig : (s₀ : ℝ) ≤ (s : ℝ) := by
    rw [hsR]; have : (0:ℝ) ≤ (T₁:ℝ) + T₂ := by positivity
    linarith [hs₀le]
  have hmono : (R₁ : ℝ) * s₀ - R₂ * s₀ ≤ (R₁ : ℝ) * s - R₂ * s := by
    have : (R₁ - R₂) * s₀ ≤ (R₁ - R₂) * s := mul_le_mul_of_nonneg_left hsbig hslope
    nlinarith [this]
  -- combine
  have : M' < (R₁ : ℝ) * s - R₂ * s := lt_of_lt_of_le hgt hmono
  push_cast
  rw [hM'] at this
  nlinarith [this]

/-- **Deconvolution of two rate-latency curves, fast-dividend case (Lemma 4.6).** When the
dividend rate strictly dominates (`R₂ < R₁`), the `(min,plus)` deconvolution of
`β_{R₁,T₁}(u) = R₁·(u − T₁)₊` by `β_{R₂,T₂}(u) = R₂·(u − T₂)₊` is `⊤`: for large shifts `s` both
curves are affine and the term grows with positive combined slope `R₁ − R₂`. -/
theorem minDeconv_rl_top (R₁ T₁ R₂ T₂ t : ℝ≥0) (hR : R₂ < R₁) :
    minDeconv (rlE R₁ T₁) (rlE R₂ T₂) t = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro M
  obtain ⟨s, hs⟩ := rl_decon_term_unbounded R₁ T₁ R₂ T₂ t hR M
  exact lt_of_lt_of_le hs (sub_le_minDeconv (rlE R₁ T₁) (rlE R₂ T₂) t s)

/-! ## (b) Deconvolution by a min of two rate-latency curves -/

/-- The closed-form deconvolution term value of one rate-latency divisor, in the slow- or
fast-divisor case: `↑(↑(R₁·(t+Tᵢ−T₁)₊))` if `R₁ ≤ Rᵢ`, else `⊤`. -/
noncomputable def rlDeconvTerm (R₁ T₁ Rᵢ Tᵢ t : ℝ≥0) : EReal :=
  if R₁ ≤ Rᵢ then (((R₁ * (t + Tᵢ - T₁) : ℝ≥0) : ℝ) : EReal) else ⊤

/-- `rlDeconvTerm` is exactly `minDeconv (rlE R₁ T₁) (rlE Rᵢ Tᵢ) t` (the slow- and fast-divisor
closed forms merged through the `R₁ ≤ Rᵢ` test). -/
theorem minDeconv_rl_eq_term (R₁ T₁ Rᵢ Tᵢ t : ℝ≥0) :
    minDeconv (rlE R₁ T₁) (rlE Rᵢ Tᵢ) t = rlDeconvTerm R₁ T₁ Rᵢ Tᵢ t := by
  unfold rlDeconvTerm
  split_ifs with h
  · exact minDeconv_rl_le R₁ T₁ Rᵢ Tᵢ t h
  · exact minDeconv_rl_top R₁ T₁ Rᵢ Tᵢ t (lt_of_not_ge h)

/-- **Deconvolution by a min of two rate-latency curves (a concave/piecewise divisor).** The
deconvolution of `β_{R₁,T₁}` by `β_{R₂,T₂} ⊓ β_{R₃,T₃}` is the join of the two single-divisor
deconvolutions (each a rate-latency closed form via `rlDeconvTerm`): the meet in the divisor
distributes to a join (`minDeconv_inf_right`). -/
theorem minDeconv_rl_inf_two (R₁ T₁ R₂ T₂ R₃ T₃ t : ℝ≥0) :
    minDeconv (rlE R₁ T₁) (rlE R₂ T₂ ⊓ rlE R₃ T₃) t
      = rlDeconvTerm R₁ T₁ R₂ T₂ t ⊔ rlDeconvTerm R₁ T₁ R₃ T₃ t := by
  rw [minDeconv_inf_right, minDeconv_rl_eq_term, minDeconv_rl_eq_term]

/-! ## (c) Deconvolution distributes over a min of a list of divisors -/

/-- Pointwise meet of a list of `EReal`-valued curves: `foldr (· ⊓ ·) ⊤` (the `⊤` curve is the
`⊓`-unit), so `minInfList []` is the constant `⊤` and `minInfList (h :: l) = h ⊓ minInfList l`. -/
noncomputable def minInfList {D : Type*} (l : List (D → EReal)) : D → EReal :=
  l.foldr (· ⊓ ·) (fun _ => ⊤)

/-- `minInfList [] = (fun _ => ⊤)`: the empty meet is the `⊤` curve. -/
@[simp] theorem minInfList_nil {D : Type*} :
    minInfList ([] : List (D → EReal)) = (fun _ => ⊤) := rfl

/-- `minInfList (h :: l) = h ⊓ minInfList l`: the meet over `h :: l` peels off `h`. -/
@[simp] theorem minInfList_cons {D : Type*} (h : D → EReal) (l : List (D → EReal)) :
    minInfList (h :: l) = h ⊓ minInfList l := rfl

/-- `minDeconv g ⊤ = (fun _ => ⊤)`: deconvolving by the `⊤` curve gives `⊤` everywhere
(each term `g (t+s) − ⊤ = ⊥`, but the supremum over the empty/`⊥` family of `EReal`... here the
divisor is `⊤` so the value is `⊤`). Stated via `sub_top` and `iSup` of a constant. -/
theorem minDeconv_top_right {D : Type*} [Add D] [Nonempty D] (g : D → EReal) (t : D) :
    minDeconv g (fun _ => (⊤ : EReal)) t = ⊥ := by
  unfold minDeconv
  simp only [EReal.sub_top, ciSup_const]

/-- **Deconvolution distributes over a list-meet of divisors:**
`minDeconv g (minInfList l) t = ⨆ h ∈ l, minDeconv g h t` — the divisor-side analog of the
convolution-distributes-over-min law. Each divisor in the list contributes a join term; the empty
list gives `minDeconv g ⊤ t = ⊥` (`= ⨆_{h ∈ []}`). Proven by induction on `l` using
`minDeconv_inf_right`. -/
theorem minDeconv_inf_list_right {D : Type*} [Add D] [Nonempty D]
    (g : D → EReal) (l : List (D → EReal)) (t : D) :
    minDeconv g (minInfList l) t = ⨆ h ∈ l, minDeconv g h t := by
  induction l with
  | nil => simp [minDeconv_top_right]
  | cons h l ih =>
    rw [minInfList_cons, minDeconv_inf_right, ih]
    simp [iSup_or, iSup_sup_eq]

/-! ## Restatements (faithfulness checks against the book's wording) -/

/-- Fast-dividend rate-latency case, written out with explicit `EReal`-coerced rate-latency
functions: deconvolving `u ↦ R₁·(u − T₁)₊` by `u ↦ R₂·(u − T₂)₊` with `R₂ < R₁` gives `⊤`. -/
example (R₁ T₁ R₂ T₂ t : ℝ≥0) (hR : R₂ < R₁) :
    minDeconv (fun u => (((R₁ * (u - T₁) : ℝ≥0) : ℝ) : EReal))
              (fun u => (((R₂ * (u - T₂) : ℝ≥0) : ℝ) : EReal)) t = ⊤ :=
  minDeconv_rl_top R₁ T₁ R₂ T₂ t hR

/-- Equal-latency pure-rate fast-dividend case (`T₁ = T₂ = 0`, `R₂ < R₁`): the deconvolution of
two pure-rate curves with the dividend faster is `⊤`. -/
example (R₁ R₂ t : ℝ≥0) (hR : R₂ < R₁) :
    minDeconv (rlE R₁ 0) (rlE R₂ 0) t = ⊤ :=
  minDeconv_rl_top R₁ 0 R₂ 0 t hR

/-- Two-rate-latency-min composite, slow-divisor on both branches (`R₁ ≤ R₂`, `R₁ ≤ R₃`): the
deconvolution by `β_{R₂,T₂} ⊓ β_{R₃,T₃}` is the join of the two finite rate-latency values
`R₁·(t+T₂−T₁)₊ ⊔ R₁·(t+T₃−T₁)₊`. -/
example (R₁ T₁ R₂ T₂ R₃ T₃ t : ℝ≥0) (h₂ : R₁ ≤ R₂) (h₃ : R₁ ≤ R₃) :
    minDeconv (rlE R₁ T₁) (rlE R₂ T₂ ⊓ rlE R₃ T₃) t
      = (((R₁ * (t + T₂ - T₁) : ℝ≥0) : ℝ) : EReal)
          ⊔ (((R₁ * (t + T₃ - T₁) : ℝ≥0) : ℝ) : EReal) := by
  rw [minDeconv_rl_inf_two]
  unfold rlDeconvTerm
  rw [if_pos h₂, if_pos h₃]

/-- Two-rate-latency-min composite with one fast branch (`R₂ < R₁`): that branch contributes `⊤`,
so the whole join is `⊤` (the meet divisor is "too slow" on the `R₂` branch). -/
example (R₁ T₁ R₂ T₂ R₃ T₃ t : ℝ≥0) (h₂ : R₂ < R₁) :
    minDeconv (rlE R₁ T₁) (rlE R₂ T₂ ⊓ rlE R₃ T₃) t = ⊤ := by
  rw [minDeconv_rl_inf_two]
  unfold rlDeconvTerm
  rw [if_neg (not_le_of_gt h₂), top_sup_eq]

/-- Single-element list: `minDeconv g (minInfList [h]) = minDeconv g h` (the lone divisor),
the base composite case of the list-distribution law. -/
example {D : Type*} [Add D] [Nonempty D] (g h : D → EReal) (t : D) :
    minDeconv g (minInfList [h]) t = minDeconv g h t := by
  rw [minDeconv_inf_list_right]; simp

end DeepWiki
