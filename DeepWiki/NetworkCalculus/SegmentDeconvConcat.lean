import DeepWiki.NetworkCalculus.BoundedSegment
import DeepWiki.NetworkCalculus.FunctionDioids

/-! # Deconvolution of two bounded segments

The §4.3 (min,plus) deconvolution `f ⊘ g` of two affine segments (book Lemma
4.6).  The deconvolution `minDeconv f g t = ⨆ s, f (t+s) − g s` is a *supremum*,
so the natural extensions invert the convolution convention: the **dividend** `f`
is padded with `⊥` (`= −∞`) off its support (`segBotE`), while the **divisor**
`g` keeps the `⊤` (`= +∞`) segment padding (`segE`).  This is exactly the book's
local convention "outside `J` set `g = −∞`": in `EReal`, `x − ⊤ = ⊥` and
`⊥ − x = ⊥`, so every shift `s` with `s ∉ J` *or* `t + s ∉ I` contributes `⊥` and
drops out of the supremum, leaving the effective range `J ∩ (I − t)` of the proof.

This file provides the bottom-padded segment `segBotE` with its satellite API and
proves, for the regime `f' ≥ g'` with `t ≤ b − d` (the proof's "maximize `u`,
`u = d`" branch), the exact value `minDeconv f g t = f (t+d) − g d`. -/

namespace DeepWiki

open scoped NNReal

/-! ## Bottom-padded segment (the deconvolution dividend)

`segBotE` is the affine `va + s·(t−a)` on `[a,b]`, `⊥` (`= −∞`) outside — the
extension a *dividend* needs under a supremum-deconvolution (off-support terms
`⊥ − g s = ⊥` drop out). -/

/-- Bottom-padded closed segment: affine `va + s·(t−a)` on `[a,b]`, `⊥` (`= −∞`)
outside.  The dividend convention for the supremum deconvolution `minDeconv`. -/
noncomputable def segBotE (a b va s : ℝ≥0) : ℝ≥0 → EReal :=
  fun t => if a ≤ t ∧ t ≤ b then (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal) else ⊥

/-- `segBotE` reduces to its `if`. -/
theorem segBotE_apply (a b va s t : ℝ≥0) :
    segBotE a b va s t =
      if a ≤ t ∧ t ≤ b then (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal) else ⊥ :=
  rfl

/-- On `[a,b]`, `segBotE` is the affine value. -/
@[simp] theorem segBotE_apply_mem (a b va s t : ℝ≥0) (h : a ≤ t ∧ t ≤ b) :
    segBotE a b va s t = (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal) :=
  if_pos h

/-- Off `[a,b]`, `segBotE` is `⊥`. -/
@[simp] theorem segBotE_apply_not_mem (a b va s t : ℝ≥0) (h : ¬ (a ≤ t ∧ t ≤ b)) :
    segBotE a b va s t = ⊥ :=
  if_neg h

/-- In-support reading from the two bounds. -/
theorem segBotE_mem (a b va s t : ℝ≥0) (hl : a ≤ t) (hr : t ≤ b) :
    segBotE a b va s t = (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal) :=
  if_pos ⟨hl, hr⟩

/-- Strictly left of `a`, the bottom-padded segment is `⊥`. -/
theorem segBotE_of_lt_left (a b va s t : ℝ≥0) (h : t < a) :
    segBotE a b va s t = ⊥ :=
  if_neg fun hmem => absurd hmem.1 (not_le.mpr h)

/-- Strictly right of `b`, the bottom-padded segment is `⊥`. -/
theorem segBotE_of_gt_right (a b va s t : ℝ≥0) (h : b < t) :
    segBotE a b va s t = ⊥ :=
  if_neg fun hmem => absurd hmem.2 (not_le.mpr h)

/-- Left endpoint value: `segBotE … a = va`. -/
theorem segBotE_left (a b va s : ℝ≥0) (h : a ≤ b) :
    segBotE a b va s a = ((va : ℝ) : EReal) := by
  rw [segBotE_mem a b va s a le_rfl h]; simp

/-- Right endpoint value: `segBotE … b = va + s·(b−a)`. -/
theorem segBotE_right (a b va s : ℝ≥0) (h : a ≤ b) :
    segBotE a b va s b = (((va + s * (b - a) : ℝ≥0) : ℝ) : EReal) :=
  segBotE_mem a b va s b h le_rfl

/-! ## Real affine value of a segment

The real number underlying a segment value `va + s·(x−a)` on its support
(`a ≤ x`), with the `ℝ≥0` truncated subtraction unfolded to genuine real `−`. -/

/-- On `a ≤ x`, the `ℝ≥0` affine value coerces to the real affine value
`↑va + ↑s·(↑x − ↑a)`. -/
theorem coe_affine_of_le (a va s x : ℝ≥0) (h : a ≤ x) :
    ((va + s * (x - a) : ℝ≥0) : ℝ) = (va : ℝ) + (s : ℝ) * ((x : ℝ) - (a : ℝ)) := by
  rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_sub h]

/-! ## Deconvolution of two segments, regime `f' ≥ g'`, `t ≤ b − d`

Book Lemma 4.6, the "maximize `u`, optimum `u = d`" branch.  The dividend is
the bottom-padded segment `f = segBotE a b va sf` on `I = [a,b]`; the divisor is
`g = segE c d vc sg` on `J = [c,d]`.  When the dividend slope dominates
(`sg ≤ sf`) and `t + d ≤ b` (i.e. `t ≤ b − d`), the deconvolution attains its
supremum at the largest shift `s = d`, with value `f (t+d) − g d`. -/

/-- Finite-shift comparison driving the upper bound: every shift `s` gives a term
`f(t+s) − g s` at most the `s = d` term `f(t+d) − g d`.  Off-support shifts give
`⊥`; for an in-support shift (`s ∈ [c,d]`, `t+s ∈ [a,b]`) the difference slope
`f' − g' = sf − sg ≥ 0` and `s ≤ d` make the affine value increase up to `s = d`. -/
theorem segDeconv_term_le_of_slope_ge
    (a b va sf c d vc sg t s : ℝ≥0)
    (hslope : sg ≤ sf) (hatd : a ≤ t + d) (htdb : t + d ≤ b) (hcd : c ≤ d) :
    segBotE a b va sf (t + s) - segE c d vc sg s ≤
      segBotE a b va sf (t + d) - segE c d vc sg d := by
  -- the `s = d` term (RHS) is finite: rewrite it to a coerced real.
  rw [segBotE_apply_mem a b va sf (t + d) ⟨hatd, htdb⟩,
      segE_apply_mem c d vc sg d ⟨hcd, le_rfl⟩,
      ← EReal.coe_sub, coe_affine_of_le a va sf (t + d) hatd,
      coe_affine_of_le c vc sg d hcd]
  by_cases hcsd : c ≤ s ∧ s ≤ d
  · -- divisor finite at `s`
    by_cases hmem : a ≤ t + s ∧ t + s ≤ b
    · -- dividend finite at `t+s`: compare two coerced reals
      rw [segBotE_apply_mem a b va sf (t + s) hmem,
          segE_apply_mem c d vc sg s hcsd,
          ← EReal.coe_sub, coe_affine_of_le a va sf (t + s) hmem.1,
          coe_affine_of_le c vc sg s hcsd.1, EReal.coe_le_coe_iff]
      -- real inequality: (sf − sg)·(d − s) ≥ 0
      have hsd : (s : ℝ) ≤ (d : ℝ) := by exact_mod_cast hcsd.2
      have hsl : (sg : ℝ) ≤ (sf : ℝ) := by exact_mod_cast hslope
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr hsl) (sub_nonneg.mpr hsd)]
    · -- dividend `= ⊥` at `t+s`
      rw [segBotE_apply_not_mem a b va sf (t + s) hmem, EReal.bot_sub]
      exact bot_le
  · -- divisor `= ⊤` at `s`, so the LHS term is `⊥`
    rw [segE_apply_not_mem c d vc sg s hcsd, EReal.sub_top]
    exact bot_le

/-- **Book Lemma 4.6, regime `f' ≥ g'`, `t ≤ b − d`.**  The deconvolution of the
bottom-padded dividend segment `f = segBotE a b va sf` on `I = [a,b]` by the
divisor segment `g = segE c d vc sg` on `J = [c,d]` attains, when the dividend
slope dominates (`sg ≤ sf`) and `t + d ≤ b`, its supremum at the largest shift
`s = d`:  `minDeconv f g t = f (t+d) − g d`. -/
theorem minDeconv_segBotE_segE_eq_of_slope_ge
    (a b va sf c d vc sg t : ℝ≥0)
    (hslope : sg ≤ sf) (hatd : a ≤ t + d) (htdb : t + d ≤ b) (hcd : c ≤ d) :
    minDeconv (segBotE a b va sf) (segE c d vc sg) t =
      segBotE a b va sf (t + d) - segE c d vc sg d := by
  refine le_antisymm ?_ ?_
  · -- upper bound: every shift term `≤` the `s = d` term
    refine minDeconv_le (fun s => ?_)
    exact segDeconv_term_le_of_slope_ge a b va sf c d vc sg t s hslope hatd htdb hcd
  · -- lower bound: the `s = d` term is one of the terms in the supremum
    exact sub_le_minDeconv (segBotE a b va sf) (segE c d vc sg) t d

/-- The regime-`f' ≥ g'` value written out in closed real-affine form:
`minDeconv f g t = (va + sf·(t+d−a)) − (vc + sg·(d−c))`, the first concatenated
segment of book Lemma 4.6 anchored at `(a−d, f(a⁺)−g(d⁻))`. -/
theorem minDeconv_segBotE_segE_value_of_slope_ge
    (a b va sf c d vc sg t : ℝ≥0)
    (hslope : sg ≤ sf) (hatd : a ≤ t + d) (htdb : t + d ≤ b) (hcd : c ≤ d) :
    minDeconv (segBotE a b va sf) (segE c d vc sg) t =
      (((va : ℝ) + (sf : ℝ) * ((t : ℝ) + (d : ℝ) - (a : ℝ))) : EReal) -
        (((vc : ℝ) + (sg : ℝ) * ((d : ℝ) - (c : ℝ))) : EReal) := by
  rw [minDeconv_segBotE_segE_eq_of_slope_ge a b va sf c d vc sg t hslope hatd htdb hcd,
      segBotE_apply_mem a b va sf (t + d) ⟨hatd, htdb⟩,
      segE_apply_mem c d vc sg d ⟨hcd, le_rfl⟩,
      coe_affine_of_le a va sf (t + d) hatd, coe_affine_of_le c vc sg d hcd]
  push_cast
  ring_nf

/-! ## Deconvolution of two segments, regime `f' < g'`, `t > a − c`

Book Lemma 4.6, the "minimize `u`, optimum `u = c`" branch.  When the divisor
slope dominates (`sf ≤ sg`) and `a ≤ t + c` (i.e. `t ≥ a − c`), the supremum is
attained at the smallest shift `s = c`, with value `f (t+c) − g c`. -/

/-- Finite-shift comparison for the `f' < g'` branch: every shift gives a term
`f(t+s) − g s` at most the `s = c` term `f(t+c) − g c`.  Off-support shifts give
`⊥`; for an in-support shift the difference slope `f' − g' = sf − sg ≤ 0` and
`c ≤ s` make the affine value decrease away from `s = c`. -/
theorem segDeconv_term_le_of_slope_lt
    (a b va sf c d vc sg t s : ℝ≥0)
    (hslope : sf ≤ sg) (hatc : a ≤ t + c) (htcb : t + c ≤ b) (hcd : c ≤ d) :
    segBotE a b va sf (t + s) - segE c d vc sg s ≤
      segBotE a b va sf (t + c) - segE c d vc sg c := by
  -- the `s = c` term (RHS) is finite: rewrite it to a coerced real.
  rw [segBotE_apply_mem a b va sf (t + c) ⟨hatc, htcb⟩,
      segE_apply_mem c d vc sg c ⟨le_rfl, hcd⟩,
      ← EReal.coe_sub, coe_affine_of_le a va sf (t + c) hatc,
      coe_affine_of_le c vc sg c le_rfl]
  by_cases hcsd : c ≤ s ∧ s ≤ d
  · -- divisor finite at `s`
    by_cases hmem : a ≤ t + s ∧ t + s ≤ b
    · -- dividend finite at `t+s`: compare two coerced reals
      rw [segBotE_apply_mem a b va sf (t + s) hmem,
          segE_apply_mem c d vc sg s hcsd,
          ← EReal.coe_sub, coe_affine_of_le a va sf (t + s) hmem.1,
          coe_affine_of_le c vc sg s hcsd.1, EReal.coe_le_coe_iff]
      -- real inequality: (sg − sf)·(s − c) ≥ 0
      have hcs : (c : ℝ) ≤ (s : ℝ) := by exact_mod_cast hcsd.1
      have hsl : (sf : ℝ) ≤ (sg : ℝ) := by exact_mod_cast hslope
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr hsl) (sub_nonneg.mpr hcs)]
    · -- dividend `= ⊥` at `t+s`
      rw [segBotE_apply_not_mem a b va sf (t + s) hmem, EReal.bot_sub]
      exact bot_le
  · -- divisor `= ⊤` at `s`, so the LHS term is `⊥`
    rw [segE_apply_not_mem c d vc sg s hcsd, EReal.sub_top]
    exact bot_le

/-- **Book Lemma 4.6, regime `f' < g'`, `t > a − c`.**  When the divisor slope
dominates (`sf ≤ sg`) and `a ≤ t + c`, the deconvolution attains its supremum at
the smallest shift `s = c`:  `minDeconv f g t = f (t+c) − g c`. -/
theorem minDeconv_segBotE_segE_eq_of_slope_lt
    (a b va sf c d vc sg t : ℝ≥0)
    (hslope : sf ≤ sg) (hatc : a ≤ t + c) (htcb : t + c ≤ b) (hcd : c ≤ d) :
    minDeconv (segBotE a b va sf) (segE c d vc sg) t =
      segBotE a b va sf (t + c) - segE c d vc sg c := by
  refine le_antisymm ?_ ?_
  · refine minDeconv_le (fun s => ?_)
    exact segDeconv_term_le_of_slope_lt a b va sf c d vc sg t s hslope hatc htcb hcd
  · exact sub_le_minDeconv (segBotE a b va sf) (segE c d vc sg) t c

/-! ## Deconvolution of two segments, regime `f' ≥ g'`, `t > b − d`

Book Lemma 4.6, the "maximize `u`, optimum `u = b − t`" branch (the upper bound
on `u` comes from `t + u ≤ b`, not from `u ≤ d`).  When the dividend slope
dominates (`sg ≤ sf`), `t ≤ b`, and the optimum shift `b − t` lands in `J`
(`c ≤ b − t ≤ d`), the supremum is attained at `s = b − t`, with value
`f b − g (b − t)`. -/

/-- Finite-shift comparison for the `f' ≥ g'`, `t > b − d` branch: every shift
gives a term `f(t+s) − g s` at most the `s = b − t` term `f b − g (b−t)`. -/
theorem segDeconv_term_le_of_slope_ge_right
    (a b va sf c d vc sg t s : ℝ≥0)
    (hslope : sg ≤ sf) (hab : a ≤ b) (htb : t ≤ b)
    (hcbt : c ≤ b - t) (hbtd : b - t ≤ d) :
    segBotE a b va sf (t + s) - segE c d vc sg s ≤
      segBotE a b va sf b - segE c d vc sg (b - t) := by
  -- the RHS term is finite: rewrite to a coerced real.
  rw [segBotE_apply_mem a b va sf b ⟨hab, le_rfl⟩,
      segE_apply_mem c d vc sg (b - t) ⟨hcbt, hbtd⟩,
      ← EReal.coe_sub, coe_affine_of_le a va sf b hab,
      coe_affine_of_le c vc sg (b - t) hcbt]
  by_cases hcsd : c ≤ s ∧ s ≤ d
  · by_cases hmem : a ≤ t + s ∧ t + s ≤ b
    · rw [segBotE_apply_mem a b va sf (t + s) hmem,
          segE_apply_mem c d vc sg s hcsd,
          ← EReal.coe_sub, coe_affine_of_le a va sf (t + s) hmem.1,
          coe_affine_of_le c vc sg s hcsd.1, EReal.coe_le_coe_iff]
      -- real inequality: (sf − sg)·(b − t − s) ≥ 0, with t+s ≤ b giving b−t−s ≥ 0
      have htsb : (t : ℝ) + (s : ℝ) ≤ (b : ℝ) := by exact_mod_cast hmem.2
      have hsl : (sg : ℝ) ≤ (sf : ℝ) := by exact_mod_cast hslope
      have hbt : ((b - t : ℝ≥0) : ℝ) = (b : ℝ) - (t : ℝ) := NNReal.coe_sub htb
      rw [hbt]; push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr hsl) (by linarith : (0:ℝ) ≤ (b:ℝ) - (t:ℝ) - (s:ℝ))]
    · rw [segBotE_apply_not_mem a b va sf (t + s) hmem, EReal.bot_sub]
      exact bot_le
  · rw [segE_apply_not_mem c d vc sg s hcsd, EReal.sub_top]
    exact bot_le

/-- **Book Lemma 4.6, regime `f' ≥ g'`, `t > b − d`.**  When the dividend slope
dominates (`sg ≤ sf`), `t ≤ b`, and the optimum shift lands in `J`
(`c ≤ b − t ≤ d`), the deconvolution attains its supremum at `s = b − t`:
`minDeconv f g t = f b − g (b − t)`. -/
theorem minDeconv_segBotE_segE_eq_of_slope_ge_right
    (a b va sf c d vc sg t : ℝ≥0)
    (hslope : sg ≤ sf) (hab : a ≤ b) (htb : t ≤ b)
    (hcbt : c ≤ b - t) (hbtd : b - t ≤ d) :
    minDeconv (segBotE a b va sf) (segE c d vc sg) t =
      segBotE a b va sf b - segE c d vc sg (b - t) := by
  refine le_antisymm ?_ ?_
  · refine minDeconv_le (fun s => ?_)
    exact segDeconv_term_le_of_slope_ge_right a b va sf c d vc sg t s hslope hab htb hcbt hbtd
  · -- the `s = b − t` term: note `t + (b − t) = b` since `t ≤ b`
    have hsum : t + (b - t) = b := add_tsub_cancel_of_le htb
    have := sub_le_minDeconv (segBotE a b va sf) (segE c d vc sg) t (b - t)
    rwa [hsum] at this

/-! ## Deconvolution of two segments, regime `f' < g'`, `t ≤ a − c`

Book Lemma 4.6, the "minimize `u`, optimum `u = a − t`" branch (the lower bound
on `u` comes from `a ≤ t + u`, not from `c ≤ u`).  When the divisor slope
dominates (`sf ≤ sg`), `t ≤ a`, and the optimum shift `a − t` lands in `J`
(`c ≤ a − t ≤ d`), the supremum is attained at `s = a − t`, with value
`f a − g (a − t)`. -/

/-- Finite-shift comparison for the `f' < g'`, `t ≤ a − c` branch: every shift
gives a term `f(t+s) − g s` at most the `s = a − t` term `f a − g (a−t)`. -/
theorem segDeconv_term_le_of_slope_lt_left
    (a b va sf c d vc sg t s : ℝ≥0)
    (hslope : sf ≤ sg) (hab : a ≤ b) (hta : t ≤ a)
    (hcat : c ≤ a - t) (hatd : a - t ≤ d) :
    segBotE a b va sf (t + s) - segE c d vc sg s ≤
      segBotE a b va sf a - segE c d vc sg (a - t) := by
  rw [segBotE_apply_mem a b va sf a ⟨le_rfl, hab⟩,
      segE_apply_mem c d vc sg (a - t) ⟨hcat, hatd⟩,
      ← EReal.coe_sub, coe_affine_of_le a va sf a le_rfl,
      coe_affine_of_le c vc sg (a - t) hcat]
  by_cases hcsd : c ≤ s ∧ s ≤ d
  · by_cases hmem : a ≤ t + s ∧ t + s ≤ b
    · rw [segBotE_apply_mem a b va sf (t + s) hmem,
          segE_apply_mem c d vc sg s hcsd,
          ← EReal.coe_sub, coe_affine_of_le a va sf (t + s) hmem.1,
          coe_affine_of_le c vc sg s hcsd.1, EReal.coe_le_coe_iff]
      -- real inequality: (sg − sf)·(t + s − a) ≥ 0, with a ≤ t+s giving t+s−a ≥ 0
      have hats : (a : ℝ) ≤ (t : ℝ) + (s : ℝ) := by exact_mod_cast hmem.1
      have hsl : (sf : ℝ) ≤ (sg : ℝ) := by exact_mod_cast hslope
      have hat : ((a - t : ℝ≥0) : ℝ) = (a : ℝ) - (t : ℝ) := NNReal.coe_sub hta
      rw [hat]; push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr hsl) (by linarith : (0:ℝ) ≤ (t:ℝ) + (s:ℝ) - (a:ℝ))]
    · rw [segBotE_apply_not_mem a b va sf (t + s) hmem, EReal.bot_sub]
      exact bot_le
  · rw [segE_apply_not_mem c d vc sg s hcsd, EReal.sub_top]
    exact bot_le

/-- **Book Lemma 4.6, regime `f' < g'`, `t ≤ a − c`.**  When the divisor slope
dominates (`sf ≤ sg`), `t ≤ a`, and the optimum shift lands in `J`
(`c ≤ a − t ≤ d`), the deconvolution attains its supremum at `s = a − t`:
`minDeconv f g t = f a − g (a − t)`. -/
theorem minDeconv_segBotE_segE_eq_of_slope_lt_left
    (a b va sf c d vc sg t : ℝ≥0)
    (hslope : sf ≤ sg) (hab : a ≤ b) (hta : t ≤ a)
    (hcat : c ≤ a - t) (hatd : a - t ≤ d) :
    minDeconv (segBotE a b va sf) (segE c d vc sg) t =
      segBotE a b va sf a - segE c d vc sg (a - t) := by
  refine le_antisymm ?_ ?_
  · refine minDeconv_le (fun s => ?_)
    exact segDeconv_term_le_of_slope_lt_left a b va sf c d vc sg t s hslope hab hta hcat hatd
  · have hsum : t + (a - t) = a := add_tsub_cancel_of_le hta
    have := sub_le_minDeconv (segBotE a b va sf) (segE c d vc sg) t (a - t)
    rwa [hsum] at this

/-! ## Restatements (verification against the book wording) -/

-- Bottom-padded segment: affine on `[a,b]`, `−∞` (`= ⊥`) outside.
example (a b va s : ℝ≥0) :
    segBotE a b va s =
      fun t => if a ≤ t ∧ t ≤ b then (((va + s * (t - a) : ℝ≥0) : ℝ) : EReal) else ⊥ :=
  rfl

-- Lemma 4.6, `f' ≥ g'`, `t ≤ b − d`: deconvolution attained at the largest shift
-- `u = d`, value `f(t+d) − g(d)`.
example (a b va sf c d vc sg t : ℝ≥0)
    (hslope : sg ≤ sf) (hatd : a ≤ t + d) (htdb : t + d ≤ b) (hcd : c ≤ d) :
    minDeconv (segBotE a b va sf) (segE c d vc sg) t =
      segBotE a b va sf (t + d) - segE c d vc sg d :=
  minDeconv_segBotE_segE_eq_of_slope_ge a b va sf c d vc sg t hslope hatd htdb hcd

-- Lemma 4.6, `f' ≥ g'`, `t > b − d`: optimum shift `u = b − t`, value `f(b) − g(b−t)`.
example (a b va sf c d vc sg t : ℝ≥0)
    (hslope : sg ≤ sf) (hab : a ≤ b) (htb : t ≤ b)
    (hcbt : c ≤ b - t) (hbtd : b - t ≤ d) :
    minDeconv (segBotE a b va sf) (segE c d vc sg) t =
      segBotE a b va sf b - segE c d vc sg (b - t) :=
  minDeconv_segBotE_segE_eq_of_slope_ge_right a b va sf c d vc sg t hslope hab htb hcbt hbtd

-- Lemma 4.6, `f' < g'`, `t ≤ a − c`: optimum shift `u = a − t`, value `f(a) − g(a−t)`.
example (a b va sf c d vc sg t : ℝ≥0)
    (hslope : sf ≤ sg) (hab : a ≤ b) (hta : t ≤ a)
    (hcat : c ≤ a - t) (hatd : a - t ≤ d) :
    minDeconv (segBotE a b va sf) (segE c d vc sg) t =
      segBotE a b va sf a - segE c d vc sg (a - t) :=
  minDeconv_segBotE_segE_eq_of_slope_lt_left a b va sf c d vc sg t hslope hab hta hcat hatd

-- Lemma 4.6, `f' < g'`, `t > a − c`: optimum shift `u = c`, value `f(t+c) − g(c)`.
example (a b va sf c d vc sg t : ℝ≥0)
    (hslope : sf ≤ sg) (hatc : a ≤ t + c) (htcb : t + c ≤ b) (hcd : c ≤ d) :
    minDeconv (segBotE a b va sf) (segE c d vc sg) t =
      segBotE a b va sf (t + c) - segE c d vc sg c :=
  minDeconv_segBotE_segE_eq_of_slope_lt a b va sf c d vc sg t hslope hatc htcb hcd

/-! ## Anchor point of the concatenation

Book Lemma 4.6 states the concatenated deconvolution is anchored at
`(a − d, f(a⁺) − g(d⁻))`.  At `t = a − d` the `f' ≥ g'` formula `f(t+d) − g d`
evaluates to `f a − g d = f(a⁺) − g(d⁻)` (left value of `f`, right value of `g`),
the claimed anchor value. -/

/-- At the left end `t = a − d` of the domain `(I−J)∩ℝ⁺`, the regime-`f' ≥ g'`
deconvolution value is the anchor `f a − g d`. -/
theorem minDeconv_segBotE_segE_anchor_of_slope_ge
    (a b va sf c d vc sg : ℝ≥0)
    (hslope : sg ≤ sf) (had : d ≤ a) (hab : a ≤ b) (hcd : c ≤ d) :
    minDeconv (segBotE a b va sf) (segE c d vc sg) (a - d) =
      segBotE a b va sf a - segE c d vc sg d := by
  have hsum : (a - d) + d = a := tsub_add_cancel_of_le had
  rw [minDeconv_segBotE_segE_eq_of_slope_ge a b va sf c d vc sg (a - d) hslope
        (by rw [hsum]) (by rw [hsum]; exact hab) hcd, hsum]

-- Anchor value `f a − g d = f(a⁺) − g(d⁻)`: `f a` is the left value `va`, `g d`
-- the right value `vc + sg·(d−c)`.
example (a b va sf c d vc sg : ℝ≥0)
    (hslope : sg ≤ sf) (had : d ≤ a) (hab : a ≤ b) (hcd : c ≤ d) :
    minDeconv (segBotE a b va sf) (segE c d vc sg) (a - d) =
      ((va : ℝ) : EReal) - (((vc + sg * (d - c) : ℝ≥0) : ℝ) : EReal) := by
  rw [minDeconv_segBotE_segE_anchor_of_slope_ge a b va sf c d vc sg hslope had hab hcd,
      segBotE_left a b va sf hab, segE_right c d vc sg hcd]

/-! ## Larger slope first (the structural shape of the concatenation)

Book Lemma 4.6: the two concatenated segments have *the larger slope first*.  The
deconvolution `minDeconv f g` is built from the dividend slope `sf` and the
(negated) divisor slope; in the `f' ≥ g'` case the value increases in `t` at the
faster of the two effective rates near the anchor.  Here we record the immediate
monotonicity backbone: `minDeconv` is monotone in `t` when the dividend is. -/

-- `segBotE` is monotone (in the dioid/`EReal` order) in `t`: off-support is `⊥`,
-- and on-support the affine value increases — but the global function is NOT
-- monotone (it jumps from finite to `⊥` past `b`), so monotonicity is recorded
-- only through the deconvolution's per-shift structure above, not as a blanket
-- `Monotone (segBotE …)` (which is false).  The four regime equalities are the
-- faithful statement of "larger slope first": each regime's value is an affine
-- function of `t` whose slope is `sf`, `−sg` (via `b − t`), `−sg` (via `a − t`),
-- and `sf` respectively, and the active regime switches at the breakpoints
-- `t = b − d` and `t = a − c`, ordering the slopes with the larger first.

end DeepWiki
