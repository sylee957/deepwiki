import DeepWiki.NetworkCalculus.FunctionDioids
import Mathlib.Data.EReal.Operations

/-! # (min,plus) deconvolution of affine curves (toward Lemma 4.6, §4.3)
The deconvolution `minDeconv g h t = ⨆_s g (t + s) - h s` of two affine curves
`g(u) = a + p·u`, `h(u) = b + q·u` (as `EReal` coes of `ℝ≥0`): when the divisor's slope
dominates (`p ≤ q`) the `s`-coefficient `p − q ≤ 0`, so the supremum is attained at `s = 0`
and equals the finite real `(a + p·t) − b`; when `q < p` the `s`-coefficient is positive and
the supremum is `⊤`. The `p ≤ q` case is the building block used downstream in the
segment-deconvolution of Lemma 4.6. -/

namespace DeepWiki

open scoped NNReal

/-- `↑(↑x : ℝ) − ↑(↑y : ℝ) = ↑((x : ℝ) − (y : ℝ))` in `EReal` for `x y : ℝ≥0`: the difference of
two finite (`ℝ≥0`-valued) `EReal` coercions is the `EReal` coercion of the real difference (which
may be negative). -/
theorem coe_sub_coe_nnreal (x y : ℝ≥0) :
    (((x : ℝ) : EReal)) - (((y : ℝ) : EReal)) = ((((x : ℝ) - (y : ℝ)) : ℝ) : EReal) :=
  (EReal.coe_sub _ _).symm

/-- An affine curve `u ↦ a + p·u` as an `EReal`-valued function (coe of its `ℝ≥0` value). -/
noncomputable def affineE (a p : ℝ≥0) : ℝ≥0 → EReal :=
  fun u => (((a + p * u : ℝ≥0) : ℝ) : EReal)

/-- `affineE a p u = ↑(↑(a + p·u))`: the defining evaluation. -/
theorem affineE_apply (a p u : ℝ≥0) :
    affineE a p u = (((a + p * u : ℝ≥0) : ℝ) : EReal) := rfl

/-- `affineE a p 0 = ↑(↑a)`: value at the origin. -/
@[simp] theorem affineE_zero (a p : ℝ≥0) :
    affineE a p 0 = (((a : ℝ≥0) : ℝ) : EReal) := by
  simp [affineE]

/-- Each deconvolution term of two affine curves is bounded by the `s = 0` term when the divisor
slope dominates: for `p ≤ q` and `s : ℝ≥0`,
`affineE a p (t + s) − affineE b q s ≤ ↑(↑(a + p·t)) − ↑(↑b)` (the `s`-coefficient `p − q ≤ 0`). -/
theorem affine_decon_term_le (a p b q t : ℝ≥0) (hpq : p ≤ q) (s : ℝ≥0) :
    affineE a p (t + s) - affineE b q s
      ≤ (((a + p * t : ℝ≥0) : ℝ) : EReal) - (((b : ℝ≥0) : ℝ) : EReal) := by
  rw [affineE_apply, affineE_apply, coe_sub_coe_nnreal, coe_sub_coe_nnreal,
    EReal.coe_le_coe_iff]
  -- reduces to a real comparison: `p·s ≤ q·s`
  have hps : (p : ℝ) * s ≤ (q : ℝ) * s := by
    have : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
    gcongr
  push_cast
  nlinarith [hps]

/-- **Deconvolution of two affine curves, slow-divisor case.** When the divisor slope dominates
(`p ≤ q`), the `(min,plus)` deconvolution of `g(u) = a + p·u` by `h(u) = b + q·u` is the finite
real value `(a + p·t) − b` (the supremum over `s` is attained at `s = 0`). -/
theorem minDeconv_affine_le (a p b q t : ℝ≥0) (hpq : p ≤ q) :
    minDeconv (affineE a p) (affineE b q) t
      = (((a + p * t : ℝ≥0) : ℝ) : EReal) - (((b : ℝ≥0) : ℝ) : EReal) := by
  apply le_antisymm
  · -- upper bound: every term is `≤` the `s = 0` value
    exact minDeconv_le (fun s => affine_decon_term_le a p b q t hpq s)
  · -- lower bound: the `s = 0` term realizes the value
    refine le_trans (le_of_eq ?_) (sub_le_minDeconv (affineE a p) (affineE b q) t 0)
    rw [affineE_apply, affineE_apply]
    congr 2 <;> [norm_num; simp]

/-- Each deconvolution term, divergent case: when the dividend slope strictly dominates (`q < p`),
the `s`-coefficient `p − q > 0`, so the term at `s` grows without bound. Concretely, for any
real `M`, choosing `s` large makes `affineE a p (t + s) − affineE b q s > ↑M`. -/
theorem affine_decon_term_unbounded (a p b q t : ℝ≥0) (hqp : q < p) (M : ℝ) :
    ∃ s : ℝ≥0, ((M : ℝ) : EReal) < affineE a p (t + s) - affineE b q s := by
  -- coefficient of `s` is `(p - q : ℝ) > 0`
  have hd : (0 : ℝ) < (p : ℝ) - (q : ℝ) := by
    have : (q : ℝ) < (p : ℝ) := by exact_mod_cast hqp
    linarith
  -- pick `s ≥ (M - (a + p·t) + b) / (p - q)`, then clamp to ℝ≥0
  set c : ℝ := (M - ((a : ℝ) + p * t) + b) / ((p : ℝ) - q) with hc
  refine ⟨Real.toNNReal (c + 1), ?_⟩
  rw [affineE_apply, affineE_apply, coe_sub_coe_nnreal, EReal.coe_lt_coe_iff]
  have hs : (c + 1 : ℝ) ≤ (Real.toNNReal (c + 1) : ℝ) := Real.le_coe_toNNReal _
  -- want: M < (a + p·(t+s)) - (b + q·s) = (a+p·t) - b + (p-q)·s
  set s : ℝ := (Real.toNNReal (c + 1) : ℝ) with hsdef
  have hsc : c < s := lt_of_lt_of_le (by linarith) hs
  have key : (p - q) * c = M - ((a : ℝ) + p * t) + b := by
    rw [hc]; field_simp
  have hmul : (p - q) * c < (p - q) * s := by
    apply mul_lt_mul_of_pos_left hsc hd
  push_cast
  nlinarith [hmul, key]

/-- **Deconvolution of two affine curves, fast-dividend case.** When the dividend slope strictly
dominates (`q < p`), the `(min,plus)` deconvolution of `g(u) = a + p·u` by `h(u) = b + q·u` is
`⊤` (the supremum over `s` of the linearly-growing terms is unbounded). -/
theorem minDeconv_affine_top (a p b q t : ℝ≥0) (hqp : q < p) :
    minDeconv (affineE a p) (affineE b q) t = ⊤ := by
  -- `x = ⊤ ↔ ∀ M : ℝ, ↑M < x`: it suffices to exceed every finite `M`
  rw [EReal.eq_top_iff_forall_lt]
  intro M
  obtain ⟨s, hs⟩ := affine_decon_term_unbounded a p b q t hqp M
  exact lt_of_lt_of_le hs (sub_le_minDeconv (affineE a p) (affineE b q) t s)

/-! ## Restatements (faithfulness checks against the book's wording) -/

/-- Slow-divisor case, written out with explicit `EReal`-coerced affine functions: the
deconvolution of `u ↦ a + p·u` by `u ↦ b + q·u` (with `p ≤ q`) equals `(a + p·t) − b`. -/
example (a p b q t : ℝ≥0) (hpq : p ≤ q) :
    minDeconv (fun u => (((a + p * u : ℝ≥0) : ℝ) : EReal))
              (fun u => (((b + q * u : ℝ≥0) : ℝ) : EReal)) t
      = (((a + p * t : ℝ≥0) : ℝ) : EReal) - (((b : ℝ≥0) : ℝ) : EReal) :=
  minDeconv_affine_le a p b q t hpq

/-- Fast-dividend case (`q < p`): the deconvolution is `⊤`. -/
example (a p b q t : ℝ≥0) (hqp : q < p) :
    minDeconv (fun u => (((a + p * u : ℝ≥0) : ℝ) : EReal))
              (fun u => (((b + q * u : ℝ≥0) : ℝ) : EReal)) t = ⊤ :=
  minDeconv_affine_top a p b q t hqp

/-- Two pure-rate curves (`a = b = 0`, `p ≤ q`): the deconvolution is the finite value `p·t`
(the latency-free specialization, the shape that recurs in Lemma 4.6's segment pieces). -/
example (p q t : ℝ≥0) (hpq : p ≤ q) :
    minDeconv (affineE 0 p) (affineE 0 q) t = (((p * t : ℝ≥0) : ℝ) : EReal) := by
  rw [minDeconv_affine_le 0 p 0 q t hpq]; simp

end DeepWiki
