import DeepWiki.NetworkCalculus.Convex
import DeepWiki.NetworkCalculus.FunctionDioids

/-! # Convolution of convex curves is convex (Prop 3.13, the `f ∗ g` part)
The infimal-convolution closure of `IsConvexEReal`: the `(min,+)` convolution of two **nonnegative**
convex curves is convex. (The pointwise `+`/`max` parts are `IsConvexEReal.add`/`.sup`.) The proof
needs an `EReal` `⨅`-arithmetic layer — a nonnegative scalar and a nonnegative constant each push
through an infimum — which Mathlib supplies for `ℝ≥0∞` but not `EReal`; it is built here for
nonnegative families, where the `⊤`/`⊥` indeterminacies of `EReal` do not arise. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- `EReal`: a nonnegative real scalar pushes through an infimum,
`↑c * ⨅ i, f i = ⨅ i, ↑c * f i` (`0 ≤ c`). -/
theorem mul_iInf_coe_nonneg {ι : Type*} [Nonempty ι] {c : ℝ} (hc : 0 ≤ c) (f : ι → EReal) :
    (c : EReal) * ⨅ i, f i = ⨅ i, (c : EReal) * f i := by
  rcases hc.lt_or_eq with hpos | h0
  · have hc0 : (0 : EReal) ≤ (c : EReal) := by exact_mod_cast hpos.le
    have hcinv0 : (0 : EReal) ≤ ((c⁻¹ : ℝ) : EReal) := by exact_mod_cast (inv_pos.2 hpos).le
    have hcc : (c : EReal) * ((c⁻¹ : ℝ) : EReal) = 1 := by
      rw [← EReal.coe_mul, mul_inv_cancel₀ hpos.ne', EReal.coe_one]
    refine le_antisymm (le_iInf fun i => mul_le_mul_of_nonneg_left (iInf_le f i) hc0) ?_
    have key : ((c⁻¹ : ℝ) : EReal) * ⨅ i, (c : EReal) * f i ≤ ⨅ i, f i := by
      refine le_iInf fun i => ?_
      calc ((c⁻¹ : ℝ) : EReal) * ⨅ j, (c : EReal) * f j
          ≤ ((c⁻¹ : ℝ) : EReal) * ((c : EReal) * f i) :=
            mul_le_mul_of_nonneg_left (iInf_le _ i) hcinv0
        _ = f i := by rw [← mul_assoc, mul_comm ((c⁻¹ : ℝ) : EReal) (c : EReal), hcc, one_mul]
    have hrw : (c : EReal) * (((c⁻¹ : ℝ) : EReal) * ⨅ i, (c : EReal) * f i)
        = ⨅ i, (c : EReal) * f i := by rw [← mul_assoc, hcc, one_mul]
    calc ⨅ i, (c : EReal) * f i
        = (c : EReal) * (((c⁻¹ : ℝ) : EReal) * ⨅ i, (c : EReal) * f i) := hrw.symm
      _ ≤ (c : EReal) * ⨅ i, f i := mul_le_mul_of_nonneg_left key hc0
  · simp only [← h0, EReal.coe_zero, zero_mul, iInf_const]

/-- `EReal`: addition by a nonnegative constant pushes through an infimum of a nonnegative family,
`(⨅ i, f i) + c = ⨅ i, (f i + c)`. -/
theorem iInf_add_of_nonneg {ι : Type*} [Nonempty ι] {f : ι → EReal} (hf : ∀ i, 0 ≤ f i)
    {c : EReal} (hc : 0 ≤ c) :
    (⨅ i, f i) + c = ⨅ i, (f i + c) := by
  have hinf0 : (0 : EReal) ≤ ⨅ i, f i := le_iInf hf
  have hinfb : (⨅ i, f i) ≠ ⊥ := (EReal.bot_lt_zero.trans_le hinf0).ne'
  refine le_antisymm (le_iInf fun i => add_le_add (iInf_le f i) (le_refl _)) ?_
  by_cases hct : c = ⊤
  · subst hct
    have h1 : ∀ i, f i + (⊤ : EReal) = ⊤ :=
      fun i => EReal.add_top_of_ne_bot (EReal.bot_lt_zero.trans_le (hf i)).ne'
    rw [EReal.add_top_of_ne_bot hinfb]
    simp only [h1, iInf_const, le_refl]
  · have hcb : c ≠ ⊥ := (EReal.bot_lt_zero.trans_le hc).ne'
    obtain ⟨r, rfl⟩ : ∃ r : ℝ, c = (r : EReal) := ⟨c.toReal, (EReal.coe_toReal hct hcb).symm⟩
    have cancel : ∀ x : EReal, x + (r : EReal) + (-(r : EReal)) = x := fun x => by
      induction x using EReal.rec with
      | bot => rw [EReal.bot_add, EReal.bot_add]
      | top =>
          rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot r),
            EReal.top_add_of_ne_bot (by rw [← EReal.coe_neg]; exact EReal.coe_ne_bot _)]
      | coe s => rw [← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_add]; congr 1; ring
    have hstep : (⨅ i, (f i + (r : EReal))) + (-(r : EReal)) ≤ ⨅ i, f i :=
      le_iInf fun i => by
        calc (⨅ j, (f j + (r : EReal))) + (-(r : EReal))
            ≤ (f i + (r : EReal)) + (-(r : EReal)) := add_le_add (iInf_le _ i) (le_refl _)
          _ = f i := cancel (f i)
    calc ⨅ i, (f i + (r : EReal))
        = ((⨅ i, (f i + (r : EReal))) + (-(r : EReal))) + (r : EReal) := by
          rw [add_assoc, ← EReal.coe_neg, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]
      _ ≤ (⨅ i, f i) + (r : EReal) := add_le_add hstep (le_refl _)

/-- `EReal`: a nonnegative constant pushes through an infimum of a nonnegative family on the left. -/
theorem add_iInf_of_nonneg {ι : Type*} [Nonempty ι] {c : EReal} (hc : 0 ≤ c)
    {f : ι → EReal} (hf : ∀ i, 0 ≤ f i) :
    c + ⨅ i, f i = ⨅ i, (c + f i) := by
  simp only [add_comm c]
  exact iInf_add_of_nonneg hf hc

/-- **Proposition 3.13**, convolution: the `(min,+)` convolution of two nonnegative convex curves is
convex. The dioid sum (`min`) and pointwise `+` parts are `IsConvexEReal.sup`/`.add`. (Plain name,
not dot-notation: `IsConvexEReal.minConv` would clash with the `minConv` definition.) -/
theorem isConvexEReal_minConv {f g : ℝ≥0 → EReal}
    (hf : IsConvexEReal f) (hg : IsConvexEReal g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    IsConvexEReal (minConv f g) := by
  intro a b p hp
  haveI : Nonempty {q : ℝ≥0 × ℝ≥0 // q.1 + q.2 = a} := ⟨⟨(a, 0), add_zero a⟩⟩
  haveI : Nonempty {q : ℝ≥0 × ℝ≥0 // q.1 + q.2 = b} := ⟨⟨(b, 0), add_zero b⟩⟩
  have hpe : (0 : ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have hqe : (0 : ℝ) ≤ ((1 - p : ℝ≥0) : ℝ) := (1 - p : ℝ≥0).coe_nonneg
  have mul_nn : ∀ (x y : EReal), 0 ≤ x → 0 ≤ y → 0 ≤ x * y :=
    fun x y hx hy => by simpa using mul_le_mul_of_nonneg_left hy hx
  -- nonnegativity of the scaled split values
  have hAnn : ∀ sa : {q : ℝ≥0 × ℝ≥0 // q.1 + q.2 = a},
      (0 : EReal) ≤ ((p : ℝ) : EReal) * (f sa.1.1 + g sa.1.2) :=
    fun sa => mul_nn _ _ (by exact_mod_cast hpe) (add_nonneg (hf0 _) (hg0 _))
  have hBnn : ∀ sb : {q : ℝ≥0 × ℝ≥0 // q.1 + q.2 = b},
      (0 : EReal) ≤ (((1 - p : ℝ≥0) : ℝ) : EReal) * (f sb.1.1 + g sb.1.2) :=
    fun sb => mul_nn _ _ (by exact_mod_cast hqe) (add_nonneg (hf0 _) (hg0 _))
  have hBinf : (0 : EReal) ≤ ⨅ sb : {q : ℝ≥0 × ℝ≥0 // q.1 + q.2 = b},
      (((1 - p : ℝ≥0) : ℝ) : EReal) * (f sb.1.1 + g sb.1.2) := le_iInf hBnn
  -- push the two scalars into the convolution infima, then merge the two sums
  rw [show (minConv f g a) = ⨅ sa : {q : ℝ≥0 × ℝ≥0 // q.1 + q.2 = a}, (f sa.1.1 + g sa.1.2) from rfl,
      show (minConv f g b) = ⨅ sb : {q : ℝ≥0 × ℝ≥0 // q.1 + q.2 = b}, (f sb.1.1 + g sb.1.2) from rfl,
      mul_iInf_coe_nonneg hpe, mul_iInf_coe_nonneg hqe,
      iInf_add_of_nonneg hAnn hBinf]
  refine le_iInf fun sa => ?_
  rw [add_iInf_of_nonneg (hAnn sa) hBnn]
  refine le_iInf fun sb => ?_
  -- per-split bound: the combined split is convex-combination optimal
  have hsplit : (p * sa.1.1 + (1 - p) * sb.1.1) + (p * sa.1.2 + (1 - p) * sb.1.2)
      = p * a + (1 - p) * b := by
    have key : p * sa.1.1 + (1 - p) * sb.1.1 + (p * sa.1.2 + (1 - p) * sb.1.2)
        = p * (sa.1.1 + sa.1.2) + (1 - p) * (sb.1.1 + sb.1.2) := by
      generalize (1 - p : ℝ≥0) = c; ring
    rw [key, sa.2, sb.2]
  calc minConv f g (p * a + (1 - p) * b)
      ≤ f (p * sa.1.1 + (1 - p) * sb.1.1) + g (p * sa.1.2 + (1 - p) * sb.1.2) :=
        minConv_le_add f g hsplit
    _ ≤ (((p : ℝ) : EReal) * f sa.1.1 + (((1 - p : ℝ≥0) : ℝ) : EReal) * f sb.1.1)
          + (((p : ℝ) : EReal) * g sa.1.2 + (((1 - p : ℝ≥0) : ℝ) : EReal) * g sb.1.2) :=
        add_le_add (hf sa.1.1 sb.1.1 p hp) (hg sa.1.2 sb.1.2 p hp)
    _ = ((p : ℝ) : EReal) * (f sa.1.1 + g sa.1.2)
          + (((1 - p : ℝ≥0) : ℝ) : EReal) * (f sb.1.1 + g sb.1.2) := by
        rw [add_add_add_comm,
          ← EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hpe) (EReal.coe_ne_top _),
          ← EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hqe) (EReal.coe_ne_top _)]

-- Restatement (book Prop 3.13, convolution): convolution preserves convexity of nonneg curves.
example (f g : ℝ≥0 → EReal) (hf : IsConvexEReal f) (hg : IsConvexEReal g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    IsConvexEReal (minConv f g) :=
  isConvexEReal_minConv hf hg hf0 hg0

end DeepWiki
