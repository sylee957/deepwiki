import DeepWiki.NetworkCalculus.ConcaveDioid
import DeepWiki.NetworkCalculus.ConcaveProps
import DeepWiki.NetworkCalculus.ClosuresEReal
import DeepWiki.NetworkCalculus.RealCurves

/-! # Piecewise-linear concave functions in normal form (Definition 4.1)
A concave piecewise-linear function is the pointwise infimum of finitely many *token-bucket*
curves `γ_{r,b}(t) = (r·t + b) ⊓ convUnit` (`0` at the origin, the affine `r·t + b` for `t > 0`).
This file lays the data layer for DNC §4.2: the token-bucket `EReal` curve `tbEReal` and its
concavity, the inf-of-token-buckets evaluation `concaveNFEval`, its concavity (Proposition 4.1,
item 1), and the **normal-form** predicate of Definition 4.1 (strictly decreasing rates +
irredundancy). The segment representation, intersection points, and the convolution
segment-merge algorithm build on this layer. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Function

/-! ## The token-bucket `EReal` curve `γ_{r,b}` -/

/-- The token-bucket curve `γ_{r,b}` as an `EReal` curve: the affine `r·t + b` met with the
convolution unit, giving `0` at the origin and `r·t + b` for `t > 0`. -/
noncomputable def tbEReal (r b : ℝ≥0) : ℝ≥0 → EReal :=
  (rateEReal r + const ℝ≥0 (((b : ℝ)) : EReal)) ⊓ convUnitEReal

/-- The constant-rate `EReal` curve `t ↦ r·t` is concave (it is affine, so the chord holds
with equality). -/
theorem isConcaveEReal_rateEReal (r : ℝ≥0) : IsConcaveEReal (rateEReal r) := by
  intro s t p hp
  simp only [rateEReal]
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
  apply le_of_eq
  push_cast [NNReal.coe_sub hp]
  ring

/-- The token-bucket curve `γ_{r,b}` is concave: an affine curve met with the (concave)
convolution unit. -/
theorem isConcaveEReal_tbEReal (r b : ℝ≥0) : IsConcaveEReal (tbEReal r b) :=
  IsConcaveEReal.inf _ _
    (IsConcaveEReal.add _ _ (isConcaveEReal_rateEReal r) (isConcaveEReal_const (b : ℝ)))
    isConcaveEReal_convUnitEReal

/-- `γ_{r,b}(0) = 0` (the convolution unit pins the origin to `0`, below the burst `b ≥ 0`). -/
@[simp] theorem tbEReal_zero (r b : ℝ≥0) : tbEReal r b 0 = 0 := by
  unfold tbEReal
  rw [Pi.inf_apply, convUnitEReal, if_pos rfl, inf_eq_right, Pi.add_apply, const_apply]
  have h1 : (0 : EReal) ≤ rateEReal r 0 := by
    simp only [rateEReal, mul_zero, NNReal.coe_zero, EReal.coe_zero]; rfl
  have h2 : (0 : EReal) ≤ (((b : ℝ)) : EReal) := by exact_mod_cast b.coe_nonneg
  exact add_nonneg h1 h2

/-- `γ_{r,b}(t) = r·t + b` for `t > 0` (off the origin the convolution unit is `⊤`). -/
theorem tbEReal_pos {t : ℝ≥0} (ht : t ≠ 0) (r b : ℝ≥0) :
    tbEReal r b t = rateEReal r t + (((b : ℝ)) : EReal) := by
  unfold tbEReal
  rw [Pi.inf_apply, convUnitEReal, if_neg ht, Pi.add_apply, const_apply, inf_eq_left]
  exact le_top

/-- Token-buckets are monotone in both parameters off the origin: a smaller rate and a
smaller burst give a pointwise-smaller curve at every `t > 0`. -/
theorem tbEReal_mono_of {r r' b b' t : ℝ≥0} (ht : t ≠ 0) (hr : r ≤ r') (hb : b ≤ b') :
    tbEReal r b t ≤ tbEReal r' b' t := by
  rw [tbEReal_pos ht, tbEReal_pos ht]
  refine add_le_add ?_ ?_
  · simp only [rateEReal]
    rw [EReal.coe_le_coe_iff, NNReal.coe_le_coe]
    gcongr
  · exact_mod_cast hb

/-! ## Intersection points (the `tᵢ` sequence of Definition 4.1) -/

/-- The crossing time of two token-buckets `γ_{r,b}` and `γ_{r',b'}`:
`t = (b' − b)/(r − r')`, the point where the affine parts `b + r·t` and `b' + r'·t` agree
(the book's `tᵢ` for adjacent buckets, with `r > r'` and `b < b'`). -/
noncomputable def tbCross (r b r' b' : ℝ≥0) : ℝ≥0 := (b' - b) / (r - r')

/-- The crossing time is positive when the rates strictly decrease and the bursts strictly
increase (`r' < r`, `b < b'`). -/
theorem tbCross_pos {r b r' b' : ℝ≥0} (hr : r' < r) (hb : b < b') : 0 < tbCross r b r' b' :=
  div_pos (tsub_pos_of_lt hb) (tsub_pos_of_lt hr)

/-- The affine parts agree at the crossing: `b + r·t = b' + r'·t` at `t = (b'−b)/(r−r')`. -/
theorem tb_affine_eq_at_cross {r b r' b' : ℝ≥0} (hr : r' < r) (hb : b ≤ b') :
    b + r * tbCross r b r' b' = b' + r' * tbCross r b r' b' := by
  have hne : (r : ℝ) - r' ≠ 0 := by
    have : (r' : ℝ) < r := by exact_mod_cast hr
    linarith
  have ht : ((tbCross r b r' b' : ℝ≥0) : ℝ) = ((b' : ℝ) - b) / ((r : ℝ) - r') := by
    rw [tbCross, NNReal.coe_div, NNReal.coe_sub hb, NNReal.coe_sub hr.le]
  rw [← NNReal.coe_inj]
  push_cast [ht]
  field_simp
  ring

/-- The two token-buckets are equal at their crossing time `tbCross`. -/
theorem tbEReal_eq_at_cross {r b r' b' : ℝ≥0} (hr : r' < r) (hb : b ≤ b') :
    tbEReal r b (tbCross r b r' b') = tbEReal r' b' (tbCross r b r' b') := by
  rcases eq_or_lt_of_le hb with rfl | hblt
  · have h0 : tbCross r b r' b = 0 := by rw [tbCross, tsub_self, zero_div]
    rw [h0, tbEReal_zero, tbEReal_zero]
  · have htpos : tbCross r b r' b' ≠ 0 := (tbCross_pos hr hblt).ne'
    rw [tbEReal_pos htpos, tbEReal_pos htpos]
    have heq : r * tbCross r b r' b' + b = r' * tbCross r b r' b' + b' := by
      rw [add_comm (r * _) b, add_comm (r' * _) b']; exact tb_affine_eq_at_cross hr hb
    simp only [rateEReal]
    rw [← EReal.coe_add, ← EReal.coe_add, ← NNReal.coe_add, ← NNReal.coe_add, heq]

/-- Ordering across the crossing: with decreasing rates (`r' < r`) and `b ≤ b'`, the
high-rate/low-burst bucket `γ_{r,b}` is strictly below `γ_{r',b'}` exactly *before* the crossing
time. (So `γ_{r,b}` is the minimum on `(0, tbCross)` and `γ_{r',b'}` beyond it.) -/
theorem tb_lt_iff_lt_cross {r b r' b' : ℝ≥0} (hr : r' < r) (hb : b ≤ b') {t : ℝ≥0} (ht : t ≠ 0) :
    tbEReal r b t < tbEReal r' b' t ↔ t < tbCross r b r' b' := by
  rw [tbEReal_pos ht, tbEReal_pos ht]
  simp only [rateEReal]
  rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_lt_coe_iff, ← NNReal.coe_lt_coe, tbCross,
    NNReal.coe_div, NNReal.coe_sub hr.le, NNReal.coe_sub hb]
  have hrr : (0 : ℝ) < (r : ℝ) - r' := by
    have : (r' : ℝ) < r := by exact_mod_cast hr
    linarith
  rw [lt_div_iff₀ hrr]
  push_cast
  constructor <;> intro h <;> nlinarith [h]

/-- Ordering after the crossing: the low-rate/high-burst bucket `γ_{r',b'}` is strictly below
`γ_{r,b}` exactly *after* the crossing time. -/
theorem tb_gt_iff_cross_lt {r b r' b' : ℝ≥0} (hr : r' < r) (hb : b ≤ b') {t : ℝ≥0} (ht : t ≠ 0) :
    tbEReal r' b' t < tbEReal r b t ↔ tbCross r b r' b' < t := by
  rw [tbEReal_pos ht, tbEReal_pos ht]
  simp only [rateEReal]
  rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_lt_coe_iff, ← NNReal.coe_lt_coe, tbCross,
    NNReal.coe_div, NNReal.coe_sub hr.le, NNReal.coe_sub hb]
  have hrr : (0 : ℝ) < (r : ℝ) - r' := by
    have : (r' : ℝ) < r := by exact_mod_cast hr
    linarith
  rw [div_lt_iff₀ hrr]
  push_cast
  constructor <;> intro h <;> nlinarith [h]

/-- The crossing points increase (the local step of Proposition 4.1, item 3): if the middle
bucket `γ_{r₂,b₂}` is the strict minimum of three consecutive buckets at some positive time, its
two crossing points satisfy `tbCross γ₁γ₂ < tbCross γ₂γ₃`. Otherwise `γ₂` would be dominated by
`min(γ₁,γ₃)` everywhere, contradicting irredundancy. -/
theorem tbCross_lt_tbCross_of_strictMin {r₁ b₁ r₂ b₂ r₃ b₃ : ℝ≥0}
    (h₁₂ : r₂ < r₁) (h₂₃ : r₃ < r₂) (hb₁₂ : b₁ ≤ b₂) (hb₂₃ : b₂ ≤ b₃) {t : ℝ≥0} (ht : t ≠ 0)
    (hm₁ : tbEReal r₂ b₂ t < tbEReal r₁ b₁ t) (hm₃ : tbEReal r₂ b₂ t < tbEReal r₃ b₃ t) :
    tbCross r₁ b₁ r₂ b₂ < tbCross r₂ b₂ r₃ b₃ :=
  lt_trans ((tb_gt_iff_cross_lt h₁₂ hb₁₂ ht).mp hm₁) ((tb_lt_iff_lt_cross h₂₃ hb₂₃ ht).mp hm₃)

/-- Up to the crossing, the high-rate/low-burst bucket is `≤` the other (the `≤` form of
`tb_lt_iff_lt_cross`, including the endpoints `t = 0` and `t = tbCross`). -/
theorem tb_le_of_le_cross {r b r' b' : ℝ≥0} (hr : r' < r) (hb : b ≤ b') {t : ℝ≥0}
    (ht : t ≤ tbCross r b r' b') : tbEReal r b t ≤ tbEReal r' b' t := by
  rcases eq_or_ne t 0 with rfl | h0
  · rw [tbEReal_zero, tbEReal_zero]
  · rcases lt_or_eq_of_le ht with hlt | heq
    · exact ((tb_lt_iff_lt_cross hr hb h0).mpr hlt).le
    · rw [heq]; exact (tbEReal_eq_at_cross hr hb).le

/-- Beyond the crossing, the low-rate/high-burst bucket is `≤` the other. -/
theorem tb_ge_of_cross_le {r b r' b' : ℝ≥0} (hr : r' < r) (hb : b ≤ b') {t : ℝ≥0}
    (ht : tbCross r b r' b' ≤ t) : tbEReal r' b' t ≤ tbEReal r b t := by
  rcases eq_or_ne t 0 with rfl | h0
  · rw [tbEReal_zero, tbEReal_zero]
  · rcases lt_or_eq_of_le ht with hlt | heq
    · exact ((tb_gt_iff_cross_lt hr hb h0).mpr hlt).le
    · rw [← heq]; exact (tbEReal_eq_at_cross hr hb).ge

/-! ## Concave PWL evaluation and Definition 4.1 (normal form) -/

/-- A list of `(rate, burst)` pairs evaluated as a concave piecewise-linear curve: the
pointwise infimum of the token-buckets `γ_{rᵢ,bᵢ}` (`topCurve = +∞` for the empty list). -/
noncomputable def concaveNFEval (l : List (ℝ≥0 × ℝ≥0)) : ℝ≥0 → EReal :=
  l.foldr (fun rb acc => tbEReal rb.1 rb.2 ⊓ acc) topCurve

@[simp] theorem concaveNFEval_nil : concaveNFEval [] = topCurve := rfl

@[simp] theorem concaveNFEval_cons (rb : ℝ≥0 × ℝ≥0) (l : List (ℝ≥0 × ℝ≥0)) :
    concaveNFEval (rb :: l) = tbEReal rb.1 rb.2 ⊓ concaveNFEval l := rfl

/-- **Proposition 4.1, item 1.** A concave piecewise-linear function (the infimum of token
buckets) is concave — the infimum of concave curves is concave. -/
theorem isConcaveEReal_concaveNFEval (l : List (ℝ≥0 × ℝ≥0)) :
    IsConcaveEReal (concaveNFEval l) := by
  induction l with
  | nil => exact isConcaveEReal_topCurve
  | cons rb l ih =>
      rw [concaveNFEval_cons]
      exact IsConcaveEReal.inf _ _ (isConcaveEReal_tbEReal rb.1 rb.2) ih

/-- The constant-rate curve `t ↦ r·t` is nondecreasing. -/
theorem monotone_rateEReal (r : ℝ≥0) : Monotone (rateEReal r) := by
  intro a b hab
  simp only [rateEReal]
  rw [EReal.coe_le_coe_iff, NNReal.coe_le_coe]
  gcongr

/-- The convolution unit `convUnitEReal` (`0` at the origin, `⊤` elsewhere) is nondecreasing. -/
theorem monotone_convUnitEReal : Monotone convUnitEReal := by
  intro a b hab
  unfold convUnitEReal
  by_cases ha : a = 0
  · by_cases hb : b = 0 <;> simp [ha, hb]
  · have hb : b ≠ 0 := by rintro rfl; exact ha (le_antisymm hab zero_le)
    simp [ha, hb]

/-- Each token-bucket curve `γ_{r,b}` is nondecreasing. -/
theorem monotone_tbEReal (r b : ℝ≥0) : Monotone (tbEReal r b) := by
  unfold tbEReal
  exact ((monotone_rateEReal r).add_const _).inf monotone_convUnitEReal

/-- A concave piecewise-linear function is nondecreasing — an infimum of nondecreasing
token-buckets. -/
theorem monotone_concaveNFEval (l : List (ℝ≥0 × ℝ≥0)) : Monotone (concaveNFEval l) := by
  induction l with
  | nil => exact monotone_const
  | cons rb l ih => rw [concaveNFEval_cons]; exact (monotone_tbEReal rb.1 rb.2).inf ih

/-- Each token-bucket curve is non-negative. -/
theorem tbEReal_nonneg (r b : ℝ≥0) (t : ℝ≥0) : 0 ≤ tbEReal r b t := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [tbEReal_zero]
  · rw [tbEReal_pos ht]
    exact add_nonneg (by simp only [rateEReal]; exact_mod_cast (r * t).coe_nonneg)
      (by exact_mod_cast b.coe_nonneg)

/-- A concave piecewise-linear function is non-negative. -/
theorem concaveNFEval_nonneg (l : List (ℝ≥0 × ℝ≥0)) (t : ℝ≥0) : 0 ≤ concaveNFEval l t := by
  induction l with
  | nil => exact le_top
  | cons rb l ih =>
      rw [concaveNFEval_cons, Pi.inf_apply]
      exact le_inf (tbEReal_nonneg rb.1 rb.2 t) ih

/-- The evaluation is `≤` every member token-bucket (it is their infimum). -/
theorem concaveNFEval_le_of_mem {l : List (ℝ≥0 × ℝ≥0)} {s : ℝ≥0 × ℝ≥0} (hs : s ∈ l) (t : ℝ≥0) :
    concaveNFEval l t ≤ tbEReal s.1 s.2 t := by
  induction l with
  | nil => exact absurd hs (by simp)
  | cons a l ih =>
      rw [concaveNFEval_cons, Pi.inf_apply]
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact inf_le_left
      · exact le_trans inf_le_right (ih hs')

/-- A lower bound for every member token-bucket is a lower bound for the evaluation. -/
theorem le_concaveNFEval {l : List (ℝ≥0 × ℝ≥0)} {x : EReal} {t : ℝ≥0}
    (h : ∀ s ∈ l, x ≤ tbEReal s.1 s.2 t) : x ≤ concaveNFEval l t := by
  induction l with
  | nil => rw [concaveNFEval_nil]; exact le_top
  | cons a l ih =>
      rw [concaveNFEval_cons, Pi.inf_apply]
      exact le_inf (h a List.mem_cons_self) (ih (fun s hs => h s (List.mem_cons_of_mem a hs)))

/-- **Proposition 4.1, item 4** (pointwise envelope form): wherever a token-bucket of the list
is the minimum, the concave PWL function equals it. Combined with the crossing ordering
(`tb_le_of_le_cross` / `tb_ge_of_cross_le`), this gives the book's per-interval formula
`⋀ⱼγⱼ = γᵢ` on `[tᵢ, tᵢ₊₁]` once `γᵢ` is shown minimal there. -/
theorem concaveNFEval_eq_of_isMin {l : List (ℝ≥0 × ℝ≥0)} {s : ℝ≥0 × ℝ≥0} (hs : s ∈ l) {t : ℝ≥0}
    (hmin : ∀ s' ∈ l, tbEReal s.1 s.2 t ≤ tbEReal s'.1 s'.2 t) :
    concaveNFEval l t = tbEReal s.1 s.2 t :=
  le_antisymm (concaveNFEval_le_of_mem hs t) (le_concaveNFEval hmin)

/-- **Proposition 4.1, item 4** (general piecewise form): a non-empty concave PWL function equals
*one of its token-buckets* at every time — the minimum of a finite list of buckets is always
attained. (The book's per-interval statement additionally identifies *which* bucket, via the
crossing intervals.) -/
theorem exists_mem_concaveNFEval_eq {l : List (ℝ≥0 × ℝ≥0)} (hne : l ≠ []) (t : ℝ≥0) :
    ∃ s ∈ l, concaveNFEval l t = tbEReal s.1 s.2 t := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a l ih =>
      rcases eq_or_ne l [] with rfl | hl
      · refine ⟨a, List.mem_cons_self, ?_⟩
        rw [concaveNFEval_cons, concaveNFEval_nil, Pi.inf_apply, inf_eq_left]; exact le_top
      · obtain ⟨s, hs, hseq⟩ := ih hl
        rw [concaveNFEval_cons, Pi.inf_apply, hseq]
        rcases le_total (tbEReal a.1 a.2 t) (tbEReal s.1 s.2 t) with hle | hle
        · exact ⟨a, List.mem_cons_self, inf_eq_left.mpr hle⟩
        · exact ⟨s, List.mem_cons_of_mem a hs, inf_eq_right.mpr hle⟩

/-- **Proposition 4.1, item 4** for two buckets (the `n = 2` per-interval formula): up to the
crossing the concave PWL function `γ_{r,b} ⊓ γ_{r',b'}` equals the high-rate bucket `γ_{r,b}`. -/
theorem concaveNFEval_pair_eq_left {r b r' b' : ℝ≥0} (hr : r' < r) (hb : b ≤ b') {t : ℝ≥0}
    (ht : t ≤ tbCross r b r' b') :
    concaveNFEval [(r, b), (r', b')] t = tbEReal r b t := by
  refine concaveNFEval_eq_of_isMin (s := (r, b)) (by simp) ?_
  intro s' hs'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
  rcases hs' with rfl | rfl
  · exact le_refl _
  · exact tb_le_of_le_cross hr hb ht

/-- **Proposition 4.1, item 4** for two buckets: beyond the crossing the function equals the
low-rate bucket `γ_{r',b'}`. -/
theorem concaveNFEval_pair_eq_right {r b r' b' : ℝ≥0} (hr : r' < r) (hb : b ≤ b') {t : ℝ≥0}
    (ht : tbCross r b r' b' ≤ t) :
    concaveNFEval [(r, b), (r', b')] t = tbEReal r' b' t := by
  refine concaveNFEval_eq_of_isMin (s := (r', b')) (by simp) ?_
  intro s' hs'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
  rcases hs' with rfl | rfl
  · exact tb_ge_of_cross_le hr hb ht
  · exact le_refl _

/-- **Definition 4.1** (Concave piecewise-linear normal form). A list `[(r₁,b₁), …, (rₙ,bₙ)]`
of token-bucket parameters is in *concave normal form* when

* the rates are strictly decreasing along the list (`i < j ⟹ rᵢ > rⱼ`, equation [4.2]), and
* no token-bucket is redundant: each is the *strict* minimum at some positive time
  (equation [4.3]).

The evaluation `f = ⋀ᵢ γ_{rᵢ,bᵢ}` is then `concaveNFEval l`. -/
def IsConcaveNormalForm (l : List (ℝ≥0 × ℝ≥0)) : Prop :=
  l.Pairwise (fun a b => b.1 < a.1) ∧
  ∀ i : Fin l.length, ∃ t : ℝ≥0, 0 < t ∧
    ∀ j : Fin l.length, j ≠ i →
      tbEReal (l.get i).1 (l.get i).2 t < tbEReal (l.get j).1 (l.get j).2 t

/-- **Proposition 4.1, item 2.** In a concave normal form the bursts are strictly increasing
along the list (`bᵢ < bⱼ` for `i < j`). If `bᵢ ≥ bⱼ` while `rᵢ > rⱼ` then `γᵢ ≥ γⱼ` pointwise,
making `γᵢ` redundant — contradicting irredundancy at `i`. -/
theorem IsConcaveNormalForm.burst_strictMono {l : List (ℝ≥0 × ℝ≥0)}
    (h : IsConcaveNormalForm l) : l.Pairwise (fun a b => a.2 < b.2) := by
  obtain ⟨hrate, hirr⟩ := h
  rw [List.pairwise_iff_get]
  intro i j hij
  have hr : (l.get j).1 < (l.get i).1 := (List.pairwise_iff_get.mp hrate) i j hij
  obtain ⟨t, ht, hmin⟩ := hirr i
  have hlt : tbEReal (l.get i).1 (l.get i).2 t < tbEReal (l.get j).1 (l.get j).2 t :=
    hmin j hij.ne'
  by_contra hb
  rw [not_lt] at hb
  exact absurd (lt_of_lt_of_le hlt (tbEReal_mono_of (ne_of_gt ht) hr.le hb)) (lt_irrefl _)

/-- **Proposition 4.1, item 3.** In a concave normal form the intersection points are strictly
increasing: for every `i` with `i+2 < n`, the consecutive crossings satisfy
`tbCross γᵢ γᵢ₊₁ < tbCross γᵢ₊₁ γᵢ₊₂`. (With `t₁ = 0` and `tᵢ` the `(i−1)`-th crossing this is the
book's `tᵢ < tᵢ₊₁`.) The middle bucket's irredundancy witness places it strictly below both
neighbours at one time, which sandwiches that time between the two crossings. -/
theorem IsConcaveNormalForm.cross_strictMono {l : List (ℝ≥0 × ℝ≥0)} (h : IsConcaveNormalForm l)
    {i : ℕ} (hi : i + 2 < l.length) :
    tbCross (l.get ⟨i, by omega⟩).1 (l.get ⟨i, by omega⟩).2
            (l.get ⟨i + 1, by omega⟩).1 (l.get ⟨i + 1, by omega⟩).2 <
    tbCross (l.get ⟨i + 1, by omega⟩).1 (l.get ⟨i + 1, by omega⟩).2
            (l.get ⟨i + 2, by omega⟩).1 (l.get ⟨i + 2, by omega⟩).2 := by
  obtain ⟨hrate, hirr⟩ := h
  have hget := List.pairwise_iff_get.mp hrate
  have hbget := List.pairwise_iff_get.mp (IsConcaveNormalForm.burst_strictMono ⟨hrate, hirr⟩)
  have hlt01 : (⟨i, by omega⟩ : Fin l.length) < ⟨i + 1, by omega⟩ := by rw [Fin.mk_lt_mk]; omega
  have hlt12 : (⟨i + 1, by omega⟩ : Fin l.length) < ⟨i + 2, by omega⟩ := by rw [Fin.mk_lt_mk]; omega
  obtain ⟨t, ht, hmin⟩ := hirr ⟨i + 1, by omega⟩
  exact tbCross_lt_tbCross_of_strictMin (hget _ _ hlt01) (hget _ _ hlt12)
    (hbget _ _ hlt01).le (hbget _ _ hlt12).le (ne_of_gt ht)
    (hmin ⟨i, by omega⟩ (Fin.ne_of_val_ne (by omega)))
    (hmin ⟨i + 2, by omega⟩ (Fin.ne_of_val_ne (by omega)))

/-! ## The per-interval formula (Proposition 4.1, item 4)

For a list in concave normal form, on the inter-crossing interval the matching token-bucket is
the pointwise minimum, so `concaveNFEval l` equals it there. The crux is *transitive
minimality*: index `i` beats every other index `j` at a time `t` between its two bounding
crossings — for `j > i` by chaining `tb_le_of_le_cross` along the (increasing) crossings, for
`j < i` by chaining `tb_ge_of_cross_le`. -/

/-- In a concave normal form, the rate strictly decreases across any index gap: `i < j ⟹
rⱼ < rᵢ`. -/
theorem IsConcaveNormalForm.rate_lt_of_lt {l : List (ℝ≥0 × ℝ≥0)} (h : IsConcaveNormalForm l)
    {i j : Fin l.length} (hij : i < j) : (l.get j).1 < (l.get i).1 :=
  (List.pairwise_iff_get.mp h.1) i j hij

/-- In a concave normal form, the burst strictly increases across any index gap: `i < j ⟹
bᵢ < bⱼ`. -/
theorem IsConcaveNormalForm.burst_lt_of_lt {l : List (ℝ≥0 × ℝ≥0)} (h : IsConcaveNormalForm l)
    {i j : Fin l.length} (hij : i < j) : (l.get i).2 < (l.get j).2 :=
  (List.pairwise_iff_get.mp h.burst_strictMono) i j hij

/-- **Transitive minimality, upward half.** If `t` is at most the `i`/`i+1` crossing then the
`i`-th bucket is `≤` every later bucket `i+k+1` at `t` (chaining `tb_le_of_le_cross` along the
increasing crossings). -/
theorem IsConcaveNormalForm.le_of_le_cross_succ {l : List (ℝ≥0 × ℝ≥0)} (h : IsConcaveNormalForm l)
    {t : ℝ≥0} {i k : ℕ} (hk : i + k + 1 < l.length)
    (ht : t ≤ tbCross (l.get ⟨i, by omega⟩).1 (l.get ⟨i, by omega⟩).2
                      (l.get ⟨i + 1, by omega⟩).1 (l.get ⟨i + 1, by omega⟩).2) :
    tbEReal (l.get ⟨i, by omega⟩).1 (l.get ⟨i, by omega⟩).2 t ≤
    tbEReal (l.get ⟨i + k + 1, hk⟩).1 (l.get ⟨i + k + 1, hk⟩).2 t := by
  induction k generalizing i with
  | zero =>
      have hlt : (⟨i, by omega⟩ : Fin l.length) < ⟨i + 1, by omega⟩ := by rw [Fin.mk_lt_mk]; omega
      exact tb_le_of_le_cross (h.rate_lt_of_lt hlt) (h.burst_lt_of_lt hlt).le ht
  | succ k ih =>
      -- base step `i ≤ i+1`, then `i+1 ≤ i+1+k+1` by IH at `i+1`
      have hlt : (⟨i, by omega⟩ : Fin l.length) < ⟨i + 1, by omega⟩ := by rw [Fin.mk_lt_mk]; omega
      have hstep : tbEReal (l.get ⟨i, by omega⟩).1 (l.get ⟨i, by omega⟩).2 t ≤
          tbEReal (l.get ⟨i + 1, by omega⟩).1 (l.get ⟨i + 1, by omega⟩).2 t :=
        tb_le_of_le_cross (h.rate_lt_of_lt hlt) (h.burst_lt_of_lt hlt).le ht
      -- carry the bound to the next crossing via `cross_strictMono`
      have ht' : t ≤ tbCross (l.get ⟨i + 1, by omega⟩).1 (l.get ⟨i + 1, by omega⟩).2
                              (l.get ⟨i + 2, by omega⟩).1 (l.get ⟨i + 2, by omega⟩).2 :=
        le_trans ht (h.cross_strictMono (by omega)).le
      have hrec : tbEReal (l.get ⟨i + 1, by omega⟩).1 (l.get ⟨i + 1, by omega⟩).2 t ≤
          tbEReal (l.get ⟨i + 1 + k + 1, by omega⟩).1 (l.get ⟨i + 1 + k + 1, by omega⟩).2 t :=
        ih (by omega) ht'
      have he : (⟨i + 1 + k + 1, by omega⟩ : Fin l.length) = ⟨i + (k + 1) + 1, hk⟩ := by
        simp only [Fin.mk.injEq]; omega
      rw [he] at hrec
      exact le_trans hstep hrec

/-- **Transitive minimality, downward half.** If `t` is at least the `i`/`i+1` crossing then the
`i+1`-th bucket is `≤` every earlier bucket `i-k` at `t` (chaining `tb_ge_of_cross_le` along the
increasing crossings). -/
theorem IsConcaveNormalForm.le_of_cross_le_pred {l : List (ℝ≥0 × ℝ≥0)} (h : IsConcaveNormalForm l)
    {t : ℝ≥0} {i k : ℕ} (hi : i + 1 < l.length) (hk : k ≤ i)
    (ht : tbCross (l.get ⟨i, by omega⟩).1 (l.get ⟨i, by omega⟩).2
                  (l.get ⟨i + 1, by omega⟩).1 (l.get ⟨i + 1, by omega⟩).2 ≤ t) :
    tbEReal (l.get ⟨i + 1, hi⟩).1 (l.get ⟨i + 1, hi⟩).2 t ≤
    tbEReal (l.get ⟨i - k, by omega⟩).1 (l.get ⟨i - k, by omega⟩).2 t := by
  induction k generalizing i with
  | zero =>
      have hlt : (⟨i, by omega⟩ : Fin l.length) < ⟨i + 1, by omega⟩ := by rw [Fin.mk_lt_mk]; omega
      simpa using tb_ge_of_cross_le (h.rate_lt_of_lt hlt) (h.burst_lt_of_lt hlt).le ht
  | succ k ih =>
      -- `i+1 ≤ i` (base), then `i ≤ i-(k+1)` by IH at `i-1`
      have hi1 : 1 ≤ i := by omega
      have hlt : (⟨i, by omega⟩ : Fin l.length) < ⟨i + 1, by omega⟩ := by rw [Fin.mk_lt_mk]; omega
      have hstep : tbEReal (l.get ⟨i + 1, hi⟩).1 (l.get ⟨i + 1, hi⟩).2 t ≤
          tbEReal (l.get ⟨i, by omega⟩).1 (l.get ⟨i, by omega⟩).2 t :=
        tb_ge_of_cross_le (h.rate_lt_of_lt hlt) (h.burst_lt_of_lt hlt).le ht
      -- previous crossing `(i-1)/i` is below the current one, hence below `t`
      have hcs : tbCross (l.get ⟨i - 1, by omega⟩).1 (l.get ⟨i - 1, by omega⟩).2
                          (l.get ⟨i - 1 + 1, by omega⟩).1 (l.get ⟨i - 1 + 1, by omega⟩).2 <
                 tbCross (l.get ⟨i - 1 + 1, by omega⟩).1 (l.get ⟨i - 1 + 1, by omega⟩).2
                          (l.get ⟨i - 1 + 2, by omega⟩).1 (l.get ⟨i - 1 + 2, by omega⟩).2 :=
        h.cross_strictMono (by omega)
      have he1 : (⟨i - 1 + 1, by omega⟩ : Fin l.length) = ⟨i, by omega⟩ := by simp only [Fin.mk.injEq]; omega
      have he2 : (⟨i - 1 + 2, by omega⟩ : Fin l.length) = ⟨i + 1, by omega⟩ := by
        simp only [Fin.mk.injEq]; omega
      rw [he1, he2] at hcs
      have ht' : tbCross (l.get ⟨i - 1, by omega⟩).1 (l.get ⟨i - 1, by omega⟩).2
                          (l.get ⟨i - 1 + 1, by omega⟩).1 (l.get ⟨i - 1 + 1, by omega⟩).2 ≤ t := by
        rw [he1]; exact le_trans hcs.le ht
      have hrec : tbEReal (l.get ⟨i - 1 + 1, by omega⟩).1 (l.get ⟨i - 1 + 1, by omega⟩).2 t ≤
          tbEReal (l.get ⟨i - 1 - k, by omega⟩).1 (l.get ⟨i - 1 - k, by omega⟩).2 t :=
        ih (by omega) (by omega) ht'
      have he3 : (⟨i - 1 + 1, by omega⟩ : Fin l.length) = ⟨i, by omega⟩ := by simp only [Fin.mk.injEq]; omega
      have he4 : (⟨i - 1 - k, by omega⟩ : Fin l.length) = ⟨i - (k + 1), by omega⟩ := by
        simp only [Fin.mk.injEq]; omega
      rw [he3, he4] at hrec
      exact le_trans hstep hrec

/-- **Per-interval minimality (Proposition 4.1, item 4, crux).** For a list in concave normal
form, index `i` realizes the pointwise minimum at every time `t` of its inter-crossing interval:
`tᵢ ≤ t ≤ tᵢ₊₁`, encoded by the two conditional crossing bounds (`hlo`: `tᵢ = tbCross(i-1,i) ≤ t`
when `i ≥ 1`, with `t₁ = 0` vacuous at `i = 0`; `hhi`: `t ≤ tᵢ₊₁ = tbCross(i,i+1)` when
`i+1 < n`, with `tₙ₊₁ = ∞` vacuous at `i = n-1`). Then `γᵢ(t) ≤ γⱼ(t)` for every `j`. -/
theorem IsConcaveNormalForm.isMin_of_mem_interval {l : List (ℝ≥0 × ℝ≥0)}
    (h : IsConcaveNormalForm l) {t : ℝ≥0} (i : Fin l.length)
    (hlo : ∀ hi : 1 ≤ i.val, tbCross (l.get ⟨i.val - 1, by omega⟩).1 (l.get ⟨i.val - 1, by omega⟩).2
                                      (l.get i).1 (l.get i).2 ≤ t)
    (hhi : ∀ hi : i.val + 1 < l.length, t ≤ tbCross (l.get i).1 (l.get i).2
                                          (l.get ⟨i.val + 1, hi⟩).1 (l.get ⟨i.val + 1, hi⟩).2)
    (j : Fin l.length) :
    tbEReal (l.get i).1 (l.get i).2 t ≤ tbEReal (l.get j).1 (l.get j).2 t := by
  rcases lt_trichotomy j.val i.val with hji | hji | hij
  · -- `j < i`: downward chaining with the lower crossing bound (set `m = i-1`, `k = m - j`)
    have hi1 : 1 ≤ i.val := by omega
    have hmlen : i.val - 1 + 1 < l.length := by omega
    have hkle : i.val - 1 - j.val ≤ i.val - 1 := by omega
    have hei : i = ⟨i.val - 1 + 1, hmlen⟩ := by simp only [Fin.ext_iff]; omega
    have hej : j = ⟨i.val - 1 - (i.val - 1 - j.val), by omega⟩ := by simp only [Fin.ext_iff]; omega
    have hcross : tbCross (l.get ⟨i.val - 1, by omega⟩).1 (l.get ⟨i.val - 1, by omega⟩).2
                          (l.get ⟨i.val - 1 + 1, hmlen⟩).1 (l.get ⟨i.val - 1 + 1, hmlen⟩).2 ≤ t := by
      have hlo' := hlo hi1
      rw [congrArg l.get hei] at hlo'; exact hlo'
    rw [hei, hej]
    exact h.le_of_cross_le_pred hmlen hkle hcross
  · -- `j = i`
    rw [Fin.ext hji.symm]
  · -- `j > i`: upward chaining with the upper crossing bound (set `k = j - i - 1`)
    have hi1 : i.val + 1 < l.length := by omega
    have hklen : i.val + (j.val - i.val - 1) + 1 < l.length := by omega
    have hei : i = ⟨i.val, by omega⟩ := (Fin.eta i i.isLt).symm
    have hej : j = ⟨i.val + (j.val - i.val - 1) + 1, hklen⟩ := by simp only [Fin.ext_iff]; omega
    have hcross : t ≤ tbCross (l.get ⟨i.val, by omega⟩).1 (l.get ⟨i.val, by omega⟩).2
                              (l.get ⟨i.val + 1, by omega⟩).1 (l.get ⟨i.val + 1, by omega⟩).2 := by
      have hhi' := hhi hi1
      rw [congrArg l.get hei] at hhi'; exact hhi'
    rw [hei, hej]
    exact h.le_of_le_cross_succ hklen hcross

/-- **Proposition 4.1, item 4** (per-interval formula). For a list in concave normal form, the
concave PWL function equals its `i`-th token-bucket on the `i`-th inter-crossing interval: at any
`t` with `tᵢ ≤ t ≤ tᵢ₊₁` (the bounding crossings, with `t₁ = 0` and `tₙ₊₁ = ∞` as the vacuous
endpoint conventions), `(⋀ⱼ γⱼ)(t) = γ_{rᵢ,bᵢ}(t)`. -/
theorem IsConcaveNormalForm.concaveNFEval_eq_get_of_mem_interval {l : List (ℝ≥0 × ℝ≥0)}
    (h : IsConcaveNormalForm l) {t : ℝ≥0} (i : Fin l.length)
    (hlo : ∀ hi : 1 ≤ i.val, tbCross (l.get ⟨i.val - 1, by omega⟩).1 (l.get ⟨i.val - 1, by omega⟩).2
                                      (l.get i).1 (l.get i).2 ≤ t)
    (hhi : ∀ hi : i.val + 1 < l.length, t ≤ tbCross (l.get i).1 (l.get i).2
                                          (l.get ⟨i.val + 1, hi⟩).1 (l.get ⟨i.val + 1, hi⟩).2) :
    concaveNFEval l t = tbEReal (l.get i).1 (l.get i).2 t := by
  refine concaveNFEval_eq_of_isMin (List.get_mem l i) ?_
  intro s' hs'
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hs'
  exact h.isMin_of_mem_interval i hlo hhi j

-- Book wording check (Proposition 4.1, item 4): on the `i`-th inter-crossing interval
-- `[tᵢ, tᵢ₊₁]` (bounding crossings, `t₁ = 0`, `tₙ₊₁ = ∞`) the concave PWL function `⋀ⱼ γⱼ`
-- coincides with its `i`-th token-bucket `γ_{rᵢ,bᵢ}`.
example {l : List (ℝ≥0 × ℝ≥0)} (h : IsConcaveNormalForm l) {t : ℝ≥0} (i : Fin l.length)
    (hlo : ∀ hi : 1 ≤ i.val, tbCross (l.get ⟨i.val - 1, by omega⟩).1 (l.get ⟨i.val - 1, by omega⟩).2
                                      (l.get i).1 (l.get i).2 ≤ t)
    (hhi : ∀ hi : i.val + 1 < l.length, t ≤ tbCross (l.get i).1 (l.get i).2
                                          (l.get ⟨i.val + 1, hi⟩).1 (l.get ⟨i.val + 1, hi⟩).2) :
    concaveNFEval l t = tbEReal (l.get i).1 (l.get i).2 t :=
  h.concaveNFEval_eq_get_of_mem_interval i hlo hhi

end DeepWiki
