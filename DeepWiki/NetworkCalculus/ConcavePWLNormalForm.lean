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

end DeepWiki
