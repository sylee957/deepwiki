import Book.DeviationsComposition
import Book.ServersConcatenation
import Book.ArrivalCurvesOutput

/-! # Tandem delay bounds at the server level
A flow crossing a tandem of min-plus servers admits two delay-bound routes:
per hop, with the deconvolved output bound `α ⊘ β₁` feeding hop 2
(method 1), or end-to-end through the concatenation theorem against
`hDev α (β₁ ∗ β₂)` (method 2). The `toENN` convolution bridge shows
method 2's bound is below method 1's sum: pay burst only once, at the
server level. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

namespace Deviation

/-- **Tandem delay bound through concatenation** (method 2): a pair of the
tandem `Relation.Comp S₁ S₂` has end-to-end delay at most
`hDev α (toENN (β₁ ∗ β₂))`. -/
theorem delay_le_hDev_minConv_of_comp
    {S₁ S₂ : Curve → Curve → Prop} {β₁ β₂ : ℝ≥0 → EReal}
    {α : ℝ≥0 → ℝ≥0∞} {A C : Curve}
    (hβ₁ : IsMinimalServiceCurve β₁ S₁) (hβ₂ : IsMinimalServiceCurve β₂ S₂)
    (hp : Relation.Comp S₁ S₂ A C)
    (hnn₁ : IsNonneg β₁) (hnn₂ : IsNonneg β₂)
    (hβ₁mono : Monotone β₁) (hβ₂mono : Monotone β₂)
    (harr : IsMaximalArrivalBound (liftENN ⇑A) α) :
    delay ⇑A ⇑C ≤ (hDev α (toENN (minConv β₁ β₂)) : ℝ≥0∞) :=
  delay_le_hDev_of_isMinimalServiceCurve
    (hβ₁.comp hβ₂ hnn₁.isBddBelowReal hnn₂.isBddBelowReal) hp
    (hnn₁.conv hnn₂) (monotone_minConv hβ₁mono hβ₂mono) harr

/-- **Per-hop tandem delay bounds** (method 1): hop 1 against `hDev α β₁`,
hop 2 against the deconvolved output bound `hDev (α ⊘ β₁) β₂`. -/
theorem delay_add_delay_le_hDev_add_hDev_minDeconv
    {S₁ S₂ : Curve → Curve → Prop} {β₁ β₂ : ℝ≥0 → EReal}
    {α : ℝ≥0 → ℝ≥0∞} {A B C : Curve} (hc₁ : IsCausal S₁)
    (hβ₁ : IsMinimalServiceCurve β₁ S₁) (hβ₂ : IsMinimalServiceCurve β₂ S₂)
    (hp₁ : S₁ A B) (hp₂ : S₂ B C)
    (hnn₁ : IsNonneg β₁) (hnn₂ : IsNonneg β₂)
    (hβ₁mono : Monotone β₁) (hβ₂mono : Monotone β₂)
    (harr : IsMaximalArrivalBound (liftENN ⇑A) α) :
    delay ⇑A ⇑B + delay ⇑B ⇑C
      ≤ (hDev α (toENN β₁) : ℝ≥0∞)
        + hDev (minDeconv α (toENN β₁)) (toENN β₂) :=
  add_le_add
    (delay_le_hDev_of_isMinimalServiceCurve hβ₁ hp₁ hnn₁ hβ₁mono harr)
    (delay_le_hDev_of_isMinimalServiceCurve hβ₂ hp₂ hnn₂ hβ₂mono
      (isMaximalArrivalBound_output_of_isMinimalServiceCurve hc₁ hβ₁
        hnn₁ hp₁ harr))

/-- Pay burst only once survives the `ℝ≥0∞` reading: `hDev α (toENN (β₁ ∗ β₂))
≤ hDev α (toENN β₁) + hDev (α ⊘ toENN β₁) (toENN β₂)`. -/
theorem hDev_toENN_minConv_le_add_hDev_minDeconv
    {β₁ β₂ : ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0∞} (hαmono : Monotone α)
    (hnn₁ : IsNonneg β₁) (hnn₂ : IsNonneg β₂)
    (hβ₁mono : Monotone β₁) (hβ₂mono : Monotone β₂) :
    (hDev α (toENN (minConv β₁ β₂)) : ℝ≥0∞)
      ≤ hDev α (toENN β₁) + hDev (minDeconv α (toENN β₁)) (toENN β₂) := by
  rw [toENN_minConv hnn₁ hnn₂]
  exact hDev_minConv_le_add_hDev_minDeconv hαmono
    (monotone_toENN hβ₁mono) (monotone_toENN hβ₂mono)

/-- **End-to-end beats per hop**: the tandem delay obeys method 1's per-hop
sum through method 2's single concatenation bound. -/
theorem delay_le_hDev_add_hDev_minDeconv_of_comp
    {S₁ S₂ : Curve → Curve → Prop} {β₁ β₂ : ℝ≥0 → EReal}
    {α : ℝ≥0 → ℝ≥0∞} {A C : Curve}
    (hβ₁ : IsMinimalServiceCurve β₁ S₁) (hβ₂ : IsMinimalServiceCurve β₂ S₂)
    (hp : Relation.Comp S₁ S₂ A C)
    (hnn₁ : IsNonneg β₁) (hnn₂ : IsNonneg β₂) (hαmono : Monotone α)
    (hβ₁mono : Monotone β₁) (hβ₂mono : Monotone β₂)
    (harr : IsMaximalArrivalBound (liftENN ⇑A) α) :
    delay ⇑A ⇑C
      ≤ (hDev α (toENN β₁) : ℝ≥0∞)
        + hDev (minDeconv α (toENN β₁)) (toENN β₂) :=
  le_trans
    (delay_le_hDev_minConv_of_comp hβ₁ hβ₂ hp hnn₁ hnn₂
      hβ₁mono hβ₂mono harr)
    (hDev_toENN_minConv_le_add_hDev_minDeconv hαmono hnn₁ hnn₂
      hβ₁mono hβ₂mono)

/-! ## Book restatement (the two delay-bound methods for a tandem)
Crossing `S₁` then `S₂` with an `α`-constrained arrival: summing per-hop
bounds gives `d(A,B) + d(B,C) ≤ hDev(α, β₁) + hDev(α ⊘ β₁, β₂)`
(method 1, the output bound feeding hop 2), while the concatenation
theorem bounds the end-to-end delay by `hDev(α, β₁ ∗ β₂)` (method 2),
itself below method 1's sum: the burst is paid only once. -/

example {S₁ S₂ : Curve → Curve → Prop} {β₁ β₂ : ℝ≥0 → EReal}
    {α : ℝ≥0 → ℝ≥0∞} {A B C : Curve} (hc₁ : IsCausal S₁)
    (hβ₁ : IsMinimalServiceCurve β₁ S₁) (hβ₂ : IsMinimalServiceCurve β₂ S₂)
    (hp₁ : S₁ A B) (hp₂ : S₂ B C)
    (hnn₁ : IsNonneg β₁) (hnn₂ : IsNonneg β₂)
    (hβ₁mono : Monotone β₁) (hβ₂mono : Monotone β₂)
    (harr : IsMaximalArrivalBound (liftENN ⇑A) α) :
    delay ⇑A ⇑B + delay ⇑B ⇑C
      ≤ (hDev α (toENN β₁) : ℝ≥0∞)
        + hDev (minDeconv α (toENN β₁)) (toENN β₂) :=
  delay_add_delay_le_hDev_add_hDev_minDeconv hc₁ hβ₁ hβ₂ hp₁ hp₂
    hnn₁ hnn₂ hβ₁mono hβ₂mono harr

example {S₁ S₂ : Curve → Curve → Prop} {β₁ β₂ : ℝ≥0 → EReal}
    {α : ℝ≥0 → ℝ≥0∞} {A C : Curve}
    (hβ₁ : IsMinimalServiceCurve β₁ S₁) (hβ₂ : IsMinimalServiceCurve β₂ S₂)
    (hp : Relation.Comp S₁ S₂ A C)
    (hnn₁ : IsNonneg β₁) (hnn₂ : IsNonneg β₂) (hαmono : Monotone α)
    (hβ₁mono : Monotone β₁) (hβ₂mono : Monotone β₂)
    (harr : IsMaximalArrivalBound (liftENN ⇑A) α) :
    delay ⇑A ⇑C
      ≤ (hDev α (toENN β₁) : ℝ≥0∞)
        + hDev (minDeconv α (toENN β₁)) (toENN β₂) :=
  calc delay ⇑A ⇑C
      ≤ (hDev α (toENN (minConv β₁ β₂)) : ℝ≥0∞) :=
        delay_le_hDev_minConv_of_comp hβ₁ hβ₂ hp hnn₁ hnn₂
          hβ₁mono hβ₂mono harr
    _ ≤ (hDev α (toENN β₁) : ℝ≥0∞)
        + hDev (minDeconv α (toENN β₁)) (toENN β₂) :=
        hDev_toENN_minConv_le_add_hDev_minDeconv hαmono hnn₁ hnn₂
          hβ₁mono hβ₂mono

end Deviation

end DeepWiki
