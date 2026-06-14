import DeepWiki.NetworkCalculus.ArrivalCurvesOutput
import DeepWiki.NetworkCalculus.ServersConcatenationChain

/-! # Output arrival curves along a server chain (propagation)
Feed-forward propagation of a maximal arrival curve: the output of one server
is the input of the next, so an arrival curve `αu` crossing a chain of
strict-service servers `β₁, …, βₙ` emerges deconvolved by each in turn,
`αu ⊘ β₁ ⊘ ⋯ ⊘ βₙ` (`concatDeconv`, the left fold of `minDeconv`). The atomic
step is the two-server tandem; the chain form folds it over a `concatComp`
path. This is the building block of network arrival-curve propagation — turning
an ingress constraint into a constraint at every downstream server. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Deviation

/-- **Two-server tandem output arrival curve** (the atomic feed-forward
propagation step): a flow with ingress maximal arrival curve `αu` served by a
causal strict-service server `β₁` and then by `β₂` (the output `M` of the first
is the input of the second) has output `D` allowing `(αu ⊘ β₁) ⊘ β₂`. -/
theorem isMaximalArrivalBound_tandem_output
    {S₁ S₂ : Curve → Curve → Prop} {β₁ β₂ : ℝ≥0 → ℝ≥0} {αu : ℝ≥0 → ℝ≥0∞}
    (hc₁ : IsCausal S₁) (hβ₁ : IsStrictMinimalServiceCurve β₁ S₁)
    (hc₂ : IsCausal S₂) (hβ₂ : IsStrictMinimalServiceCurve β₂ S₂)
    {A M D : Curve} (hp₁ : S₁ A M) (hp₂ : S₂ M D)
    (harru : IsMaximalArrivalBound (liftENN ⇑A) αu) :
    IsMaximalArrivalBound (liftENN ⇑D)
      (minDeconv (minDeconv αu (liftENN β₁)) (liftENN β₂)) :=
  isMaximalArrivalBound_output_of_isStrictMinimalServiceCurve hc₂ hβ₂ hp₂
    (isMaximalArrivalBound_output_of_isStrictMinimalServiceCurve hc₁ hβ₁ hp₁ harru)

/-- Deconvolution fold of a maximal arrival curve along a path: passing through
server `h` deconvolves by `β h`, then the rest of the path, so
`concatDeconv β (h :: hs) αu = concatDeconv β hs (αu ⊘ β h)`. -/
noncomputable def concatDeconv {ι : Type*} (β : ι → ℝ≥0 → ℝ≥0∞) :
    List ι → (ℝ≥0 → ℝ≥0∞) → (ℝ≥0 → ℝ≥0∞)
  | [], αu => αu
  | h :: hs, αu => concatDeconv β hs (minDeconv αu (β h))

/-- `concatDeconv β [] αu = αu`: the empty path leaves the curve unchanged. -/
@[simp] theorem concatDeconv_nil {ι : Type*} (β : ι → ℝ≥0 → ℝ≥0∞)
    (αu : ℝ≥0 → ℝ≥0∞) : concatDeconv β [] αu = αu := rfl

/-- `concatDeconv β (h :: hs) αu = concatDeconv β hs (αu ⊘ β h)`. -/
theorem concatDeconv_cons {ι : Type*} (β : ι → ℝ≥0 → ℝ≥0∞)
    (h : ι) (hs : List ι) (αu : ℝ≥0 → ℝ≥0∞) :
    concatDeconv β (h :: hs) αu = concatDeconv β hs (minDeconv αu (β h)) := rfl

/-- **Output arrival curve along a chain** (feed-forward propagation): a flow
crossing the server chain `path` of causal strict-service servers, with ingress
maximal arrival curve `αu`, has output allowing the deconvolution fold
`concatDeconv (liftENN ∘ β) path αu = αu ⊘ β₁ ⊘ ⋯ ⊘ βₙ`. -/
theorem isMaximalArrivalBound_concatComp_output {ι : Type*}
    {S : ι → Curve → Curve → Prop} {β : ι → ℝ≥0 → ℝ≥0}
    (hc : ∀ h, IsCausal (S h)) (hβ : ∀ h, IsStrictMinimalServiceCurve (β h) (S h)) :
    ∀ (path : List ι) {A D : Curve} {αu : ℝ≥0 → ℝ≥0∞},
      concatComp S path A D → IsMaximalArrivalBound (liftENN ⇑A) αu →
      IsMaximalArrivalBound (liftENN ⇑D)
        (concatDeconv (fun h => liftENN (β h)) path αu)
  | [], _, _, _, hp, harru => by
      rw [concatComp_nil] at hp; subst hp; exact harru
  | h :: hs, _, _, _, hp, harru => by
      rw [concatComp_cons] at hp
      obtain ⟨M, hAM, hMD⟩ := hp
      exact isMaximalArrivalBound_concatComp_output hc hβ hs hMD
        (isMaximalArrivalBound_output_of_isStrictMinimalServiceCurve
          (hc h) (hβ h) hAM harru)

/-! ## Book restatement (feed-forward propagation)
A flow crossing a chain of causal servers, each offering a strict service
curve `β h`, with an ingress maximal arrival curve `αu`, keeps a maximal
arrival curve at the chain's output: the ingress curve deconvolved by every
server's service curve along the path. -/
example {ι : Type*} {S : ι → Curve → Curve → Prop} {β : ι → ℝ≥0 → ℝ≥0}
    {αu : ℝ≥0 → ℝ≥0∞} (hc : ∀ h, IsCausal (S h))
    (hβ : ∀ h, IsStrictMinimalServiceCurve (β h) (S h))
    (path : List ι) {A D : Curve} (hp : concatComp S path A D)
    (harru : IsMaximalArrivalBound (liftENN ⇑A) αu) :
    IsMaximalArrivalBound (liftENN ⇑D)
      (concatDeconv (fun h => liftENN (β h)) path αu) :=
  isMaximalArrivalBound_concatComp_output hc hβ path hp harru

end DeepWiki
