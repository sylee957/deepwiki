import DeepWiki.NetworkCalculus.ArrivalCurves
import DeepWiki.NetworkCalculus.ArrivalCurvesMaximal
import DeepWiki.NetworkCalculus.ServiceCurveMaximal

/-! # σ-shapers
Servers whose every output allows `σ` as a maximal arrival curve, `D ≤ D ∗ σ`
(`σ : ℝ≥0 → EReal`, `F₀` hypotheses at use sites): the largest shaper
`shaperRel σ`, its closure and monotonicity properties, the universal `δ₀`-
and `⊤`-shapers, and the containment in the maximal-service relation. -/

namespace DeepWiki

open scoped Classical NNReal

/-! ## Allowing an arrival curve, on `EReal` outputs -/

/-- Allowing `sigma` gives the increment bound for every convolution power
`sigmaⁿ`, for `IsNeverBot f` and nonnegative `sigma`. -/
theorem increment_convPowEReal_of_isMaximalArrivalBound
    {f sigma : ℝ≥0 → EReal} (hf : IsNeverBot f) (hnn : IsNonneg sigma)
    (h : IsMaximalArrivalBound f sigma) (n : ℕ) (u s : ℝ≥0) :
    f (u + s) ≤ f u + convPowEReal sigma n s := by
  induction n generalizing u s with
  | zero => exact hf.increment_convUnitEReal u s
  | succ k ih =>
      show f (u + s) ≤ f u + minConv (convPowEReal sigma k) sigma s
      have hbot : minConv (convPowEReal sigma k) sigma s ≠ ⊥ :=
        ne_bot_of_nonneg (IsNonneg.conv (convPowEReal_isNonneg hnn k) hnn s)
      refine le_trans (le_iInf ?_) (iInf_add_le_add_iInf (hf u) hbot)
      rintro ⟨⟨a, b⟩, (hab : a + b = s)⟩
      calc f (u + s) = f ((u + a) + b) := by rw [add_assoc, hab]
        _ ≤ f (u + a) + sigma b :=
            (isMaximalArrivalBound_iff_increment f sigma).mp h (u + a) b
        _ ≤ (f u + convPowEReal sigma k a) + sigma b :=
            add_le_add (ih u a) le_rfl
        _ = f u + (convPowEReal sigma k a + sigma b) := add_assoc _ _ _

/-- `f` allows the sub-additive closure `sigma⋆` iff it allows `sigma`
(`IsNeverBot f`, nonnegative `sigma`). -/
theorem isMaximalArrivalBound_subadditiveClosureEReal_iff
    {f sigma : ℝ≥0 → EReal} (hf : IsNeverBot f) (hnn : IsNonneg sigma) :
    IsMaximalArrivalBound f (subadditiveClosureEReal sigma) ↔
      IsMaximalArrivalBound f sigma := by
  constructor
  · intro h t
    refine le_trans (h t) (minConv_le_minConv (fun _ => le_rfl)
      (fun s => subadditiveClosureEReal_le sigma
        hnn.isBddBelowReal.isNeverBot s) t)
  · intro h
    refine (isMaximalArrivalBound_iff_increment _ _).mpr (fun u s => ?_)
    show f (u + s) ≤ f u + subadditiveClosureEReal sigma s
    have hbot : (⨅ n : ℕ, convPowEReal sigma n s) ≠ ⊥ :=
      subadditiveClosureEReal_isNeverBot hnn s
    refine le_trans (le_iInf (fun n => ?_)) (iInf_add_le_add_iInf (hf u) hbot)
    exact increment_convPowEReal_of_isMaximalArrivalBound hf hnn h n u s

/-! ## σ-shapers -/

/-- `S` is a shaper for `sigma`: every output allows `sigma` as a maximal
arrival curve, `D ≤ D ∗ sigma`. -/
def IsShaper (sigma : ℝ≥0 → EReal) (S : Curve → Curve → Prop) : Prop :=
  ∀ A D : Curve, S A D → IsMaximalArrivalBound (curveEReal D) sigma

/-- The largest relation shaping outputs to `sigma`: the causal pairs whose
output allows `sigma`. -/
def shaperRel (sigma : ℝ≥0 → EReal) : Curve → Curve → Prop :=
  fun A D => D ≤ A ∧ IsMaximalArrivalBound (curveEReal D) sigma

/-- `shaperRel sigma A D` unfolds to causality and the arrival-curve bound. -/
theorem mem_shaperRel_iff {sigma : ℝ≥0 → EReal} {A D : Curve} :
    shaperRel sigma A D ↔
      D ≤ A ∧ IsMaximalArrivalBound (curveEReal D) sigma :=
  Iff.rfl

/-- The zero output allows every nonnegative `sigma`. -/
theorem isMaximalArrivalBound_zeroCurve {sigma : ℝ≥0 → EReal}
    (hnn : IsNonneg sigma) :
    IsMaximalArrivalBound (curveEReal zeroCurve) sigma := by
  intro t
  rw [curveEReal_zeroCurve]
  exact IsNonneg.conv (curveEReal_nonneg zeroCurve) hnn t

/-- For nonnegative `sigma`, `shaperRel sigma` is a server: causality is the
first conjunct, and `zeroCurve` gives left-totality. -/
theorem isServer_shaperRel {sigma : ℝ≥0 → EReal} (hnn : IsNonneg sigma) :
    IsServer (shaperRel sigma) :=
  ⟨fun _ _ hp => hp.1,
    fun _ => ⟨zeroCurve, fun _ => zero_le,
      isMaximalArrivalBound_zeroCurve hnn⟩⟩

/-- A causal `S` is a shaper for `sigma` iff its pairs lie in
`shaperRel sigma`: `shaperRel sigma` is the largest shaper for `sigma`. -/
theorem isShaper_iff_subset {S : Curve → Curve → Prop} (hc : IsCausal S)
    {sigma : ℝ≥0 → EReal} :
    IsShaper sigma S ↔ ∀ A D : Curve, S A D → shaperRel sigma A D := by
  constructor
  · intro h A D hp
    exact ⟨hc _ _ hp, h A D hp⟩
  · intro h A D hp
    exact (h A D hp).2

/-- `shaperRel sigma` is itself a shaper for `sigma`. -/
theorem isShaper_shaperRel (sigma : ℝ≥0 → EReal) :
    IsShaper sigma (shaperRel sigma) :=
  fun _ _ hp => hp.2

/-- Every relation — in particular every server — is a `δ₀`-shaper:
`D ∗ δ₀ = D`. -/
theorem isShaper_delayEReal_zero (S : Curve → Curve → Prop) :
    IsShaper (delayEReal 0) S :=
  fun _ D _ t => le_of_eq (congrFun (minConv_delayEReal_zero D) t).symm

/-- Every relation — in particular every server — is a shaper for the
everywhere-`⊤` curve: `D ∗ ⊤ = ⊤` dominates any output. -/
theorem isShaper_top (S : Curve → Curve → Prop) :
    IsShaper (⊤ : ℝ≥0 → EReal) S := by
  intro A D _
  refine fun t => le_minConv fun u s _ => ?_
  rw [Pi.top_apply, EReal.add_top_of_ne_bot (isNeverBot_curveEReal D u)]
  exact le_top

/-! ## Properties of shapers -/

/-- A shaper for `sigma` is a shaper for any larger `sigma'`. -/
theorem IsShaper.mono {S : Curve → Curve → Prop}
    {sigma sigma' : ℝ≥0 → EReal} (h : sigma ≤ sigma')
    (hS : IsShaper sigma S) : IsShaper sigma' S :=
  fun A D hp t =>
    le_trans (hS A D hp t) (minConv_le_minConv (fun _ => le_rfl) h t)

/-- `shaperRel` is monotone in the curve: `sigma ≤ sigma'` gives the
containment of relations. -/
theorem shaperRel_mono {sigma sigma' : ℝ≥0 → EReal} (h : sigma ≤ sigma') :
    shaperRel sigma ≤ shaperRel sigma' := by
  intro A D hp
  exact ⟨hp.1, ((isShaper_shaperRel sigma).mono h) A D hp⟩

/-- A shaper for nonnegative `sigma` is a shaper for the sub-additive closure
`sigma⋆`. -/
theorem IsShaper.closure {S : Curve → Curve → Prop} {sigma : ℝ≥0 → EReal}
    (hnn : IsNonneg sigma) (hS : IsShaper sigma S) :
    IsShaper (subadditiveClosureEReal sigma) S :=
  fun A D hp =>
    (isMaximalArrivalBound_subadditiveClosureEReal_iff
      (isNeverBot_curveEReal D) hnn).mpr (hS A D hp)

/-- Shaping to nonnegative `sigma` and to its sub-additive closure `sigma⋆`
coincide: `shaperRel sigma = shaperRel sigma⋆`. -/
theorem shaperRel_closure {sigma : ℝ≥0 → EReal} (hnn : IsNonneg sigma) :
    shaperRel sigma = shaperRel (subadditiveClosureEReal sigma) := by
  funext A D
  apply propext
  have hiff := isMaximalArrivalBound_subadditiveClosureEReal_iff
    (isNeverBot_curveEReal D) hnn
  exact ⟨fun hp => ⟨hp.1, hiff.mpr hp.2⟩, fun hp => ⟨hp.1, hiff.mp hp.2⟩⟩

/-- **Conjunction of shapers**: a flow is shaped by `σ₁ ⊓ σ₂` exactly when it is
shaped by each, `shaperRel (σ₁ ⊓ σ₂) = shaperRel σ₁ ⊓ shaperRel σ₂` — the output
allows the smaller curve iff it allows both. -/
theorem shaperRel_inf (σ₁ σ₂ : ℝ≥0 → EReal) :
    shaperRel (σ₁ ⊓ σ₂) = shaperRel σ₁ ⊓ shaperRel σ₂ := by
  funext A D
  apply propext
  rw [mem_shaperRel_iff, isMaximalArrivalBound_inf_iff]
  exact ⟨fun ⟨hA, h1, h2⟩ => ⟨⟨hA, h1⟩, hA, h2⟩,
    fun ⟨⟨hA, h1⟩, _, h2⟩ => ⟨hA, h1, h2⟩⟩

/-! Combining the conjunction and closure invariances: shaping a flow by both
nonnegative `σ₁` and `σ₂` is the same as shaping by the sub-additive closure of
their conjunction, `shaperRel σ₁ ⊓ shaperRel σ₂ = shaperRel ((σ₁ ⊓ σ₂)⋆)`. -/
example {σ₁ σ₂ : ℝ≥0 → EReal} (h1 : IsNonneg σ₁) (h2 : IsNonneg σ₂) :
    shaperRel σ₁ ⊓ shaperRel σ₂
      = shaperRel (subadditiveClosureEReal (σ₁ ⊓ σ₂)) := by
  rw [← shaperRel_inf,
    shaperRel_closure (sigma := σ₁ ⊓ σ₂) (fun t => le_inf (h1 t) (h2 t))]

/-- **Conjunction of shapers, convolution form**: shaping a flow by both
nonnegative `σ₁` and `σ₂` equals shaping by the convolution of their closures,
`shaperRel σ₁ ⊓ shaperRel σ₂ = shaperRel (σ₁⋆ ∗ σ₂⋆)` — the conjunction
invariance, the closure invariance, and the `EReal` star-of-meet combined. -/
theorem shaperRel_inf_minConv_closure {σ₁ σ₂ : ℝ≥0 → EReal}
    (h1 : IsNonneg σ₁) (h2 : IsNonneg σ₂) :
    shaperRel σ₁ ⊓ shaperRel σ₂
      = shaperRel (minConv (subadditiveClosureEReal σ₁) (subadditiveClosureEReal σ₂)) := by
  rw [← shaperRel_inf,
    shaperRel_closure (sigma := σ₁ ⊓ σ₂) (fun t => le_inf (h1 t) (h2 t))]
  congr 1
  exact subadditiveClosureEReal_min h1 h2

/-! ## A shaper offers a maximal service curve -/

/-- A causal shaper for `sigma` offers `sigma` as a maximal service curve:
`D ≤ A` and `D ≤ D ∗ sigma` give `D ≤ A ∗ sigma` by isotony of the
convolution. -/
theorem IsShaper.isMaximalServiceCurve {S : Curve → Curve → Prop}
    {sigma : ℝ≥0 → EReal} (hc : IsCausal S) (hS : IsShaper sigma S) :
    IsMaximalServiceCurve sigma S :=
  fun A D hp t =>
    le_trans (hS A D hp t)
      (minConv_le_minConv (curveEReal_mono (hc A D hp)) (fun _ => le_rfl) t)

/-- The largest-relation form: the largest shaper is contained in the largest
server offering `sigma` as a maximal service curve. -/
theorem shaperRel_le_maximalServiceRel (sigma : ℝ≥0 → EReal) :
    shaperRel sigma ≤ maximalServiceRel sigma := by
  intro A D hp
  exact (isShaper_shaperRel sigma).isMaximalServiceCurve
    (fun _ _ hq => hq.1) A D hp

end DeepWiki
