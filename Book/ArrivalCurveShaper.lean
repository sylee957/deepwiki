import Book.ArrivalCurves
import Book.ServiceCurveMaximal

/-! # σ-shapers
Servers whose every output allows `σ` as a maximal arrival curve, `D ≤ D ∗ σ`
(`σ : ℝ≥0 → EReal`, `F₀` hypotheses at use sites): the largest shaper
`shaperRel σ`, its closure and monotonicity properties, the universal
`δ₀`-shaper, and the containment in the maximal-service relation. -/

namespace DeepWiki

open scoped Classical NNReal

/-! ## Allowing an arrival curve, on `EReal` outputs -/

/-- Allowing `sigma` gives the increment bound for every convolution power
`sigmaⁿ`, for `NeverBot f` and nonnegative `sigma`. -/
theorem increment_convPowEReal_of_isMaximalArrivalCurve
    {f sigma : ℝ≥0 → EReal} (hf : NeverBot f) (hnn : IsNonneg sigma)
    (h : IsMaximalArrivalCurve f sigma) (n : ℕ) (u s : ℝ≥0) :
    f (u + s) ≤ f u + convPowEReal sigma n s := by
  induction n generalizing u s with
  | zero =>
      rcases eq_or_ne s 0 with hs | hs
      · subst hs
        rw [add_zero]
        show f u ≤ f u + convUnitEReal 0
        rw [convUnitEReal, if_pos rfl, add_zero]
      · show f (u + s) ≤ f u + convUnitEReal s
        rw [convUnitEReal, if_neg hs, EReal.add_top_of_ne_bot (hf u)]
        exact le_top
  | succ k ih =>
      show f (u + s) ≤ f u + minConv (convPowEReal sigma k) sigma s
      have hbot : (⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = s},
          convPowEReal sigma k p.1.1 + sigma p.1.2) ≠ ⊥ :=
        ne_bot_of_nonneg (le_iInf (fun p =>
          add_nonneg (convPowEReal_isNonneg hnn k p.1.1) (hnn p.1.2)))
      refine le_trans (le_iInf ?_) (iInf_add_le_add_iInf (hf u) hbot)
      rintro ⟨⟨a, b⟩, (hab : a + b = s)⟩
      show f (u + s) ≤ f u + (convPowEReal sigma k a + sigma b)
      have hsplit : u + s = (u + a) + b := by rw [add_assoc, hab]
      rw [hsplit]
      calc f ((u + a) + b)
          ≤ f (u + a) + sigma b :=
            (isMaximalArrivalCurve_iff_increment f sigma).mp h (u + a) b
        _ ≤ (f u + convPowEReal sigma k a) + sigma b :=
            add_le_add (ih u a) le_rfl
        _ = f u + (convPowEReal sigma k a + sigma b) := add_assoc _ _ _

/-- `f` allows the sub-additive closure `sigma⋆` iff it allows `sigma`
(`NeverBot f`, nonnegative `sigma`). -/
theorem isMaximalArrivalCurve_subadditiveClosureEReal_iff
    {f sigma : ℝ≥0 → EReal} (hf : NeverBot f) (hnn : IsNonneg sigma) :
    IsMaximalArrivalCurve f (subadditiveClosureEReal sigma) ↔
      IsMaximalArrivalCurve f sigma := by
  constructor
  · intro h t
    refine le_trans (h t) (minConv_le_minConv (fun _ => le_rfl)
      (fun s => subadditiveClosureEReal_le sigma
        hnn.bddBelowReal.neverBot s) t)
  · intro h
    refine (isMaximalArrivalCurve_iff_increment _ _).mpr (fun u s => ?_)
    show f (u + s) ≤ f u + subadditiveClosureEReal sigma s
    have hbot : (⨅ n : ℕ, convPowEReal sigma n s) ≠ ⊥ :=
      ne_bot_of_nonneg (le_iInf (fun n => convPowEReal_isNonneg hnn n s))
    refine le_trans (le_iInf (fun n => ?_)) (iInf_add_le_add_iInf (hf u) hbot)
    exact increment_convPowEReal_of_isMaximalArrivalCurve hf hnn h n u s

/-! ## σ-shapers -/

/-- `S` is a shaper for `sigma`: every output allows `sigma` as a maximal
arrival curve, `D ≤ D ∗ sigma`. -/
def IsShaper (sigma : ℝ≥0 → EReal) (S : Curve → Curve → Prop) : Prop :=
  ∀ A D : Curve, S A D → IsMaximalArrivalCurve (curveE D) sigma

/-- The largest relation shaping outputs to `sigma`: the causal pairs whose
output allows `sigma`. -/
def shaperRel (sigma : ℝ≥0 → EReal) : Curve → Curve → Prop :=
  fun A D => D ≤ A ∧ IsMaximalArrivalCurve (curveE D) sigma

/-- `shaperRel sigma A D` unfolds to causality and the arrival-curve bound. -/
theorem mem_shaperRel_iff {sigma : ℝ≥0 → EReal} {A D : Curve} :
    shaperRel sigma A D ↔
      D ≤ A ∧ IsMaximalArrivalCurve (curveE D) sigma :=
  Iff.rfl

/-- The zero output allows every nonnegative `sigma`. -/
theorem isMaximalArrivalCurve_zeroCurve {sigma : ℝ≥0 → EReal}
    (hnn : IsNonneg sigma) :
    IsMaximalArrivalCurve (curveE zeroCurve) sigma := by
  intro t
  rw [curveE_zeroCurve]
  exact IsNonneg.conv (curveE_nonneg zeroCurve) hnn t

/-- For nonnegative `sigma`, `shaperRel sigma` is a server: causality is the
first conjunct, and `zeroCurve` gives left-totality. -/
theorem isServer_shaperRel {sigma : ℝ≥0 → EReal} (hnn : IsNonneg sigma) :
    IsServer (shaperRel sigma) :=
  ⟨fun _ _ hp => hp.1,
    fun _ => ⟨zeroCurve, fun _ => zero_le',
      isMaximalArrivalCurve_zeroCurve hnn⟩⟩

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
    (isMaximalArrivalCurve_subadditiveClosureEReal_iff
      (curveE_neverBot D) hnn).mpr (hS A D hp)

/-- Shaping to nonnegative `sigma` and to its sub-additive closure `sigma⋆`
coincide: `shaperRel sigma = shaperRel sigma⋆`. -/
theorem shaperRel_closure {sigma : ℝ≥0 → EReal} (hnn : IsNonneg sigma) :
    shaperRel sigma = shaperRel (subadditiveClosureEReal sigma) := by
  funext A D
  apply propext
  have hiff := isMaximalArrivalCurve_subadditiveClosureEReal_iff
    (curveE_neverBot D) hnn
  exact ⟨fun hp => ⟨hp.1, hiff.mpr hp.2⟩, fun hp => ⟨hp.1, hiff.mp hp.2⟩⟩

/-! ## A shaper offers a maximal service curve -/

/-- A causal shaper for `sigma` offers `sigma` as a maximal service curve:
`D ≤ A` and `D ≤ D ∗ sigma` give `D ≤ A ∗ sigma` by isotony of the
convolution. -/
theorem IsShaper.isMaximalServiceCurve {S : Curve → Curve → Prop}
    {sigma : ℝ≥0 → EReal} (hc : IsCausal S) (hS : IsShaper sigma S) :
    IsMaximalServiceCurve sigma S :=
  fun A D hp t =>
    le_trans (hS A D hp t)
      (minConv_le_minConv (curveE_mono (hc A D hp)) (fun _ => le_rfl) t)

/-- The largest-relation form: the largest shaper is contained in the largest
server offering `sigma` as a maximal service curve. -/
theorem shaperRel_le_maximalServiceRel (sigma : ℝ≥0 → EReal) :
    shaperRel sigma ≤ maximalServiceRel sigma := by
  intro A D hp
  exact (isShaper_shaperRel sigma).isMaximalServiceCurve
    (fun _ _ hq => hq.1) A D hp

end DeepWiki
