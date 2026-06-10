import Book.ArrivalCurveShaper
import Book.ConvolutionContinuity

/-! # Greedy shapers
The greedy shaper outputs exactly `A ∗ σ`: the relation `greedyShaperRel σ`,
well-defined for `σ` in `F₀` left-continuous (the output is again a curve, up
to a piecewise-continuity witness). A greedy shaper is a `σ`-shaper and a
min-plus service curve; `greedyShaperRel σ = minimalServiceRel σ ⊓ shaperRel σ`. -/

namespace DeepWiki

open scoped Classical NNReal

/-- `S` is a greedy shaper for `sigma`: every output is exactly `A ∗ sigma`. -/
def IsGreedyShaper (sigma : ℝ≥0 → EReal) (S : Curve → Curve → Prop) : Prop :=
  ∀ A D : Curve, S A D → curveE D = minConv (curveE A) sigma

/-- The greedy-shaper relation: the output is exactly `A ∗ sigma`. -/
def greedyShaperRel (sigma : ℝ≥0 → EReal) : Curve → Curve → Prop :=
  fun A D => curveE D = minConv (curveE A) sigma

/-- `greedyShaperRel sigma A D` unfolds to `D = A ∗ sigma` (via `curveE`). -/
theorem mem_greedyShaperRel_iff {sigma : ℝ≥0 → EReal} {A D : Curve} :
    greedyShaperRel sigma A D ↔ curveE D = minConv (curveE A) sigma :=
  Iff.rfl

/-- `IsGreedyShaper sigma S` iff `S ≤ greedyShaperRel sigma`. -/
theorem isGreedyShaper_iff_subset {S : Curve → Curve → Prop}
    {sigma : ℝ≥0 → EReal} :
    IsGreedyShaper sigma S ↔
      ∀ A D : Curve, S A D → greedyShaperRel sigma A D :=
  Iff.rfl

/-- `greedyShaperRel sigma` is itself a greedy shaper for `sigma`. -/
theorem isGreedyShaper_greedyShaperRel (sigma : ℝ≥0 → EReal) :
    IsGreedyShaper sigma (greedyShaperRel sigma) :=
  fun _ _ hp => hp

/-- A greedy shaper for `sigma` with `sigma 0 ≤ 0` is causal: the output
`A ∗ sigma` lies below `A`. -/
theorem IsGreedyShaper.isCausal {S : Curve → Curve → Prop}
    {sigma : ℝ≥0 → EReal} (h0 : sigma 0 ≤ 0)
    (hS : IsGreedyShaper sigma S) : IsCausal S :=
  fun A D hp => curveE_le_iff.mp
    (le_of_eq_of_le (hS A D hp) (minConv_self_le h0 A))

/-! ## Well-definedness: the greedy output is a curve
For `sigma` in `F₀` (nonnegative, nondecreasing, null at zero) and
left-continuous, `A ∗ sigma` is nonnegative, finite, nondecreasing, null at
the origin, and left-continuous (`isLeftContinuous_minConv_ereal`). Piecewise
continuity of the convolution is the one remaining witness, supplied as a
hypothesis; sub-additivity is not needed for the output to be a curve, only
for the shaper property (`IsGreedyShaper.isShaper`). -/

/-- `A ∗ sigma` is finite when `sigma 0 ≤ 0`: it is bounded by `A`. -/
theorem minConv_curveE_ne_top (A : Curve) {sigma : ℝ≥0 → EReal}
    (h0 : sigma 0 ≤ 0) (t : ℝ≥0) :
    minConv (curveE A) sigma t ≠ ⊤ :=
  (lt_of_le_of_lt (minConv_self_le h0 A t) (EReal.coe_lt_top _)).ne

/-- The greedy output `A ∗ sigma`, read back as an `ℝ≥0`-valued function. -/
noncomputable def greedyFun (A : Curve) (sigma : ℝ≥0 → EReal) : ℝ≥0 → ℝ≥0 :=
  fun t => (minConv (curveE A) sigma t).toReal.toNNReal

/-- `A ∗ sigma` is nonnegative (nonnegative `sigma`) and finite (null-at-zero
`sigma` bounds it by `A`), so the `ℝ≥0` reading round-trips:
`(greedyFun A sigma t : EReal) = (A ∗ sigma) t`. -/
theorem coe_greedyFun (A : Curve) {sigma : ℝ≥0 → EReal}
    (hnn : IsNonneg sigma) (h0 : sigma 0 = 0) (t : ℝ≥0) :
    ((greedyFun A sigma t : ℝ) : EReal) = minConv (curveE A) sigma t := by
  have hpos : (0 : EReal) ≤ minConv (curveE A) sigma t :=
    IsNonneg.conv (curveE_nonneg A) hnn t
  have hne_bot : minConv (curveE A) sigma t ≠ ⊥ := ne_bot_of_nonneg hpos
  have hne_top := minConv_curveE_ne_top A h0.le t
  show (((minConv (curveE A) sigma t).toReal.toNNReal : ℝ) : EReal) = _
  rw [Real.coe_toNNReal _ (EReal.toReal_nonneg hpos),
    EReal.coe_toReal hne_top hne_bot]

/-- `greedyFun A sigma` is nondecreasing. -/
theorem greedyFun_mono (A : Curve) {sigma : ℝ≥0 → EReal}
    (hmono : Monotone sigma) (h0 : sigma 0 = 0) :
    Monotone (greedyFun A sigma) := by
  intro a b hab
  have hm := monotone_minConv (monotone_curveE A) hmono hab
  have hpos : (0 : EReal) ≤ minConv (curveE A) sigma a :=
    IsNonneg.conv (curveE_nonneg A)
      (isNonneg_of_monotone_of_nullAtOrigin hmono h0) a
  exact Real.toNNReal_mono
    (EReal.toReal_le_toReal hm (ne_bot_of_nonneg hpos)
      (minConv_curveE_ne_top A h0.le b))

/-- `greedyFun A sigma` vanishes at the origin. -/
theorem greedyFun_zero (A : Curve) {sigma : ℝ≥0 → EReal} (h0 : sigma 0 = 0) :
    IsNullAtOrigin (greedyFun A sigma) := by
  have hm : minConv (curveE A) sigma 0 = 0 :=
    IsNullAtOrigin.conv (curveE_zero A) h0
  show (minConv (curveE A) sigma 0).toReal.toNNReal = 0
  rw [hm, EReal.toReal_zero, Real.toNNReal_zero]

/-- `greedyFun A sigma` is left-continuous: the convolution is left-continuous
(`isLeftContinuous_minConv_ereal`), and its values are finite. -/
theorem greedyFun_leftCont (A : Curve) {sigma : ℝ≥0 → EReal}
    (hmono : Monotone sigma) (h0 : sigma 0 = 0)
    (hlc : IsLeftContinuous sigma) :
    IsLeftContinuous (greedyFun A sigma) := by
  have hm : IsLeftContinuous (minConv (curveE A) sigma) :=
    isLeftContinuous_minConv_ereal _ _ (monotone_curveE A) hmono
      (isLeftContinuous_curveE A) hlc
      (fun r u => addDefined_curveE A u (sigma (r - u)))
  intro t
  have hpos : (0 : EReal) ≤ minConv (curveE A) sigma t :=
    IsNonneg.conv (curveE_nonneg A)
      (isNonneg_of_monotone_of_nullAtOrigin hmono h0) t
  have htr : ContinuousAt EReal.toReal (minConv (curveE A) sigma t) :=
    EReal.tendsto_toReal (minConv_curveE_ne_top A h0.le t)
      (ne_bot_of_nonneg hpos)
  exact ((continuous_real_toNNReal.continuousAt).comp htr
    ).comp_continuousWithinAt (hm t)

/-- The greedy output `A ∗ sigma` as a `Curve`, for `sigma` nondecreasing,
nonnegative, null at zero, and left-continuous; the piecewise-continuity
witness for the convolution is the remaining hypothesis. -/
noncomputable def greedyCurve (A : Curve) (sigma : ℝ≥0 → EReal)
    (hmono : Monotone sigma) (h0 : sigma 0 = 0)
    (hlc : IsLeftContinuous sigma)
    (hpwc : IsPiecewiseContinuous (greedyFun A sigma)) : Curve :=
  ⟨greedyFun A sigma, greedyFun_mono A hmono h0, greedyFun_zero A h0,
    hpwc, greedyFun_leftCont A hmono h0 hlc⟩

/-- The greedy curve realizes the convolution:
`curveE (greedyCurve …) = A ∗ sigma`. -/
theorem curveE_greedyCurve (A : Curve) {sigma : ℝ≥0 → EReal}
    (hmono : Monotone sigma) (h0 : sigma 0 = 0)
    (hlc : IsLeftContinuous sigma)
    (hpwc : IsPiecewiseContinuous (greedyFun A sigma)) :
    curveE (greedyCurve A sigma hmono h0 hlc hpwc)
      = minConv (curveE A) sigma :=
  funext (coe_greedyFun A
    (isNonneg_of_monotone_of_nullAtOrigin hmono h0) h0)

/-- For `sigma` in `F₀` and left-continuous, `greedyShaperRel sigma` is a server:
causality is `A ∗ sigma ≤ A` (`minConv_self_le`), and `greedyCurve` realizes
each output — given the piecewise-continuity witness `hpwc` for the
convolution (the remaining regularity gap). -/
theorem isServer_greedyShaperRel {sigma : ℝ≥0 → EReal}
    (hmono : Monotone sigma) (h0 : sigma 0 = 0)
    (hlc : IsLeftContinuous sigma)
    (hpwc : ∀ A : Curve, IsPiecewiseContinuous (greedyFun A sigma)) :
    IsServer (greedyShaperRel sigma) :=
  ⟨(isGreedyShaper_greedyShaperRel sigma).isCausal h0.le,
    fun A => ⟨greedyCurve A sigma hmono h0 hlc (hpwc A),
      curveE_greedyCurve A hmono h0 hlc (hpwc A)⟩⟩

/-! ## A greedy shaper is a shaper and a minimal service curve -/

/-- Because of the defining equality, a greedy shaper offers `sigma` as a
min-plus (minimal) service curve: `A ∗ sigma ≤ D`. -/
theorem IsGreedyShaper.isMinimalServiceCurve {S : Curve → Curve → Prop}
    {sigma : ℝ≥0 → EReal} (hS : IsGreedyShaper sigma S) :
    IsMinimalServiceCurve sigma S :=
  fun A D hp => le_of_eq (hS A D hp).symm

/-- A sub-additive `sigma` allows itself as an arrival curve. -/
theorem isMaximalArrivalBound_self_of_subadditive {T : Type*} [Add T]
    [ConditionallyCompleteLattice T] [OrderBot T] {sigma : ℝ≥0 → T}
    (hsub : IsSubadditive sigma) :
    IsMaximalArrivalBound sigma sigma :=
  (isMaximalArrivalBound_iff_increment sigma sigma).mpr hsub

/-- For nonnegative `f` and sub-additive nonnegative `sigma`, the greedy
output `f ∗ sigma` allows `sigma`. -/
theorem isMaximalArrivalBound_minConv_of_subadditive
    {f sigma : ℝ≥0 → EReal} (hf : IsNonneg f) (hnn : IsNonneg sigma)
    (hsub : IsSubadditive sigma) :
    IsMaximalArrivalBound (minConv f sigma) sigma := by
  refine (isMaximalArrivalBound_iff_increment _ _).mpr (fun u s => ?_)
  show minConv f sigma (u + s) ≤ minConv f sigma u + sigma s
  have hbot : minConv f sigma u ≠ ⊥ :=
    ne_bot_of_nonneg (IsNonneg.conv hf hnn u)
  rw [add_comm (minConv f sigma u) (sigma s)]
  refine le_trans (le_iInf ?_)
    (iInf_add_le_add_iInf (ne_bot_of_nonneg (hnn s)) hbot)
  rintro ⟨⟨a, b⟩, (hab : a + b = u)⟩
  calc minConv f sigma (u + s)
      ≤ f a + sigma (b + s) := minConv_le_add f sigma (by rw [← hab, add_assoc])
    _ ≤ f a + (sigma b + sigma s) := add_le_add le_rfl (hsub b s)
    _ = sigma s + (f a + sigma b) := by
        rw [← add_assoc, add_comm (f a + sigma b) (sigma s)]

/-- A greedy shaper for sub-additive nonnegative `sigma` is a `sigma`-shaper:
its outputs `A ∗ sigma` allow `sigma`. -/
theorem IsGreedyShaper.isShaper {S : Curve → Curve → Prop}
    {sigma : ℝ≥0 → EReal} (hnn : IsNonneg sigma) (hsub : IsSubadditive sigma)
    (hS : IsGreedyShaper sigma S) : IsShaper sigma S := by
  intro A D hp
  rw [show curveE D = minConv (curveE A) sigma from hS A D hp]
  exact isMaximalArrivalBound_minConv_of_subadditive
    (curveE_nonneg A) hnn hsub

/-! ## Greedy shaper is minimal and maximal service -/

/-- A greedy shaper offers `sigma` as a maximal service curve:
`D ≤ A ∗ sigma` from the defining equality. -/
theorem IsGreedyShaper.isMaximalServiceCurve {S : Curve → Curve → Prop}
    {sigma : ℝ≥0 → EReal} (hS : IsGreedyShaper sigma S) :
    IsMaximalServiceCurve sigma S :=
  fun A D hp => le_of_eq (hS A D hp)

/-- Pointwise form of the minimal-and-maximal characterization: for
`sigma 0 ≤ 0`, `D = A ∗ sigma` iff the pair is in both the min-plus and the
maximal-service relations. -/
theorem mem_greedyShaperRel_iff_minimal_and_maximal {sigma : ℝ≥0 → EReal}
    (h0 : sigma 0 ≤ 0) {A D : Curve} :
    greedyShaperRel sigma A D ↔
      minimalServiceRel sigma A D ∧ maximalServiceRel sigma A D := by
  constructor
  · intro hp
    exact ⟨⟨le_trans (le_of_eq (hp : curveE D = _)) (minConv_self_le h0 A),
        le_of_eq (hp : curveE D = _).symm⟩,
      le_of_eq (hp : curveE D = _)⟩
  · rintro ⟨⟨_, hge⟩, hle⟩
    exact le_antisymm hle hge

/-- The greedy shaper is exactly minimal-and-maximal service: for
`sigma 0 ≤ 0`, `greedyShaperRel sigma` is the intersection of `minimalServiceRel
sigma` and `maximalServiceRel sigma`. -/
theorem greedyShaperRel_eq_minimalServiceRel_inf_maximalServiceRel {sigma : ℝ≥0 → EReal}
    (h0 : sigma 0 ≤ 0) :
    greedyShaperRel sigma =
      minimalServiceRel sigma ⊓ maximalServiceRel sigma := by
  funext A D
  simp only [Pi.inf_apply, inf_Prop_eq]
  exact propext (mem_greedyShaperRel_iff_minimal_and_maximal h0)

/-- The greedy-shaper relation is contained in the shaper relation: for `F₀`
sub-additive `sigma`, `D = A ∗ sigma` gives `D ≤ A` and `D ≤ D ∗ sigma`. -/
theorem greedyShaperRel_le_shaperRel {sigma : ℝ≥0 → EReal} (h0 : sigma 0 ≤ 0)
    (hnn : IsNonneg sigma) (hsub : IsSubadditive sigma) :
    greedyShaperRel sigma ≤ shaperRel sigma := by
  intro A D hp
  exact ⟨(isGreedyShaper_greedyShaperRel sigma).isCausal h0 A D hp,
    (isGreedyShaper_greedyShaperRel sigma).isShaper hnn hsub A D hp⟩

/-- Reduced form of `greedyShaperRel_eq_minimalServiceRel_inf_maximalServiceRel`:
the greedy shaper is exactly minimal service plus shaping,
`greedyShaperRel sigma = minimalServiceRel sigma ⊓ shaperRel sigma` (for `F₀`
sub-additive `sigma`). -/
theorem greedyShaperRel_eq_minimalServiceRel_inf_shaperRel {sigma : ℝ≥0 → EReal}
    (h0 : sigma 0 ≤ 0) (hnn : IsNonneg sigma) (hsub : IsSubadditive sigma) :
    greedyShaperRel sigma = minimalServiceRel sigma ⊓ shaperRel sigma := by
  funext A D
  simp only [Pi.inf_apply, inf_Prop_eq]
  apply propext
  constructor
  · intro hp
    exact ⟨((mem_greedyShaperRel_iff_minimal_and_maximal h0).mp hp).1,
      greedyShaperRel_le_shaperRel h0 hnn hsub A D hp⟩
  · rintro ⟨⟨hca, hge⟩, hsh⟩
    refine le_antisymm (fun t => ?_) hge
    exact le_trans (hsh.2 t)
      (minConv_le_minConv hca (fun _ => le_rfl) t)

end DeepWiki
