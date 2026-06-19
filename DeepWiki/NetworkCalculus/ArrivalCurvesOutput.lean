import DeepWiki.NetworkCalculus.ArrivalCurvesShaper
import DeepWiki.NetworkCalculus.ArrivalCurvesShaperGreedy
import DeepWiki.NetworkCalculus.ArrivalCurvesMaximal
import DeepWiki.NetworkCalculus.Deconvolution
import DeepWiki.NetworkCalculus.DeviationsBoundsServer
import DeepWiki.NetworkCalculus.RealCurvesConv
import DeepWiki.NetworkCalculus.ServiceCurveStrictMinimal

/-! # Output arrival curves
A server offering a minimal service curve `βᵐ`, a maximal service curve `βᴹ`,
and shaping to `σ` propagates arrival curves to its output `D`: the maximal
side is the deconvolution bound `((αᵘ ∗ βᴹ) ⊘ βᵐ) ⊓ σ`, the minimal side the
convolution bound `αˡ ∗ (βᵐ ⊘̄ βᴹ)`; a greedy shaper for sub-additive `σ`
specializes these to `αᵘ ∗ σ` and `αˡ ∗ (σ ⊘̄ σ)`; the backlog bound shifts
a sub-additive `αᵘ` by the vertical deviation `vDev`. The `ℝ≥0∞` reading
(`liftENN`/`toENN`, truncated subtraction) restricts the curves to
nonnegative ones. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Deviation

namespace Deviation

/-- A pair served with a nonnegative maximal service curve `beta` satisfies
the `ℝ≥0∞` convolution upper bound `D t ≤ (A ∗ beta) t`. -/
theorem le_minConv_toENN_of_isMaximalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → EReal}
    (hβ : IsMaximalServiceCurve beta S) (hnn : IsNonneg beta)
    {A D : Curve} (hp : S A D) (t : ℝ≥0) :
    (D t : ℝ≥0∞) ≤ minConv (liftENN ⇑A) (toENN beta) t :=
  (coe_le_minConv_toENN_iff A hnn (D t) t).mpr (hβ A D hp t)

/-- The `ℝ≥0∞` reading of the `EReal` delay curve is the `ℝ≥0∞` delay curve:
`toENN (delayEReal d) = delayNN d`. -/
theorem toENN_delayEReal (d : ℝ≥0) :
    toENN (delayEReal d) = delayNN d := by
  funext t
  show (delayEReal d t).toENNReal = delayNN d t
  rcases le_or_gt t d with ht | ht
  · rw [show delayEReal d t = 0 from delay_eq_zero d ht,
      show delayNN d t = 0 from delay_eq_zero d ht]
    exact EReal.toENNReal_zero
  · rw [show delayEReal d t = ⊤ from delay_eq_top d ht,
      show delayNN d t = ⊤ from delay_eq_top d ht]
    exact EReal.toENNReal_top

end Deviation

/-- The `ℝ≥0∞` reading of a maximal arrival curve: if `curveEReal f` allows the
nonnegative `sigma`, then `liftENN ⇑f` allows `toENN sigma`. -/
theorem IsMaximalArrivalBound.toENN {f : Curve} {sigma : ℝ≥0 → EReal}
    (h : IsMaximalArrivalBound (curveEReal f) sigma) (hnn : IsNonneg sigma) :
    IsMaximalArrivalBound (liftENN ⇑f) (Deviation.toENN sigma) := fun t =>
  (coe_le_minConv_toENN_iff f hnn (f t) t).mpr (h t)

/-- **Output arrival curve, deconvolution part.** A pair served with
nonnegative minimal and maximal service curves `betam`, `betaM`, the arrival
allowing `αu`, has output allowing `(αu ∗ betaM) ⊘ betam` (`minDeconv`,
`ℝ≥0∞` reading). -/
theorem isMaximalArrivalBound_output_deconv
    {S : Curve → Curve → Prop} {betam betaM : ℝ≥0 → EReal}
    {αu : ℝ≥0 → ℝ≥0∞}
    (hβm : IsMinimalServiceCurve betam S) (hnnm : IsNonneg betam)
    (hβM : IsMaximalServiceCurve betaM S) (hnnM : IsNonneg betaM)
    {A D : Curve} (hp : S A D)
    (harru : IsMaximalArrivalBound (liftENN ⇑A) αu) :
    IsMaximalArrivalBound (liftENN ⇑D)
      (minDeconv (minConv αu (toENN betaM)) (toENN betam)) := by
  rw [isMaximalArrivalBound_iff_increment]
  intro t d
  -- replace `D t` by its lower bound `(A ∗ betam) t`
  have h1 : minConv (liftENN ⇑A) (toENN betam) t ≤ (D t : ℝ≥0∞) :=
    minConv_toENN_le_of_isMinimalServiceCurve hβm hnnm hp t
  refine le_trans ?_ (add_le_add h1 le_rfl)
  rw [← tsub_le_iff_right]
  refine le_minConv fun u s hus => ?_
  rw [tsub_le_iff_right]
  -- the `s`-term of the deconvolution supremum recovers `(αu ∗ betaM) (d + s)`
  have h2 : minConv αu (toENN betaM) (d + s)
      ≤ toENN betam s
        + minDeconv (minConv αu (toENN betaM)) (toENN betam) d :=
    le_add_tsub.trans (add_le_add le_rfl
      (sub_le_minDeconv (minConv αu (toENN betaM)) (toENN betam) d s))
  -- `D (t+d) ≤ (A ∗ betaM) (t+d) ≤ A u + (αu ∗ betaM) (d + s)` via the
  -- arrival increment of `A` on each split
  have h3 : (D (t + d) : ℝ≥0∞)
      ≤ liftENN ⇑A u + minConv αu (toENN betaM) (d + s) := by
    rw [← tsub_le_iff_left]
    refine le_minConv fun p q hpq => ?_
    rw [tsub_le_iff_left]
    calc (D (t + d) : ℝ≥0∞)
        ≤ minConv (liftENN ⇑A) (toENN betaM) (t + d) :=
          le_minConv_toENN_of_isMaximalServiceCurve hβM hnnM hp (t + d)
      _ ≤ liftENN ⇑A (u + p) + toENN betaM q :=
          minConv_le_add _ _
            (by rw [add_assoc, hpq, add_comm d s, ← add_assoc, hus])
      _ ≤ (liftENN ⇑A u + αu p) + toENN betaM q :=
          add_le_add
            ((isMaximalArrivalBound_iff_increment _ _).mp harru u p) le_rfl
      _ = liftENN ⇑A u + (αu p + toENN betaM q) := add_assoc _ _ _
  calc (D (t + d) : ℝ≥0∞)
      ≤ liftENN ⇑A u + minConv αu (toENN betaM) (d + s) := h3
    _ ≤ liftENN ⇑A u + (toENN betam s
          + minDeconv (minConv αu (toENN betaM)) (toENN betam) d) :=
        add_le_add le_rfl h2
    _ = liftENN ⇑A u + toENN betam s
          + minDeconv (minConv αu (toENN betaM)) (toENN betam) d :=
        (add_assoc _ _ _).symm

/-- **Output arrival curve (maximal).** Under nonnegative minimal and maximal
service curves `betam`, `betaM` and a nonnegative `sigma`-shaper, the output
allows `((αu ∗ betaM) ⊘ betam) ⊓ sigma` as a maximal arrival curve. -/
theorem isMaximalArrivalBound_output
    {S : Curve → Curve → Prop} {betam betaM sigma : ℝ≥0 → EReal}
    {αu : ℝ≥0 → ℝ≥0∞}
    (hβm : IsMinimalServiceCurve betam S) (hnnm : IsNonneg betam)
    (hβM : IsMaximalServiceCurve betaM S) (hnnM : IsNonneg betaM)
    (hsh : IsShaper sigma S) (hnns : IsNonneg sigma)
    {A D : Curve} (hp : S A D)
    (harru : IsMaximalArrivalBound (liftENN ⇑A) αu) :
    IsMaximalArrivalBound (liftENN ⇑D)
      (minDeconv (minConv αu (toENN betaM)) (toENN betam)
        ⊓ toENN sigma) :=
  (isMaximalArrivalBound_output_deconv hβm hnnm hβM hnnM hp harru).inf
    ((hsh A D hp).toENN hnns)

/-- **Output arrival curve from minimal service alone.** Under causality, a
pair served with a nonnegative minimal service curve `betam`, the arrival
allowing `αu`, has output allowing the deconvolution `αu ⊘ betam`: the output
theorem at `betaM = δ₀` (a maximal service curve of every causal relation)
and the everywhere-`⊤` shaper. -/
theorem isMaximalArrivalBound_output_of_isMinimalServiceCurve
    {S : Curve → Curve → Prop} {betam : ℝ≥0 → EReal}
    {αu : ℝ≥0 → ℝ≥0∞} (hc : IsCausal S)
    (hβm : IsMinimalServiceCurve betam S) (hnnm : IsNonneg betam)
    {A D : Curve} (hp : S A D)
    (harru : IsMaximalArrivalBound (liftENN ⇑A) αu) :
    IsMaximalArrivalBound (liftENN ⇑D) (minDeconv αu (toENN betam)) := by
  have h := isMaximalArrivalBound_output hβm hnnm
    (isMaximalServiceCurve_delayEReal_zero hc) (isNonneg_delayEReal 0)
    (isShaper_top S) (fun _ => le_top) hp harru
  rwa [toENN_delayEReal, conv_delayNN_zero,
    show toENN (⊤ : ℝ≥0 → EReal) = (⊤ : ℝ≥0 → ℝ≥0∞) from rfl,
    inf_top_eq] at h

/-- **Output arrival curve from strict service.** Under causality, a pair
served with a strict service curve `beta`, the arrival allowing `αu`, has
output allowing the deconvolution `αu ⊘ beta`: the minimal-service output
theorem through the strict-to-min-plus inclusion. -/
theorem isMaximalArrivalBound_output_of_isStrictMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0}
    {αu : ℝ≥0 → ℝ≥0∞} (hc : IsCausal S)
    (hβ : IsStrictMinimalServiceCurve beta S)
    {A D : Curve} (hp : S A D)
    (harru : IsMaximalArrivalBound (liftENN ⇑A) αu) :
    IsMaximalArrivalBound (liftENN ⇑D) (minDeconv αu (liftENN beta)) := by
  have h := isMaximalArrivalBound_output_of_isMinimalServiceCurve hc
    (hβ.isMinimalServiceCurve hc) (isNonneg_liftEReal beta) hp harru
  rwa [toENN_liftEReal] at h

/-- Bundle form of the general maximal output theorem: the refined
shaped output curve is itself a maximal arrival curve, for monotone
`betaM` and `sigma`. -/
theorem isMaximalArrivalCurve_output
    {S : Curve → Curve → Prop} {betam betaM sigma : ℝ≥0 → EReal}
    {αu : ℝ≥0 → ℝ≥0∞}
    (hβm : IsMinimalServiceCurve betam S) (hnnm : IsNonneg betam)
    (hβM : IsMaximalServiceCurve betaM S) (hnnM : IsNonneg betaM)
    (hMmono : Monotone betaM)
    (hsh : IsShaper sigma S) (hnns : IsNonneg sigma)
    (hsmono : Monotone sigma)
    {A D : Curve} (hp : S A D)
    (harru : IsMaximalArrivalCurve (liftENN ⇑A) αu) :
    IsMaximalArrivalCurve (liftENN ⇑D)
      (minDeconv (minConv αu (toENN betaM)) (toENN betam)
        ⊓ toENN sigma) :=
  ⟨Monotone.inf
      (monotone_minDeconv _ _
        (monotone_minConv harru.1 (monotone_toENN hMmono)))
      (monotone_toENN hsmono),
    isMaximalArrivalBound_output hβm hnnm hβM hnnM hsh hnns hp
      harru.2⟩

/-- Bundle form of the strict-service output: the deconvolved output
curve is a maximal arrival curve. -/
theorem isMaximalArrivalCurve_output_of_isStrictMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0} {αu : ℝ≥0 → ℝ≥0∞}
    (hc : IsCausal S) (hβ : IsStrictMinimalServiceCurve beta S)
    {A D : Curve} (hp : S A D)
    (harru : IsMaximalArrivalCurve (liftENN ⇑A) αu) :
    IsMaximalArrivalCurve (liftENN ⇑D)
      (minDeconv αu (liftENN beta)) :=
  ⟨monotone_minDeconv _ _ harru.1,
    isMaximalArrivalBound_output_of_isStrictMinimalServiceCurve hc hβ
      hp harru.2⟩

/-- Bundle form: the deconvolved output curve of a min-plus server is
itself a maximal arrival curve — monotonicity transports through the
deconvolution's first slot. -/
theorem isMaximalArrivalCurve_output_of_isMinimalServiceCurve
    {S : Curve → Curve → Prop} {betam : ℝ≥0 → EReal}
    {αu : ℝ≥0 → ℝ≥0∞} (hc : IsCausal S)
    (hβm : IsMinimalServiceCurve betam S) (hnnm : IsNonneg betam)
    {A D : Curve} (hp : S A D)
    (harru : IsMaximalArrivalCurve (liftENN ⇑A) αu) :
    IsMaximalArrivalCurve (liftENN ⇑D)
      (minDeconv αu (toENN betam)) :=
  ⟨monotone_minDeconv _ _ harru.1,
    isMaximalArrivalBound_output_of_isMinimalServiceCurve hc hβm hnnm
      hp harru.2⟩

/-- **Output arrival curve (minimal).** Under causality and nonnegative
minimal and maximal service curves `betam`, `betaM`, the output keeps
`αl ∗ (betam ⊘̄ betaM)` (`maxDeconv`, the dual deconvolution) as a minimal
arrival curve. -/
theorem isMinimalArrivalBound_output
    {S : Curve → Curve → Prop} {betam betaM : ℝ≥0 → EReal}
    {αl : ℝ≥0 → ℝ≥0∞} (hc : IsCausal S)
    (hβm : IsMinimalServiceCurve betam S) (hnnm : IsNonneg betam)
    (hβM : IsMaximalServiceCurve betaM S) (hnnM : IsNonneg betaM)
    {A D : Curve} (hp : S A D)
    (harrl : IsMinimalArrivalBound (liftENN ⇑A) αl) :
    IsMinimalArrivalBound (liftENN ⇑D)
      (minConv αl (maxDeconv (toENN betam) (toENN betaM))) := by
  -- the arrival's minimal curve is null at the origin
  have hA0 : liftENN ⇑A 0 = 0 := A.zero.liftENN
  have hl0 : αl 0 = 0 := by
    have hterm : liftENN ⇑A 0 + αl 0 ≤ maxConv (liftENN ⇑A) αl 0 :=
      add_le_maxConv _ _ (add_zero 0)
    rw [hA0, zero_add] at hterm
    exact le_zero_iff.mp ((hterm.trans (harrl 0)).trans_eq hA0)
  intro T
  refine maxConv_le fun t d htd => ?_
  subst htd
  by_cases hη : minConv αl (maxDeconv (toENN betam) (toENN betaM)) d = 0
  · -- degenerate split: the candidate increment clamps to `0`, monotonicity
    rw [hη, add_zero]
    exact ENNReal.coe_le_coe.mpr (D.mono le_self_add)
  · -- reduce to the convolution lower bound `A ∗ betam ≤ D` at `t + d`
    refine le_trans ?_
      (minConv_toENN_le_of_isMinimalServiceCurve hβm hnnm hp (t + d))
    refine le_minConv fun s w hsw => ?_
    rcases le_or_gt s t with hst | hts
    · -- early split `s ≤ t`: route through the maximal service bound at `t`
      have hw : w = (t - s) + d := by
        refine add_left_cancel (a := s) ?_
        rw [hsw, ← add_assoc, add_tsub_cancel_of_le hst]
      have hx : minConv αl (maxDeconv (toENN betam) (toENN betaM)) d
          ≤ toENN betam w - toENN betaM (t - s) := by
        have h0 : minConv αl (maxDeconv (toENN betam) (toENN betaM)) d
            ≤ αl 0 + maxDeconv (toENN betam) (toENN betaM) d :=
          minConv_le_add _ _ (zero_add d)
        rw [hl0, zero_add] at h0
        refine h0.trans ?_
        have hterm : maxDeconv (toENN betam) (toENN betaM) d
            ≤ toENN betam (d + (t - s)) - toENN betaM (t - s) :=
          maxDeconv_le_sub (toENN betam) (toENN betaM) d (t - s)
        rwa [show d + (t - s) = w from by rw [hw, add_comm]] at hterm
      rcases le_or_gt (toENN betam w) (toENN betaM (t - s)) with hle | hlt
      · -- the deconvolution term clamps to `0`, contradicting the case split
        rw [tsub_eq_zero_of_le hle] at hx
        exact absurd (le_zero_iff.mp hx) hη
      · have hD : (D t : ℝ≥0∞) ≤ liftENN ⇑A s + toENN betaM (t - s) :=
          (le_minConv_toENN_of_isMaximalServiceCurve hβM hnnM hp t).trans
            (minConv_le_add _ _ (add_tsub_cancel_of_le hst))
        calc (D t : ℝ≥0∞)
              + minConv αl (maxDeconv (toENN betam) (toENN betaM)) d
            ≤ (liftENN ⇑A s + toENN betaM (t - s))
              + (toENN betam w - toENN betaM (t - s)) := add_le_add hD hx
          _ = liftENN ⇑A s + (toENN betaM (t - s)
                + (toENN betam w - toENN betaM (t - s))) := add_assoc _ _ _
          _ = liftENN ⇑A s + toENN betam w := by
              rw [add_tsub_cancel_of_le hlt.le]
    · -- late split `t < s`: route through causality and the `αl` increment
      have hd : (s - t) + w = d := by
        refine add_left_cancel (a := t) ?_
        rw [← add_assoc, add_tsub_cancel_of_le hts.le, hsw]
      have hyw : maxDeconv (toENN betam) (toENN betaM) w ≤ toENN betam w := by
        have h0 : maxDeconv (toENN betam) (toENN betaM) w
            ≤ toENN betam (w + 0) - toENN betaM 0 :=
          maxDeconv_le_sub (toENN betam) (toENN betaM) w 0
        rw [add_zero] at h0
        exact h0.trans tsub_le_self
      have hη_le : minConv αl (maxDeconv (toENN betam) (toENN betaM)) d
          ≤ αl (s - t) + toENN betam w :=
        (minConv_le_add _ _ hd).trans (add_le_add le_rfl hyw)
      have hincr : liftENN ⇑A t + αl (s - t) ≤ liftENN ⇑A s := by
        have h := (add_le_maxConv (liftENN ⇑A) αl
          (rfl : t + (s - t) = t + (s - t))).trans (harrl (t + (s - t)))
        rwa [add_tsub_cancel_of_le hts.le] at h
      calc (D t : ℝ≥0∞)
            + minConv αl (maxDeconv (toENN betam) (toENN betaM)) d
          ≤ liftENN ⇑A t + (αl (s - t) + toENN betam w) :=
            add_le_add (ENNReal.coe_le_coe.mpr (hc A D hp t)) hη_le
        _ = (liftENN ⇑A t + αl (s - t)) + toENN betam w := (add_assoc _ _ _).symm
        _ ≤ liftENN ⇑A s + toENN betam w := add_le_add hincr le_rfl

/-- **Output arrival curve for a greedy shaper (maximal).** A pair served by
a greedy shaper for sub-additive nonnegative `sigma`, the arrival allowing
`αu`, has output allowing `αu ∗ sigma`: the output theorem at
`betam = betaM = sigma`, collapsed by `(αu ∗ sigma) ⊘ sigma ≤ αu ∗ sigma`. -/
theorem isMaximalArrivalBound_output_of_isGreedyShaper
    {S : Curve → Curve → Prop} {sigma : ℝ≥0 → EReal} {αu : ℝ≥0 → ℝ≥0∞}
    (hgr : IsGreedyShaper sigma S) (hnns : IsNonneg sigma)
    (hsub : IsSubadditive sigma)
    {A D : Curve} (hp : S A D)
    (harru : IsMaximalArrivalBound (liftENN ⇑A) αu) :
    IsMaximalArrivalBound (liftENN ⇑D) (minConv αu (toENN sigma)) := by
  have h := isMaximalArrivalBound_output hgr.isMinimalServiceCurve hnns
    hgr.isMaximalServiceCurve hnns (hgr.isShaper hnns hsub) hnns hp harru
  refine h.mono (le_trans inf_le_left ?_)
  refine le_trans (minDeconv_minConv_le αu (toENN sigma) (toENN sigma)) ?_
  -- `αu ∗ (sigma ⊘ sigma) ≤ αu ∗ sigma` by sub-additivity of `sigma`
  exact fun t => minConv_le_minConv (fun _ => le_rfl)
    (minDeconv_self_le_of_isSubadditive hsub.toENN) t

/-- **Output arrival curve for a greedy shaper (minimal).** A pair served by
a greedy shaper for nonnegative `sigma` with `sigma 0 ≤ 0`, the arrival
allowing minimal curve `αl`, has output keeping `αl ∗ (sigma ⊘̄ sigma)`: the
output theorem at `betam = betaM = sigma`. -/
theorem isMinimalArrivalBound_output_of_isGreedyShaper
    {S : Curve → Curve → Prop} {sigma : ℝ≥0 → EReal} {αl : ℝ≥0 → ℝ≥0∞}
    (hgr : IsGreedyShaper sigma S) (hnns : IsNonneg sigma)
    (h0 : sigma 0 ≤ 0)
    {A D : Curve} (hp : S A D)
    (harrl : IsMinimalArrivalBound (liftENN ⇑A) αl) :
    IsMinimalArrivalBound (liftENN ⇑D)
      (minConv αl (maxDeconv (toENN sigma) (toENN sigma))) :=
  isMinimalArrivalBound_output (hgr.isCausal h0) hgr.isMinimalServiceCurve
    hnns hgr.isMaximalServiceCurve hnns hp harrl

/-- Bundle form of the general minimal output theorem: the kept
minimal output curve is itself a minimal arrival curve, for monotone
`betam`. -/
theorem isMinimalArrivalCurve_output
    {S : Curve → Curve → Prop} {betam betaM : ℝ≥0 → EReal}
    {αl : ℝ≥0 → ℝ≥0∞} (hc : IsCausal S)
    (hβm : IsMinimalServiceCurve betam S) (hnnm : IsNonneg betam)
    (hmmono : Monotone betam)
    (hβM : IsMaximalServiceCurve betaM S) (hnnM : IsNonneg betaM)
    {A D : Curve} (hp : S A D)
    (harrl : IsMinimalArrivalCurve (liftENN ⇑A) αl) :
    IsMinimalArrivalCurve (liftENN ⇑D)
      (minConv αl (maxDeconv (toENN betam) (toENN betaM))) :=
  ⟨monotone_minConv harrl.1
      (monotone_maxDeconv _ _ (monotone_toENN hmmono)),
    isMinimalArrivalBound_output hc hβm hnnm hβM hnnM hp harrl.2⟩

/-- Bundle form of the greedy-shaper output (maximal): the shaped
output curve `αᵘ ∗ σ` is a maximal arrival curve for monotone `σ`. -/
theorem isMaximalArrivalCurve_output_of_isGreedyShaper
    {S : Curve → Curve → Prop} {sigma : ℝ≥0 → EReal} {αu : ℝ≥0 → ℝ≥0∞}
    (hgr : IsGreedyShaper sigma S) (hnns : IsNonneg sigma)
    (hsub : IsSubadditive sigma) (hmono : Monotone sigma)
    {A D : Curve} (hp : S A D)
    (harru : IsMaximalArrivalCurve (liftENN ⇑A) αu) :
    IsMaximalArrivalCurve (liftENN ⇑D) (minConv αu (toENN sigma)) :=
  ⟨monotone_minConv harru.1 (monotone_toENN hmono),
    isMaximalArrivalBound_output_of_isGreedyShaper hgr hnns hsub hp
      harru.2⟩

/-- Bundle form of the greedy-shaper output (minimal): the kept
minimal curve `αˡ ∗ (σ ⊘̄ σ)` is a minimal arrival curve for monotone
`σ`. -/
theorem isMinimalArrivalCurve_output_of_isGreedyShaper
    {S : Curve → Curve → Prop} {sigma : ℝ≥0 → EReal} {αl : ℝ≥0 → ℝ≥0∞}
    (hgr : IsGreedyShaper sigma S) (hnns : IsNonneg sigma)
    (h0 : sigma 0 ≤ 0) (hmono : Monotone sigma)
    {A D : Curve} (hp : S A D)
    (harrl : IsMinimalArrivalCurve (liftENN ⇑A) αl) :
    IsMinimalArrivalCurve (liftENN ⇑D)
      (minConv αl (maxDeconv (toENN sigma) (toENN sigma))) :=
  ⟨monotone_minConv harrl.1
      (monotone_maxDeconv _ _ (monotone_toENN hmono)),
    isMinimalArrivalBound_output_of_isGreedyShaper hgr hnns h0 hp
      harrl.2⟩

/-- **Output arrival curve from the backlog bound.** A causal pair served
with a nonnegative minimal service curve `beta`, the arrival allowing a
sub-additive `α`, has output allowing `α` shifted by the vertical deviation:
`α + Function.const _ (vDev α (toENN beta))`. -/
theorem isMaximalArrivalBound_output_add_vDev
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0∞}
    (hc : IsCausal S)
    (hβ : IsMinimalServiceCurve beta S) (hnn : IsNonneg beta)
    {A D : Curve} (hp : S A D)
    (harr : IsMaximalArrivalBound (liftENN ⇑A) α) (hsub : IsSubadditive α) :
    IsMaximalArrivalBound (liftENN ⇑D)
      (α + Function.const ℝ≥0 (vDev α (toENN beta))) := by
  refine (isMaximalArrivalBound_output_of_isMinimalServiceCurve
    hc hβ hnn hp harr).mono fun d => ?_
  rw [vDev_eq_deconv_zero]
  exact minDeconv_le_add_minDeconv_zero (toENN beta) hsub d

/-- **Improved output arrival curve from the backlog bound.** With a constant
`c` below `α` on positive times — e.g. the right limit `Function.rightLim α 0`
of a monotone `α` — such that `α - Function.const _ c` is sub-additive, the
vertical-deviation shift improves to `vDev α (toENN beta) - c`, zeroed at the
origin by `δ₀`. -/
theorem isMaximalArrivalBound_output_add_vDev_tsub
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0∞}
    {c : ℝ≥0∞} (hc : IsCausal S)
    (hβ : IsMinimalServiceCurve beta S) (hnn : IsNonneg beta)
    {A D : Curve} (hp : S A D)
    (harr : IsMaximalArrivalBound (liftENN ⇑A) α)
    (hcle : ∀ s, 0 < s → c ≤ α s)
    (hsubc : IsSubadditive (α - Function.const ℝ≥0 c)) :
    IsMaximalArrivalBound (liftENN ⇑D)
      ((α + Function.const ℝ≥0 (vDev α (toENN beta) - c))
        ⊓ delayNN 0) := by
  rw [isMaximalArrivalBound_iff_increment]
  intro t d
  rcases eq_or_ne d 0 with hd | hd
  · -- `d = 0`: the `δ₀` component zeroes the increment
    subst hd
    rw [Pi.inf_apply, show delayNN 0 0 = 0 from delayNN_zero_eq 0,
      inf_eq_right.mpr zero_le, add_zero, add_zero]
  · have hd' : 0 < d := pos_of_ne_zero hd
    rw [Pi.inf_apply, show delayNN 0 d = ⊤ from delay_eq_top 0 hd',
      inf_top_eq]
    -- the deconvolution increment from the minimal-service corollary
    refine le_trans ((isMaximalArrivalBound_iff_increment _ _).mp
      (isMaximalArrivalBound_output_of_isMinimalServiceCurve
        hc hβ hnn hp harr) t d) (add_le_add le_rfl ?_)
    -- `(α ⊘ beta) d ≤ α d + (vDev - c)` for `d > 0`, term by term
    refine iSup_le fun u => ?_
    rcases eq_or_ne u 0 with hu | hu
    · -- the `u = 0` term is absorbed by the truncation
      subst hu
      rw [add_zero]
      exact tsub_le_self.trans le_self_add
    · have hu' : 0 < u := pos_of_ne_zero hu
      have h1 : α (d + u) ≤ ((α d - c) + (α u - c)) + c :=
        le_tsub_add.trans (add_le_add (hsubc d u) le_rfl)
      calc α (d + u) - toENN beta u
          ≤ (((α d - c) + (α u - c)) + c) - toENN beta u :=
            tsub_le_tsub_right h1 _
        _ = ((α d - c) + ((α u - c) + c)) - toENN beta u := by
            rw [add_assoc]
        _ ≤ (α d - c) + (((α u - c) + c) - toENN beta u) := add_tsub_le_assoc
        _ = (α d - c) + (α u - toENN beta u) := by
            rw [tsub_add_cancel_of_le (hcle u hu')]
        _ ≤ (α d - c) + vDev α (toENN beta) :=
            add_le_add le_rfl (vDevAt_le_vDev α (toENN beta) u)
        _ ≤ (α d - c) + ((vDev α (toENN beta) - c) + c) :=
            add_le_add le_rfl le_tsub_add
        _ = ((α d - c) + c) + (vDev α (toENN beta) - c) := by
            rw [add_comm (vDev α (toENN beta) - c) c, ← add_assoc]
        _ = α d + (vDev α (toENN beta) - c) := by
            rw [tsub_add_cancel_of_le (hcle d hd')]

/-! ## Book restatement
A server `S` offering `betam`, `betaM` and shaping to `sigma`, with arrival
`A` allowing maximal curve `αu` and minimal curve `αl`, gives every output
`D` the maximal arrival curve `((αu ∗ betaM) ⊘ betam) ⊓ sigma` and the
minimal arrival curve `αl ∗ (betam ⊘̄ betaM)`. -/
example {S : Curve → Curve → Prop} {betam betaM sigma : ℝ≥0 → EReal}
    {αu αl : ℝ≥0 → ℝ≥0∞} (hSrv : IsServer S)
    (hβm : IsMinimalServiceCurve betam S) (hnnm : IsNonneg betam)
    (hβM : IsMaximalServiceCurve betaM S) (hnnM : IsNonneg betaM)
    (hsh : IsShaper sigma S) (hnns : IsNonneg sigma)
    {A : Curve}
    (harru : IsMaximalArrivalBound (liftENN ⇑A) αu)
    (harrl : IsMinimalArrivalBound (liftENN ⇑A) αl) :
    ∀ D : Curve, S A D →
      IsMaximalArrivalBound (liftENN ⇑D)
        (minDeconv (minConv αu (toENN betaM)) (toENN betam)
          ⊓ toENN sigma) ∧
      IsMinimalArrivalBound (liftENN ⇑D)
        (minConv αl (maxDeconv (toENN betam) (toENN betaM))) :=
  fun _ hp =>
    ⟨isMaximalArrivalBound_output hβm hnnm hβM hnnM hsh hnns hp harru,
      isMinimalArrivalBound_output hSrv.1 hβm hnnm hβM hnnM hp harrl⟩

/-! ## Book restatement (minimal-service corollary)
A server `S` offering only `betam`, with arrival `A` allowing maximal curve
`αu`, gives every output `D` the maximal arrival curve `αu ⊘ betam`. -/
example {S : Curve → Curve → Prop} {betam : ℝ≥0 → EReal}
    {αu : ℝ≥0 → ℝ≥0∞} (hSrv : IsServer S)
    (hβm : IsMinimalServiceCurve betam S) (hnnm : IsNonneg betam)
    {A : Curve} (harru : IsMaximalArrivalBound (liftENN ⇑A) αu) :
    ∀ D : Curve, S A D →
      IsMaximalArrivalBound (liftENN ⇑D) (minDeconv αu (toENN betam)) :=
  fun _ hp => isMaximalArrivalBound_output_of_isMinimalServiceCurve
    hSrv.1 hβm hnnm hp harru

/-! ## Book restatement (greedy-shaper corollary)
A greedy shaper for sub-additive `sigma` in `F₀`, with arrival `A` allowing
maximal curve `αu` and minimal curve `αl`, gives every output `D` the
maximal arrival curve `αu ∗ sigma⋆` (`= αu ∗ sigma`, since sub-additive
`sigma` is its own closure) and the minimal arrival curve
`αl ∗ (sigma ⊘̄ sigma)`. -/
example {S : Curve → Curve → Prop} {sigma : ℝ≥0 → EReal}
    {αu αl : ℝ≥0 → ℝ≥0∞}
    (hgr : IsGreedyShaper sigma S) (hnns : IsNonneg sigma)
    (hsub : IsSubadditive sigma) (h0 : sigma 0 = 0)
    {A : Curve}
    (harru : IsMaximalArrivalBound (liftENN ⇑A) αu)
    (harrl : IsMinimalArrivalBound (liftENN ⇑A) αl) :
    ∀ D : Curve, S A D →
      IsMaximalArrivalBound (liftENN ⇑D)
        (minConv αu (toENN (subadditiveClosureEReal sigma))) ∧
      IsMinimalArrivalBound (liftENN ⇑D)
        (minConv αl (maxDeconv (toENN sigma) (toENN sigma))) :=
  fun _ hp => by
    rw [subadditiveClosureEReal_eq_self sigma hnns.isBddBelowReal.isNeverBot
      hsub h0]
    exact
      ⟨isMaximalArrivalBound_output_of_isGreedyShaper hgr hnns hsub hp harru,
        isMinimalArrivalBound_output_of_isGreedyShaper hgr hnns h0.le hp harrl⟩

/-! ## Book restatement (backlog-bound output curves)
A server `S ⊆ S_mp(beta)`, with arrival `A` allowing a sub-additive
nondecreasing maximal curve `α`, gives every output `D` the maximal arrival
curve `α + vDev(α, beta)`; when `α - Function.const _ (α(0⁺))` is
sub-additive — `α(0⁺) = Function.rightLim α 0`, the right limit of `α` at
the origin — this improves to `(α + (vDev(α, beta) - α(0⁺))) ⊓ δ₀`. -/
example {S : Curve → Curve → Prop} {beta : ℝ≥0 → EReal} {α : ℝ≥0 → ℝ≥0∞}
    (hSrv : IsServer S)
    (hβ : IsMinimalServiceCurve beta S) (hnn : IsNonneg beta)
    {A : Curve}
    (harr : IsMaximalArrivalBound (liftENN ⇑A) α) (hsub : IsSubadditive α)
    (hmono : Monotone α)
    (hsubc : IsSubadditive
      (α - Function.const ℝ≥0 (Function.rightLim α 0))) :
    ∀ D : Curve, S A D →
      IsMaximalArrivalBound (liftENN ⇑D)
        (α + Function.const ℝ≥0 (vDev α (toENN beta))) ∧
      IsMaximalArrivalBound (liftENN ⇑D)
        ((α + Function.const ℝ≥0
            (vDev α (toENN beta) - Function.rightLim α 0))
          ⊓ delayNN 0) :=
  fun _ hp =>
    ⟨isMaximalArrivalBound_output_add_vDev hSrv.1 hβ hnn hp harr hsub,
      isMaximalArrivalBound_output_add_vDev_tsub hSrv.1 hβ hnn hp harr
        (fun _ hs => hmono.rightLim_le hs) hsubc⟩

end DeepWiki
