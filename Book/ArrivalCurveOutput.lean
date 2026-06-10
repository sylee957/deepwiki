import Book.ArrivalCurveShaper
import Book.ArrivalCurveShaperGreedy
import Book.ArrivalCurvesMaximal
import Book.Deconvolution
import Book.DeviationsBoundsServer
import Book.RealCurvesConv

/-! # Output arrival curves
A server offering a minimal service curve `βᵐ`, a maximal service curve `βᴹ`,
and shaping to `σ` propagates arrival curves to its output `D`: the maximal
side is the deconvolution bound `((αᵘ ∗ βᴹ) ⊘ βᵐ) ⊓ σ`, the minimal side the
convolution bound `αˡ ∗ (βᵐ ⊘̄ βᴹ)`; a greedy shaper for sub-additive `σ`
specializes these to `αᵘ ∗ σ` and `αˡ ∗ (σ ⊘̄ σ)`. The `ℝ≥0∞` reading
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
    (D t : ℝ≥0∞) ≤ minConv (liftENN ⇑A) (toENN beta) t := by
  rw [← EReal.coe_ennreal_le_coe_ennreal_iff, coe_minConv_toENN A hnn t]
  calc (((D t : ℝ≥0) : ℝ≥0∞) : EReal)
      = curveE D t := EReal.coe_nnreal_eq_coe_real (D t)
    _ ≤ minConv (curveE A) beta t := hβ A D hp t

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

/-- Sub-additivity transports through the `ℝ≥0∞` reading: `toENN sigma` is
sub-additive when `sigma` is. -/
theorem IsSubadditive.toENN {sigma : ℝ≥0 → EReal}
    (hsub : IsSubadditive sigma) : IsSubadditive (Deviation.toENN sigma) :=
  fun u s =>
    (EReal.toENNReal_le_toENNReal (hsub u s)).trans EReal.toENNReal_add_le

/-- The `ℝ≥0∞` reading of a maximal arrival curve: if `curveE f` allows the
nonnegative `sigma`, then `liftENN ⇑f` allows `toENN sigma`. -/
theorem IsMaximalArrivalCurve.toENN {f : Curve} {sigma : ℝ≥0 → EReal}
    (h : IsMaximalArrivalCurve (curveE f) sigma) (hnn : IsNonneg sigma) :
    IsMaximalArrivalCurve (liftENN ⇑f) (Deviation.toENN sigma) := by
  intro t
  rw [← EReal.coe_ennreal_le_coe_ennreal_iff, coe_minConv_toENN f hnn t]
  calc ((liftENN ⇑f t : ℝ≥0∞) : EReal)
      = curveE f t := EReal.coe_nnreal_eq_coe_real (f t)
    _ ≤ minConv (curveE f) sigma t := h t

/-- **Output arrival curve, deconvolution part.** A pair served with
nonnegative minimal and maximal service curves `betam`, `betaM`, the arrival
allowing `αu`, has output allowing `(αu ∗ betaM) ⊘ betam` (`minDeconv`,
`ℝ≥0∞` reading). -/
theorem isMaximalArrivalCurve_output_deconv
    {S : Curve → Curve → Prop} {betam betaM : ℝ≥0 → EReal}
    {αu : ℝ≥0 → ℝ≥0∞}
    (hβm : IsMinimalServiceCurve betam S) (hnnm : IsNonneg betam)
    (hβM : IsMaximalServiceCurve betaM S) (hnnM : IsNonneg betaM)
    {A D : Curve} (hp : S A D)
    (harru : IsMaximalArrivalCurve (liftENN ⇑A) αu) :
    IsMaximalArrivalCurve (liftENN ⇑D)
      (minDeconv (minConv αu (toENN betaM)) (toENN betam)) := by
  rw [isMaximalArrivalCurve_iff_increment]
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
            ((isMaximalArrivalCurve_iff_increment _ _).mp harru u p) le_rfl
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
theorem isMaximalArrivalCurve_output
    {S : Curve → Curve → Prop} {betam betaM sigma : ℝ≥0 → EReal}
    {αu : ℝ≥0 → ℝ≥0∞}
    (hβm : IsMinimalServiceCurve betam S) (hnnm : IsNonneg betam)
    (hβM : IsMaximalServiceCurve betaM S) (hnnM : IsNonneg betaM)
    (hsh : IsShaper sigma S) (hnns : IsNonneg sigma)
    {A D : Curve} (hp : S A D)
    (harru : IsMaximalArrivalCurve (liftENN ⇑A) αu) :
    IsMaximalArrivalCurve (liftENN ⇑D)
      (minDeconv (minConv αu (toENN betaM)) (toENN betam)
        ⊓ toENN sigma) :=
  (isMaximalArrivalCurve_output_deconv hβm hnnm hβM hnnM hp harru).inf
    ((hsh A D hp).toENN hnns)

/-- **Output arrival curve from minimal service alone.** Under causality, a
pair served with a nonnegative minimal service curve `betam`, the arrival
allowing `αu`, has output allowing the deconvolution `αu ⊘ betam`: the output
theorem at `betaM = δ₀` (a maximal service curve of every causal relation)
and the everywhere-`⊤` shaper. -/
theorem isMaximalArrivalCurve_output_of_isMinimalServiceCurve
    {S : Curve → Curve → Prop} {betam : ℝ≥0 → EReal}
    {αu : ℝ≥0 → ℝ≥0∞} (hc : IsCausal S)
    (hβm : IsMinimalServiceCurve betam S) (hnnm : IsNonneg betam)
    {A D : Curve} (hp : S A D)
    (harru : IsMaximalArrivalCurve (liftENN ⇑A) αu) :
    IsMaximalArrivalCurve (liftENN ⇑D) (minDeconv αu (toENN betam)) := by
  have h := isMaximalArrivalCurve_output hβm hnnm
    (isMaximalServiceCurve_delayEReal_zero hc) (isNonneg_delayEReal 0)
    (isShaper_top S) (fun _ => le_top) hp harru
  rwa [toENN_delayEReal, conv_delayNN_zero,
    show toENN (⊤ : ℝ≥0 → EReal) = (⊤ : ℝ≥0 → ℝ≥0∞) from rfl,
    inf_top_eq] at h

/-- **Output arrival curve (minimal).** Under causality and nonnegative
minimal and maximal service curves `betam`, `betaM`, the output keeps
`αl ∗ (betam ⊘̄ betaM)` (`maxDeconv`, the dual deconvolution) as a minimal
arrival curve. -/
theorem isMinimalArrivalCurve_output
    {S : Curve → Curve → Prop} {betam betaM : ℝ≥0 → EReal}
    {αl : ℝ≥0 → ℝ≥0∞} (hc : IsCausal S)
    (hβm : IsMinimalServiceCurve betam S) (hnnm : IsNonneg betam)
    (hβM : IsMaximalServiceCurve betaM S) (hnnM : IsNonneg betaM)
    {A D : Curve} (hp : S A D)
    (harrl : IsMinimalArrivalCurve (liftENN ⇑A) αl) :
    IsMinimalArrivalCurve (liftENN ⇑D)
      (minConv αl (maxDeconv (toENN betam) (toENN betaM))) := by
  -- the arrival's minimal curve is null at the origin
  have hA0 : liftENN ⇑A 0 = 0 := by
    show ((A 0 : ℝ≥0) : ℝ≥0∞) = 0
    rw [show A 0 = 0 from A.zero, ENNReal.coe_zero]
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
theorem isMaximalArrivalCurve_output_of_isGreedyShaper
    {S : Curve → Curve → Prop} {sigma : ℝ≥0 → EReal} {αu : ℝ≥0 → ℝ≥0∞}
    (hgr : IsGreedyShaper sigma S) (hnns : IsNonneg sigma)
    (hsub : IsSubadditive sigma)
    {A D : Curve} (hp : S A D)
    (harru : IsMaximalArrivalCurve (liftENN ⇑A) αu) :
    IsMaximalArrivalCurve (liftENN ⇑D) (minConv αu (toENN sigma)) := by
  have h := isMaximalArrivalCurve_output hgr.isMinimalServiceCurve hnns
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
theorem isMinimalArrivalCurve_output_of_isGreedyShaper
    {S : Curve → Curve → Prop} {sigma : ℝ≥0 → EReal} {αl : ℝ≥0 → ℝ≥0∞}
    (hgr : IsGreedyShaper sigma S) (hnns : IsNonneg sigma)
    (h0 : sigma 0 ≤ 0)
    {A D : Curve} (hp : S A D)
    (harrl : IsMinimalArrivalCurve (liftENN ⇑A) αl) :
    IsMinimalArrivalCurve (liftENN ⇑D)
      (minConv αl (maxDeconv (toENN sigma) (toENN sigma))) :=
  isMinimalArrivalCurve_output (hgr.isCausal h0) hgr.isMinimalServiceCurve
    hnns hgr.isMaximalServiceCurve hnns hp harrl

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
    (harru : IsMaximalArrivalCurve (liftENN ⇑A) αu)
    (harrl : IsMinimalArrivalCurve (liftENN ⇑A) αl) :
    ∀ D : Curve, S A D →
      IsMaximalArrivalCurve (liftENN ⇑D)
        (minDeconv (minConv αu (toENN betaM)) (toENN betam)
          ⊓ toENN sigma) ∧
      IsMinimalArrivalCurve (liftENN ⇑D)
        (minConv αl (maxDeconv (toENN betam) (toENN betaM))) :=
  fun _ hp =>
    ⟨isMaximalArrivalCurve_output hβm hnnm hβM hnnM hsh hnns hp harru,
      isMinimalArrivalCurve_output hSrv.1 hβm hnnm hβM hnnM hp harrl⟩

/-! ## Book restatement (minimal-service corollary)
A server `S` offering only `betam`, with arrival `A` allowing maximal curve
`αu`, gives every output `D` the maximal arrival curve `αu ⊘ betam`. -/
example {S : Curve → Curve → Prop} {betam : ℝ≥0 → EReal}
    {αu : ℝ≥0 → ℝ≥0∞} (hSrv : IsServer S)
    (hβm : IsMinimalServiceCurve betam S) (hnnm : IsNonneg betam)
    {A : Curve} (harru : IsMaximalArrivalCurve (liftENN ⇑A) αu) :
    ∀ D : Curve, S A D →
      IsMaximalArrivalCurve (liftENN ⇑D) (minDeconv αu (toENN betam)) :=
  fun _ hp => isMaximalArrivalCurve_output_of_isMinimalServiceCurve
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
    (harru : IsMaximalArrivalCurve (liftENN ⇑A) αu)
    (harrl : IsMinimalArrivalCurve (liftENN ⇑A) αl) :
    ∀ D : Curve, S A D →
      IsMaximalArrivalCurve (liftENN ⇑D)
        (minConv αu (toENN (subadditiveClosureEReal sigma))) ∧
      IsMinimalArrivalCurve (liftENN ⇑D)
        (minConv αl (maxDeconv (toENN sigma) (toENN sigma))) :=
  fun _ hp => by
    rw [subadditiveClosureEReal_eq_self sigma hnns.bddBelowReal.neverBot
      hsub h0]
    exact
      ⟨isMaximalArrivalCurve_output_of_isGreedyShaper hgr hnns hsub hp harru,
        isMinimalArrivalCurve_output_of_isGreedyShaper hgr hnns h0.le hp harrl⟩

end DeepWiki
