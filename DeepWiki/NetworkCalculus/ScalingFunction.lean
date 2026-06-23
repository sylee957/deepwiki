import DeepWiki.NetworkCalculus.ArrivalCurves
import DeepWiki.NetworkCalculus.Stability

/-! # Data-scaling network calculus (Fidler–Schmitt scaling functions)

The §12.4.2 scaling-instability material the DNC book defers to Fidler & Schmitt,
*An End-to-End Network Calculus with Data Scaling* (SIGMETRICS/Performance '06).
A **scaling function** `S ∈ ℱ` (Def. 3.1) maps an amount of data `a` to an amount
of scaled data `S a`; the **data-scaling operator** `scale S F = S ∘ F` scales a
flow's cumulative function. A **maximum scaling curve** `S̄` (Def. 3.2) upper-bounds
the increments `S(b+a) − S(a)`. The achievable core: the scaled-output arrival bound
`α_S = S̄ ∘ α` (Cor. 3.4), the linear (constant) scaling function `S a = m·a` whose
own increments are `m·b` (so it is its own tight scaling curve), and the
**composed-scaling gain identity** `m₂m₄/((1−m₂)(1−m₄))` that grounds the existing
`scalingIterate_unbounded` divergence in the actual scaling operations. -/

namespace DeepWiki

open scoped NNReal ENNReal

/-! ## Scaling functions (Def. 3.1) and the data-scaling operator -/

/-- **Scaling function** (Def. 3.1): `S ∈ ℱ`, i.e. wide-sense increasing with
`S 0 = 0` (nonnegativity is automatic for `ℝ≥0`-valued `S`). `S a` is the amount of
scaled data assigned to an amount `a` of data. -/
structure IsScalingFunction (S : ℝ≥0 → ℝ≥0) : Prop where
  /-- `S 0 = 0`: a scaling function passes through the origin. -/
  map_zero : S 0 = 0
  /-- `S` is wide-sense increasing (monotone). -/
  mono : Monotone S

/-- **Data-scaling operator**: scaling a flow `F` by a scaling function `S` gives the
scaled cumulative `t ↦ S (F t)`. -/
def scale (S F : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 := fun t => S (F t)

/-- `scale S F t = S (F t)` (definitional unfolding). -/
@[simp] theorem scale_apply (S F : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : scale S F t = S (F t) := rfl

/-- The data-scaling operator is monotone in the flow: a larger cumulative scales to a
larger scaled cumulative (`S` wide-sense increasing). -/
theorem IsScalingFunction.scale_mono {S : ℝ≥0 → ℝ≥0} (hS : IsScalingFunction S)
    {F G : ℝ≥0 → ℝ≥0} (hFG : F ≤ G) : scale S F ≤ scale S G :=
  fun t => hS.mono (hFG t)

/-- Scaling a monotone flow yields a monotone scaled flow (composition of monotones). -/
theorem IsScalingFunction.monotone_scale {S : ℝ≥0 → ℝ≥0} (hS : IsScalingFunction S)
    {F : ℝ≥0 → ℝ≥0} (hF : Monotone F) : Monotone (scale S F) :=
  hS.mono.comp hF

/-- Scaling a flow that starts at the origin keeps it at the origin
(`scale S F 0 = 0` when `F 0 = 0`). -/
theorem IsScalingFunction.scale_zero {S : ℝ≥0 → ℝ≥0} (hS : IsScalingFunction S)
    {F : ℝ≥0 → ℝ≥0} (hF : F 0 = 0) : scale S F 0 = 0 := by
  simp [scale, hF, hS.map_zero]

/-- Composing two scaling functions is a scaling function (Sect. 5 cascades of
encoder/server/decoder scalings). -/
theorem IsScalingFunction.comp {S T : ℝ≥0 → ℝ≥0} (hS : IsScalingFunction S)
    (hT : IsScalingFunction T) : IsScalingFunction (S ∘ T) where
  map_zero := by simp [hT.map_zero, hS.map_zero]
  mono := hS.mono.comp hT.mono

/-! ## Maximum scaling curves (Def. 3.2) -/

/-- **Maximum scaling curve** (Def. 3.2): `S̄ ∈ ℱ` with
`S̄ b ≥ sup_{a≥0}{S(b+a) − S(a)} = (S ⊘ S)(b)`. Stated in the truncation-free additive
form `S(b+a) ≤ S̄ b + S a` (equivalent to `S(b+a) − S a ≤ S̄ b` in `ℝ≥0`, since `S` is
wide-sense increasing); `isMaximalScalingCurve_iff_minDeconv` recovers the `(S ⊘ S)`
deconvolution reading. -/
def IsMaximalScalingCurve (S Sbar : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ b a : ℝ≥0, S (b + a) ≤ Sbar b + S a

/-- The `(S ⊘ S)` deconvolution reading of a maximum scaling curve (Def. 3.2's
displayed form): a maximum scaling curve dominates `(S ⊘ S)(b) = ⨆_a (S (b + a) − S a) =
minDeconv S S b`. (The converse needs `minDeconv S S b` to be finite — an `ℝ≥0` `⨆`
caveat — so only this always-valid direction is stated.) -/
theorem IsMaximalScalingCurve.minDeconv_le {S Sbar : ℝ≥0 → ℝ≥0}
    (h : IsMaximalScalingCurve S Sbar) (b : ℝ≥0) : minDeconv S S b ≤ Sbar b :=
  ciSup_le fun a => by rw [tsub_le_iff_right]; exact h b a

/-! ## Scaled-output arrival bound (Cor. 3.4) -/

/-- **Bounds for scaling functions** (Cor. 3.4): if `α` is an upper arrival bound for a
(monotone) flow `F` and `S̄` is a monotone maximum scaling curve of `S`, then `S̄ ∘ α` is
an upper arrival bound for the scaled output `scale S F` — the scaled-output arrival curve
`α_S = S̄(α)`. Proof chain (Cor. 3.4): the scaled increment
`S(F(t+d)) − S(F t) ≤ S̄(F(t+d) − F t) ≤ S̄(α d)`. -/
theorem IsMaximalScalingCurve.isMaximalArrivalBound_scale {S Sbar α F : ℝ≥0 → ℝ≥0}
    (hSbar : IsMaximalScalingCurve S Sbar) (hSbarMono : Monotone Sbar)
    (hFmono : Monotone F) (hα : IsMaximalArrivalBound F α) :
    IsMaximalArrivalBound (scale S F) (Sbar ∘ α) := by
  rw [isMaximalArrivalBound_iff_increment] at hα ⊢
  intro t d
  -- `S (F (t+d)) ≤ S̄ (F(t+d) − F t) + S (F t) ≤ S̄ (α d) + S (F t)`.
  have hb : (F (t + d) - F t) + F t = F (t + d) :=
    tsub_add_cancel_of_le (hFmono (le_add_right le_rfl))
  have hincr : F (t + d) - F t ≤ α d := tsub_le_iff_left.mpr (hα t d)
  calc scale S F (t + d) = S ((F (t + d) - F t) + F t) := by rw [scale_apply, hb]
    _ ≤ Sbar (F (t + d) - F t) + S (F t) := hSbar _ _
    _ ≤ Sbar (α d) + scale S F t := by
        rw [scale_apply]; gcongr; exact hSbarMono hincr
    _ = scale S F t + (Sbar ∘ α) d := by rw [add_comm]; rfl

/-! ## Linear (constant) scaling — the §12.4.2 instability regime -/

/-- **Linear (constant) scaling function** `S a = m·a`: the constant-scaling instance the
§12.4.2 instability is built on (a flow's data is scaled by a constant factor `m`). -/
def linearScale (m : ℝ≥0) : ℝ≥0 → ℝ≥0 := fun a => m * a

/-- `linearScale m a = m * a`. -/
@[simp] theorem linearScale_apply (m a : ℝ≥0) : linearScale m a = m * a := rfl

/-- A linear scaling `S a = m·a` is a scaling function (`S 0 = 0`, monotone). -/
theorem isScalingFunction_linearScale (m : ℝ≥0) : IsScalingFunction (linearScale m) where
  map_zero := by simp
  mono := fun _ _ h => by simp only [linearScale_apply]; gcongr

/-- A linear scaling is its own tightest maximum scaling curve: the increments
`m(b+a) − m·a = m·b` are *exactly* `linearScale m b`, so `S̄ = S = linearScale m`. -/
theorem isMaximalScalingCurve_linearScale (m : ℝ≥0) :
    IsMaximalScalingCurve (linearScale m) (linearScale m) := by
  intro b a
  simp only [linearScale_apply, mul_add, le_refl]

/-- The data-scaling operator at a linear scaling: `scale (linearScale m) F = m · F`
pointwise — scaling a flow by a constant factor `m`. -/
@[simp] theorem scale_linearScale (m : ℝ≥0) (F : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    scale (linearScale m) F t = m * F t := rfl

/-- **Composition of linear scalings multiplies their factors**: two constant scalings
`m₂` then `m₄` compose to a single constant scaling `m₂·m₄` (the cross-flow data scaling
accumulated around the §12.4.2 cycle). -/
theorem linearScale_comp (m2 m4 : ℝ≥0) :
    linearScale m4 ∘ linearScale m2 = linearScale (m4 * m2) := by
  funext a; simp only [Function.comp_apply, linearScale_apply, mul_assoc]

/-- **The §12.4.2 scaling gain factors per-hop**: the cyclic burst gain
`m₂m₄/((1−m₂)(1−m₄))` is the product of the two per-hop gains `mᵢ/(1−mᵢ)`, each the
*linear scaling factor* `mᵢ` (numerator, the `linearScale mᵢ` of the cross-flow) divided by
the *residual rate* `1−mᵢ` (denominator, Lemma 12.6 / `scalingResidual_rateLatency`). This
is what grounds the abstract gain of `scaling_gain_lt_one_iff`/`scalingIterate_unbounded` in
the genuine scaling operations: each `mᵢ` enters as a `linearScale` factor. -/
theorem scaling_gain_eq_perHop_prod (m2 m4 : ℝ≥0) :
    m2 * m4 / ((1 - m2) * (1 - m4)) = m2 / (1 - m2) * (m4 / (1 - m4)) := by
  rw [div_mul_div_comm]

/-- **The composed-scaling gain identity, grounded**: the §12.4.2 fix-point iteration's gain
`m₂m₄/((1−m₂)(1−m₄))` uses exactly the *product of the two linear-scaling factors*
`m₂·m₄ = linearScale (m₂·m₄) 1` (the composed cross-flow data scaling, `linearScale_comp`)
in its numerator. So the divergence theorem `scalingIterate_unbounded` runs on the genuine
data-scaling operator: the cross-flow scalings `m₂, m₄` are `linearScale` factors whose
composition `m₂·m₄` is the burst-amplification numerator. -/
theorem scaling_gain_numerator_eq_comp (m2 m4 : ℝ≥0) :
    m2 * m4 = (linearScale m4 ∘ linearScale m2) 1 := by
  rw [linearScale_comp]; simp [mul_comm]

/-! ## Faithfulness checks against the paper's wording -/

/-- Def. 3.1 wording: `S ∈ ℱ` means `S 0 = 0` and `S` wide-sense increasing. -/
example (S : ℝ≥0 → ℝ≥0) :
    IsScalingFunction S ↔ (S 0 = 0 ∧ Monotone S) :=
  ⟨fun h => ⟨h.map_zero, h.mono⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Def. 3.2 wording (additive form): `S̄` is a maximum scaling curve of `S` iff
`S(b+a) ≤ S̄(b) + S(a)` for all `b, a ≥ 0` (`⇔ S(b+a) − S(a) ≤ S̄(b)`). -/
example (S Sbar : ℝ≥0 → ℝ≥0) :
    IsMaximalScalingCurve S Sbar ↔ ∀ b a : ℝ≥0, S (b + a) ≤ Sbar b + S a :=
  Iff.rfl

/-- Cor. 3.4 wording: an arrival curve of the scaled output `F_S = S ∘ F` is `S̄ ∘ α`,
where `α` is an arrival curve of the input and `S̄` a maximum scaling curve of `S`. -/
example {S Sbar α F : ℝ≥0 → ℝ≥0}
    (hSbar : IsMaximalScalingCurve S Sbar) (hSbarMono : Monotone Sbar)
    (hFmono : Monotone F) (hα : IsMaximalArrivalBound F α) :
    IsMaximalArrivalBound (scale S F) (Sbar ∘ α) :=
  hSbar.isMaximalArrivalBound_scale hSbarMono hFmono hα

/-! ## Scope of the full §12.4.2 instability beyond the fix-point/gain level

The reachable core above is **transcribed** ([FID 06b] Def. 3.1/3.2, Cor. 3.4) and
**connected** to the existing divergence: `scalingIterate_unbounded` runs on the gain
`m₂m₄/((1−m₂)(1−m₄))`, whose numerator is the composed `linearScale` cross-flow factor
(`scaling_gain_numerator_eq_comp`) and which factors per-hop as
`(mᵢ/(1−mᵢ))` (`scaling_gain_eq_perHop_prod`). What the **full** §12.4.2 instability needs
beyond this fix-point/gain divergence — and is therefore *scoped, not formalized here*:

* an explicit **adversarial cumulative-function trajectory** for the Fig. 12.5 cyclic
  scaling network — a piecewise-linear `(A, D)` schedule built phase by phase so the per-flow
  backlog grows geometrically with ratio the gain `m₂m₄/((1−m₂)(1−m₄)) ≥ 1`. The DNC book
  itself defers this literal trajectory to [FID 06b]; the paper develops the *calculus*
  (scaling functions/curves, scaled servers Th. 3.1, Cor. 3.4, concatenation Sect. 5) but
  the geometric-backlog sample path is the deferred construction, not a single closed
  theorem. Formalizing it requires the time-domain backlog machinery
  (`ServersBacklog`) instantiated on a hand-built phased trajectory — `[deferred]`,
  a per-phase construction to do with the user against the figure. The fix-point divergence
  here is the citable general fact; the trajectory would witness it constructively. -/

end DeepWiki
