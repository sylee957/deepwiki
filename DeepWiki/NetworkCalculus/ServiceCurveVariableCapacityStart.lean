import DeepWiki.NetworkCalculus.ServiceCurveVariableCapacity
import Mathlib.Topology.Semicontinuity.Basic

/-! # Variable capacity nodes: the start-anchored closed form
The book's closed form `D(t) = A(Start(t)) + C(t) − C(Start(t))` is
false for general left-continuous capacity: a right jump of `C` fired
into a right-limit-empty queue is harvested by the driving infimum
without being attained (see the counterexample ladder). It is
repaired by *jump domination* — the arrivals absorb every right jump
of the capacity (`IsJumpDominated`), automatic for monotone arrivals
and continuous capacity. Under it the infimum is attained at an
equality point, the
closed form holds, and the variable-capacity node is a strict server
for its capacity curve — the repaired bottom inclusion of the
hierarchy. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Filter Topology Set Function

/-- Jump domination: the arrivals absorb every right jump of the
capacity, `A(u) + C(u⁺) ≤ A(u⁺) + C(u)`. -/
def IsJumpDominated (A C : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ u, A u + Function.rightLim C u ≤ Function.rightLim A u + C u

/-- Continuous capacity is jump-dominated by monotone arrivals. -/
theorem isJumpDominated_of_continuous {A C : ℝ≥0 → ℝ≥0}
    (hAmono : Monotone A) (hC : Continuous C) :
    IsJumpDominated A C := by
  intro u
  have hCr : Function.rightLim C u = C u := by
    letI : (nhdsWithin u (Set.Ioi u)).NeBot := inferInstance
    exact rightLim_eq_of_tendsto
      ((hC.continuousAt).tendsto.mono_left nhdsWithin_le_nhds)
  rw [hCr]
  exact add_le_add (hAmono.le_rightLim le_rfl) le_rfl

/-- Under jump domination the real reading of `A − C` is lower
semicontinuous on every `[0, t]`: a left jump of `C` pushes it up, and
on the right the jump domination caps the drop. -/
theorem lowerSemicontinuousOn_sub_of_isJumpDominated
    {A C : ℝ≥0 → ℝ≥0} (hAmono : Monotone A)
    (hAlc : IsLeftContinuous A) (hCmono : Monotone C)
    (hjump : IsJumpDominated A C) (t : ℝ≥0) :
    LowerSemicontinuousOn (fun u => (A u : ℝ) - (C u : ℝ))
      (Set.Icc 0 t) := by
  intro x _ y hy
  have hsplit : nhdsWithin x (Set.Icc 0 t)
      ≤ nhdsWithin x (Set.Iio x) ⊔ nhdsWithin x (Set.Ici x) := by
    rw [← nhdsWithin_union]
    refine nhdsWithin_mono x fun v _ => ?_
    rcases lt_or_ge v x with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine Filter.Eventually.filter_mono hsplit ?_
  rw [Filter.eventually_sup]
  refine ⟨?_, ?_⟩
  · -- from the left: `C` only drops, `A` converges
    have hev : ∀ᶠ v in nhdsWithin x (Set.Iio x),
        y + (C x : ℝ) < (A v : ℝ) := by
      have hcoe : ContinuousWithinAt (fun v => (A v : ℝ))
          (Set.Iio x) x :=
        (NNReal.continuous_coe.continuousAt).comp_continuousWithinAt
          (hAlc x)
      exact hcoe.eventually (eventually_gt_nhds (by linarith))
    filter_upwards [hev, self_mem_nhdsWithin] with v hv
      (hvx : v ∈ Set.Iio x)
    have hC : (C v : ℝ) ≤ C x :=
      NNReal.coe_le_coe.mpr (hCmono (le_of_lt hvx))
    linarith
  · -- from the right: split off the point itself
    have hsplit2 : nhdsWithin x (Set.Ici x)
        ≤ nhdsWithin x {x} ⊔ nhdsWithin x (Set.Ioi x) := by
      rw [← nhdsWithin_union]
      refine nhdsWithin_mono x fun v hv => ?_
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hv) with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    refine Filter.Eventually.filter_mono hsplit2 ?_
    rw [Filter.eventually_sup]
    refine ⟨?_, ?_⟩
    · rw [nhdsWithin_singleton, Filter.eventually_pure]
      exact hy
    · have hεpos : (0 : ℝ) < ((A x : ℝ) - C x - y) / 2 := by linarith
      have hCev : ∀ᶠ v in nhdsWithin x (Set.Ioi x),
          (C v : ℝ) < ((Function.rightLim C x : ℝ≥0) : ℝ)
            + ((A x : ℝ) - C x - y) / 2 := by
        have htends : Tendsto (fun v => (C v : ℝ))
            (nhdsWithin x (Set.Ioi x))
            (nhds ((Function.rightLim C x : ℝ≥0) : ℝ)) :=
          (NNReal.continuous_coe.continuousAt).tendsto.comp
            (hCmono.tendsto_rightLim x)
        exact htends.eventually (eventually_lt_nhds (by linarith))
      filter_upwards [hCev, self_mem_nhdsWithin] with v hv
        (hvx : v ∈ Set.Ioi x)
      have hA : ((Function.rightLim A x : ℝ≥0) : ℝ) ≤ A v :=
        NNReal.coe_le_coe.mpr (hAmono.rightLim_le hvx)
      have hj : (A x : ℝ) + ((Function.rightLim C x : ℝ≥0) : ℝ)
          ≤ ((Function.rightLim A x : ℝ≥0) : ℝ) + (C x : ℝ) := by
        exact_mod_cast hjump x
      linarith

/-- **Attainment**: under jump domination the driving infimum is
attained — there is a minimizing split realizing the output. -/
theorem exists_isMinOn_variableCapacityOutput {A C : ℝ≥0 → ℝ≥0}
    (hAmono : Monotone A) (hAlc : IsLeftContinuous A)
    (hCmono : Monotone C) (hjump : IsJumpDominated A C) (t : ℝ≥0) :
    ∃ s, s ≤ t
      ∧ (∀ u, u ≤ t → A s + (C t - C s) ≤ A u + (C t - C u))
      ∧ variableCapacityOutput A C t = A s + (C t - C s) := by
  obtain ⟨s, hs, hmin⟩ :=
    (lowerSemicontinuousOn_sub_of_isJumpDominated hAmono hAlc hCmono
      hjump t).exists_isMinOn (Set.nonempty_Icc.mpr zero_le)
      isCompact_Icc
  have hterm : ∀ u, u ≤ t →
      A s + (C t - C s) ≤ A u + (C t - C u) := by
    intro u hu
    have hg := (isMinOn_iff.mp hmin) u (Set.mem_Icc.mpr ⟨zero_le, hu⟩)
    rw [← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub (hCmono (Set.mem_Icc.mp hs).2),
      NNReal.coe_sub (hCmono hu)]
    linarith
  exact ⟨s, (Set.mem_Icc.mp hs).2, hterm,
    le_antisymm (variableCapacityOutput_le_add (Set.mem_Icc.mp hs).2)
      (le_variableCapacityOutput hterm)⟩

/-- Every minimizing split is an equality point: the arrivals at it
are fully served. -/
theorem apply_eq_variableCapacityOutput_of_isMinOn {A C : ℝ≥0 → ℝ≥0}
    (hCmono : Monotone C) {s t : ℝ≥0} (hst : s ≤ t)
    (hmin : ∀ u, u ≤ t → A s + (C t - C s) ≤ A u + (C t - C u)) :
    A s = variableCapacityOutput A C s := by
  refine le_antisymm (le_variableCapacityOutput fun u hu => ?_)
    (variableCapacityOutput_le_apply A C s)
  have h := hmin u (hu.trans hst)
  rw [← NNReal.coe_le_coe] at h ⊢
  push_cast [NNReal.coe_sub (hCmono hst),
    NNReal.coe_sub (hCmono (hu.trans hst)),
    NNReal.coe_sub (hCmono hu)] at h ⊢
  linarith

/-- **The start-anchored closed form, repaired**: under jump
domination the output is anchored at the start of the backlogged
period, `D(t) = A(Start(t)) + (C(t) − C(Start(t)))`. False for
general left-continuous capacity — see the counterexample ladder. -/
theorem variableCapacityOutput_start_eq {A C : ℝ≥0 → ℝ≥0}
    (hAmono : Monotone A) (hAlc : IsLeftContinuous A)
    (hCmono : Monotone C) (hClc : IsLeftContinuous C)
    (hjump : IsJumpDominated A C) (t : ℝ≥0) :
    variableCapacityOutput A C t
      = A (start A (variableCapacityOutput A C) t)
        + (C t - C (start A (variableCapacityOutput A C) t)) := by
  obtain ⟨s, hst, hmin, hattain⟩ :=
    exists_isMinOn_variableCapacityOutput hAmono hAlc hCmono hjump t
  have heqpt : A s = variableCapacityOutput A C s :=
    apply_eq_variableCapacityOutput_of_isMinOn hCmono hst hmin
  have hsσ : s ≤ start A (variableCapacityOutput A C) t :=
    le_csSup ⟨t, fun x hx => hx.1⟩ ⟨hst, heqpt⟩
  have hσt : start A (variableCapacityOutput A C) t ≤ t := start_le _ _ t
  have hσeq : A (start A (variableCapacityOutput A C) t)
      = variableCapacityOutput A C (start A (variableCapacityOutput A C) t) :=
    apply_start_eq hAlc
      (isLeftContinuous_variableCapacityOutput hAmono hCmono hClc)
      (variableCapacityOutput_zero_eq A C).symm (variableCapacityOutput_le_apply A C) t
  refine le_antisymm (variableCapacityOutput_le_add hσt) ?_
  rw [hattain, hσeq]
  refine le_trans (add_le_add (variableCapacityOutput_le_add hsσ) le_rfl) ?_
  rw [add_assoc, add_comm (C _ - C s) (C t - C _),
    tsub_add_tsub_cancel (hCmono hσt) (hCmono hsσ)]

/-- **The backlogged window carries the full capacity**: under jump
domination, on a backlogged window the output increment equals the
capacity increment — the direct route to strict service, with no
left-continuity of the capacity needed. -/
theorem variableCapacityOutput_add_capacity_eq_of_isBacklogged {A C : ℝ≥0 → ℝ≥0}
    (hAmono : Monotone A) (hAlc : IsLeftContinuous A)
    (hCmono : Monotone C) (hjump : IsJumpDominated A C)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged A (variableCapacityOutput A C) (Set.Ioc s t)) :
    variableCapacityOutput A C s + (C t - C s) = variableCapacityOutput A C t := by
  refine le_antisymm ?_ (variableCapacityOutput_le_add_capacity hCmono hst)
  obtain ⟨u, hut, hmin, hattain⟩ :=
    exists_isMinOn_variableCapacityOutput hAmono hAlc hCmono hjump t
  have hequ : A u = variableCapacityOutput A C u :=
    apply_eq_variableCapacityOutput_of_isMinOn hCmono hut hmin
  have hus : u ≤ s := by
    by_contra hcon
    push Not at hcon
    exact absurd hequ (ne_of_gt (hbl u ⟨hcon, hut⟩))
  rw [hattain]
  refine le_trans (add_le_add (variableCapacityOutput_le_add hus) le_rfl) ?_
  rw [add_assoc, add_comm (C s - C u) (C t - C s),
    tsub_add_tsub_cancel (hCmono hst) (hCmono hus)]

/-- A jump-dominated variable-capacity output is a strict server for
its capacity curve. -/
theorem strictServiceRel_of_variableCapacityOutput {beta : ℝ≥0 → ℝ≥0}
    {A D : Curve} (C : Curve)
    (hD : ∀ t, D t = variableCapacityOutput ⇑A ⇑C t)
    (hcap : ∀ s t, s ≤ t → beta (t - s) ≤ C t - C s)
    (hjump : IsJumpDominated ⇑A ⇑C) :
    strictServiceRel beta A D := by
  constructor
  · intro t
    rw [hD t]
    exact variableCapacityOutput_le_apply ⇑A ⇑C t
  · intro s t hst hbl
    have hbl' : IsBacklogged ⇑A (variableCapacityOutput ⇑A ⇑C) (Set.Ioc s t) := by
      intro v hv
      have h := hbl v hv
      rwa [hD v] at h
    have heq : variableCapacityOutput ⇑A ⇑C s + (C t - C s) = variableCapacityOutput ⇑A ⇑C t :=
      variableCapacityOutput_add_capacity_eq_of_isBacklogged A.mono
        A.leftCont C.mono hjump hst hbl'
    rw [hD s, hD t, ← heq]
    exact add_le_add le_rfl (hcap s t hst)

/-- The jump-dominated variable-capacity relation: the capacity
witness additionally has its right jumps absorbed by the arrivals. -/
def variableCapacityJumpRel (beta : ℝ≥0 → ℝ≥0) :
    Curve → Curve → Prop :=
  fun A D => ∃ C : Curve,
    (∀ t, D t = variableCapacityOutput ⇑A ⇑C t)
    ∧ (∀ s t, s ≤ t → beta (t - s) ≤ C t - C s)
    ∧ IsJumpDominated ⇑A ⇑C

/-- `variableCapacityJumpRel beta A D` unfolds to the constrained
capacity witness. -/
theorem mem_variableCapacityJumpRel_iff {beta : ℝ≥0 → ℝ≥0}
    {A D : Curve} :
    variableCapacityJumpRel beta A D ↔ ∃ C : Curve,
      (∀ t, D t = variableCapacityOutput ⇑A ⇑C t)
      ∧ (∀ s t, s ≤ t → beta (t - s) ≤ C t - C s)
      ∧ IsJumpDominated ⇑A ⇑C :=
  Iff.rfl

/-- The jump-dominated relation is antitone in `beta`. -/
theorem variableCapacityJumpRel_mono {beta beta' : ℝ≥0 → ℝ≥0}
    (h : beta' ≤ beta) :
    variableCapacityJumpRel beta ≤ variableCapacityJumpRel beta' := by
  intro A D hp
  obtain ⟨C, hD, hcap, hjump⟩ := hp
  exact ⟨C, hD, fun s t hst => le_trans (h _) (hcap s t hst), hjump⟩

/-- The jump-dominated relation is closure-invariant. -/
theorem variableCapacityJumpRel_closure (beta : ℝ≥0 → ℝ≥0)
    (hbdd : ∀ t, BddAbove
      (Set.range (fun u : {u // u ≤ t} => beta u.1))) :
    variableCapacityJumpRel (ndClosure beta)
      = variableCapacityJumpRel beta := by
  funext A D
  refine propext ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨C, hD, hcap, hjump⟩ := hp
    exact ⟨C, hD, fun s t hst =>
      le_trans (le_ndClosure beta hbdd (t - s)) (hcap s t hst), hjump⟩
  · obtain ⟨C, hD, hcap, hjump⟩ := hp
    exact ⟨C, hD, ndClosure_le_capacity hcap, hjump⟩

/-- Forgetting the jump constraint lands in the plain
variable-capacity relation. -/
theorem variableCapacityJumpRel_le_variableCapacityRel
    (beta : ℝ≥0 → ℝ≥0) :
    variableCapacityJumpRel beta ≤ variableCapacityRel beta := by
  intro A D hp
  obtain ⟨C, h1, h2, -⟩ := hp
  exact ⟨C, h1, h2⟩

/-- **Hierarchy, repaired bottom inclusion**: a jump-dominated
variable-capacity node is a strict server. For general
left-continuous capacity the inclusion fails — capacity right jumps
fired into a right-limit-empty queue are counted by `beta` yet
physically lost (see the counterexample ladder). -/
theorem variableCapacityJumpRel_le_strictServiceRel
    (beta : ℝ≥0 → ℝ≥0) :
    variableCapacityJumpRel beta ≤ strictServiceRel beta := by
  intro A D hp
  obtain ⟨C, hD, hcap, hjump⟩ := hp
  exact strictServiceRel_of_variableCapacityOutput C hD hcap hjump

/-! ## Book restatement (the closed form and the bottom inclusion)
The book derives `D(t) = A(Start(t)) + C(t) − C(Start(t))` for every
variable-capacity node and concludes `S_vcn(β) ⊆ S_strict(β)`
unconditionally. **Adjudicated (three independent analyses,
unanimous):** both fail for left-continuous capacity with right
jumps — the infimum step "necessarily reached at `Start(t)`" is a non
sequitur, and the book's own closing remark that monotonicity is
unused marks the gap (the repair's right side runs on monotonicity
of the arrivals — right-limit jump domination is meaningless without
it). The repair is jump domination
`A(u) + C(u⁺) ≤ A(u⁺) + C(u)` (`IsJumpDominated`), automatic for
continuous capacity; the equality criterion the book attaches to the
hierarchy (finite self-deconvolution) is refuted by the same
counterexample family. -/
example (beta : ℝ≥0 → ℝ≥0) :
    variableCapacityJumpRel beta ≤ strictServiceRel beta
      ∧ variableCapacityJumpRel beta ≤ variableCapacityRel beta :=
  ⟨variableCapacityJumpRel_le_strictServiceRel beta,
    variableCapacityJumpRel_le_variableCapacityRel beta⟩

end DeepWiki
