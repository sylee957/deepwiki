import Book.ServiceCurveWeaklyStrict

/-! # Variable capacity nodes
The bottom layer of the service-curve hierarchy: the output is driven
by a cumulative capacity process `C` with `β`-dominating increments,
`D(t) = ⨅_{s ≤ t} (A(s) + (C(t) − C(s)))`. The relation is antitone
and invariant under both the non-decreasing closure and the max-plus
self-convolution; causality is derived, not assumed. The inclusion
into the strict layer goes through the closed form
`D(t) = A(Start(t)) + C(t) − C(Start(t))`, whose attainment step the
book glosses — it is formalized separately once adjudicated. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- Output of a variable-capacity node:
`variableCapacityOutput A C t = ⨅_{s ≤ t} (A(s) + (C(t) − C(s)))`. -/
noncomputable def variableCapacityOutput (A C : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : ℝ≥0 :=
  ⨅ s : {s // s ≤ t}, (A s.1 + (C t - C s.1))

/-- Elim: every split bounds the output,
`variableCapacityOutput A C t ≤ A s + (C t − C s)` for `s ≤ t`. -/
theorem variableCapacityOutput_le_add {A C : ℝ≥0 → ℝ≥0} {s t : ℝ≥0} (h : s ≤ t) :
    variableCapacityOutput A C t ≤ A s + (C t - C s) :=
  ciInf_le (OrderBot.bddBelow _) (⟨s, h⟩ : {s // s ≤ t})

/-- Intro: a uniform lower bound over the splits bounds the output
from below. -/
theorem le_variableCapacityOutput {A C : ℝ≥0 → ℝ≥0} {x t : ℝ≥0}
    (h : ∀ s, s ≤ t → x ≤ A s + (C t - C s)) :
    x ≤ variableCapacityOutput A C t :=
  le_ciInf fun s : {s // s ≤ t} => h s.1 s.2

/-- `variableCapacityOutput A C 0 = A 0` — the origin agreement of the start
machinery is free. -/
theorem variableCapacityOutput_zero_eq (A C : ℝ≥0 → ℝ≥0) :
    variableCapacityOutput A C 0 = A 0 := by
  refine le_antisymm ?_ (le_variableCapacityOutput fun s hs => ?_)
  · have h := variableCapacityOutput_le_add (A := A) (C := C) (le_refl 0)
    rwa [tsub_self, add_zero] at h
  · have hs0 : s = 0 := le_antisymm hs zero_le'
    subst hs0
    exact le_self_add

/-- The output is causal: `variableCapacityOutput A C t ≤ A t` (the `s = t`
split). -/
theorem variableCapacityOutput_le_apply (A C : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    variableCapacityOutput A C t ≤ A t := by
  have h := variableCapacityOutput_le_add (A := A) (C := C) (le_refl t)
  rwa [tsub_self, add_zero] at h

/-- The output is capacity-bounded for null-at-origin arrivals:
`variableCapacityOutput A C t ≤ C t` (the `s = 0` split). -/
theorem variableCapacityOutput_le_capacity {A C : ℝ≥0 → ℝ≥0} (h0 : A 0 = 0)
    (t : ℝ≥0) : variableCapacityOutput A C t ≤ C t := by
  refine le_trans (variableCapacityOutput_le_add zero_le') ?_
  rw [h0, zero_add]
  exact tsub_le_self

/-- Restricting the infimum to earlier splits:
`variableCapacityOutput A C t ≤ variableCapacityOutput A C t' + (C t − C t')` for `t' ≤ t`. -/
theorem variableCapacityOutput_le_add_capacity {A C : ℝ≥0 → ℝ≥0} (hCmono : Monotone C)
    {t' t : ℝ≥0} (hst : t' ≤ t) :
    variableCapacityOutput A C t ≤ variableCapacityOutput A C t' + (C t - C t') := by
  rw [← tsub_le_iff_right]
  refine le_variableCapacityOutput fun s hs => ?_
  rw [tsub_le_iff_right, add_assoc,
    add_comm (C t' - C s) (C t - C t'),
    tsub_add_tsub_cancel (hCmono hst) (hCmono hs)]
  exact variableCapacityOutput_le_add (hs.trans hst)

/-- The output is monotone for monotone arrivals and capacity. -/
theorem variableCapacityOutput_mono {A C : ℝ≥0 → ℝ≥0} (hAmono : Monotone A)
    (hCmono : Monotone C) : Monotone (variableCapacityOutput A C) := by
  intro t' t hst
  refine le_variableCapacityOutput fun s hs => ?_
  rcases le_total s t' with hst' | ht's
  · exact le_trans (variableCapacityOutput_le_add hst')
      (add_le_add le_rfl (tsub_le_tsub_right (hCmono hst) (C s)))
  · exact le_trans (variableCapacityOutput_le_apply A C t')
      (le_trans (hAmono ht's) le_self_add)

/-- The output is left-continuous once the capacity is — squeezed
between monotonicity and the restricted infimum; no continuity of the
arrivals is needed. -/
theorem isLeftContinuous_variableCapacityOutput {A C : ℝ≥0 → ℝ≥0}
    (hAmono : Monotone A) (hCmono : Monotone C)
    (hClc : IsLeftContinuous C) :
    IsLeftContinuous (variableCapacityOutput A C) := by
  intro t
  show Filter.Tendsto (variableCapacityOutput A C) (nhdsWithin t (Set.Iio t))
    (nhds (variableCapacityOutput A C t))
  have hCt : Filter.Tendsto (fun t' => C t - C t')
      (nhdsWithin t (Set.Iio t)) (nhds 0) := by
    have h := ((continuous_sub_left (C t)).tendsto (C t)).comp (hClc t)
    rwa [tsub_self] at h
  have hlow : Filter.Tendsto
      (fun t' => variableCapacityOutput A C t - (C t - C t'))
      (nhdsWithin t (Set.Iio t)) (nhds (variableCapacityOutput A C t)) := by
    have h := ((continuous_sub_left (variableCapacityOutput A C t)).tendsto 0).comp hCt
    rwa [tsub_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow
    tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t' (ht' : t' ∈ Set.Iio t)
    rw [tsub_le_iff_right]
    exact variableCapacityOutput_le_add_capacity hCmono (le_of_lt ht')
  · filter_upwards [self_mem_nhdsWithin] with t' (ht' : t' ∈ Set.Iio t)
    exact variableCapacityOutput_mono hAmono hCmono (le_of_lt ht')

/-- The variable-capacity-node relation: some cumulative capacity
process `C` with `β`-dominating increments drives the output,
`D = variableCapacityOutput A C`. -/
def variableCapacityRel (beta : ℝ≥0 → ℝ≥0) :
    Curve → Curve → Prop :=
  fun A D => ∃ C : Curve,
    (∀ t, D t = variableCapacityOutput ⇑A ⇑C t)
    ∧ ∀ s t, s ≤ t → beta (t - s) ≤ C t - C s

/-- `variableCapacityRel beta A D` unfolds to the capacity witness. -/
theorem mem_variableCapacityRel_iff {beta : ℝ≥0 → ℝ≥0}
    {A D : Curve} :
    variableCapacityRel beta A D ↔ ∃ C : Curve,
      (∀ t, D t = variableCapacityOutput ⇑A ⇑C t)
      ∧ ∀ s t, s ≤ t → beta (t - s) ≤ C t - C s :=
  Iff.rfl

/-- Causality is derived, with no hypotheses: the `s = t` split of
the driving infimum gives `D ≤ A` for every served pair. -/
theorem isCausal_variableCapacityRel (beta : ℝ≥0 → ℝ≥0) :
    IsCausal (variableCapacityRel beta) := by
  intro A D hp
  obtain ⟨C, hD, -⟩ := hp
  intro t
  rw [hD t]
  exact variableCapacityOutput_le_apply ⇑A ⇑C t

/-- The variable-capacity relation is antitone in `beta`: the same
capacity witness dominates a smaller curve. -/
theorem variableCapacityRel_mono {beta beta' : ℝ≥0 → ℝ≥0}
    (h : beta' ≤ beta) :
    variableCapacityRel beta ≤ variableCapacityRel beta' := by
  intro A D hp
  obtain ⟨C, hD, hcap⟩ := hp
  exact ⟨C, hD, fun s t hst => le_trans (h _) (hcap s t hst)⟩

/-- The variable-capacity relation is closure-invariant:
`variableCapacityRel (ndClosure beta) = variableCapacityRel beta` for
`beta` bounded on each `[0, t]` — the capacity increments dominate
every earlier value of `beta` through monotonicity of `C`. -/
theorem variableCapacityRel_closure (beta : ℝ≥0 → ℝ≥0)
    (hbdd : ∀ t, BddAbove
      (Set.range (fun u : {u // u ≤ t} => beta u.1))) :
    variableCapacityRel (ndClosure beta)
      = variableCapacityRel beta := by
  funext A D
  refine propext ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨C, hD, hcap⟩ := hp
    exact ⟨C, hD, fun s t hst =>
      le_trans (le_ndClosure beta hbdd (t - s)) (hcap s t hst)⟩
  · obtain ⟨C, hD, hcap⟩ := hp
    refine ⟨C, hD, fun s t hst => ?_⟩
    unfold ndClosure
    haveI : Nonempty {v // v ≤ t - s} := ⟨⟨0, zero_le'⟩⟩
    refine ciSup_le fun v => ?_
    obtain ⟨v, (hv : v ≤ t - s)⟩ := v
    have hsv : s + v ≤ t := by
      have h1 : s + v ≤ s + (t - s) := by gcongr
      rwa [add_tsub_cancel_of_le hst] at h1
    have hb := hcap s (s + v) le_self_add
    rw [show (s + v) - s = v by
      rw [add_comm]; exact add_tsub_cancel_right v s] at hb
    exact le_trans hb (tsub_le_tsub_right (C.mono hsv) (C s))

/-- The capacity increments dominate the max-plus self-convolution:
the variable-capacity relation absorbs `maxConvProj`. -/
theorem variableCapacityRel_le_maxConvProj (beta : ℝ≥0 → ℝ≥0) :
    variableCapacityRel beta
      ≤ variableCapacityRel (maxConvProj beta beta) := by
  intro A D hp
  obtain ⟨C, hD, hcap⟩ := hp
  refine ⟨C, hD, fun s t hst => ?_⟩
  refine maxConvProj_le fun a b hab => ?_
  have hsum : s + (a + b) = t := by
    rw [hab, add_tsub_cancel_of_le hst]
  have hsa : s + a ≤ t :=
    le_trans (by gcongr; exact le_self_add) hsum.le
  have hrs : (s + a) - s = a := by
    rw [add_comm]; exact add_tsub_cancel_right a s
  have htr : t - (s + a) = b := by
    rw [← hsum,
      show s + (a + b) = (s + a) + b by ring,
      add_tsub_cancel_left]
  have h1 := hcap s (s + a) le_self_add
  rw [hrs] at h1
  have h2 := hcap (s + a) t hsa
  rw [htr] at h2
  calc beta a + beta b
      ≤ (C (s + a) - C s) + (C t - C (s + a)) := add_le_add h1 h2
    _ = (C t - C (s + a)) + (C (s + a) - C s) := add_comm _ _
    _ = C t - C s :=
        tsub_add_tsub_cancel (C.mono hsa) (C.mono le_self_add)

/-- Every max-plus self-convolution power is absorbed. -/
theorem variableCapacityRel_le_maxConvProjPow (beta : ℝ≥0 → ℝ≥0)
    (n : ℕ) :
    variableCapacityRel beta
      ≤ variableCapacityRel (maxConvProjPow beta n) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      exact le_trans ih
        (variableCapacityRel_le_maxConvProj (maxConvProjPow beta n))

end DeepWiki
