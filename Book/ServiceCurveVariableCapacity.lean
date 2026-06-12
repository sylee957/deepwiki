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

/-- The variable-capacity-node relation: some cumulative capacity
process `C` with `β`-dominating increments drives the output,
`D(t) = ⨅_{s ≤ t} (A(s) + (C(t) − C(s)))`. -/
def variableCapacityRel (beta : ℝ≥0 → ℝ≥0) :
    Curve → Curve → Prop :=
  fun A D => ∃ C : Curve,
    (∀ t, D t = ⨅ s : {s // s ≤ t}, (A s.1 + (C t - C s.1)))
    ∧ ∀ s t, s ≤ t → beta (t - s) ≤ C t - C s

/-- `variableCapacityRel beta A D` unfolds to the capacity witness. -/
theorem mem_variableCapacityRel_iff {beta : ℝ≥0 → ℝ≥0}
    {A D : Curve} :
    variableCapacityRel beta A D ↔ ∃ C : Curve,
      (∀ t, D t = ⨅ s : {s // s ≤ t}, (A s.1 + (C t - C s.1)))
      ∧ ∀ s t, s ≤ t → beta (t - s) ≤ C t - C s :=
  Iff.rfl

/-- Causality is derived: the `s = t` split of the driving infimum
gives `D ≤ A`. -/
theorem variableCapacityRel_causal {beta : ℝ≥0 → ℝ≥0} {A D : Curve}
    (hp : variableCapacityRel beta A D) : D ≤ A := by
  obtain ⟨C, hD, -⟩ := hp
  intro t
  rw [hD t]
  refine le_trans (ciInf_le (OrderBot.bddBelow _) ⟨t, le_rfl⟩) ?_
  rw [tsub_self, add_zero]

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
