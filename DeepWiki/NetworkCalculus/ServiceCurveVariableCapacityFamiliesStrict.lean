import DeepWiki.NetworkCalculus.ServiceCurveVariableCapacity

/-! # Variable capacity families: the infinite-family law is false
The book's variable-capacity hierarchy claims
`⋂_{i∈I} S_vcn(βᵢ) = S_vcn((⨆ᵢ βᵢ)^⊛̄)` by "replacing the departure `D`
of the fixed-capacity item by a per-flow capacity `Cᵢ`". That step is a
non sequitur for **infinite** families: each `βᵢ` is realised by *its own*
capacity `Cᵢ`, and there is no shared capacity merging the `{Cᵢ}`.

The obstruction is **Archimedean**, not a jump pathology. With the
*continuous* ramp capacities `Cᵢ(t) = i·t` (each jump-dominated, so jump
domination does **not** repair the infinite case), the families
`βᵢ(u) = min(i·u, 1)` are each realised at the `(0, 0)` pair, yet their
pointwise supremum `⨆ᵢ βᵢ` is the unit step `1_{>0}`. Any single capacity
realising the unit-step floor would need increment `≥ 1` on *every*
positive window; telescoping `n+1` equal windows of `[0, 1]` forces
`C(1) ≥ n+1` for all `n` — impossible for a finite-valued curve. The
finite-family `⊆`, by contrast, holds *under per-`i` jump domination* —
realised by the merged capacity `mergeCapN` in
`ServiceCurveVariableCapacityFamilies`
(`variableCapacityJumpFamilyRel_le_variableCapacityRel_iSup`); the
unconditional finite case is open. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The ramp family `βᵢ(u) = min(i·u, 1)`: a unit floor reached ever
faster as `i` grows, whose supremum is the unit step. -/
noncomputable def rampFamily (i : ℕ) : ℝ≥0 → ℝ≥0 :=
  fun u => min ((i : ℝ≥0) * u) 1

/-- The ramp capacity `Cᵢ(t) = i·t`: continuous, hence jump-dominated. -/
noncomputable def rampCapacity (i : ℕ) : Curve :=
  ⟨fun t => (i : ℝ≥0) * t,
    fun _ _ h => mul_le_mul_of_nonneg_left h (zero_le'),
    mul_zero _,
    isPiecewiseContinuous_of_continuous _ (continuous_const.mul continuous_id),
    isLeftContinuous_of_continuous _ (continuous_const.mul continuous_id)⟩

/-- `rampCapacity i t = i·t`. -/
@[simp] theorem rampCapacity_apply (i : ℕ) (t : ℝ≥0) :
    rampCapacity i t = (i : ℝ≥0) * t := rfl

/-- Each ramp family is realised at the `(0, 0)` pair: the capacity
witness `Cᵢ = rampCapacity i` drives the zero output and dominates
`βᵢ` because `min(i·(t−s), 1) ≤ i·(t−s) = Cᵢ t − Cᵢ s`. -/
theorem zeroPair_mem_variableCapacityRel_rampFamily (i : ℕ) :
    variableCapacityRel (rampFamily i) 0 0 := by
  refine ⟨rampCapacity i, fun t => ?_, fun s t hst => ?_⟩
  · -- the zero output: `A = 0` forces `D t = 0` via the `s = t` split
    show (0 : ℝ≥0) = variableCapacityOutput (⇑(0 : Curve)) (⇑(rampCapacity i)) t
    refine le_antisymm zero_le' ?_
    have h := variableCapacityOutput_le_apply (⇑(0 : Curve)) (⇑(rampCapacity i)) t
    rwa [Curve.zero_apply] at h
  · -- the capacity domination: `min(i·(t−s), 1) ≤ i·t − i·s`
    show min ((i : ℝ≥0) * (t - s)) 1 ≤ (i : ℝ≥0) * t - (i : ℝ≥0) * s
    rw [← mul_tsub]
    exact min_le_left _ _

/-- The pointwise supremum of the ramp family is the unit step:
`(⨆ i, βᵢ) u = 1` for every `u > 0`. -/
theorem iSup_rampFamily_pos {u : ℝ≥0} (hu : 0 < u) :
    (⨆ i, rampFamily i u) = 1 := by
  refine le_antisymm ?_ ?_
  · -- each term is at most `1`
    exact ciSup_le fun i => min_le_right _ _
  · -- some `n·u ≥ 1` saturates the floor
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (u : ℝ))
    have hun : (1 : ℝ≥0) ≤ (n : ℝ≥0) * u := by
      rw [← NNReal.coe_le_coe]
      push_cast
      rw [div_lt_iff₀ (NNReal.coe_pos.mpr hu)] at hn
      linarith
    have hterm : rampFamily n u = 1 := by
      show min ((n : ℝ≥0) * u) 1 = 1
      exact min_eq_right hun
    rw [← hterm]
    exact le_ciSup (f := fun i => rampFamily i u)
      ⟨1, fun _ ⟨i, hi⟩ => hi ▸ min_le_right _ _⟩ n

/-- **The Archimedean escape**: no single capacity realises the unit-step
floor at the `(0, 0)` pair. Any witness `C` has increment `≥ 1` on every
positive window, so telescoping `n+1` equal windows of `[0, 1]` forces
`C(1) ≥ n+1` for all `n` — impossible for a finite-valued curve. -/
theorem not_variableCapacityRel_iSup_rampFamily :
    ¬ variableCapacityRel (fun u => ⨆ i, rampFamily i u) 0 0 := by
  rintro ⟨C, -, hcap⟩
  -- the unit-step floor: every positive window costs at least `1`
  have hstep : ∀ s t : ℝ≥0, s < t → C s + 1 ≤ C t := by
    intro s t hst
    have hfloor : (1 : ℝ≥0) ≤ C t - C s := by
      have h := hcap s t hst.le
      simp only at h
      rwa [iSup_rampFamily_pos (tsub_pos_of_lt hst)] at h
    calc C s + 1 ≤ C s + (C t - C s) := add_le_add le_rfl hfloor
      _ = C t := add_tsub_cancel_of_le (C.mono hst.le)
  -- telescoping over `n+1` equal windows: `C (k·δ) ≥ k`
  have htel : ∀ n : ℕ, (n + 1 : ℝ≥0) ≤ C 1 := by
    intro n
    set δ : ℝ≥0 := (1 : ℝ≥0) / (n + 1) with hδ
    have hδpos : 0 < δ := by
      rw [hδ]
      positivity
    have hkey : ∀ k : ℕ, k ≤ n + 1 → (k : ℝ≥0) ≤ C ((k : ℝ≥0) * δ) := by
      intro k
      induction k with
      | zero =>
          intro _
          rw [Nat.cast_zero, zero_mul]
          exact zero_le'
      | succ k ih =>
          intro hk
          have hstepk : C ((k : ℝ≥0) * δ) + 1 ≤ C (((k : ℝ≥0) + 1) * δ) := by
            refine hstep _ _ ?_
            rw [add_one_mul]
            exact lt_add_of_pos_right _ (by positivity)
          have hih : (k : ℝ≥0) ≤ C ((k : ℝ≥0) * δ) :=
            ih (Nat.le_of_succ_le hk)
          rw [Nat.cast_succ]
          calc (k : ℝ≥0) + 1 ≤ C ((k : ℝ≥0) * δ) + 1 := add_le_add hih le_rfl
            _ ≤ C (((k : ℝ≥0) + 1) * δ) := hstepk
    have hfull := hkey (n + 1) le_rfl
    have harg : ((n + 1 : ℕ) : ℝ≥0) * δ = 1 := by
      rw [hδ, Nat.cast_add, Nat.cast_one, mul_one_div, div_self]
      exact_mod_cast Nat.succ_ne_zero n
    rw [harg] at hfull
    rw [Nat.cast_add, Nat.cast_one] at hfull
    exact hfull
  -- `C 1` is finite, so it is exceeded by some `n + 1`
  obtain ⟨m, hm⟩ := exists_nat_gt (C 1)
  have hcontra : (m + 1 : ℝ≥0) ≤ C 1 := htel m
  have hmlt : (m : ℝ≥0) < (m + 1 : ℝ≥0) := lt_add_of_pos_right _ one_pos
  exact absurd (lt_of_lt_of_le hmlt hcontra) (not_lt.mpr hm.le)

/-- **The infinite-family law is false**: it is not the case that a pair
served by every `βᵢ` of a (countable) family is served by the supremum
`⨆ᵢ βᵢ`. The ramp family `βᵢ(u) = min(i·u, 1)` at the `(0, 0)` pair is a
counterexample — each `βᵢ` is realised, but the unit-step supremum is not.
Mirrors the would-be forward statement's quantifiers. -/
theorem not_forall_iInf_variableCapacityRel_le_iSup :
    ¬ ∀ (beta : ℕ → (ℝ≥0 → ℝ≥0)) (A D : Curve),
        (∀ i, variableCapacityRel (beta i) A D) →
        variableCapacityRel (fun u => ⨆ i, beta i u) A D :=
  fun h => not_variableCapacityRel_iSup_rampFamily
    (h rampFamily 0 0 zeroPair_mem_variableCapacityRel_rampFamily)

/-! ## Book restatement (item 4 fails for infinite families)
The book asserts `⋂_{i∈I} S_vcn(βᵢ) = S_vcn((⨆ᵢ βᵢ)^⊛̄)` for arbitrary
families `I`, citing the fixed-capacity item with "`D` replaced by the
capacities `Cᵢ`". **Adjudicated (three independent analyses with a
recomputing adjudicator):** the swap is a genuine non sequitur for
infinite `I` — each `βᵢ` carries its own capacity `Cᵢ`, and merging an
infinite `{Cᵢ}` is unproven and here impossible. The ramp witnesses are
*continuous* (so jump-dominated): jump domination does **not** rescue the
infinite case; the obstruction is the unbounded idle-period capacity (an
Archimedean escape). The book's literal right-hand side is the
*super-additive closure* `(⨆ᵢ βᵢ)^⊛̄`; for the ramp witness the sup is
the unit step, whose closure is unbounded (its self-convolutions
diverge), so no finite capacity realises it either — the closure form
fails a fortiori, the formalized `¬∀` on the sup itself being the
citable core. The finite-family `⊆`, by contrast, holds under per-`i`
jump domination (`variableCapacityJumpFamilyRel_le_variableCapacityRel_iSup`,
`ServiceCurveVariableCapacityFamilies`); the unconditional finite case
is open. -/
example :
    (∀ i, variableCapacityRel (rampFamily i) 0 0)
      ∧ ¬ variableCapacityRel (fun u => ⨆ i, rampFamily i u) 0 0 :=
  ⟨zeroPair_mem_variableCapacityRel_rampFamily,
    not_variableCapacityRel_iSup_rampFamily⟩

end DeepWiki
