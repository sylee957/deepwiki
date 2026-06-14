import Book.ServiceCurveVariableCapacityStart
import Book.ServiceCurveFamilies

namespace DeepWiki
open Set Topology Filter Function Finset
open scoped Classical NNReal ENNReal BigOperators

/-! # Variable-capacity families (the `⊆` direction under jump domination)
For a finite family of variable-capacity (`vcn`) servers, the trajectory intersection is
served by the pointwise supremum `⨆ᵢ βᵢ` — provided each per-`i` capacity is jump-dominated
(the repair the book elides with "Idem item 3, replacing `D` by `C`"; cf. the single-server
jump repairs). The witness is the merged capacity `∑ᵢ (Cᵢ − D) + D`. The reverse
`⊇` is unconditional. Adjudicated 2026-06-14 (prove-vs-refute panel): no finite-family
counterexample exists; the unconditional `⊆` is open in the rising-arrival/harvested-jump
regime, and for *infinite* families it is refuted in the `…FamiliesStrict` sibling. -/

/-! ## The n-ary merged capacity (function level) -/

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {A : ℝ≥0 → ℝ≥0} {C : ι → ℝ≥0 → ℝ≥0} {D : ℝ≥0 → ℝ≥0}

/-- The merged capacity `∑ᵢ (Cᵢ − D) + D`: each capacity's "waste" `Cᵢ − D` summed back onto `D`. -/
noncomputable def mergeCapN (C : ι → ℝ≥0 → ℝ≥0) (D : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => (∑ i, (C i t - D t)) + D t

omit [Nonempty ι] in
/-- `mergeCapN C D t` read in `ℝ`: `∑ᵢ (Cᵢ t − D t) + D t` (when `D ≤ Cᵢ`). -/
theorem mergeCapN_coe (hDC : ∀ i, D ≤ C i) (t : ℝ≥0) :
    (mergeCapN C D t : ℝ) = (∑ i, ((C i t : ℝ) - D t)) + D t := by
  unfold mergeCapN
  push_cast
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [NNReal.coe_sub (hDC i t)]

omit [Nonempty ι] in
/-- `mergeCapN C D` is monotone (sum of monotone wastes plus monotone `D`). -/
theorem mergeCapN_mono (hDmono : Monotone D) (hDC : ∀ i, D ≤ C i)
    (hW : ∀ i, Monotone (fun t => (C i t : ℝ) - D t)) :
    Monotone (mergeCapN C D) := by
  intro s t hst
  rw [← NNReal.coe_le_coe, mergeCapN_coe hDC, mergeCapN_coe hDC]
  have hsum : (∑ i, ((C i s : ℝ) - D s)) ≤ ∑ i, ((C i t : ℝ) - D t) :=
    Finset.sum_le_sum fun i _ => hW i hst
  have h3 : (D s : ℝ) ≤ D t := by exact_mod_cast hDmono hst
  linarith

omit [Fintype ι] [Nonempty ι] in
/-- On `t`'s backlogged period the `i`-th capacity increment from the start equals `D`'s increment (jump-dominated attainment). -/
theorem waste_const_on_backlogN
    (hAmono : Monotone A) (hAlc : IsLeftContinuous A)
    (i : ι) (hCmono : Monotone (C i)) (hjump : IsJumpDominated A (C i))
    (hD : D = variableCapacityOutput A (C i)) (t : ℝ≥0) :
    D (start A D t) + (C i t - C i (start A D t)) = D t := by
  subst hD
  set D := variableCapacityOutput A (C i) with hDdef
  set σ := start A D t with hσ
  have hσt : σ ≤ t := start_le A D t
  have hbl : IsBacklogged A D (Set.Ioc σ t) := by
    intro u hu
    obtain ⟨hσu, hut⟩ := hu
    have hcaus : D u ≤ A u := variableCapacityOutput_le_apply A (C i) u
    rcases hcaus.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have : u ≤ σ := le_csSup ⟨t, fun x hx => hx.1⟩ ⟨hut, heq.symm⟩
      exact absurd this (not_le.mpr hσu)
  exact variableCapacityOutput_add_capacity_eq_of_isBacklogged
    hAmono hAlc hCmono hjump hσt hbl

/-- **The merged capacity reproduces `D`**: `variableCapacityOutput A (mergeCapN C D) = D`, under per-`i` jump domination. -/
theorem variableCapacityOutput_mergeCapN_eq
    (hAmono : Monotone A) (hAlc : IsLeftContinuous A) (h0 : A 0 = 0)
    (hCmono : ∀ i, Monotone (C i)) (hj : ∀ i, IsJumpDominated A (C i))
    (hD : ∀ i, D = variableCapacityOutput A (C i))
    (hDlc : IsLeftContinuous D)
    (t : ℝ≥0) :
    variableCapacityOutput A (mergeCapN C D) t = D t := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hDmono : Monotone D := by
    rw [hD i₀]; exact variableCapacityOutput_mono hAmono (hCmono i₀)
  have hDC : ∀ i, D ≤ C i := fun i u => by
    rw [hD i]; exact variableCapacityOutput_le_capacity h0 u
  have hCa : ∀ u, D u ≤ A u := fun u => by
    rw [hD i₀]; exact variableCapacityOutput_le_apply A (C i₀) u
  have hW : ∀ i, Monotone (fun t => (C i t : ℝ) - D t) := by
    intro i
    have h := sub_variableCapacityOutput_mono h0 (hCmono i)
    intro s t hst
    have hh := h hst
    rw [← NNReal.coe_le_coe] at hh
    rw [NNReal.coe_sub (by rw [hD i] at *; exact variableCapacityOutput_le_capacity h0 s),
      NNReal.coe_sub (by rw [hD i] at *; exact variableCapacityOutput_le_capacity h0 t)] at hh
    simp only [hD i]; exact hh
  set Cm := mergeCapN C D with hCm
  refine le_antisymm ?_ ?_
  · set σ := start A D t with hσ
    have hσt : σ ≤ t := start_le A D t
    have hD0 : A 0 = D 0 := by rw [hD i₀, variableCapacityOutput_zero_eq, h0]
    have hAσ : A σ = D σ := apply_start_eq hAlc hDlc hD0 hCa t
    have hwc' : ∀ i, (C i t : ℝ) - D t = (C i σ : ℝ) - D σ := by
      intro i
      have hc := waste_const_on_backlogN hAmono hAlc i (hCmono i) (hj i) (hD i) t
      have : ((D σ + (C i t - C i σ) : ℝ≥0) : ℝ) = ((D t : ℝ≥0) : ℝ) := by rw [hc]
      rw [NNReal.coe_add, NNReal.coe_sub ((hCmono i) hσt)] at this
      linarith
    refine le_trans (variableCapacityOutput_le_add hσt) ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_add,
      NNReal.coe_sub ((mergeCapN_mono hDmono hDC hW) hσt),
      mergeCapN_coe hDC, mergeCapN_coe hDC]
    have hsumeq : (∑ i, ((C i t : ℝ) - D t)) = ∑ i, ((C i σ : ℝ) - D σ) :=
      Finset.sum_congr rfl fun i _ => hwc' i
    have hAσ' : (A σ : ℝ) = D σ := by rw [hAσ]
    have hDt : (D σ : ℝ) ≤ D t := by exact_mod_cast hDmono hσt
    rw [hsumeq]; linarith
  · refine le_variableCapacityOutput fun s hs => ?_
    have hincr : C i₀ t - C i₀ s ≤ Cm t - Cm s := by
      rw [← NNReal.coe_le_coe, NNReal.coe_sub ((hCmono i₀) hs),
        NNReal.coe_sub ((mergeCapN_mono hDmono hDC hW) hs),
        mergeCapN_coe hDC, mergeCapN_coe hDC]
      have hsingle : ((C i₀ t : ℝ) - D t) - ((C i₀ s : ℝ) - D s)
          ≤ (∑ i, ((C i t : ℝ) - D t)) - (∑ i, ((C i s : ℝ) - D s)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.single_le_sum (f := fun i => ((C i t : ℝ) - D t) - ((C i s : ℝ) - D s))
          (fun i _ => ?_) (Finset.mem_univ i₀)
        have := hW i hs
        linarith
      have h3 : (D s : ℝ) ≤ D t := by exact_mod_cast hDmono hs
      linarith
    calc D t = variableCapacityOutput A (C i₀) t := by rw [hD i₀]
      _ ≤ A s + (C i₀ t - C i₀ s) := variableCapacityOutput_le_add hs
      _ ≤ A s + (Cm t - Cm s) := add_le_add le_rfl hincr

omit [Nonempty ι] in
/-- Each `Cⱼ` increment is dominated by the merged-capacity increment. -/
theorem capacity_le_mergeCapN_increment
    (hDmono : Monotone D) (hDC : ∀ i, D ≤ C i)
    (hW : ∀ i, Monotone (fun t => (C i t : ℝ) - D t))
    (hCmono : ∀ i, Monotone (C i))
    (j : ι) {s t : ℝ≥0} (hst : s ≤ t) :
    C j t - C j s ≤ mergeCapN C D t - mergeCapN C D s := by
  rw [← NNReal.coe_le_coe, NNReal.coe_sub ((hCmono j) hst),
    NNReal.coe_sub ((mergeCapN_mono hDmono hDC hW) hst),
    mergeCapN_coe hDC, mergeCapN_coe hDC]
  have hsingle : ((C j t : ℝ) - D t) - ((C j s : ℝ) - D s)
      ≤ (∑ i, ((C i t : ℝ) - D t)) - (∑ i, ((C i s : ℝ) - D s)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.single_le_sum (f := fun i => ((C i t : ℝ) - D t) - ((C i s : ℝ) - D s))
      (fun i _ => ?_) (Finset.mem_univ j)
    have := hW i hst
    linarith
  have h3 : (D s : ℝ) ≤ D t := by exact_mod_cast hDmono hst
  linarith

/-! ## The relation-level finite-family theorem -/

/-- A pair jump-dominated-`vcn`-served by every member `βᵢ` of the family. -/
def variableCapacityJumpFamilyRel {ι : Type*} (β : ι → ℝ≥0 → ℝ≥0) :
    Curve → Curve → Prop :=
  fun A D => ∀ i, variableCapacityJumpRel (β i) A D

/-- `variableCapacityJumpFamilyRel β A D` unfolds to per-member jump-dominated `vcn` service. -/
theorem mem_variableCapacityJumpFamilyRel_iff {ι : Type*} {β : ι → ℝ≥0 → ℝ≥0} {A D : Curve} :
    variableCapacityJumpFamilyRel β A D ↔ ∀ i, variableCapacityJumpRel (β i) A D := Iff.rfl

/-- **Finite-family `⊆`, jump-dominated repair**: a finite family of jump-dominated variable-capacity servers is jointly served by the pointwise supremum `⨆ᵢ βᵢ` — the merged capacity `mergeCapN` carries every `βᵢ`-increment at once and reproduces `D`. (The unconditional `⊆` is open in the rising-arrival/harvested-jump regime; for infinite families it is false, `ServiceCurveVariableCapacityFamiliesStrict`.) -/
theorem variableCapacityJumpFamilyRel_le_variableCapacityRel_iSup
    {ι : Type*} [Fintype ι] [Nonempty ι] (β : ι → ℝ≥0 → ℝ≥0) :
    variableCapacityJumpFamilyRel β
      ≤ fun A D => variableCapacityRel (fun u => ⨆ i, β i u) A D := by
  intro A D hp
  choose C hD hcap hj using hp
  have h0 : (A : ℝ≥0 → ℝ≥0) 0 = 0 := A.zero
  have hCmono : ∀ i, Monotone (C i : ℝ≥0 → ℝ≥0) := fun i => (C i).mono
  have hDfun : ∀ i, (D : ℝ≥0 → ℝ≥0) = variableCapacityOutput (⇑A) (⇑(C i)) :=
    fun i => funext (hD i)
  have hDmono : Monotone (D : ℝ≥0 → ℝ≥0) := D.mono
  have hDC : ∀ i, (D : ℝ≥0 → ℝ≥0) ≤ C i := fun i u => by
    rw [hDfun i]; exact variableCapacityOutput_le_capacity h0 u
  have hW : ∀ i, Monotone (fun t => ((C i) t : ℝ) - D t) := by
    intro i
    have h := sub_variableCapacityOutput_mono h0 (hCmono i)
    intro s t hst
    have hh := h hst
    rw [← NNReal.coe_le_coe] at hh
    rw [NNReal.coe_sub (by rw [hDfun i] at *; exact variableCapacityOutput_le_capacity h0 s),
      NNReal.coe_sub (by rw [hDfun i] at *; exact variableCapacityOutput_le_capacity h0 t)] at hh
    simp only [hDfun i]; exact hh
  let W : ι → Curve := fun i => (C i).wasteSub D (by
    intro s t hst
    have := hW i hst
    rw [← NNReal.coe_le_coe, NNReal.coe_sub (hDC i s), NNReal.coe_sub (hDC i t)]
    exact this)
  let Cm : Curve := (∑ i, W i) + D
  have hCmFun : (Cm : ℝ≥0 → ℝ≥0) = mergeCapN (fun i => ⇑(C i)) ⇑D := by
    funext t
    show (∑ i, W i) t + D t = (∑ i, ((C i) t - D t)) + D t
    rw [Curve.coe_sum]
    rfl
  refine ⟨Cm, fun t => ?_, fun s t hst => ?_⟩
  · rw [hCmFun]
    exact (variableCapacityOutput_mergeCapN_eq A.mono A.leftCont h0 hCmono hj
      hDfun D.leftCont t).symm
  · rw [hCmFun]
    refine ciSup_le fun i => ?_
    refine le_trans (hcap i s t hst) ?_
    exact capacity_le_mergeCapN_increment hDmono hDC hW hCmono i hst

example {ι : Type*} [Fintype ι] [Nonempty ι] (β : ι → ℝ≥0 → ℝ≥0)
    (A D : Curve) (hp : ∀ i, variableCapacityJumpRel (β i) A D) :
    variableCapacityRel (fun u => ⨆ i, β i u) A D :=
  variableCapacityJumpFamilyRel_le_variableCapacityRel_iSup β A D hp

example {ι : Type*} [Fintype ι] [Nonempty ι] (β : ι → ℝ≥0 → ℝ≥0)
    (hbdd : ∀ t, BddAbove (Set.range
      (fun n => maxConvProjPow (fun u => ⨆ i, β i u) n t)))
    (A D : Curve) (hp : ∀ i, variableCapacityJumpRel (β i) A D) :
    variableCapacityRel (superadditiveClosureMax (fun u => ⨆ i, β i u)) A D := by
  rw [variableCapacityRel_superadditiveClosureMax hbdd]
  exact variableCapacityJumpFamilyRel_le_variableCapacityRel_iSup β A D hp

/-! ## The reverse inclusion (unconditional) -/

/-- The easy half: a pair served by the pointwise-sup curve is served by every family
member (`vcn` is antitone, and `β i ≤ ⨆ⱼ βⱼ`). Any finite index; no jump domination. -/
theorem iInter_variableCapacityRel_of_variableCapacityRel_iSup {ι : Type*} [Fintype ι]
    {β : ι → ℝ≥0 → ℝ≥0} {A D : Curve}
    (hp : variableCapacityRel (fun t => ⨆ i, β i t) A D) :
    ∀ i, variableCapacityRel (β i) A D := by
  intro i
  refine variableCapacityRel_mono (fun t => ?_) A D hp
  exact le_ciSup (Set.Finite.bddAbove (Set.finite_range (fun j => β j t))) i

end DeepWiki
