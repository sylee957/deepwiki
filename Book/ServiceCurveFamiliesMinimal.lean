import Book.ServiceCurveFamilies
import Book.ServiceCurveMonotony
import Mathlib.Topology.Order.Lattice

/-! # Min-plus families: the forcing direction (Thm 9.4 item 1, ⟹)
The forward half of the finite-family min-plus criterion: if a finite family `(βᵢ)` and `(β'ⱼ)`
induce the same trajectory intersection, their downward closures agree. The engine is a
*forcing lemma*: `⋂ᵢ S_mp(βᵢ) ⊆ S_mp(β') ⟹ ∃i, β' ≤ βᵢ`. Its witness is the **step-staircase
arrival** `A(u) = ⨅ᵢ (β'(T) − β'(vᵢ) if u ≤ T − vᵢ else β'(T))`, built here as a `Curve` (the
families are monotone, so this is finite-valued — no `+∞` arrivals needed, unlike items 2/3).
`vᵢ` are crossing points where `βᵢ(vᵢ) < β'(vᵢ)` and `T = maxᵢ vᵢ`. -/

namespace DeepWiki

open Set Topology Filter
open scoped Classical NNReal ENNReal

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- `+ y` distributes through a finite `inf'` over `EReal` (`+ y` is monotone and the inf is
attained). -/
theorem inf'_add_ereal {κ : Type*} {s : Finset κ} (hne : s.Nonempty) (x : κ → EReal) (y : EReal) :
    s.inf' hne x + y = s.inf' hne (fun j => x j + y) := by
  obtain ⟨j₀, hj₀, hxj₀⟩ := Finset.exists_mem_eq_inf' hne x
  refine le_antisymm (Finset.le_inf' _ _ (fun j hj => ?_)) ?_
  · gcongr
    exact Finset.inf'_le _ hj
  · calc s.inf' hne (fun j => x j + y) ≤ x j₀ + y := Finset.inf'_le _ hj₀
      _ = s.inf' hne x + y := by rw [hxj₀]

/-- **Min-plus convolution distributes over a finite `inf'` of arrivals**:
`(⨅ⱼ fⱼ) ∗ g = ⨅ⱼ (fⱼ ∗ g)`. The keystone that turns the inf-staircase arrival's convolution
into a finite inf of single-step convolutions (each piecewise-continuous). -/
theorem minConv_finset_inf' {κ : Type*} {s : Finset κ} (hne : s.Nonempty)
    (f : κ → ℝ≥0 → EReal) (g : ℝ≥0 → EReal) (t : ℝ≥0) :
    minConv (fun u => s.inf' hne (fun j => f j u)) g t
      = s.inf' hne (fun j => minConv (f j) g t) := by
  simp only [minConv, inf'_add_ereal]
  exact le_antisymm
    (Finset.le_inf' _ _ (fun j hj => le_iInf (fun p => (iInf_le _ p).trans (Finset.inf'_le _ hj))))
    (le_iInf (fun p => Finset.le_inf' _ _ (fun j hj => (Finset.inf'_le _ hj).trans (iInf_le _ p))))

/-- A single step term of the forcing staircase: `β'(T) − β'(vᵢ)` up to `T − vᵢ`, then `β'(T)`. -/
noncomputable def forcingStep (β' : ℝ≥0 → ℝ≥0) (vi T : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun u => if u ≤ T - vi then β' T - β' vi else β' T

/-- The step term is monotone (a single upward jump at `T − vᵢ`). -/
theorem forcingStep_mono (β' : ℝ≥0 → ℝ≥0) (vi T : ℝ≥0) : Monotone (forcingStep β' vi T) := by
  intro a b hab
  simp only [forcingStep]
  by_cases hb : b ≤ T - vi
  · rw [if_pos hb, if_pos (le_trans hab hb)]
  · rw [if_neg hb]
    by_cases ha : a ≤ T - vi
    · rw [if_pos ha]; exact tsub_le_self
    · rw [if_neg ha]

/-- The step term is left-continuous. -/
theorem forcingStep_leftCont (β' : ℝ≥0 → ℝ≥0) (vi T : ℝ≥0) :
    IsLeftContinuous (forcingStep β' vi T) := by
  intro u₀
  rcases le_or_gt u₀ (T - vi) with h | h
  · have hc : ContinuousWithinAt (fun _ : ℝ≥0 => β' T - β' vi) (Iio u₀) u₀ :=
      continuousWithinAt_const
    refine hc.congr_of_eventuallyEq ?_ (if_pos h)
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact if_pos (le_of_lt (lt_of_lt_of_le hu h))
  · have hc : ContinuousWithinAt (fun _ : ℝ≥0 => β' T) (Iio u₀) u₀ := continuousWithinAt_const
    refine hc.congr_of_eventuallyEq ?_ (if_neg (not_le.mpr h))
    filter_upwards [Ioo_mem_nhdsLT h] with u hu
    exact if_neg (not_le.mpr hu.1)

/-- The forcing staircase arrival `A(u) = ⨅ᵢ forcingStep β' vᵢ T u`. -/
noncomputable def forcingArrFun (β' : ℝ≥0 → ℝ≥0) (v : ι → ℝ≥0) (T : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun u => Finset.univ.inf' Finset.univ_nonempty (fun i => forcingStep β' (v i) T u)

/-- `forcingArrFun` is monotone (a finite inf of monotone step terms). -/
theorem forcingArrFun_mono (β' : ℝ≥0 → ℝ≥0) (v : ι → ℝ≥0) (T : ℝ≥0) :
    Monotone (forcingArrFun β' v T) := by
  intro a b hab
  refine Finset.le_inf' _ _ (fun j _ => le_trans (Finset.inf'_le _ (Finset.mem_univ j)) ?_)
  exact forcingStep_mono β' (v j) T hab

/-- `forcingArrFun` is left-continuous (a finite inf of left-continuous step terms). -/
theorem forcingArrFun_leftCont (β' : ℝ≥0 → ℝ≥0) (v : ι → ℝ≥0) (T : ℝ≥0) :
    IsLeftContinuous (forcingArrFun β' v T) :=
  fun u => ContinuousWithinAt.finset_inf'_apply _ (fun i _ => forcingStep_leftCont β' (v i) T u)

/-- `forcingArrFun` has finite image: the inf is attained at some `i`, so each value is
`β' T` or one of the finitely many `β' T − β' (v i)`. -/
theorem forcingArrFun_finite_image (β' : ℝ≥0 → ℝ≥0) (v : ι → ℝ≥0) (T : ℝ≥0) (S : Set ℝ≥0) :
    (forcingArrFun β' v T '' S).Finite := by
  refine Set.Finite.subset
    ((Set.finite_range (fun i => β' T - β' (v i))).insert (β' T)) ?_
  rintro y ⟨u, -, rfl⟩
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => forcingStep β' (v i) T u)
  have heq : forcingArrFun β' v T u = forcingStep β' (v j) T u := hj
  rw [heq]
  simp only [forcingStep]
  by_cases h : u ≤ T - v j
  · rw [if_pos h]; exact Set.mem_insert_of_mem _ ⟨j, rfl⟩
  · rw [if_neg h]; exact Set.mem_insert _ _

/-- `forcingArrFun β' v T 0 = 0` when `T` is attained as some `v i₀` (so the `i₀`-term is
`β' T − β' T = 0`) and all `v i ≤ T` (so every term is the finite branch). -/
theorem forcingArrFun_zero (β' : ℝ≥0 → ℝ≥0) (v : ι → ℝ≥0) (T : ℝ≥0)
    {i₀ : ι} (hi₀ : v i₀ = T) : forcingArrFun β' v T 0 = 0 := by
  refine le_antisymm (le_trans (Finset.inf'_le _ (Finset.mem_univ i₀)) (le_of_eq ?_)) zero_le'
  simp only [forcingStep]
  rw [if_pos zero_le', hi₀, tsub_self]

/-- At `T − vᵢ` the staircase is at most `β'(T) − β'(vᵢ)` (the `i`-th step bounds the inf). -/
theorem forcingArrFun_le_step (β' : ℝ≥0 → ℝ≥0) (v : ι → ℝ≥0) (T : ℝ≥0) (i : ι) :
    forcingArrFun β' v T (T - v i) ≤ β' T - β' (v i) := by
  refine le_trans (Finset.inf'_le _ (Finset.mem_univ i)) (le_of_eq ?_)
  simp only [forcingStep, if_pos (le_refl (T - v i))]

/-- The staircase dominates `β'(T) − β'(T − u)` — which forces `A ∗ β'(T) = β'(T)`. -/
theorem le_forcingArrFun (β' : ℝ≥0 → ℝ≥0) (hmono : Monotone β') (v : ι → ℝ≥0) (T : ℝ≥0)
    (hvT : ∀ i, v i ≤ T) (u : ℝ≥0) : β' T - β' (T - u) ≤ forcingArrFun β' v T u := by
  refine Finset.le_inf' _ _ (fun i _ => ?_)
  simp only [forcingStep]
  by_cases h : u ≤ T - v i
  · rw [if_pos h]
    have h1 : u + v i ≤ T := (le_tsub_iff_right (hvT i)).mp h
    exact tsub_le_tsub_left (hmono (le_tsub_of_add_le_left h1)) _
  · rw [if_neg h]; exact tsub_le_self

/-- The forcing staircase arrival, as a `Curve`. -/
noncomputable def forcingArr (β' : Curve) (v : ι → ℝ≥0) (T : ℝ≥0)
    {i₀ : ι} (hi₀ : v i₀ = T) : Curve where
  toFun := forcingArrFun (⇑β') v T
  mono := forcingArrFun_mono _ v T
  zero := forcingArrFun_zero _ v T hi₀
  pwc := isPiecewiseContinuous_of_monotone_of_finite_image (forcingArrFun_mono _ v T)
    (forcingArrFun_leftCont _ v T) (fun T' => forcingArrFun_finite_image _ v T (Set.Icc 0 T'))
  leftCont := forcingArrFun_leftCont _ v T

/-- `forcingArr … u = forcingArrFun ⇑β' v T u`. -/
@[simp] theorem forcingArr_apply (β' : Curve) (v : ι → ℝ≥0) (T : ℝ≥0)
    {i₀ : ι} (hi₀ : v i₀ = T) (u : ℝ≥0) :
    forcingArr β' v T hi₀ u = forcingArrFun (⇑β') v T u := rfl

/-- **The staircase is `β'`-tight at `T`**: `A ∗ β'(T) = β'(T)` — the `≥` half (the `≤` half is
the `u = 0` split). Every split `a + s = T` has `A(a) ≥ β'(T) − β'(s)`, so `A(a) + β'(s) ≥ β'(T)`. -/
theorem le_minConv_forcingArr (β' : Curve) (v : ι → ℝ≥0) (T : ℝ≥0) (hvT : ∀ i, v i ≤ T)
    {i₀ : ι} (hi₀ : v i₀ = T) :
    curveEReal β' T ≤ minConv (curveEReal (forcingArr β' v T hi₀)) (curveEReal β') T := by
  refine le_minConv (fun a s hus => ?_)
  have hsa : s = T - a := eq_tsub_of_add_eq (by rw [add_comm]; exact hus)
  have key : β' T ≤ forcingArrFun (⇑β') v T a + β' s := by
    calc β' T = (β' T - β' (T - a)) + β' (T - a) :=
          (tsub_add_cancel_of_le (β'.mono tsub_le_self)).symm
      _ ≤ forcingArrFun (⇑β') v T a + β' (T - a) :=
          add_le_add (le_forcingArrFun (⇑β') β'.mono v T hvT a) le_rfl
      _ = forcingArrFun (⇑β') v T a + β' s := by rw [hsa]
  simp only [curveEReal_apply, forcingArr_apply]
  rw [← EReal.coe_add]
  exact_mod_cast key

/-- **The staircase under-serves `βᵢ` at `T`**: `A ∗ βᵢ(T) < β'(T)`. The split `(T − vᵢ, vᵢ)`
gives `A ∗ βᵢ(T) ≤ A(T − vᵢ) + βᵢ(vᵢ) ≤ (β'(T) − β'(vᵢ)) + βᵢ(vᵢ) < β'(T)`, the last step
because `βᵢ(vᵢ) < β'(vᵢ)`. -/
theorem minConv_forcingArr_lt (β' β : Curve) (v : ι → ℝ≥0) (T : ℝ≥0) (hvT : ∀ i, v i ≤ T)
    {i₀ : ι} (hi₀ : v i₀ = T) (i : ι) (hcross : β (v i) < β' (v i)) :
    minConv (curveEReal (forcingArr β' v T hi₀)) (curveEReal β) T < curveEReal β' T := by
  have hsplit : (T - v i) + v i = T := tsub_add_cancel_of_le (hvT i)
  have key : forcingArrFun (⇑β') v T (T - v i) + β (v i) < β' T :=
    calc forcingArrFun (⇑β') v T (T - v i) + β (v i)
        ≤ (β' T - β' (v i)) + β (v i) := add_le_add (forcingArrFun_le_step _ v T i) le_rfl
      _ < (β' T - β' (v i)) + β' (v i) := add_lt_add_of_le_of_lt le_rfl hcross
      _ = β' T := tsub_add_cancel_of_le (β'.mono (hvT i))
  refine lt_of_le_of_lt (minConv_le_add _ _ hsplit) ?_
  simp only [curveEReal_apply, forcingArr_apply]
  rw [← EReal.coe_add]
  exact_mod_cast key

end DeepWiki
