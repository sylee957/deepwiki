import Book.ServiceCurveFamilies
import Book.ServiceCurveMonotony
import Book.ArrivalCurvesShaperGreedy
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

/-! ## Departure component is piecewise-continuous (Thm 9.4 item 1 ⟹, piece 2b)
The convolution `A ∗ βᵢ` of the staircase arrival with a curve is piecewise-continuous — so it
bundles as a `Curve` via `greedyCurve`. Route: `A = ⨅ⱼ forcingStepⱼ`, conv distributes over the
inf (`minConv_finset_inf'`), each single-step conv is `min (lo + βᵢ(·−c)) hi` (pwc), the finite
inf of pwc is pwc, and `greedyFun` reads it faithfully (finite-valued). -/

/-! ## Helper lemmas -/

/-- The EReal lift of a single forcing step. -/
noncomputable def forcingStepEReal (β' : ℝ≥0 → ℝ≥0) (vi T : ℝ≥0) : ℝ≥0 → EReal :=
  fun u => ((forcingStep β' vi T u : ℝ) : EReal)

/-- The single-step convolution computes to a `min` of a shifted `b` plus a constant
and a constant: `(step ∗ b)(t) = min (lo + b (t − c)) hi`, with `c = T − vi`,
`lo = β'(T) − β'(vi)`, `hi = β'(T)`. -/
theorem minConv_forcingStepEReal (β' : ℝ≥0 → ℝ≥0) (vi T : ℝ≥0) (b : Curve) (t : ℝ≥0) :
    minConv (forcingStepEReal β' vi T) (curveEReal b) t
      = min (((β' T - β' vi : ℝ≥0) : ℝ) + ((b (t - (T - vi)) : ℝ≥0) : ℝ) : EReal)
          (((β' T : ℝ≥0) : ℝ) : EReal) := by
  set c := T - vi with hc
  set lo := β' T - β' vi with hlo
  set hi := β' T with hhi
  have hlohi : lo ≤ hi := tsub_le_self
  refine le_antisymm ?_ ?_
  · refine le_min ?_ ?_
    · have hsplit : min c t + (t - c) = t := by
        rcases le_total c t with h | h
        · rw [min_eq_left h, add_tsub_cancel_of_le h]
        · rw [min_eq_right h, tsub_eq_zero_of_le h, add_zero]
      refine le_trans (minConv_le_add _ _ hsplit) (le_of_eq ?_)
      have hstep : forcingStepEReal β' vi T (min c t) = ((lo : ℝ) : EReal) := by
        simp only [forcingStepEReal, forcingStep]
        rw [if_pos (le_trans (min_le_left c t) hc.ge)]
      rw [hstep, curveEReal_apply, ← EReal.coe_add]
    · refine le_trans (minConv_le_add _ _ (add_zero t)) ?_
      have hb0 : curveEReal b 0 = 0 := curveEReal_zero b
      rw [hb0, add_zero]
      simp only [forcingStepEReal, forcingStep]
      by_cases h : t ≤ c
      · rw [if_pos (le_trans h hc.ge)]; exact_mod_cast hlohi
      · rw [if_neg (fun hcon => h (le_trans hcon hc.le))]
  · refine le_minConv (fun u s hus => ?_)
    by_cases h : u ≤ c
    · have hstep : forcingStepEReal β' vi T u = ((lo : ℝ) : EReal) := by
        simp only [forcingStepEReal, forcingStep]
        rw [if_pos (le_trans h hc.ge)]
      rw [hstep]
      refine le_trans (min_le_left _ _) ?_
      have hsle : t - c ≤ s := by
        have : t - c ≤ t - u := tsub_le_tsub_left h t
        rwa [show t - u = s from by rw [← hus, add_tsub_cancel_left]] at this
      rw [curveEReal_apply, ← EReal.coe_add, ← EReal.coe_add]
      exact_mod_cast add_le_add (le_refl _) (b.mono hsle)
    · have hstep : forcingStepEReal β' vi T u = ((hi : ℝ) : EReal) := by
        simp only [forcingStepEReal, forcingStep]
        rw [if_neg (fun hcon => h (le_trans hcon hc.le))]
      rw [hstep]
      refine le_trans (min_le_right _ _) ?_
      have : (0 : EReal) ≤ curveEReal b s := curveEReal_nonneg b s
      calc ((hi : ℝ) : EReal) = ((hi : ℝ) : EReal) + 0 := (add_zero _).symm
        _ ≤ ((hi : ℝ) : EReal) + curveEReal b s := by gcongr

/-- `curveEReal b` is piecewise-continuous: the coercions are continuous, so its
discontinuities are exactly those of `b`. -/
theorem isPiecewiseContinuous_curveEReal (b : Curve) :
    IsPiecewiseContinuous (curveEReal b) := by
  intro T'
  have hsub : discontSet (curveEReal b) ⊆ discontSet (⇑b) := by
    intro t ht hcon
    exact ht ((continuous_coe_real_ereal.comp NNReal.continuous_coe).continuousAt.comp hcon)
  exact (b.pwc T').subset (Set.inter_subset_inter_left _ hsub)

/-- A `min` of (a real constant plus a right-shift of a piecewise-continuous `cb`) and
a constant is piecewise-continuous: discontinuities occur only at `t ≥ sh`, where the
shift `(· − sh)` is injective, so they inject into `cb`'s finitely many discontinuities. -/
theorem isPiecewiseContinuous_min_shift_const (cb : ℝ≥0 → EReal)
    (hpwc : IsPiecewiseContinuous cb) (lo : ℝ) (hi : EReal) (sh : ℝ≥0) :
    IsPiecewiseContinuous (fun t => min ((lo : EReal) + cb (t - sh)) hi) := by
  intro T'
  set g : ℝ≥0 → EReal := fun t => min ((lo : EReal) + cb (t - sh)) hi with hg
  have hcont : ∀ t : ℝ≥0, ContinuousAt cb (t - sh) → ContinuousAt g t := by
    intro t hct
    have hsh : ContinuousAt (fun x : ℝ≥0 => x - sh) t := (continuous_sub_right sh).continuousAt
    have hcomp : ContinuousAt (fun x : ℝ≥0 => cb (x - sh)) t :=
      ContinuousAt.comp (g := cb) (f := fun x : ℝ≥0 => x - sh) hct hsh
    have hpair : ContinuousAt (fun x : ℝ≥0 => ((lo : EReal), cb (x - sh))) t :=
      continuousAt_const.prodMk hcomp
    have hadd : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) ((lo : EReal), cb (t - sh)) :=
      EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))
    have h1 : ContinuousAt (fun x : ℝ≥0 => (lo : EReal) + cb (x - sh)) t :=
      ContinuousAt.comp (g := fun p : EReal × EReal => p.1 + p.2)
        (f := fun x : ℝ≥0 => ((lo : EReal), cb (x - sh))) hadd hpair
    exact h1.min continuousAt_const
  have hltcont : ∀ t : ℝ≥0, t < sh → ContinuousAt g t := by
    intro t ht
    have hev : (fun x : ℝ≥0 => min ((lo : EReal) + cb (x - sh)) hi)
        =ᶠ[𝓝 t] (fun _ : ℝ≥0 => min ((lo : EReal) + cb 0) hi) := by
      filter_upwards [Iio_mem_nhds ht] with x hx
      rw [tsub_eq_zero_of_le (le_of_lt hx)]
    exact (continuousAt_const).congr hev.symm
  refine Set.Finite.subset (Set.Finite.image (fun x => x + sh) (hpwc T')) ?_
  rintro t ⟨htd, htI⟩
  have htge : sh ≤ t := by
    by_contra hlt
    exact htd (hltcont t (not_le.mp hlt))
  have hcbd : (t - sh) ∈ discontSet cb := fun hcon => htd (hcont t hcon)
  have htsI : (t - sh) ∈ Set.Icc (0 : ℝ≥0) T' :=
    ⟨zero_le', le_trans tsub_le_self htI.2⟩
  exact ⟨t - sh, ⟨hcbd, htsI⟩, tsub_add_cancel_of_le htge⟩

/-- A finite `inf'` of piecewise-continuous functions (into an order with continuous
inf) is piecewise-continuous: its discontinuities are contained in the union of the
families' discontinuities. -/
theorem isPiecewiseContinuous_finset_inf' {κ X : Type*} [TopologicalSpace X]
    [SemilatticeInf X] [ContinuousInf X] {s : Finset κ} (hne : s.Nonempty)
    {f : κ → ℝ≥0 → X} (hf : ∀ i ∈ s, IsPiecewiseContinuous (f i)) :
    IsPiecewiseContinuous (fun t => s.inf' hne (fun j => f j t)) := by
  intro T'
  refine Set.Finite.subset
    (Set.Finite.biUnion s.finite_toSet (fun i hi => hf i hi T')) ?_
  rintro t ⟨htd, htI⟩
  by_contra hnot
  refine htd (ContinuousAt.finset_inf'_apply hne (fun i hi => ?_))
  by_contra hci
  exact hnot (Set.mem_biUnion hi ⟨hci, htI⟩)

/-! ## Assembly -/

/-- `curveEReal (forcingArr …)` is the finite `inf'` of the lifted single steps. -/
theorem curveEReal_forcingArr_eq (bp : Curve) (v : ι → ℝ≥0) (T : ℝ≥0)
    {i₀ : ι} (hi₀ : v i₀ = T) :
    curveEReal (forcingArr bp v T hi₀)
      = fun u => Finset.univ.inf' Finset.univ_nonempty
          (fun i => forcingStepEReal (⇑bp) (v i) T u) := by
  funext u
  rw [curveEReal_apply, forcingArr_apply, forcingArrFun]
  rw [Finset.comp_inf'_eq_inf'_comp Finset.univ_nonempty
    (g := fun x : ℝ≥0 => ((x : ℝ) : EReal)) (fun x y => by
      show ((((min x y : ℝ≥0) : ℝ)) : EReal) = min (((x : ℝ) : EReal)) (((y : ℝ) : EReal))
      rw [NNReal.coe_min]
      exact (Monotone.map_min (fun a b h => by exact_mod_cast h)))]
  rfl

/-- The forcing convolution `(forcingArr …) ∗ b` is piecewise-continuous (EReal view):
it is a finite `inf'` of single-step convolutions, each a `min` of a shifted `b` plus a
constant and a constant. -/
theorem isPiecewiseContinuous_minConv_curveEReal_forcingArr
    (bp : Curve) (b : Curve) (v : ι → ℝ≥0) (T : ℝ≥0) {i₀ : ι} (hi₀ : v i₀ = T) :
    IsPiecewiseContinuous
      (minConv (curveEReal (forcingArr bp v T hi₀)) (curveEReal b)) := by
  have hrw : minConv (curveEReal (forcingArr bp v T hi₀)) (curveEReal b)
      = fun t => Finset.univ.inf' Finset.univ_nonempty
          (fun i => minConv (forcingStepEReal (⇑bp) (v i) T) (curveEReal b) t) := by
    funext t
    rw [curveEReal_forcingArr_eq bp v T hi₀,
      minConv_finset_inf' Finset.univ_nonempty
        (fun i => forcingStepEReal (⇑bp) (v i) T) (curveEReal b) t]
  rw [hrw]
  refine isPiecewiseContinuous_finset_inf' Finset.univ_nonempty (fun i _ => ?_)
  have hstep : minConv (forcingStepEReal (⇑bp) (v i) T) (curveEReal b)
      = fun t => min (((bp T - bp (v i) : ℝ≥0) : ℝ)
            + ((b (t - (T - v i)) : ℝ≥0) : ℝ) : EReal)
          (((bp T : ℝ≥0) : ℝ) : EReal) := by
    funext t; exact minConv_forcingStepEReal (⇑bp) (v i) T b t
  rw [hstep]
  have hpwcb : IsPiecewiseContinuous (fun t => ((b t : ℝ) : EReal)) :=
    isPiecewiseContinuous_curveEReal b
  exact isPiecewiseContinuous_min_shift_const (fun t => ((b t : ℝ) : EReal)) hpwcb
    (((bp T - bp (v i) : ℝ≥0) : ℝ)) (((bp T : ℝ≥0) : ℝ) : EReal) (T - v i)

/-- **The forcing departure component is piecewise-continuous.** The greedy output
`(forcingArr …) ∗ b` (read back in `ℝ≥0`) inherits piecewise continuity from the
EReal convolution: at every point where the convolution is continuous (and it always
is finite and nonnegative), the `toReal`-then-`toNNReal` reading is continuous. -/
theorem isPiecewiseContinuous_greedyFun_forcingArr
    (bp : Curve) (b : Curve) (v : ι → ℝ≥0) (T : ℝ≥0) {i₀ : ι} (hi₀ : v i₀ = T) :
    IsPiecewiseContinuous (greedyFun (forcingArr bp v T hi₀) (curveEReal b)) := by
  set A := forcingArr bp v T hi₀ with hA
  have hconv : IsPiecewiseContinuous (minConv (curveEReal A) (curveEReal b)) :=
    isPiecewiseContinuous_minConv_curveEReal_forcingArr bp b v T hi₀
  intro T'
  refine (hconv T').subset (Set.inter_subset_inter_left _ ?_)
  intro t ht hcon
  -- continuity of the EReal convolution at t implies continuity of greedyFun at t
  refine ht ?_
  have hpos : (0 : EReal) ≤ minConv (curveEReal A) (curveEReal b) t :=
    IsNonneg.conv (curveEReal_nonneg A) (curveEReal_nonneg b) t
  have htr : ContinuousAt EReal.toReal (minConv (curveEReal A) (curveEReal b) t) :=
    EReal.tendsto_toReal (minConv_curveEReal_ne_top A (curveEReal_zero b).le t)
      (ne_bot_of_nonneg hpos)
  exact ((continuous_real_toNNReal.continuousAt).comp htr).comp hcon

/-! ## Finite supremum of curves (the departure `D = ⨆ᵢ A ∗ βᵢ`) -/

noncomputable def supCurve {ι : Type*} [Fintype ι] [Nonempty ι] (C : ι → Curve) : Curve where
  toFun := fun t => Finset.univ.sup' Finset.univ_nonempty (fun i => C i t)
  mono := by
    intro a b hab
    show Finset.univ.sup' Finset.univ_nonempty (fun i => C i a)
        ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => C i b)
    exact Finset.sup'_le _ _ (fun i _ =>
      le_trans ((C i).mono hab) (Finset.le_sup' (fun i => C i b) (Finset.mem_univ i)))
  zero := by
    show Finset.univ.sup' Finset.univ_nonempty (fun i => C i 0) = 0
    refine le_antisymm (Finset.sup'_le _ _ (fun i _ => le_of_eq (C i).zero)) ?_
    exact (le_of_eq (C (Classical.arbitrary ι)).zero.symm).trans
      (Finset.le_sup' (fun i => C i 0) (Finset.mem_univ _))
  pwc := fun T => by
    refine Set.Finite.subset (Set.finite_iUnion (fun i => (C i).pwc T)) (fun t ht => ?_)
    rw [Set.mem_iUnion]
    by_contra hcon
    exact ht.1 (ContinuousAt.finset_sup'_apply Finset.univ_nonempty (fun i _ => by
      by_contra hdi
      exact hcon ⟨i, hdi, ht.2⟩))
  leftCont := fun t => ContinuousWithinAt.finset_sup'_apply Finset.univ_nonempty
    (fun i _ => (C i).leftCont t)

@[simp] theorem supCurve_apply {ι : Type*} [Fintype ι] [Nonempty ι] (C : ι → Curve) (t : ℝ≥0) :
    supCurve C t = Finset.univ.sup' Finset.univ_nonempty (fun i => C i t) := rfl

theorem le_supCurve {ι : Type*} [Fintype ι] [Nonempty ι] (C : ι → Curve) (i : ι) :
    C i ≤ supCurve C := fun t => Finset.le_sup' (fun i => C i t) (Finset.mem_univ i)

theorem supCurve_le {ι : Type*} [Fintype ι] [Nonempty ι] {C : ι → Curve} {D : Curve}
    (h : ∀ i, C i ≤ D) : supCurve C ≤ D :=
  fun t => Finset.sup'_le Finset.univ_nonempty _ (fun i _ => h i t)

end DeepWiki
