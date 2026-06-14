import DeepWiki.NetworkCalculus.ClosuresNd
import DeepWiki.NetworkCalculus.Continuity

/-! # Regularity preservation under the non-decreasing closure
The running-sup closure `ndClosure f = (t ↦ ⨆_{s ≤ t} f s)` preserves left-continuity
and piecewise-continuity over a complete linear order with the order topology (`ℝ≥0∞`,
`EReal`): its only discontinuities are the *upward* jumps of `f`, so
`discontSet (ndClosure f) ⊆ discontSet f`. These let `ndClosure` of a regular curve be
bundled as a curve (the `CurveENN` closure feeding the `δ_0`-probing theorems). -/

namespace DeepWiki

open Topology Filter Set
open scoped Classical NNReal ENNReal

variable {β : Type*} [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]

omit [TopologicalSpace β] [OrderTopology β] in
/-- `ndClosure f` is monotone (over a complete lattice prefix-boundedness is automatic). -/
theorem monotone_ndClosure_complete (f : ℝ≥0 → β) : Monotone (ndClosure f) :=
  ndClosure_mono f (fun _ => OrderTop.bddAbove _)

omit [TopologicalSpace β] [OrderTopology β] in
/-- `f u ≤ ndClosure f t` whenever `u ≤ t` (the closure dominates each earlier value). -/
theorem le_ndClosure_apply (f : ℝ≥0 → β) {u t : ℝ≥0} (hut : u ≤ t) :
    f u ≤ ndClosure f t :=
  le_iSup (fun s : {s : ℝ≥0 // s ≤ t} => f s) ⟨u, hut⟩

omit [TopologicalSpace β] [OrderTopology β] in
/-- `ndClosure f 0 = f 0`: the prefix `{s ≤ 0}` is just `{0}`. -/
theorem ndClosure_zero_eq (f : ℝ≥0 → β) : ndClosure f 0 = f 0 :=
  le_antisymm (iSup_le fun u => le_of_eq (by
    rw [show (u : ℝ≥0) = 0 from le_antisymm u.2 zero_le'])) (le_ndClosure_apply f le_rfl)

/-- **Left-continuity is preserved by `ndClosure`**: the running sup of a left-continuous
function is left-continuous. At `t`, a left-jump of `ndClosure f` past `⨆_{s < t} f s`
would need `f t` to exceed that prefix sup, contradicting `f t = lim_{s ↑ t} f s`. -/
theorem isLeftContinuous_ndClosure {f : ℝ≥0 → β} (hlc : IsLeftContinuous f) :
    IsLeftContinuous (ndClosure f) := by
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · exact isLeftContinuousAt_zero _
  refine tendsto_order.2 ⟨fun a ha => ?_, fun c hc => ?_⟩
  · -- `a < ndClosure f t` ⟹ eventually `a < ndClosure f s` from the left
    obtain ⟨u, hu⟩ := lt_iSup_iff.mp ha
    rcases eq_or_lt_of_le u.2 with hut | hut
    · -- `↑u = t`: `a < f t`, propagate by left-continuity of `f`
      have ha' : a < f t := hut ▸ hu
      filter_upwards [(hlc t).eventually (lt_mem_nhds ha')] with s hs
      exact lt_of_lt_of_le hs (le_ndClosure_apply f (le_refl s))
    · -- `↑u < t`: on `Ioo ↑u t` the closure already dominates `f ↑u > a`
      filter_upwards [Ioo_mem_nhdsLT hut] with s hs
      exact lt_of_lt_of_le hu (le_ndClosure_apply f (le_of_lt hs.1))
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact lt_of_le_of_lt (monotone_ndClosure_complete f (le_of_lt hs)) hc

variable [DenselyOrdered β]

/-- **Continuity transfers to `ndClosure`**: where `f` is continuous, so is its running
sup — a jump of `ndClosure f` at `t` would be an *upward* jump of `f` at `t`. To the left
the bound rides left-continuity (as above); to the right a value `f u` exceeding the
target would have to occur in `(t, s]`, but `f t ≤ ndClosure f t` is below the target and
`f` stays below it on a right interval. -/
theorem continuousAt_ndClosure {f : ℝ≥0 → β} {t : ℝ≥0} (hf : ContinuousAt f t) :
    ContinuousAt (ndClosure f) t := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun c hc => ?_⟩
  · obtain ⟨u, hu⟩ := lt_iSup_iff.mp ha
    rcases eq_or_lt_of_le u.2 with hut | hut
    · have ha' : a < f t := hut ▸ hu
      filter_upwards [hf.eventually (lt_mem_nhds ha')] with s hs
      exact lt_of_lt_of_le hs (le_ndClosure_apply f (le_refl s))
    · filter_upwards [Ioi_mem_nhds hut] with s hs
      exact lt_of_lt_of_le hu (le_ndClosure_apply f (le_of_lt hs))
  · obtain ⟨c', hgc', hc'c⟩ := exists_between hc
    have hsplit : 𝓝[Set.Iic t] t ⊔ 𝓝[Set.Ioi t] t = 𝓝 t := by
      rw [← nhdsWithin_union, Set.Iic_union_Ioi, nhdsWithin_univ]
    rw [← hsplit, Filter.eventually_sup]
    refine ⟨?_, ?_⟩
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact lt_of_le_of_lt (monotone_ndClosure_complete f hs) (hgc'.trans hc'c)
    · have hftc' : f t < c' := lt_of_le_of_lt (le_ndClosure_apply f (le_refl t)) hgc'
      have hev : ∀ᶠ u in 𝓝 t, f u < c' := hf.eventually (Iio_mem_nhds hftc')
      obtain ⟨b, htb, hsub⟩ :=
        mem_nhdsGT_iff_exists_Ioo_subset.mp (hev.filter_mono nhdsWithin_le_nhds)
      filter_upwards [Ioo_mem_nhdsGT htb] with s hs
      refine lt_of_le_of_lt (iSup_le fun u => ?_) hc'c
      rcases le_or_gt (u : ℝ≥0) t with hut | hut
      · exact le_of_lt (lt_of_le_of_lt (le_ndClosure_apply f hut) hgc')
      · exact le_of_lt (hsub ⟨hut, lt_of_le_of_lt u.2 hs.2⟩)

/-- `ndClosure f` is continuous wherever `f` is: its discontinuities are a subset of
`f`'s (only `f`'s upward jumps survive in the running sup). -/
theorem discontSet_ndClosure_subset {f : ℝ≥0 → β} :
    discontSet (ndClosure f) ⊆ discontSet f := fun _ ht =>
  fun hcont => ht (continuousAt_ndClosure hcont)

/-- **Piecewise-continuity is preserved by `ndClosure`** (`discontSet (ndClosure f) ⊆
discontSet f`, finite on each `[0, T]`). -/
theorem isPiecewiseContinuous_ndClosure {f : ℝ≥0 → β}
    (hf : IsPiecewiseContinuous f) : IsPiecewiseContinuous (ndClosure f) :=
  fun T => (hf T).subset
    (Set.inter_subset_inter_left _ discontSet_ndClosure_subset)

end DeepWiki
