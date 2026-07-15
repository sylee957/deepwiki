import DeepWiki.NetworkCalculus.ConvolutionMinimum
import DeepWiki.NetworkCalculus.ConvolutionMinimumExt
import DeepWiki.NetworkCalculus.ConvolutionMinimumRC
import DeepWiki.NetworkCalculus.Continuity
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Left-continuity of the (min,+) convolution

The convolution of two nondecreasing left-continuous curves is itself
left-continuous. The genuine content is lower semicontinuity of the convolution
— an infimum of a jointly lsc objective over the compact split-region, obtained
via a cluster point of the minimizers; left-continuity then follows because a
monotone lower-semicontinuous function is left-continuous.

Stated over `ℝ≥0∞` (where `+` is globally continuous) and over `EReal` (the
analysis substrate for the dioid; `+` is discontinuous at the `(+∞)+(−∞)`
collision, so a pointwise `AddDefined` side condition at the split pairs is
required — `NoOppositeInfinities` packages it).
-/

namespace DeepWiki

open Topology Filter Set
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- A monotone, lower semicontinuous `g : ℝ≥0 → T` is left-continuous: the left
limit `⨆_{s<t} g s` reaches `g t` because lsc forbids it from staying below. -/
theorem isLeftContinuous_of_mono_lsc
    {T : Type*} [ConditionallyCompleteLinearOrder T] [TopologicalSpace T]
    [OrderTopology T] (g : ℝ≥0 → T) (hmono : Monotone g)
    (hlsc : LowerSemicontinuous g) :
    IsLeftContinuous g := by
  rw [isLeftContinuous_iff_leftLim_eq hmono]
  funext t
  -- `leftLim g t = g t`: `≤` is monotonicity; `≥` is lower semicontinuity.
  apply le_antisymm (hmono.leftLim_le le_rfl)
  rcases eq_or_ne (𝓝[<] t) ⊥ with hbot | hbot
  · rw [leftLim_eq_of_eq_bot g hbot]
  · letI : (𝓝[<] t).NeBot := neBot_iff.2 hbot
    rw [hmono.leftLim_eq_sSup]
    by_contra hlt
    rw [not_le] at hlt
    set y := sSup (g '' Iio t) with hy
    have hev : ∀ᶠ s in 𝓝 t, y < g s := hlsc t y hlt
    have hfreq : ∃ᶠ s in 𝓝[<] t, y < g s := by
      have : (𝓝[<] t).NeBot := neBot_iff.2 hbot
      exact (hev.filter_mono nhdsWithin_le_nhds).frequently
    obtain ⟨s, hsy, hslt⟩ :=
      (hfreq.and_eventually self_mem_nhdsWithin).exists
    have hle : g s ≤ y :=
      le_csSup (hmono.map_bddAbove ⟨t, fun _ hb => hb.le⟩)
        ⟨s, hslt, rfl⟩
    exact absurd hle (not_le.2 hsy)

/-- The split objective `(t, u) ↦ f u + g (t − u)` is jointly lower
semicontinuous with an explicit pointwise `ContinuousAt (+)` hypothesis (for
carriers like `EReal` where `+` is not globally continuous). -/
theorem lowerSemicontinuous_splitPair_of_contAt
    {T : Type*} [_root_.AddCommMonoid T] [LinearOrder T]
    [IsOrderedAddMonoid T] [TopologicalSpace T] [OrderTopology T]
    (f g : ℝ≥0 → T) (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g)
    (hcont : ∀ p : ℝ≥0 × ℝ≥0,
      ContinuousAt (fun q : T × T => q.1 + q.2) (f p.2, g (p.1 - p.2))) :
    LowerSemicontinuous (fun p : ℝ≥0 × ℝ≥0 => f p.2 + g (p.1 - p.2)) := by
  have h1 : LowerSemicontinuous (fun p : ℝ≥0 × ℝ≥0 => f p.2) :=
    hf.comp continuous_snd
  have hsub : Continuous (fun p : ℝ≥0 × ℝ≥0 => p.1 - p.2) := by continuity
  exact h1.add' (hg.comp hsub) hcont

/-- The split objective as a function of the *pair* `(t, u)`, `f u + g (t − u)`,
is jointly lower semicontinuous when `f`, `g` are. -/
theorem lowerSemicontinuous_splitPair
    {T : Type*} [_root_.AddCommMonoid T] [LinearOrder T]
    [IsOrderedAddMonoid T] [TopologicalSpace T] [OrderTopology T]
    [ContinuousAdd T] (f g : ℝ≥0 → T)
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) :
    LowerSemicontinuous (fun p : ℝ≥0 × ℝ≥0 => f p.2 + g (p.1 - p.2)) :=
  lowerSemicontinuous_splitPair_of_contAt f g hf hg
    (fun _ => continuous_add.continuousAt)

/-- Lower semicontinuity of the (min,+) convolution: core form. Given joint lsc
of the split objective and a per-point minimizer `u_r ∈ [0,r]` with
`f u_r + g (r − u_r) = minConv f g r`, the convolution is lower semicontinuous.
As `r → t` a cluster point `u⋆ ≤ t` of the minimizers exists by compactness, and
joint lsc bounds `minConv f g t` by the limiting value. -/
theorem lowerSemicontinuous_minConv_of_splitPairLsc
    {T : Type*} [_root_.AddCommMonoid T] [CompleteLinearOrder T]
    [IsOrderedAddMonoid T] [TopologicalSpace T] [OrderTopology T]
    (f g : ℝ≥0 → T)
    (hΨlsc : LowerSemicontinuous (fun p : ℝ≥0 × ℝ≥0 => f p.2 + g (p.1 - p.2)))
    (hattain : ∀ r : ℝ≥0, ∃ u ∈ Set.Icc (0 : ℝ≥0) r,
      minConv f g r = f u + g (r - u)) :
    LowerSemicontinuous (minConv f g) := by
  set Ψ : ℝ≥0 × ℝ≥0 → T := fun p => f p.2 + g (p.1 - p.2) with hΨ
  -- minimizer `U r ≤ r` with `Ψ (r, U r) = minConv f g r`
  choose U hUmem hUeq using hattain
  rw [lowerSemicontinuous_iff_frequently]
  intro t y hfreq
  -- restrict `𝓝 t` to where `minConv f g ≤ y`
  set l₀ : Filter ℝ≥0 := 𝓝 t ⊓ 𝓟 {r | minConv f g r ≤ y} with hl₀def
  haveI hl₀ne : l₀.NeBot := by
    rw [hl₀def, ← frequently_iff_neBot]; exact hfreq
  have hl₀le : l₀ ≤ 𝓝 t := by rw [hl₀def]; exact inf_le_left
  set w : ℝ≥0 → ℝ≥0 × ℝ≥0 := fun r => (r, U r) with hwdef
  -- minimizers stay in a fixed compact box near `t`
  have hbox : ∀ᶠ r in l₀, w r ∈ Set.Icc 0 (t + 1) ×ˢ Set.Icc 0 (t + 1) := by
    have hlt1 : ∀ᶠ r in l₀, r < t + 1 :=
      (eventually_lt_nhds (lt_add_of_pos_right t one_pos)).filter_mono hl₀le
    filter_upwards [hlt1] with r hr
    exact ⟨⟨zero_le, hr.le⟩, ⟨zero_le, (hUmem r).2.trans hr.le⟩⟩
  have hcompact :
      IsCompact (Set.Icc (0 : ℝ≥0) (t + 1) ×ˢ Set.Icc 0 (t + 1)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨p, _hpmem, hclust⟩ :=
    hcompact.exists_mapClusterPt_of_frequently (l := l₀) (f := w)
      hbox.frequently
  -- the first coordinate of the cluster point is `t`
  have hfst : p.1 = t := by
    have hc1 : ClusterPt p.1 l₀ := by
      have := (hclust.tendsto_comp
        (f := fun q : ℝ≥0 × ℝ≥0 => q.1) continuous_fst.continuousAt)
      simpa [hwdef, MapClusterPt, Function.comp_def] using this.clusterPt
    refine eq_of_nhds_neBot (x := p.1) (y := t) ?_
    exact hc1.neBot.mono (inf_le_inf_left _ hl₀le)
  -- the cluster point lies in the closed split-region `u ≤ r`
  have hsnd : p.2 ≤ p.1 := by
    have hclosed : IsClosed {q : ℝ≥0 × ℝ≥0 | q.2 ≤ q.1} :=
      isClosed_le continuous_snd continuous_fst
    refine hclosed.mem_of_mapClusterPt hclust ?_
    filter_upwards with r using (hUmem r).2
  -- `Ψ p ≤ y` by lower semicontinuity of `Ψ` at the cluster point
  have hΨp : Ψ p ≤ y := by
    refine (lowerSemicontinuousAt_iff_frequently.mp (hΨlsc p)) y ?_
    have hmem : {q : ℝ≥0 × ℝ≥0 | Ψ q ≤ y} ∈ map w l₀ := by
      rw [mem_map]
      have : {r : ℝ≥0 | minConv f g r ≤ y} ∈ l₀ := by
        rw [hl₀def]; exact mem_inf_of_right (mem_principal_self _)
      filter_upwards [this] with r hr
      show Ψ (w r) ≤ y
      simpa [hwdef, hΨ, ← hUeq r] using hr
    exact hclust.clusterPt.frequently' hmem
  -- conclude: `minConv f g t ≤ Ψ p ≤ y` via the split `(p.2, t − p.2)`
  have hsplit : minConv f g t ≤ Ψ p := by
    show minConv f g t ≤ f p.2 + g (p.1 - p.2)
    rw [hfst]
    refine iInf_le_of_le ⟨(p.2, t - p.2), ?_⟩ le_rfl
    rw [add_tsub_cancel_of_le (hfst ▸ hsnd)]
  exact hsplit.trans hΨp

/-! ### Over `ℝ≥0∞` (globally continuous `+`) -/

/-- Lower semicontinuity of the (min,+) convolution of monotone left-continuous
curves over `ℝ≥0∞`. -/
theorem lowerSemicontinuous_minConv_ennreal
    (f g : ℝ≥0 → ℝ≥0∞) (hf : Monotone f) (hg : Monotone g)
    (hfc : IsLeftContinuous f) (hgc : IsLeftContinuous g) :
    LowerSemicontinuous (minConv f g) :=
  lowerSemicontinuous_minConv_of_splitPairLsc f g
    (lowerSemicontinuous_splitPair f g
      (lowerSemicontinuous_of_mono_isLeftContinuous f hf hfc)
      (lowerSemicontinuous_of_mono_isLeftContinuous g hg hgc))
    (fun r => exists_minConv_eq_split_of_curves f g hf hg hfc hgc r)

/-- (min,+) convolution of two nondecreasing left-continuous curves
`ℝ≥0 → ℝ≥0∞` is left-continuous. -/
theorem isLeftContinuous_minConv_ennreal
    (f g : ℝ≥0 → ℝ≥0∞) (hf : Monotone f) (hg : Monotone g)
    (hfc : IsLeftContinuous f) (hgc : IsLeftContinuous g) :
    IsLeftContinuous (minConv f g) :=
  isLeftContinuous_of_mono_lsc (minConv f g)
    (monotone_minConv hf hg)
    (lowerSemicontinuous_minConv_ennreal f g hf hg hfc hgc)

/-! ### Over `EReal` (analysis substrate; `+` discontinuous at the collision) -/

/-- Lower semicontinuity of the (min,+) convolution of monotone left-continuous
curves `ℝ≥0 → EReal`, given `AddDefined (f u) (g (r − u))` at every split of
every `r` (no `(+∞)+(−∞)` collision at the split pairs). -/
theorem lowerSemicontinuous_minConv_ereal
    (f g : ℝ≥0 → EReal) (hf : Monotone f) (hg : Monotone g)
    (hfc : IsLeftContinuous f) (hgc : IsLeftContinuous g)
    (hpair : ∀ r u : ℝ≥0, AddDefined (f u) (g (r - u))) :
    LowerSemicontinuous (minConv f g) :=
  lowerSemicontinuous_minConv_of_splitPairLsc f g
    (lowerSemicontinuous_splitPair_of_contAt f g
      (lowerSemicontinuous_of_mono_isLeftContinuous f hf hfc)
      (lowerSemicontinuous_of_mono_isLeftContinuous g hg hgc)
      (fun p => (hpair p.1 p.2).continuousAt))
    (fun r =>
      exists_minConv_eq_split_of_curves_of_contAt f g hf hg hfc hgc r
        (fun u => (hpair r u).continuousAt))

/-- (min,+) convolution of two nondecreasing left-continuous curves
`ℝ≥0 → EReal` is left-continuous, given no `(+∞)+(−∞)` collision at the split
pairs. -/
theorem isLeftContinuous_minConv_ereal
    (f g : ℝ≥0 → EReal) (hf : Monotone f) (hg : Monotone g)
    (hfc : IsLeftContinuous f) (hgc : IsLeftContinuous g)
    (hpair : ∀ r u : ℝ≥0, AddDefined (f u) (g (r - u))) :
    IsLeftContinuous (minConv f g) :=
  isLeftContinuous_of_mono_lsc (minConv f g)
    (monotone_minConv hf hg)
    (lowerSemicontinuous_minConv_ereal f g hf hg hfc hgc hpair)

end DeepWiki
