import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic

open Set Filter Topology

/-!
# Min-plus convolution attains its infimum (Prop. 3.10, part 1)

We prove that for `f g : ℝ → ℝ` that are nondecreasing (`Monotone`) and left-continuous,
the min-plus convolution

  `(f ∗ g)(t) = ⨅ {s : 0 ≤ s ≤ t}, f s + g (t - s)`

is actually a *minimum*: there exists `s₀ ∈ [0, t]` minimizing `f s + g (t - s)` over `[0, t]`.

The mathematical core is that `s ↦ f s + g (t - s)` is lower semicontinuous on the
nonempty compact set `[0, t]`, hence attains its infimum.
-/

namespace NetworkCalculus

/-- A nondecreasing, left-continuous function `ℝ → ℝ` is lower semicontinuous.

Left-continuity is expressed as continuity within `Iic x` at every point `x`. -/
theorem lowerSemicontinuous_of_monotone_leftContinuous
    {f : ℝ → ℝ} (hmono : Monotone f)
    (hleft : ∀ x, ContinuousWithinAt f (Iic x) x) :
    LowerSemicontinuous f := by
  intro x y hy
  -- `𝓝 x = 𝓝[≤] x ⊔ 𝓝[≥] x`; show `y < f ·` eventually on each piece.
  rw [← nhdsLE_sup_nhdsGE x, eventually_sup]
  refine ⟨?_, ?_⟩
  · -- Left side: left-continuity gives `f x' → f x > y`.
    exact (hleft x).tendsto.eventually (eventually_gt_nhds hy)
  · -- Right side: monotonicity gives `f x' ≥ f x > y` for `x' ≥ x`.
    filter_upwards [self_mem_nhdsWithin] with x' hx'
    exact hy.trans_le (hmono hx')

/-- A nonincreasing (`Antitone`), right-continuous function `ℝ → ℝ` is lower semicontinuous.

Right-continuity is expressed as continuity within `Ici x` at every point `x`. -/
theorem lowerSemicontinuous_of_antitone_rightContinuous
    {f : ℝ → ℝ} (hanti : Antitone f)
    (hright : ∀ x, ContinuousWithinAt f (Ici x) x) :
    LowerSemicontinuous f := by
  intro x y hy
  rw [← nhdsLE_sup_nhdsGE x, eventually_sup]
  refine ⟨?_, ?_⟩
  · -- Left side: monotonicity (antitone) gives `f x' ≥ f x > y` for `x' ≤ x`.
    filter_upwards [self_mem_nhdsWithin] with x' hx'
    exact hy.trans_le (hanti hx')
  · -- Right side: right-continuity gives `f x' → f x > y`.
    exact (hright x).tendsto.eventually (eventually_gt_nhds hy)

/-- **Proposition 3.10, part 1.**
If `f` and `g` are nondecreasing and left-continuous, then the min-plus convolution
`⨅ s ∈ [0,t], f s + g (t - s)` is attained: there is a minimizer `s₀ ∈ [0, t]`. -/
theorem convolution_isMinOn
    {f g : ℝ → ℝ}
    (hf_mono : Monotone f) (hf_left : ∀ x, ContinuousWithinAt f (Iic x) x)
    (hg_mono : Monotone g) (hg_left : ∀ x, ContinuousWithinAt g (Iic x) x)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ s₀ ∈ Icc (0 : ℝ) t, ∀ s ∈ Icc (0 : ℝ) t,
      f s₀ + g (t - s₀) ≤ f s + g (t - s) := by
  -- The objective function.
  set h : ℝ → ℝ := fun s => f s + g (t - s) with hh
  -- `f` is lower semicontinuous.
  have hf_lsc : LowerSemicontinuous f :=
    lowerSemicontinuous_of_monotone_leftContinuous hf_mono hf_left
  -- `s ↦ g (t - s)` is antitone and right-continuous, hence lower semicontinuous.
  have hg_comp_lsc : LowerSemicontinuous (fun s => g (t - s)) := by
    apply lowerSemicontinuous_of_antitone_rightContinuous
    · -- antitone: `s ↦ t - s` reverses order, `g` monotone.
      intro a b hab
      exact hg_mono (by linarith)
    · -- right-continuous: compose left-continuity of `g` with the continuous decreasing map.
      intro x
      have hcont : ContinuousWithinAt (fun s => t - s) (Ici x) x :=
        (continuousWithinAt_const.sub continuousWithinAt_id)
      -- `(fun s => t - s) '' (Ici x) ⊆ Iic (t - x)`, and `g` is left-continuous at `t - x`.
      have := (hg_left (t - x)).comp hcont ?_
      · simpa using this
      · intro s hs
        simp only [mem_Ici] at hs
        simp only [mem_Iic]
        linarith
  -- The sum `h` is lower semicontinuous.
  have hh_lsc : LowerSemicontinuous h := hf_lsc.add hg_comp_lsc
  -- `[0, t]` is compact and nonempty.
  have hcompact : IsCompact (Icc (0 : ℝ) t) := isCompact_Icc
  have hne : (Icc (0 : ℝ) t).Nonempty := nonempty_Icc.mpr ht
  -- Apply the extreme value theorem for LSC functions.
  obtain ⟨s₀, hs₀_mem, hs₀_min⟩ :=
    (hh_lsc.lowerSemicontinuousOn (Icc (0 : ℝ) t)).exists_isMinOn hne hcompact
  refine ⟨s₀, hs₀_mem, ?_⟩
  intro s hs
  exact (isMinOn_iff.mp hs₀_min) s hs

end NetworkCalculus
