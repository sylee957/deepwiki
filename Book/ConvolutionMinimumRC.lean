import Book.ConvolutionMinimum
import Book.ConvolutionMinimumExt
import Book.ContinuityClosure
import Book.MinPlusExtTopology
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Convolution minimum: the right-continuous (continuous-`h`) refinement

The left-continuous attainment lemma (`Book.ConvolutionMinimum`) asks both
curves to be left-continuous and returns `minConv f h t = f u₀ + h (t − u₀)`.
Here we drop left-continuity of `f` and ask the *other* curve `h` to be (fully)
continuous; the convolution is then still attained, but at the **left limit**
`f(u₀⁻)`: `minConv f h t = leftLim f u₀ + h (t − u₀)`.

The mathematical content is the bridge `minConv f h t = minConv (leftLim f) h t`
(`minConv_eq_minConv_leftLim_of_cont`): replacing `f` by its left limit does not
change the convolution when `h` is continuous. This is exactly where continuity
of `h` (not mere left-continuity) is consumed — as `u' ↗ u` the argument
`t − u'` of `h` *decreases* to `t − u`, a right-approach in `h`.

Stated over `EReal`, the book's `R̄min = WithTop (WithBot ℝ)`, and (as the clean
headline corollary) `ℝ≥0∞`. On the two-sided codomains a pointwise add-defined
side condition is required at the limit pair `(leftLim f u, h (t − u))`
(gotcha #2: addition is discontinuous at the `(+∞)+(−∞)` collision); on `ℝ≥0∞`
addition is globally continuous and the side condition disappears.
-/

namespace DeepWiki

open Topology Filter Set Function
open scoped Classical NNReal ENNReal Algebra.Bridge DeepWiki.MinPlusExt

/-- The convolution bridge (continuous `h`): `minConv f h t` is unchanged when
`f` is replaced by its left limit `leftLim f`. The `≤` direction is monotonicity
of the summand (`leftLim f ≤ f`); the `≥` direction takes `u' ↗ u` and uses
continuity of `h` at `t − u` together with add-continuity `hadd` at the limit
pair `(leftLim f u, h (t − u))`. -/
theorem minConv_eq_minConv_leftLim_of_cont
    {T : Type*} [_root_.AddCommMonoid T] [CompleteLinearOrder T]
    [IsOrderedAddMonoid T] [TopologicalSpace T] [OrderTopology T] [T3Space T]
    (f h : ℝ≥0 → T) (hfm : Monotone f) (hhc : Continuous h) (t : ℝ≥0)
    (hadd : ∀ u : ℝ≥0,
      ContinuousAt (fun p : T × T => p.1 + p.2) (leftLim f u, h (t - u))) :
    minConv f h t = minConv (leftLim f) h t := by
  have hsub : Continuous (fun u : ℝ≥0 => t - u) := by continuity
  apply le_antisymm
  · -- HARD direction `minConv f h t ≤ minConv (leftLim f) h t`. By `le_iInf`
    -- over the `leftLim f`-infimum, suffices for each split `(u, t−u)`:
    -- `minConv f h t ≤ leftLim f u + h (t − u)`, shown via `u' ↗ u` (where
    -- `f u' → leftLim f u`, and continuity of `h` handles `t − u' ↘ t − u`).
    refine le_iInf ?_
    rintro ⟨⟨u, s⟩, (hus : u + s = t)⟩
    have hut : u ≤ t := hus ▸ le_self_add
    have hsu : s = t - u := by rw [← hus, add_tsub_cancel_left]
    subst hsu
    rcases eq_or_lt_of_le (zero_le' (a := u)) with hu0 | hu0
    · -- `u = 0`: `leftLim f 0 = f 0`, so the target is an `f`-summand.
      have h0 : leftLim f u = f u := by
        have : u = 0 := hu0.symm
        subst this; exact leftLim_eq_of_isBot isBot_bot
      rw [h0]
      exact iInf_le_of_le ⟨(u, t - u), add_tsub_cancel_of_le hut⟩ le_rfl
    · -- `u > 0`: take `u' ↗ u`; each `f u' + h (t − u') ≥ minConv f h t`,
      -- and the family tends to `leftLim f u + h (t − u)`.
      have hbot : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hu0⟩
      have hlim : Tendsto (fun u' : ℝ≥0 => f u' + h (t - u'))
          (𝓝[<] u) (𝓝 (leftLim f u + h (t - u))) := by
        have h1 : Tendsto (fun u' : ℝ≥0 => f u') (𝓝[<] u)
            (𝓝 (leftLim f u)) := hfm.tendsto_leftLim u
        have h2 : Tendsto (fun u' : ℝ≥0 => h (t - u')) (𝓝[<] u)
            (𝓝 (h (t - u))) :=
          ((hhc.comp hsub).continuousAt).continuousWithinAt
        have hpair : Tendsto (fun u' : ℝ≥0 => (f u', h (t - u')))
            (𝓝[<] u) (𝓝 (leftLim f u, h (t - u))) := h1.prodMk_nhds h2
        exact (hadd u).tendsto.comp hpair
      refine ge_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin] with u' (hu' : u' < u)
      have hu't : u' ≤ t := hu'.le.trans hut
      exact iInf_le_of_le ⟨(u', t - u'), add_tsub_cancel_of_le hu't⟩ le_rfl
  · -- EASY direction `minConv (leftLim f) h t ≤ minConv f h t`: termwise,
    -- `leftLim f u + h s ≤ f u + h s` since `leftLim f ≤ f`.
    refine le_iInf ?_
    rintro ⟨⟨u, s⟩, (hus : u + s = t)⟩
    refine iInf_le_of_le ⟨(u, s), hus⟩ ?_
    gcongr
    exact hfm.leftLim_le (le_refl u)

/-- Generic core. For monotone `f` and **continuous** `h`, with `+` continuous
at each limit pair `(leftLim f u, h (t − u))`, the convolution is attained at
the *left limit* of `f`: `minConv f h t = leftLim f u₀ + h (t − u₀)` for some
`u₀ ∈ [0,t]`. The single `hadd` hypothesis feeds both the bridge
`minConv f h = minConv (leftLim f) h` and the attainment of
`minConv (leftLim f) h`. -/
theorem exists_minConv_eq_leftLim_split_of_cont_core
    {T : Type*} [_root_.AddCommMonoid T] [CompleteLinearOrder T]
    [IsOrderedAddMonoid T] [TopologicalSpace T] [OrderTopology T] [T3Space T]
    (f h : ℝ≥0 → T) (hfm : Monotone f) (hhm : Monotone h)
    (hhc : Continuous h) (t : ℝ≥0)
    (hadd : ∀ u : ℝ≥0,
      ContinuousAt (fun p : T × T => p.1 + p.2) (leftLim f u, h (t - u))) :
    ∃ u₀ ∈ Set.Icc (0 : ℝ≥0) t,
      minConv f h t = leftLim f u₀ + h (t - u₀) := by
  obtain ⟨u₀, hu₀, heq⟩ :=
    exists_minConv_eq_split_of_curves_of_contAt (leftLim f) h hfm.leftLim hhm
      (isLeftContinuous_leftLim hfm) (isLeftContinuous_of_continuous h hhc) t hadd
  exact ⟨u₀, hu₀,
    (minConv_eq_minConv_leftLim_of_cont f h hfm hhc t hadd).trans heq⟩

/-- Over `EReal`. For monotone `f` and continuous `h : ℝ⁺ → ℝ̄` with
`AddDefined (leftLim f u) (h (t − u))` at every split (no `(+∞)+(−∞)` collision
at the limit pairs), the min-plus convolution is attained at the left limit of
`f`: `minConv f h t = leftLim f u₀ + h (t − u₀)` for some `u₀ ∈ [0,t]`. Dropping
left-continuity of `f` is paid for by strengthening `h` to continuous; the value
is `f(u₀⁻)`, not `f u₀`. -/
theorem exists_minConv_eq_leftLim_split_of_cont
    (f h : ℝ≥0 → EReal)
    (hfm : Monotone f) (hhm : Monotone h)
    (hhc : Continuous h) (t : ℝ≥0)
    (hpair : ∀ u : ℝ≥0, AddDefined (leftLim f u) (h (t - u))) :
    ∃ u₀ ∈ Set.Icc (0 : ℝ≥0) t,
      minConv f h t = leftLim f u₀ + h (t - u₀) :=
  exists_minConv_eq_leftLim_split_of_cont_core f h hfm hhm hhc t
    (fun u => (hpair u).continuousAt)

/-- The general precondition for the `EReal` left-limit attainment, named for
what it is: at no split `u` do `leftLim f` and `h` take *opposite* infinities
(`(+∞,−∞)` or `(−∞,+∞)`) — the only pairs where `EReal` addition is
discontinuous. This is the weakest such condition; a strictly weaker one would
hit a real discontinuity and make the conclusion false. -/
def NoOppositeInfinities (f h : ℝ≥0 → EReal) (t : ℝ≥0) : Prop :=
  ∀ u : ℝ≥0, ¬ ((leftLim f u = ⊤ ∧ h (t - u) = ⊥) ∨
                (leftLim f u = ⊥ ∧ h (t - u) = ⊤))

/-- `NoOppositeInfinities` is exactly the per-split `AddDefined` family — the two
are equivalent, so the named form loses no generality. -/
theorem noOppositeInfinities_iff_addDefined (f h : ℝ≥0 → EReal) (t : ℝ≥0) :
    NoOppositeInfinities f h t ↔
      ∀ u : ℝ≥0, AddDefined (leftLim f u) (h (t - u)) := by
  unfold NoOppositeInfinities AddDefined
  refine ⟨fun H u => ?_, fun H u => ?_⟩
  · have h2 := H u
    push Not at h2
    refine ⟨?_, ?_⟩
    · rcases eq_or_ne (leftLim f u) ⊤ with h1 | h1
      · exact Or.inr (h2.1 h1)
      · exact Or.inl h1
    · rcases eq_or_ne (leftLim f u) ⊥ with h1 | h1
      · exact Or.inr (h2.2 h1)
      · exact Or.inl h1
  · rintro (⟨ht, hb⟩ | ⟨hb, ht⟩)
    · rcases (H u).1 with h1 | h1
      · exact h1 ht
      · exact h1 hb
    · rcases (H u).2 with h1 | h1
      · exact h1 hb
      · exact h1 ht

/-- Over `EReal`, with the general precondition `NoOppositeInfinities`. Same
conclusion as `exists_minConv_eq_leftLim_split_of_cont`, restated with the named
(equivalent) hypothesis: at no split do `leftLim f` and `h` collide at opposite
infinities. -/
theorem exists_minConv_eq_leftLim_split_of_noOppInf
    (f h : ℝ≥0 → EReal)
    (hfm : Monotone f) (hhm : Monotone h)
    (hhc : Continuous h) (t : ℝ≥0)
    (hnd : NoOppositeInfinities f h t) :
    ∃ u₀ ∈ Set.Icc (0 : ℝ≥0) t,
      minConv f h t = leftLim f u₀ + h (t - u₀) :=
  exists_minConv_eq_leftLim_split_of_cont f h hfm hhm hhc t
    ((noOppositeInfinities_iff_addDefined f h t).mp hnd)

/-- Over the book's carrier `R̄min = WithTop (WithBot ℝ)` (top-absorbing `+`,
`(+∞)+(−∞) = +∞`). Same statement as the `EReal` version with `AddDefinedExt` at
the limit pairs, via the order topology + add-continuity of
`Book.MinPlusExtTopology`. -/
theorem exists_minConv_eq_leftLim_split_of_cont_ext
    (f h : ℝ≥0 → WithTop (WithBot ℝ))
    (hfm : Monotone f) (hhm : Monotone h)
    (hhc : Continuous h) (t : ℝ≥0)
    (hpair : ∀ u : ℝ≥0, AddDefinedExt (leftLim f u) (h (t - u))) :
    ∃ u₀ ∈ Set.Icc (0 : ℝ≥0) t,
      minConv f h t = leftLim f u₀ + h (t - u₀) :=
  exists_minConv_eq_leftLim_split_of_cont_core f h hfm hhm hhc t
    (fun u => (hpair u).continuousAt)

/-- Over `ℝ≥0∞` (headline corollary). On the one-sided extended reals `+` is
globally continuous, so no add-defined side condition is needed: for monotone
`f` and continuous `h`, the convolution is attained at the left limit,
`minConv f h t = leftLim f u₀ + h (t − u₀)` for some `u₀ ∈ [0,t]`. -/
theorem exists_minConv_eq_leftLim_split_of_cont_ennreal
    (f h : ℝ≥0 → ℝ≥0∞)
    (hfm : Monotone f) (hhm : Monotone h)
    (hhc : Continuous h) (t : ℝ≥0) :
    ∃ u₀ ∈ Set.Icc (0 : ℝ≥0) t,
      minConv f h t = leftLim f u₀ + h (t - u₀) :=
  exists_minConv_eq_leftLim_split_of_cont_core f h hfm hhm hhc t
    (fun _ => continuous_add.continuousAt)

end DeepWiki
