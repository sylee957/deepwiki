import VersoManual
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The convolution attains its minimum" =>
For real-valued, nondecreasing, left-continuous functions on $`\mathbb{R}`,
the (min,plus) convolution
$$`(f \ast g)(t) = \inf_{0 \le s \le t} \bigl(f(s) + g(t - s)\bigr)`
is not merely an infimum but an attained _minimum_: there is a point
$`s_0 \in [0, t]` realizing it. The argument is purely topological — the
objective $`s \mapsto f(s) + g(t - s)` is lower semi-continuous on the
nonempty compact interval $`[0, t]`, so it attains its infimum.

```lean
namespace NetworkCalculus
open Set Filter Topology
```

# Lower semi-continuity from monotonicity and one-sided continuity

A nondecreasing, left-continuous function $`\mathbb{R} \to \mathbb{R}` is
lower semi-continuous. Left-continuity is expressed as continuity within
$`(-\infty, x]` at each $`x`: on the left of $`x` it gives
$`f(x') \to f(x) > y`, and on the right monotonicity gives
$`f(x') \ge f(x) > y`.

```lean
theorem lsc_of_monotone_leftCont
    {f : ℝ → ℝ} (hmono : Monotone f)
    (hleft : ∀ x, ContinuousWithinAt f (Iic x) x) :
    LowerSemicontinuous f := by
  intro x y hy
  rw [← nhdsLE_sup_nhdsGE x, eventually_sup]
  refine ⟨?_, ?_⟩
  · exact (hleft x).tendsto.eventually
      (eventually_gt_nhds hy)
  · filter_upwards [self_mem_nhdsWithin] with x' hx'
    exact hy.trans_le (hmono hx')
```

*Proof.* Fix $`y < f(x)`. Split the neighbourhood filter into $`\le x` and $`\ge x`: on the left, left-continuity gives $`f(x') \to f(x) > y` eventually; on the right, monotonicity gives $`f(x') \ge f(x) > y`. $`\quad\blacksquare`

Dually, a nonincreasing, right-continuous function is lower
semi-continuous — the two one-sided arguments swap roles.

```lean
theorem lsc_of_antitone_rightCont
    {f : ℝ → ℝ} (hanti : Antitone f)
    (hright : ∀ x, ContinuousWithinAt f (Ici x) x) :
    LowerSemicontinuous f := by
  intro x y hy
  rw [← nhdsLE_sup_nhdsGE x, eventually_sup]
  refine ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x' hx'
    exact hy.trans_le (hanti hx')
  · exact (hright x).tendsto.eventually
      (eventually_gt_nhds hy)
```

*Proof.* Mirror of the monotone case: on the left, antitonicity gives $`f(x') \ge f(x) > y`; on the right, right-continuity gives $`f(x') \to f(x) > y` eventually. $`\quad\blacksquare`

# The convolution attains its minimum

If $`f` and $`g` are nondecreasing and left-continuous, the objective
$`s \mapsto f(s) + g(t - s)` is lower semi-continuous: $`f` is by the
lemma above, and $`s \mapsto g(t - s)` is nonincreasing and
right-continuous (precompose $`g` with the continuous decreasing shift
$`s \mapsto t - s`), hence lower semi-continuous too; their sum then is.
On the nonempty compact set $`[0, t]` a lower semi-continuous function
attains its infimum, giving the minimizer $`s_0`.

```lean
theorem convolution_isMinOn
    {f g : ℝ → ℝ}
    (hf_mono : Monotone f)
    (hf_left : ∀ x, ContinuousWithinAt f (Iic x) x)
    (hg_mono : Monotone g)
    (hg_left : ∀ x, ContinuousWithinAt g (Iic x) x)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ s₀ ∈ Icc (0 : ℝ) t, ∀ s ∈ Icc (0 : ℝ) t,
      f s₀ + g (t - s₀) ≤ f s + g (t - s) := by
  set h : ℝ → ℝ := fun s => f s + g (t - s) with hh
  have hf_lsc : LowerSemicontinuous f :=
    lsc_of_monotone_leftCont hf_mono hf_left
  have hg_comp_lsc :
      LowerSemicontinuous (fun s => g (t - s)) := by
    apply lsc_of_antitone_rightCont
    · intro a b hab
      exact hg_mono (by linarith)
    · intro x
      have hcont :
          ContinuousWithinAt (fun s => t - s) (Ici x) x :=
        (continuousWithinAt_const.sub
          continuousWithinAt_id)
      have := (hg_left (t - x)).comp hcont ?_
      · simpa using this
      · intro s hs
        simp only [mem_Ici] at hs
        simp only [mem_Iic]
        linarith
  have hh_lsc : LowerSemicontinuous h :=
    hf_lsc.add hg_comp_lsc
  have hcompact : IsCompact (Icc (0 : ℝ) t) :=
    isCompact_Icc
  have hne : (Icc (0 : ℝ) t).Nonempty :=
    nonempty_Icc.mpr ht
  have hlscOn :=
    hh_lsc.lowerSemicontinuousOn (Icc (0 : ℝ) t)
  obtain ⟨s₀, hs₀_mem, hs₀_min⟩ :=
    hlscOn.exists_isMinOn hne hcompact
  refine ⟨s₀, hs₀_mem, ?_⟩
  intro s hs
  exact (isMinOn_iff.mp hs₀_min) s hs
```

*Proof.* The objective $`h(s) = f(s) + g(t-s)` is lower semi-continuous: $`f` by `lsc_of_monotone_leftCont`, and $`s \mapsto g(t-s)` by `lsc_of_antitone_rightCont` (it is antitone and right-continuous, being $`g` precomposed with the decreasing shift $`s \mapsto t - s`); a sum of lsc functions is lsc. On the nonempty ($`0 \le t`) compact $`[0,t]`, an lsc function attains its infimum, giving the minimizer $`s_0`. $`\quad\blacksquare`

```lean
end NetworkCalculus
```
