import VersoManual
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Real convolutions of curves" =>
The service curves of network calculus compare a server's output to
_convolutions_ of real curves $`\mathbb{R}^{+} \to \mathbb{R}_{\ge 0}`.
This chapter collects those operators — the infimal convolution and the
super-convolution — together with the non-decreasing and super-additive
_closures_ they generate. All are defined directly on the real values,
with $`\bigsqcap` / $`\bigsqcup` the conditionally-complete infimum and
supremum on $`\mathbb{R}_{\ge 0}`.

```lean
namespace NetworkCalculus

open Set
open scoped Classical NNReal ENNReal
```

# A supremum-absorption lemma

A constant added to a conditionally-complete supremum is absorbed into
a bound: if $`c + f(i) \le y` for every `i`, then $`c + \bigsqcup_i f(i)
\le y`. This is the workhorse for the convolution and closure bounds.

*Theorem:* $`(\forall i,\ c + f(i) \le y) \implies c + \bigsqcup_i f(i) \le y`

```lean
theorem add_ciSup_le {ι : Type} [Nonempty ι]
    (c y : ℝ≥0) (f : ι → ℝ≥0)
    (h : ∀ i, c + f i ≤ y) : c + ⨆ i, f i ≤ y := by
  have hcy : c ≤ y :=
    le_trans le_self_add (h (Classical.arbitrary ι))
  have hsup : ⨆ i, f i ≤ y - c :=
    ciSup_le (fun i => le_tsub_of_add_le_left (h i))
  calc c + ⨆ i, f i ≤ c + (y - c) := by gcongr
    _ = y := add_tsub_cancel_of_le hcy
```

# The infimal convolution

The _infimal convolution_ $`(g \ast h)(t) = \inf_{u + s = t}\,(g(u) +
h(s))`. The infimum ranges over the splits of `t`, a nonempty set (the
split $`t + 0`), so it is well-defined in $`\mathbb{R}_{\ge 0}`.

*Definition:* the real infimal convolution $`(g \ast h)(t) = \inf_{u + s = t}\,(g(u) + h(s))`

```lean
instance splitNonempty (t : ℝ≥0) :
    Nonempty {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} :=
  ⟨⟨(t, 0), by simp⟩⟩

noncomputable def infConvR (g h : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      g p.1.1 + h p.1.2
```

The infimal convolution is _isotone_ in each curve: raising a curve
raises the convolution.

*Theorem:* $`\beta \le \beta' \implies A \ast \beta \le A \ast \beta'`

```lean
theorem infConvR_mono_right (A : ℝ≥0 → ℝ≥0)
    {beta beta' : ℝ≥0 → ℝ≥0} (h : beta ≤ beta') :
    infConvR A beta ≤ infConvR A beta' := by
  intro t
  unfold infConvR
  refine ciInf_mono (OrderBot.bddBelow _) (fun p => ?_)
  gcongr
  exact h p.1.2
```

# The super-convolution

The _super-convolution_ $`(\beta \boxplus \beta)(\tau) = \sup_{a + b =
\tau}\,(\beta(a) + \beta(b))` is the supremal counterpart, over the same
splits.

*Definition:* the super-convolution $`\beta \boxplus \beta`

```lean
noncomputable def superConv (beta : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun τ =>
    ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = τ},
      beta p.1.1 + beta p.1.2
```

# The non-decreasing closure

The _non-decreasing closure_ $`\beta_{\uparrow}(t) = \sup_{u \le t}
\beta(u)` is the least non-decreasing curve above `beta`.

*Definition:* the non-decreasing closure $`\beta_{\uparrow}(t) = \sup_{u \le t} \beta(u)`

```lean
noncomputable def ndClosure (beta : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t => ⨆ u : {u : ℝ≥0 // u ≤ t}, beta u

instance subLeNonempty (t : ℝ≥0) :
    Nonempty {u : ℝ≥0 // u ≤ t} :=
  ⟨⟨0, by positivity⟩⟩
```

The closure dominates the curve (it is the $`u = t` term), provided the
values are bounded on each initial interval so the supremum is genuine.

*Theorem:* $`\beta \le \beta_{\uparrow}`

```lean
theorem le_ndClosure (beta : ℝ≥0 → ℝ≥0)
    (hbdd : ∀ t, BddAbove
      (Set.range (fun u : {u // u ≤ t} => beta u.1)))
    (t : ℝ≥0) : beta t ≤ ndClosure beta t := by
  unfold ndClosure
  exact le_ciSup (hbdd t) (⟨t, le_refl t⟩ : {u // u ≤ t})
```

# The super-additive closure

The _super-additive closure_ $`\bar\beta^{*}` is the supremum of all
finite iterates of the super-convolution: $`\beta^{(0)} = \beta` and
$`\beta^{(n+1)} = \beta^{(n)} \boxplus \beta^{(n)}`.

*Definition:* the iterates $`\beta^{(n)}` and the closure $`\bar\beta^{*} = \sup_n \beta^{(n)}`

```lean
noncomputable def superPow (beta : ℝ≥0 → ℝ≥0) :
    ℕ → (ℝ≥0 → ℝ≥0)
  | 0 => beta
  | n + 1 => superConv (superPow beta n)

noncomputable def saClosure (beta : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t => ⨆ n : ℕ, superPow beta n t
```

The closure dominates the curve (it is the $`n = 0` iterate), provided
the iterates are bounded at each point.

*Theorem:* $`\beta \le \bar\beta^{*}`

```lean
theorem le_saClosure (beta : ℝ≥0 → ℝ≥0)
    (hbdd : ∀ t,
      BddAbove (Set.range (fun n => superPow beta n t)))
    (t : ℝ≥0) : beta t ≤ saClosure beta t := by
  unfold saClosure
  exact le_ciSup (hbdd t) 0
```

```lean
end NetworkCalculus
```
