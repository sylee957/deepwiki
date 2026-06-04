import VersoManual
import Book.FunctionDioids

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Additivity" =>
A function is _sub-additive_ when splitting its argument never helps:
$`g(u + s) \le g(u) + g(s)`; it is _super-additive_ in the reverse
sense. These are properties of the _values_ alone, so — like
left-continuity — we state them on plain functions
$`g : \mathbb{R}^{+} \to \overline{\mathbb{R}}_{\ge 0}^\infty`, with the
ordinary numeric order and addition. Over these we form the _(min,plus)
convolution_ $`(g \ast h)(t) = \inf_{u + s = t}\,(g(u) + h(s))`, the
classical $`(\min, +)` convolution on real functions, and prove the
fundamental fact: a sub-additive curve null at the origin is its own
self-convolution. We then show this (min,plus) convolution _is_ the
dioid convolution `conv` of the previous chapters, viewed through the
`MinPlusNN` newtype — so the two definitions coincide.

```lean
namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# Sub- and super-additive real functions

Everything here is on the bare value type $`\overline{\mathbb{R}}_{\ge
0}^\infty`, with numeric $`+` and $`\le`.

*Definition:* $`g` is sub-additive when $`g(u + s) \le g(u) + g(s)`

```lean
def IsSubadditive (g : ℝ≥0 → ℝ≥0∞) : Prop :=
  ∀ u s : ℝ≥0, g (u + s) ≤ g u + g s
```

The dual notion reverses the inequality.

*Definition:* $`g` is super-additive when $`g(u) + g(s) \le g(u + s)`

```lean
def IsSuperadditive (g : ℝ≥0 → ℝ≥0∞) : Prop :=
  ∀ u s : ℝ≥0, g u + g s ≤ g (u + s)
```

The fixed-point results below are stated in terms of the _(min,plus)
convolution_ `minConvE` and its dual `maxConvE` — the numeric infimum
and supremum over the splits $`u + s = t` — both defined in the
function-dioids chapter (`Convolutions of numeric functions`).

# The fundamental fixed-point result

A sub-additive curve null at the origin is a _fixed point_ of
(min,plus) self-convolution. Both inequalities are immediate from the
structure of the infimum:

- _Below_ $`g`: the split $`0 + t = t` contributes the term
  $`g(0) + g(t) = g(t)`, using $`g(0) = 0`; an infimum lies below any
  of its terms.
- _Above_ $`g`: sub-additivity makes every split-term
  $`g(u) + g(s) \ge g(u + s) = g(t)`, so the infimum does too.

Together they give equality.

*Theorem:* if $`g` is sub-additive and $`g(0) = 0` then $`g \ast g = g`

```lean
theorem minConvE_self_of_subadditive
    (g : ℝ≥0 → ℝ≥0∞)
    (hsub : IsSubadditive g) (h0 : g 0 = 0) :
    minConvE g g = g := by
  funext t
  unfold minConvE
  apply le_antisymm
  · refine iInf_le_of_le ⟨(0, t), by simp⟩ ?_
    simp [h0]
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, hus⟩
    simp only
    calc g t = g (u + s) := by rw [hus]
      _ ≤ g u + g s := hsub u s
```

Dually, a super-additive curve null at the origin is a fixed point of
(max,plus) self-convolution: the supremum lies above the split
$`0 + t`, and super-additivity makes every split-term lie below
$`g(t)`.

*Theorem:* if $`g` is super-additive and $`g(0) = 0` then $`g \mathbin{\overline{\ast}} g = g`

```lean
theorem maxConvE_self_of_superadditive
    (g : ℝ≥0 → ℝ≥0∞)
    (hsup : IsSuperadditive g) (h0 : g 0 = 0) :
    maxConvE g g = g := by
  funext t
  unfold maxConvE
  apply le_antisymm
  · refine iSup_le ?_
    rintro ⟨⟨u, s⟩, hus⟩
    simp only
    calc g u + g s ≤ g (u + s) := hsup u s
      _ = g t := by rw [hus]
  · exact le_iSup_of_le ⟨(0, t), by simp⟩ (by simp [h0])
```

# The two convolutions agree

The (min,plus) convolution `minConvE` on real functions is the _same
operation_ as the dioid convolution `conv` of the previous chapters,
viewed through the `MinPlusNN` newtype. Wrapping a real function by
$`s \mapsto \langle g(s)\rangle` embeds it into `Fmin`; we show that
wrapping, convolving with `conv`, and unwrapping reproduces `minConvE`.
This is the content that makes the two definitions interchangeable —
the dioid sum $`\bigsqcup` on $`\overline{\mathbb{R}}_{\ge 0}` is
exactly the numeric infimum over the splits.

*Definition:* the dioid function induced by a real function

```lean
def toF (g : ℝ≥0 → ℝ≥0∞) : Fmin := fun s => ⟨g s⟩
```

Unwrapping the dioid convolution of induced functions gives the
(min,plus) convolution, value by value. Each split-term matches: the
dioid product $`\otimes` is the numeric sum, and the dioid supremum
$`\bigsqcup` is the numeric infimum, both over the same splits.

*Theorem:* $`(\text{toF}\,g \ast \text{toF}\,h)(t)` unwraps to $`(g \ast h)(t)`

```lean
theorem conv_toF_toE (g h : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    ((conv (toF g) (toF h) t : MinPlusNN) : ℝ≥0∞)
      = minConvE g h t := by
  apply le_antisymm
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, hus⟩
    have hle := CompleteDioid.le_sSup _ _
      (show (toF g u ⊗ₒ toF h s)
          ∈ {x | ∃ u s, u + s = t
              ∧ x = toF g u ⊗ₒ toF h s}
        from ⟨u, s, hus, rfl⟩)
    rw [← conv_apply] at hle
    exact (MinPlusNN.le_iff _ _).mp hle
  · rw [conv_apply, ← MinPlusNN.le_iff]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    rw [MinPlusNN.le_iff]
    exact iInf_le_of_le ⟨(u, s), hus⟩ (le_refl _)
```

At the level of functions, the dioid convolution of induced curves is
the induced (min,plus) convolution.

*Theorem:* $`\text{toF}\,g \ast \text{toF}\,h = \text{toF}\,(g \ast h)`

```lean
theorem conv_toF (g h : ℝ≥0 → ℝ≥0∞) :
    conv (toF g) (toF h) = toF (minConvE g h) := by
  funext t
  apply MinPlusNN.ext
  exact conv_toF_toE g h t
```

# The numeric convolution inherits the dioid laws

Because the lift `toF` is _injective_ and carries `minConvE` to the
dioid product `conv`, the numeric convolution inherits the dioid's
commutative-monoid laws — commutativity and associativity — for free,
without re-deriving them from the nested infima.

*Theorem:* the lift `toF` is injective

```lean
theorem toF_inj {g h : ℝ≥0 → ℝ≥0∞}
    (H : toF g = toF h) : g = h := by
  funext t
  exact congrArg MinPlusNN.toVal (congrFun H t)
```

*Theorem:* $`g \ast h = h \ast g`

```lean
theorem minConvE_comm (g h : ℝ≥0 → ℝ≥0∞) :
    minConvE g h = minConvE h g := by
  apply toF_inj
  rw [← conv_toF, ← conv_toF, conv_comm]
```

*Theorem:* $`(f \ast g) \ast h = f \ast (g \ast h)`

```lean
theorem minConvE_assoc (f g h : ℝ≥0 → ℝ≥0∞) :
    minConvE (minConvE f g) h
      = minConvE f (minConvE g h) := by
  apply toF_inj
  rw [← conv_toF, ← conv_toF, ← conv_toF, ← conv_toF,
    conv_assoc]
```

When the pointwise minimum of two curves is itself sub-additive, the
convolution of two curves null at the origin _collapses to that
minimum_: every split-term dominates the minimum (by sub-additivity),
and the minimum is attained at the degenerate splits $`t + 0` and
$`0 + t` (using the null values). This is the engine behind the
token-bucket catalog identity, and it sidesteps the closure detour.

*Theorem:* $`f \ast g = f \wedge g` when $`f \wedge g` is sub-additive and $`f(0) = g(0) = 0`

```lean
theorem minConvE_eq_inf_of_subadd (f g : ℝ≥0 → ℝ≥0∞)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hinf : IsSubadditive (f ⊓ g)) :
    minConvE f g = f ⊓ g := by
  funext t
  apply le_antisymm
  · refine le_min ?_ ?_
    · unfold minConvE
      refine iInf_le_of_le ⟨(t, 0), by simp⟩ ?_
      simp only; rw [hg0, add_zero]
    · unfold minConvE
      refine iInf_le_of_le ⟨(0, t), by simp⟩ ?_
      simp only; rw [hf0, zero_add]
  · unfold minConvE
    refine le_iInf ?_
    rintro ⟨⟨u, s⟩, (huv : u + s = t)⟩
    simp only
    calc (f ⊓ g) t = (f ⊓ g) (u + s) := by rw [huv]
      _ ≤ (f ⊓ g) u + (f ⊓ g) s := hinf u s
      _ ≤ f u + g s :=
          add_le_add (min_le_left _ _) (min_le_right _ _)
```

The dioid self-convolution fixed point is now a corollary of the real
one: rewrite `conv` to `minConvE` and apply the fundamental result.

*Theorem:* a sub-additive real `g` null at the origin induces $`\sigma` with $`\sigma \ast \sigma = \sigma`

```lean
theorem conv_self_toF_of_subadditive
    (g : ℝ≥0 → ℝ≥0∞)
    (hsub : IsSubadditive g) (h0 : g 0 = 0) :
    conv (toF g) (toF g) = toF g := by
  rw [conv_toF, minConvE_self_of_subadditive g hsub h0]
```

```lean
end DeepWiki
```
