import VersoManual
import Book.FunctionDioids

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Sub-additivity" =>
A function is _sub-additive_ when splitting its argument never helps:
$`g(u + s) \le g(u) + g(s)`. This is a property of the _values_ alone,
so — like left-continuity — we state it on plain functions
$`g : \mathbb{R}^{+} \to \overline{\mathbb{R}}_{\ge 0}^\infty`, with the
ordinary numeric order and addition. Over these we form the _infimal
convolution_ $`(g \ast h)(t) = \inf_{u + s = t}\,(g(u) + h(s))`, the
classical $`(\min, +)` convolution on real functions, and prove the
fundamental fact: a sub-additive curve null at the origin is its own
infimal self-convolution. We then show this infimal convolution _is_
the dioid convolution `conv` of the previous chapters, viewed through
the `RplusMin` newtype — so the two definitions coincide.

```lean
namespace VerifiedWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# Sub-additive real functions

Everything here is on the bare value type $`\overline{\mathbb{R}}_{\ge
0}^\infty`, with numeric $`+` and $`\le`.

*Definition:* $`g` is sub-additive when $`g(u + s) \le g(u) + g(s)`

```lean
def IsSubadditive (g : ℝ≥0 → ℝ≥0∞) : Prop :=
  ∀ u s : ℝ≥0, g (u + s) ≤ g u + g s
```

The _infimal convolution_ is the numeric infimum, over all splits
$`u + s = t`, of $`g(u) + h(s)`. We index by the splits of `t`.

*Definition:* $`(g \ast h)(t) = \inf_{u + s = t}\,(g(u) + h(s))`

```lean
noncomputable def infConv (g h : ℝ≥0 → ℝ≥0∞) :
    ℝ≥0 → ℝ≥0∞ :=
  fun t =>
    ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      g p.1.1 + h p.1.2
```

# The fundamental fixed-point result

A sub-additive curve null at the origin is a _fixed point_ of infimal
self-convolution. Both inequalities are immediate from the structure of
the infimum:

- _Below_ $`g`: the split $`0 + t = t` contributes the term
  $`g(0) + g(t) = g(t)`, using $`g(0) = 0`; an infimum lies below any
  of its terms.
- _Above_ $`g`: sub-additivity makes every split-term
  $`g(u) + g(s) \ge g(u + s) = g(t)`, so the infimum does too.

Together they give equality.

*Theorem:* if $`g` is sub-additive and $`g(0) = 0` then $`g \ast g = g`

```lean
theorem infConv_self_of_subadditive
    (g : ℝ≥0 → ℝ≥0∞)
    (hsub : IsSubadditive g) (h0 : g 0 = 0) :
    infConv g g = g := by
  funext t
  unfold infConv
  apply le_antisymm
  · refine iInf_le_of_le ⟨(0, t), by simp⟩ ?_
    simp [h0]
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, hus⟩
    simp only
    calc g t = g (u + s) := by rw [hus]
      _ ≤ g u + g s := hsub u s
```

# The two convolutions agree

The infimal convolution `infConv` on real functions is the _same
operation_ as the dioid convolution `conv` of the previous chapters,
viewed through the `RplusMin` newtype. Wrapping a real function by
$`s \mapsto \langle g(s)\rangle` embeds it into `Fmin`; we show that
wrapping, convolving with `conv`, and unwrapping reproduces `infConv`.
This is the content that makes the two definitions interchangeable —
the dioid sum $`\bigsqcup` on $`\overline{\mathbb{R}}_{\ge 0}` is
exactly the numeric infimum over the splits.

*Definition:* the dioid function induced by a real function

```lean
def toF (g : ℝ≥0 → ℝ≥0∞) : Fmin := fun s => ⟨g s⟩
```

Unwrapping the dioid convolution of induced functions gives the
infimal convolution, value by value. Each split-term matches: the
dioid product $`\otimes` is the numeric sum, and the dioid supremum
$`\bigsqcup` is the numeric infimum, both over the same splits.

*Theorem:* $`(\text{toF}\,g \ast \text{toF}\,h)(t)` unwraps to $`(g \ast h)(t)`

```lean
theorem conv_toF_toE (g h : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    ((conv (toF g) (toF h) t : RplusMin) : ℝ≥0∞)
      = infConv g h t := by
  apply le_antisymm
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, hus⟩
    have hle := CompleteDioid.le_sSup _ _
      (show (toF g u ⊗ₒ toF h s)
          ∈ {x | ∃ u s, u + s = t
              ∧ x = toF g u ⊗ₒ toF h s}
        from ⟨u, s, hus, rfl⟩)
    rw [← conv_apply] at hle
    exact (RplusMin.le_iff _ _).mp hle
  · rw [conv_apply, ← RplusMin.le_iff]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    rw [RplusMin.le_iff]
    exact iInf_le_of_le ⟨(u, s), hus⟩ (le_refl _)
```

At the level of functions, the dioid convolution of induced curves is
the induced infimal convolution.

*Theorem:* $`\text{toF}\,g \ast \text{toF}\,h = \text{toF}\,(g \ast h)`

```lean
theorem conv_toF (g h : ℝ≥0 → ℝ≥0∞) :
    conv (toF g) (toF h) = toF (infConv g h) := by
  funext t
  apply RplusMin.ext
  exact conv_toF_toE g h t
```

The dioid self-convolution fixed point is now a corollary of the real
one: rewrite `conv` to `infConv` and apply the fundamental result.

*Theorem:* a sub-additive real `g` null at the origin induces $`\sigma` with $`\sigma \ast \sigma = \sigma`

```lean
theorem conv_self_toF_of_subadditive
    (g : ℝ≥0 → ℝ≥0∞)
    (hsub : IsSubadditive g) (h0 : g 0 = 0) :
    conv (toF g) (toF g) = toF g := by
  rw [conv_toF, infConv_self_of_subadditive g hsub h0]
```

```lean
end VerifiedWiki
```
