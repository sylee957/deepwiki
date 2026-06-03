import VersoManual
import Book.DioidFunctions

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The (min,plus) function dioid" =>
The functions of network calculus map the non-negative reals into the
complete _(min,plus)_ dioid $`\overline{\mathbb{R}}_{\min}` of extended
reals $`\mathbb{R} \cup \{\pm\infty\}`. This is the function class
$`\mathcal{F}` on which the _(min,plus) convolution_ lives, presented
here directly as the dioid product of the generic chapter, specialized
to that carrier.

```lean
namespace VerifiedWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# The function class

$`\mathcal{F}` is the set of functions from the non-negative reals
$`\mathbb{R}^{+}` into the complete _(min,plus)_ dioid
$`\overline{\mathbb{R}}_{\min} = \mathbb{R} \cup \{\pm\infty\}`
(`RbarMin`). We work over the bare function type directly; it is a
complete dioid in its own right by the generic `funCompleteDioid`
instance.

*Definition:* $`\mathcal{F} = \mathbb{R}^{+} \to \overline{\mathbb{R}}_{\min}`

```lean
abbrev FminBar := ℝ≥0 → RbarMin
```

# The (min,plus) convolution

The _(min,plus) convolution_ $`f \ast g` of two functions of
$`\mathcal{F}` is their dioid product — the generic convolution `conv`,
specialized to the carrier `RbarMin`. Its value at $`t` is the dioid
sum, over all splits $`u + s = t`, of the product $`f(u) \otimes g(s)`.
On $`\overline{\mathbb{R}}_{\min}` the dioid sum is the numeric infimum
and the product is numeric addition, so this is the infimal convolution
$$`(f \ast g)(t) = \inf_{u + s = t}\,(f(u) + g(s)).`
No new definition is needed; `conv` already _is_ this convolution on
$`\mathcal{F}`.

*Theorem:* $`(f \ast g)(t) = \bigsqcup\,\{\, f(u) \otimes g(s) \mid u + s = t \,\}`

```lean
example (f g : FminBar) (t : ℝ≥0) :
    conv f g t
      = CompleteDioid.sSup
          { x | ∃ u s, u + s = t ∧ x = f u ⊗ₒ g s } :=
  conv_apply f g t
```

The decomposition $`u + s = t` is the single variable $`s \le t` with
$`u = t - s`, giving the equivalent _single-variable_ form.

*Theorem:* $`(f \ast g)(t) = \bigsqcup\,\{\, f(t - s) \otimes g(s) \mid s \le t \,\}`

```lean
example (f g : FminBar) (t : ℝ≥0) :
    conv f g t
      = CompleteDioid.sSup
          { x | ∃ s : ℝ≥0,
              s ≤ t ∧ x = f (t - s) ⊗ₒ g s } :=
  conv_eq_sub f g t
```

```lean
end VerifiedWiki
```
