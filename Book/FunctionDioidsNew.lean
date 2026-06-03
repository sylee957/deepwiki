import VersoManual
import Book.DioidFunctions

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The (min,plus) function dioid" =>
The functions of network calculus map the non-negative reals into the
extended reals $`\mathbb{R} \cup \{\pm\infty\}`. We give the _(min,plus)
convolution_ first as a direct numeric infimum on those real functions,
then lift them into the complete _(min,plus)_ dioid
$`\overline{\mathbb{R}}_{\min}` (`RbarMin`) and check that the dioid
product `conv` of the generic chapter computes exactly the same thing.

The carrier of the extended reals is `WithTop (WithBot ℝ)`, with the
_top-absorbing_ addition $`(+\infty) + (-\infty) = +\infty` — the
addition the (min,plus) dioid needs, so that $`+\infty` (the dioid zero)
stays absorbing for the product. (This is _not_ `EReal`, whose addition
takes $`(+\infty) + (-\infty) = -\infty`; the value-by-value lift would
be unaffected, but the convolution's sum would then disagree with the
dioid product.)

```lean
namespace VerifiedWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# The (min,plus) convolution on real functions

A real function is an $`f : \mathbb{R}^{+} \to \mathbb{R} \cup
\{\pm\infty\}`. Their _(min,plus) convolution_ is the numeric infimum,
over all splits $`u + s = t`, of $`f(u) + g(s)`.

*Definition:* $`(f \ast g)(t) = \inf_{u + s = t}\,(f(u) + g(s))`

```lean
noncomputable def minConvBar
    (f g : ℝ≥0 → WithTop (WithBot ℝ)) :
    ℝ≥0 → WithTop (WithBot ℝ) :=
  fun t =>
    ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      f p.1.1 + g p.1.2
```

# The function dioid

$`\mathcal{F}` is the set of those functions read into the complete
_(min,plus)_ dioid $`\overline{\mathbb{R}}_{\min}` (`RbarMin`), the
newtype wrapping `WithTop (WithBot ℝ)` with the dioid algebra. It is a
complete dioid in its own right by the generic `funCompleteDioid`
instance.

*Definition:* $`\mathcal{F} = \mathbb{R}^{+} \to \overline{\mathbb{R}}_{\min}`

```lean
abbrev FminBar := ℝ≥0 → RbarMin
```

A real function lifts into $`\mathcal{F}` value by value, wrapping each
extended-real value in the dioid newtype. The lift uses no arithmetic,
only the wrapper, so we take it as a coercion $`\uparrow`.

*Definition:* the coercion of a real function into $`\mathcal{F}`

```lean
instance : Coe (ℝ≥0 → WithTop (WithBot ℝ)) FminBar :=
  ⟨fun f t => ⟨f t⟩⟩
```

# The two convolutions coincide

Unwrapping the dioid convolution of lifted functions gives the
real (min,plus) convolution, value by value: the dioid product
$`\otimes` is the numeric sum (the top-absorbing addition), and the
dioid supremum $`\bigsqcup` is the numeric infimum, both over the same
splits.

*Theorem:* $`(\uparrow\!f \ast \uparrow\!g)(t)` unwraps to $`(f \ast g)(t)`

```lean
theorem conv_coe_toB
    (f g : ℝ≥0 → WithTop (WithBot ℝ)) (t : ℝ≥0) :
    ((conv (↑f) (↑g) t : RbarMin)
        : WithTop (WithBot ℝ))
      = minConvBar f g t := by
  apply le_antisymm
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, hus⟩
    have hle := CompleteDioid.le_sSup _ _
      (show ((↑f : FminBar) u ⊗ₒ (↑g : FminBar) s)
          ∈ {x | ∃ u s, u + s = t
              ∧ x = (↑f : FminBar) u ⊗ₒ (↑g : FminBar) s}
        from ⟨u, s, hus, rfl⟩)
    rw [← conv_apply] at hle
    exact (RbarMin.le_iff _ _).mp hle
  · rw [conv_apply, ← RbarMin.le_iff]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    rw [RbarMin.le_iff]
    exact iInf_le_of_le ⟨(u, s), hus⟩ (le_refl _)
```

At the level of functions, the dioid convolution of lifted curves is the
lift of the real (min,plus) convolution.

*Theorem:* $`\uparrow\!f \ast \uparrow\!g = \uparrow\!(f \ast g)`

```lean
theorem conv_coe
    (f g : ℝ≥0 → WithTop (WithBot ℝ)) :
    conv (↑f : FminBar) (↑g : FminBar)
      = (↑(minConvBar f g) : FminBar) := by
  funext t
  apply RbarMin.ext
  exact conv_coe_toB f g t
```

```lean
end VerifiedWiki
```
