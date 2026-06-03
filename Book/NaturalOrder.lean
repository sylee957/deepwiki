import VersoManual
import Book.DioidFunctions

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The natural order" =>
The cumulative functions of network calculus are the concrete
specialization of the function dioid to the _(min,plus)_ carrier
$`\overline{\mathbb{R}}_{\ge 0}` (`RplusMin`): ordinary non-negative
functions embed into this carrier, while $`+\infty` supplies the
neutral needed by the min-plus sum. We write this function space
$`\mathcal{F}` (`F`) and fix it here, as the carrier for the rest of
the development.

```lean
namespace VerifiedWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# The function space of cumulative functions

*Definition:* the concrete function space $`\mathcal{F} = \mathbb{R}^{+} \to \overline{\mathbb{R}}_{\ge 0}`

```lean
abbrev F := ℝ≥0 → RplusMin
```

These functions are compared in the _natural_ order: the ordinary
pointwise numeric order on their values. On $`\mathcal{F}` this is the
_reverse_ of the dioid order — for _(min,plus)_ the dioid order is the
reversed numeric order — so the two must be kept apart. The rest of
this chapter records the natural order `≤ₙ`, its agreement with the
reversed dioid order, and that it is a preorder.

# The natural order

The relation `NatLe f g` is the ordinary pointwise numeric order,
obtained by looking through the `RplusMin` wrapper to the underlying
$`\overline{\mathbb{R}}_{\ge 0}^\infty` values.

*Definition:* $`f \le_n g \iff \forall t,\ f(t) \le g(t)` numerically

```lean
def NatLe (f g : F) : Prop :=
  ∀ t, (f t : ℝ≥0∞) ≤ g t

scoped notation:50 f:51 " ≤ₙ " g:51 => NatLe f g
```

The natural order is the opposite of the dioid order on each value:
$`f \le_n g` exactly when $`g(t) \preceq f(t)` for every `t`. It is
reflexive and transitive — a preorder.

*Theorem:* $`f \le_n g \iff \forall t,\ g(t) \preceq f(t)`, with $`\le_n` reflexive and transitive

```lean
theorem natLe_iff (f g : F) :
    f ≤ₙ g ↔ ∀ t, g t ≼ₒ f t := by
  constructor
  · intro h t
    exact (RplusMin.le_iff (g t) (f t)).mpr (h t)
  · intro h t
    exact (RplusMin.le_iff (g t) (f t)).mp (h t)

theorem NatLe.refl (f : F) : f ≤ₙ f :=
  fun _ => le_rfl

theorem NatLe.trans {f g h : F}
    (hfg : f ≤ₙ g) (hgh : g ≤ₙ h) : f ≤ₙ h :=
  fun t => le_trans (hfg t) (hgh t)
```

```lean
end VerifiedWiki
```
