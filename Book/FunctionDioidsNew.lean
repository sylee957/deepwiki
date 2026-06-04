import VersoManual
import Book.DioidFunctions

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The (min,plus) function dioid" =>
The functions of network calculus map the non-negative reals into the
extended reals $`\mathbb{R} \cup \{\pm\infty\}`. We give the _(min,plus)
convolution_ first as a direct numeric infimum on those real functions,
then lift them into the complete _(min,plus)_ dioid
$`\overline{\mathbb{R}}_{\min}` (`MinPlusExt`) and check that the dioid
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
_(min,plus)_ dioid $`\overline{\mathbb{R}}_{\min}` (`MinPlusExt`), the
newtype wrapping `WithTop (WithBot ℝ)` with the dioid algebra. It is a
complete dioid in its own right by the generic `funCompleteDioid`
instance.

*Definition:* $`\mathcal{F} = \mathbb{R}^{+} \to \overline{\mathbb{R}}_{\min}`

```lean
abbrev FminBar := ℝ≥0 → MinPlusExt
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
theorem conv_coe_min
    (f g : ℝ≥0 → WithTop (WithBot ℝ)) (t : ℝ≥0) :
    ((conv (↑f) (↑g) t : MinPlusExt)
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
    exact (MinPlusExt.le_iff _ _).mp hle
  · rw [conv_apply, ← MinPlusExt.le_iff]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    rw [MinPlusExt.le_iff]
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
  apply MinPlusExt.ext
  exact conv_coe_min f g t
```

# The dual (max,plus) convolution

The construction dualizes verbatim to the _(max,plus)_ side, on the
same extended reals but through the order-dual carrier `MaxPlusExt`
(`WithBot (WithTop ℝ)`). The _(max,plus) convolution_ is the numeric
_supremum_, over all splits $`u + s = t`, of $`f(u) + g(s)`; the
function class is $`\mathcal{F}_{\max} = \mathbb{R}^{+} \to
\overline{\mathbb{R}}_{\max}`, and the dioid product again computes it.

*Definition:* $`(f \mathbin{\overline{\ast}} g)(t) = \sup_{u + s = t}\,(f(u) + g(s))`

```lean
noncomputable def maxConvBar
    (f g : ℝ≥0 → WithBot (WithTop ℝ)) :
    ℝ≥0 → WithBot (WithTop ℝ) :=
  fun t =>
    ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      f p.1.1 + g p.1.2

abbrev FmaxBar := ℝ≥0 → MaxPlusExt

instance : Coe (ℝ≥0 → WithBot (WithTop ℝ)) FmaxBar :=
  ⟨fun f t => ⟨f t⟩⟩
```

*Theorem:* $`(\uparrow\!f \mathbin{\overline{\ast}} \uparrow\!g)(t)` unwraps to $`(f \mathbin{\overline{\ast}} g)(t)`

```lean
theorem conv_coe_max
    (f g : ℝ≥0 → WithBot (WithTop ℝ)) (t : ℝ≥0) :
    ((conv (↑f) (↑g) t : MaxPlusExt)
        : WithBot (WithTop ℝ))
      = maxConvBar f g t := by
  apply le_antisymm
  · rw [conv_apply, ← MaxPlusExt.le_iff]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    rw [MaxPlusExt.le_iff]
    exact le_iSup_of_le ⟨(u, s), hus⟩ (le_refl _)
  · refine iSup_le ?_
    rintro ⟨⟨u, s⟩, hus⟩
    have hle := CompleteDioid.le_sSup _ _
      (show ((↑f : FmaxBar) u ⊗ₒ (↑g : FmaxBar) s)
          ∈ {x | ∃ u s, u + s = t
              ∧ x = (↑f : FmaxBar) u ⊗ₒ (↑g : FmaxBar) s}
        from ⟨u, s, hus, rfl⟩)
    rw [← conv_apply] at hle
    exact (MaxPlusExt.le_iff _ _).mp hle
```

*Theorem:* $`\uparrow\!f \mathbin{\overline{\ast}} \uparrow\!g = \uparrow\!(f \mathbin{\overline{\ast}} g)`

```lean
theorem conv_coeMax
    (f g : ℝ≥0 → WithBot (WithTop ℝ)) :
    conv (↑f : FmaxBar) (↑g : FmaxBar)
      = (↑(maxConvBar f g) : FmaxBar) := by
  funext t
  apply MaxPlusExt.ext
  exact conv_coe_max f g t
```

The min-plus and max-plus convolutions are now symmetric: both on the
extended reals $`\mathbb{R} \cup \{\pm\infty\}`, one the numeric
infimum and the other the supremum over the same splits, each the dioid
product in its respective complete dioid (`MinPlusExt`, `MaxPlusExt`).

# Subsets of the function class

Network calculus restricts to four subsets of real functions, defined
by _natural-order_ conditions on the values (non-negativity, nullity at
the origin, non-decrease). We state them as predicates on
$`\mathbb{R}^{+} \to \mathbb{R} \cup \{\pm\infty\}`.

Rather than bundle each class as a monolithic predicate, we name the
three _atomic_ properties — non-negativity, nullity at the origin, and
non-decrease — and build the classes as conjunctions of them. Each
stability fact is then proved once, per atom, and the classes inherit
it by conjunction.

*Definition:* $`f` is non-negative: $`\forall t,\ 0 \le f(t)`

```lean
def isNonneg (f : ℝ≥0 → WithTop (WithBot ℝ)) : Prop :=
  ∀ t, 0 ≤ f t
```

*Definition:* $`f` is null at the origin: $`f(0) = 0`

```lean
def isNullAtOrigin (f : ℝ≥0 → WithTop (WithBot ℝ)) :
    Prop :=
  f 0 = 0
```

*Definition:* $`f` is non-decreasing: $`\forall x \le y,\ f(x) \le f(y)`

```lean
def isNondecr (f : ℝ≥0 → WithTop (WithBot ℝ)) : Prop :=
  ∀ x y, x ≤ y → f x ≤ f y
```

The textbook classes are conjunctions of these atoms:
$`\mathcal{F}^{+}` is `isNonneg`; $`\mathcal{F}_0` is
`isNonneg ∧ isNullAtOrigin`; $`\mathcal{F}^{\uparrow}` is
`isNonneg ∧ isNondecr`; and $`\mathcal{F}_0^{\uparrow}` is all three.

## Stability under the minimum

Each atomic property passes through the pointwise minimum; a class,
being a conjunction of atoms, then inherits stability by conjunction.

*Theorem:* non-negativity is stable under $`\min`

```lean
theorem isNonneg.min {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : isNonneg f) (hg : isNonneg g) :
    isNonneg (fun t => min (f t) (g t)) :=
  fun t => le_min (hf t) (hg t)
```

*Theorem:* nullity at the origin is stable under $`\min`

```lean
theorem isNullAtOrigin.min
    {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : isNullAtOrigin f) (hg : isNullAtOrigin g) :
    isNullAtOrigin (fun t => min (f t) (g t)) := by
  show Min.min (f 0) (g 0) = 0
  rw [hf, hg, min_self]
```

*Theorem:* non-decrease is stable under $`\min`

```lean
theorem isNondecr.min
    {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : isNondecr f) (hg : isNondecr g) :
    isNondecr (fun t => min (f t) (g t)) :=
  fun x y hxy => min_le_min (hf x y hxy) (hg x y hxy)
```

## Stability under the convolution

Each atom is likewise stable under the (min,plus) convolution
`minConvBar`. Non-negativity passes through because every split-sum
$`f(u) + g(s)` is non-negative, hence so is their infimum. Nullity at
the origin holds because the only split of $`0` is $`0 + 0`.

*Theorem:* non-negativity is stable under the convolution

```lean
theorem isNonneg.conv
    {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : isNonneg f) (hg : isNonneg g) :
    isNonneg (minConvBar f g) := by
  intro t
  rw [minConvBar]
  refine le_iInf ?_
  rintro ⟨⟨u, s⟩, _⟩
  calc (0 : WithTop (WithBot ℝ)) = 0 + 0 := by simp
    _ ≤ f u + g s := by gcongr; exacts [hf u, hg s]
```

*Theorem:* nullity at the origin is stable under the convolution

```lean
theorem isNullAtOrigin.conv
    {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : isNullAtOrigin f) (hg : isNullAtOrigin g) :
    isNullAtOrigin (minConvBar f g) := by
  show minConvBar f g 0 = 0
  rw [minConvBar]
  apply le_antisymm
  · exact iInf_le_of_le ⟨(0, 0), by simp⟩ (by
      simp [isNullAtOrigin] at hf hg; simp [hf, hg])
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, (hus : u + s = 0)⟩
    obtain ⟨rfl, rfl⟩ := add_eq_zero.mp hus
    simp [isNullAtOrigin] at hf hg; simp [hf, hg]
```

Non-decrease is the inf-convolution of non-decreasing functions: a
split of the larger argument is reduced to a split of the smaller one
by lowering the first coordinate to $`\min(u, x)`.

*Theorem:* non-decrease is stable under the convolution

```lean
theorem isNondecr.conv
    {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : isNondecr f) (hg : isNondecr g) :
    isNondecr (minConvBar f g) := by
  intro x y hxy
  rw [minConvBar, minConvBar]
  refine le_iInf ?_
  rintro ⟨⟨u, s⟩, (hus : u + s = y)⟩
  refine iInf_le_of_le
    ⟨(Min.min u x, x - Min.min u x), by
      rw [add_tsub_cancel_of_le (min_le_right u x)]⟩ ?_
  have hs : x - Min.min u x ≤ s := by
    rw [tsub_le_iff_right]
    rcases le_total u x with h | h
    · rw [min_eq_left h, add_comm, hus]; exact hxy
    · rw [min_eq_right h]; exact le_add_self
  gcongr
  · exact hf _ _ (min_le_left u x)
  · exact hg _ _ hs
```

# F⁺ and F↑ are complete dioids

By the stability lemmas, $`\mathcal{F}^{+}` and $`\mathcal{F}^{\uparrow}`
are sub-complete-dioids of $`\mathcal{F}`: closed under the dioid sum
$`\oplus` (the pointwise minimum), the product $`\otimes` (the
convolution), the neutrals — the zero $`\varepsilon = +\infty` (the
constant $`+\infty` function, which is non-negative and non-decreasing)
and the unit $`e` (the impulse) — and arbitrary suprema. The generic
sub-complete-dioid builder then equips each with a complete dioid
structure.

We read the atoms onto $`\mathcal{F}` through the `MinPlusExt` wrapper —
applying each property to the underlying values $`t \mapsto (f\,t)`
— and record two bridges: $`\mathcal{F}` is the lift of its own
underlying values, and the dioid product unwraps to `minConvBar`.

The classes are the subtypes of $`\mathcal{F}` cut out directly by the
atoms: $`\mathcal{F}^{+}` by non-negativity alone, and
$`\mathcal{F}^{\uparrow}` by the _conjunction_ of non-negativity and
monotonicity — written inline as the carving predicate, no named
composite.

*Definition:* $`\mathcal{F}^{+}` and $`\mathcal{F}^{\uparrow}` as subtypes

```lean
abbrev FPlus :=
  {f : FminBar // isNonneg (fun t => (f t).toVal)}

abbrev FNondecr :=
  {f : FminBar //
    isNonneg (fun t => (f t).toVal)
      ∧ isNondecr (fun t => (f t).toVal)}
```

```lean
theorem coe_toVal (a : FminBar) :
    (↑(fun t => (a t).toVal) : FminBar) = a := by
  funext t; apply MinPlusExt.ext; rfl

theorem mul_toVal (a b : FminBar) (t : ℝ≥0) :
    ((a ⊗ₒ b) t).toVal
      = minConvBar (fun t => (a t).toVal)
          (fun t => (b t).toVal) t := by
  show ((conv a b t : MinPlusExt) : WithTop (WithBot ℝ)) = _
  rw [← coe_toVal a, ← coe_toVal b]
  exact conv_coe_min _ _ t
```

The unit (impulse) and zero (constant $`+\infty`) are non-negative and
non-decreasing; with the stability lemmas this gives the five closure
conditions.

*Definition:* $`\mathcal{F}^{+}` is a sub-complete-dioid

```lean
theorem isSubCompleteDioid_FPlus :
    IsSubCompleteDioid
      (fun f : FminBar => isNonneg (fun t => (f t).toVal))
      where
  add ha hb := fun t => le_min (ha t) (hb t)
  mul {a b} ha hb := fun t => by
    show (0 : WithTop (WithBot ℝ)) ≤ ((a ⊗ₒ b) t).toVal
    rw [mul_toVal]; exact (isNonneg.conv ha hb) t
  eps := fun _ => le_top
  one := fun t => by
    show (0 : WithTop (WithBot ℝ))
        ≤ ((convUnit t : MinPlusExt)).toVal
    rcases eq_or_ne t 0 with h | h
    · rw [convUnit, if_pos h]; exact le_rfl
    · rw [convUnit, if_neg h]; exact le_top
  iSup F hF := fun t => le_iInf (fun i => hF i t)
```

*Definition:* $`\mathcal{F}^{\uparrow}` is a sub-complete-dioid

```lean
theorem isSubCompleteDioid_FNondecr :
    IsSubCompleteDioid
      (fun f : FminBar =>
        isNonneg (fun t => (f t).toVal)
          ∧ isNondecr (fun t => (f t).toVal))
      where
  add ha hb :=
    ⟨fun t => le_min (ha.1 t) (hb.1 t),
      fun x y hxy =>
        min_le_min (ha.2 x y hxy) (hb.2 x y hxy)⟩
  mul {a b} ha hb := by
    have hn := isNonneg.conv ha.1 hb.1
    have hm := isNondecr.conv ha.2 hb.2
    refine ⟨fun t => ?_, fun x y hxy => ?_⟩
    · show (0 : WithTop (WithBot ℝ)) ≤ ((a ⊗ₒ b) t).toVal
      rw [mul_toVal]; exact hn t
    · show ((a ⊗ₒ b) x).toVal ≤ ((a ⊗ₒ b) y).toVal
      rw [mul_toVal, mul_toVal]; exact hm x y hxy
  eps := ⟨fun _ => le_top, fun _ _ _ => le_top⟩
  one := by
    refine ⟨fun t => ?_, fun x y hxy => ?_⟩
    · show (0 : WithTop (WithBot ℝ))
          ≤ ((convUnit t : MinPlusExt)).toVal
      rcases eq_or_ne t 0 with h | h
      · rw [convUnit, if_pos h]; exact le_rfl
      · rw [convUnit, if_neg h]; exact le_top
    · show ((convUnit x : MinPlusExt)).toVal
          ≤ ((convUnit y : MinPlusExt)).toVal
      rcases eq_or_ne x 0 with hx | hx
      · rw [convUnit, if_pos hx]
        show (0 : WithTop (WithBot ℝ)) ≤ _
        rcases eq_or_ne y 0 with hy | hy
        · rw [convUnit, if_pos hy]; exact le_rfl
        · rw [convUnit, if_neg hy]; exact le_top
      · have hy : y ≠ 0 := by
          rintro rfl; exact hx (le_zero_iff.mp hxy)
        rw [convUnit, if_neg hx, convUnit, if_neg hy]
  iSup F hF :=
    ⟨fun t => le_iInf (fun i => (hF i).1 t),
      fun x y hxy =>
        le_iInf (fun i =>
          (iInf_le _ i).trans ((hF i).2 x y hxy))⟩
```

The builder turns each into a complete dioid.

*Definition:* the complete dioids $`\mathcal{F}^{+}` and $`\mathcal{F}^{\uparrow}`

```lean
noncomputable instance : CompleteDioid FPlus :=
  isSubCompleteDioid_FPlus.toCompleteDioid

noncomputable instance : CompleteDioid FNondecr :=
  isSubCompleteDioid_FNondecr.toCompleteDioid
```

By contrast $`\mathcal{F}_0` and $`\mathcal{F}_0^{\uparrow}` are _not_
dioids: the closure condition `eps` would require the dioid zero
$`\varepsilon = +\infty` (the constant function) to be null at the
origin, but $`+\infty \ne 0`. The sub-complete-dioid builder does not
apply, faithfully reflecting that these sets lack the neutral.

```lean
end VerifiedWiki
```
