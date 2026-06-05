import VersoManual
import Book.DioidFunctions
import Mathlib.Topology.Instances.NNReal.Lemmas

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Function dioids of real curves" =>
The function dioid $`\mathbb{R}^{+} \to T` of the previous chapter is
generic. This chapter specializes it to the scalar carriers of network
calculus and presents the real convolution operators it yields.

We work over two views of the reals. First the _extended reals_
$`\mathbb{R} \cup \{\pm\infty\}`: the (min,plus) convolution is given as
a direct numeric infimum on real functions, then lifted into the
complete _(min,plus)_ dioid $`\overline{\mathbb{R}}_{\min}`
(`MinPlusExt`), with the dioid product `conv` shown to compute exactly
the same thing — and dually for (max,plus) through `MaxPlusExt`. The
textbook function classes $`\mathcal{F}^{+}`, $`\mathcal{F}^{\uparrow}`
are then cut out as sub-complete-dioids.

Then the _non-negative reals_ $`\mathbb{R}_{\ge 0}`: cumulative
functions embed into the carriers $`\overline{\mathbb{R}}_{\ge 0}`
(`MinPlusNN`) and its (max,plus) dual (`MaxPlusNN`), and the real
convolution operators `minConv` / `maxConv` are read back from the
dioid product, each shown to equal the expected $`\inf` / $`\sup` over
the splits of $`t`.

The carrier of the extended reals is `WithTop (WithBot ℝ)`, with the
_top-absorbing_ addition $`(+\infty) + (-\infty) = +\infty` — the
addition the (min,plus) dioid needs, so that $`+\infty` (the dioid zero)
stays absorbing for the product. (This is _not_ `EReal`, whose addition
takes $`(+\infty) + (-\infty) = -\infty`; the value-by-value lift would
be unaffected, but the convolution's sum would then disagree with the
dioid product.)

```lean
namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
```

# Convolutions of numeric functions

We collect, in one place, the _direct_ convolution operators on numeric
functions — defined as a numeric infimum or supremum over the splits
$`u + s = t`, with no recourse to a dioid. There are two number-system
views, each in a (min,plus) and a (max,plus) flavour:

- on the _extended reals_ $`\mathbb{R} \cup \{\pm\infty\}` — `minConvBar`
  (infimum) and `maxConvBar` (supremum);
- on the _non-negative reals_ $`\mathbb{R}_{\ge 0}` — `minConvR`
  (infimum) and `maxConvR` (supremum).

Each is later shown to _coincide_ with the corresponding dioid product
`conv` (the extended-real pair, in the sections that follow) or with its
dioid-backed projection (the $`\mathbb{R}_{\ge 0}` pair, at the end of
the chapter). The definitions are gathered here; the coincidence proofs
stay beside the dioid material they bridge to.

A real function is an $`f : \mathbb{R}^{+} \to \mathbb{R} \cup
\{\pm\infty\}`. Its _(min,plus) convolution_ is the numeric infimum,
over all splits $`u + s = t`, of $`f(u) + g(s)`.

*Definition:* $`(f \ast g)(t) = \inf_{u + s = t}\,(f(u) + g(s))` on $`\mathbb{R} \cup \{\pm\infty\}`

```lean
noncomputable def minConvBar
    (f g : ℝ≥0 → WithTop (WithBot ℝ)) :
    ℝ≥0 → WithTop (WithBot ℝ) :=
  fun t =>
    ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      f p.1.1 + g p.1.2
```

The dual _(max,plus) convolution_ on the extended reals is the numeric
supremum over the same splits, on the order-dual carrier.

*Definition:* $`(f \mathbin{\overline{\ast}} g)(t) = \sup_{u + s = t}\,(f(u) + g(s))` on $`\mathbb{R} \cup \{\pm\infty\}`

```lean
noncomputable def maxConvBar
    (f g : ℝ≥0 → WithBot (WithTop ℝ)) :
    ℝ≥0 → WithBot (WithTop ℝ) :=
  fun t =>
    ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      f p.1.1 + g p.1.2
```

On the _non-negative reals_ $`\mathbb{R}_{\ge 0}` the same two operators
read directly off the curve values. The (min,plus) one is the numeric
infimum.

*Definition:* $`(g \ast h)(t) = \inf_{u + s = t} (g(u) + h(s))` on $`\mathbb{R}_{\ge 0}`

```lean
noncomputable def minConvR (g h : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      (g p.1.1 + h p.1.2)
```

The (max,plus) one is the numeric supremum. Over $`\mathbb{R}_{\ge 0}`
an unbounded supremum is not finite, so this direct form floors to $`0`
there; the dioid-backed `maxConv` defined later is the canonical
operator, and the two agree wherever the supremum is finite.

*Definition:* $`(g \mathbin{\overline{\ast}} h)(t) = \sup_{a + b = t} (g(a) + h(b))` on $`\mathbb{R}_{\ge 0}`

```lean
noncomputable def maxConvR (g h : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      (g p.1.1 + h p.1.2)
```

On the _extended_ non-negative reals $`\overline{\mathbb{R}}_{\ge 0}`
(`ℝ≥0∞`) the same two operators are `minConvE` and `maxConvE`; these are
the forms the sub-/super-additivity fixed-point results of the
`Additivity` chapter are stated over.

*Definition:* $`(g \ast h)(t) = \inf_{u + s = t}\,(g(u) + h(s))` on $`\overline{\mathbb{R}}_{\ge 0}`

```lean
noncomputable def minConvE (g h : ℝ≥0 → ℝ≥0∞) :
    ℝ≥0 → ℝ≥0∞ :=
  fun t =>
    ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      g p.1.1 + h p.1.2
```

*Definition:* $`(g \mathbin{\overline{\ast}} h)(t) = \sup_{u + s = t}\,(g(u) + h(s))` on $`\overline{\mathbb{R}}_{\ge 0}`

```lean
noncomputable def maxConvE (g h : ℝ≥0 → ℝ≥0∞) :
    ℝ≥0 → ℝ≥0∞ :=
  fun t =>
    ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      g p.1.1 + h p.1.2
```

The _(min,plus) deconvolution_ (the dual quotient) is the numeric
supremum, over all forward shifts $`s`, of $`g(t + s) - h(s)`.

*Definition:* $`(g \oslash h)(t) = \sup_{s}\,(g(t + s) - h(s))` on $`\overline{\mathbb{R}}_{\ge 0}`

```lean
noncomputable def minDeconvE (g h : ℝ≥0 → ℝ≥0∞) :
    ℝ≥0 → ℝ≥0∞ :=
  fun t => ⨆ s : ℝ≥0, g (t + s) - h s
```

# The extended-real function dioid

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
(`WithBot (WithTop ℝ)`). The _(max,plus) convolution_ `maxConvBar` is
the numeric _supremum_ over the splits (defined above); the function
class is $`\mathcal{F}_{\max} = \mathbb{R}^{+} \to
\overline{\mathbb{R}}_{\max}`, and the dioid product again computes it.

*Definition:* the _(max,plus)_ function space and the lift of a real function

```lean
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

## Stability under the pointwise sum

The classes are also closed under the ordinary _pointwise numeric
sum_ $`(f + g)(t) = f(t) + g(t)`. This is the top-absorbing addition
of $`\overline{\mathbb{R}}`, _not_ the dioid sum $`\oplus` (which is
the minimum); it plays no part in the sub-dioid builder below, but
$`\mathcal{F}^{\uparrow}` is stable under it all the same. Both atoms
pass through: a sum of non-negative values is non-negative, and the
sum of two non-decreasing functions is non-decreasing.

*Theorem:* non-negativity is stable under the pointwise sum

```lean
theorem isNonneg.add
    {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : isNonneg f) (hg : isNonneg g) :
    isNonneg (fun t => f t + g t) := by
  intro t
  calc (0 : WithTop (WithBot ℝ)) = 0 + 0 := by simp
    _ ≤ f t + g t := by gcongr; exacts [hf t, hg t]
```

*Theorem:* non-decrease is stable under the pointwise sum

```lean
theorem isNondecr.add
    {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : isNondecr f) (hg : isNondecr g) :
    isNondecr (fun t => f t + g t) := by
  intro x y hxy
  show f x + g x ≤ f y + g y
  gcongr
  · exact hf x y hxy
  · exact hg x y hxy
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

# The two function dioids over the non-negative reals

Each is the generic function dioid `funCompleteDioid` instantiated at a
scalar carrier: $`\mathcal{F}_{\min}` at `MinPlusNN`, $`\mathcal{F}_{\max}`
at `MaxPlusNN`. The min-plus space $`\mathcal{F}_{\min}` is the carrier
for the rest of the development.

*Definition:* the _(min,plus)_ function space $`\mathcal{F}_{\min} = \mathbb{R}^{+} \to \overline{\mathbb{R}}_{\ge 0}`

```lean
abbrev Fmin := ℝ≥0 → MinPlusNN
```

*Definition:* the _(max,plus)_ function space $`\mathcal{F}_{\max} = \mathbb{R}^{+} \to \overline{\mathbb{R}}_{\ge 0}^{\pm}`

```lean
abbrev Fmax := ℝ≥0 → MaxPlusNN
```

# The (min,plus) convolution on the function class

The _(min,plus) convolution_ $`f \ast g` of two functions of
$`\mathcal{F}_{\min}` is their dioid product — the generic convolution
`conv` of the previous chapter, specialized to the carrier `MinPlusNN`.
Its value at $`t` is the dioid sum, over all splits $`u + s = t`, of
the product $`f(u) \otimes g(s)`; since on
$`\overline{\mathbb{R}}_{\ge 0}` the dioid sum is the numeric infimum
and the product is numeric addition, this is the familiar infimal
convolution
$$`(f \ast g)(t) = \inf_{u + s = t}\,(f(u) + g(s)).`
No new definition is needed; `conv` already _is_ this convolution on
$`\mathcal{F}_{\min}`.

*Theorem:* $`(f \ast g)(t) = \bigsqcup\,\{\, f(u) \otimes g(s) \mid u + s = t \,\}` on $`\mathcal{F}_{\min}`

```lean
example (f g : Fmin) (t : ℝ≥0) :
    conv f g t
      = CompleteDioid.sSup
          { x | ∃ u s, u + s = t ∧ x = f u ⊗ₒ g s } :=
  conv_apply f g t
```

The decomposition $`u + s = t` is the single variable $`s \le t` with
$`u = t - s`, giving the equivalent _single-variable_ form.

*Theorem:* $`(f \ast g)(t) = \bigsqcup\,\{\, f(t - s) \otimes g(s) \mid s \le t \,\}`

```lean
example (f g : Fmin) (t : ℝ≥0) :
    conv f g t
      = CompleteDioid.sSup
          { x | ∃ s : ℝ≥0,
              s ≤ t ∧ x = f (t - s) ⊗ₒ g s } :=
  conv_eq_sub f g t
```

The unit for the convolution is the impulse `convUnit`; it is a
two-sided identity on $`\mathcal{F}_{\min}`.

*Theorem:* $`\delta_0 \ast f = f`

```lean
example (f : Fmin) : conv convUnit f = f :=
  convUnit_left f
```

# A supremum-absorption lemma

A constant added to a conditionally-complete supremum is absorbed into
a bound: if $`c + f(i) \le y` for every `i`, then $`c + \bigsqcup_i f(i)
\le y`. This is the workhorse for the (max,plus) convolution bounds
below.

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

# Embedding and projecting curves

A real curve embeds into either dioid by wrapping each value; the
finite result of a dioid convolution projects back to
$`\mathbb{R}_{\ge 0}`. For _(min,plus)_ the embedding is into
$`\mathcal{F}_{\min}` (reading off the underlying
$`\mathbb{R}_{\ge 0}^{\infty}`); for _(max,plus)_ it is into
$`\mathcal{F}_{\max}`, projecting through its underlying
`WithBot ℝ≥0∞`.

*Definition:* the _(min,plus)_ and _(max,plus)_ embeddings of a real curve

```lean
def embMin (g : ℝ≥0 → ℝ≥0) : Fmin :=
  fun t => ⟨(g t : ℝ≥0∞)⟩

def embMax (g : ℝ≥0 → ℝ≥0) : Fmax :=
  fun t => ⟨((g t : ℝ≥0∞) : WithBot ℝ≥0∞)⟩
```

Every split of `t` into $`u + s` is a nonempty set — the split
$`t + 0` — so the convolution's $`\inf` / $`\sup` is over a
nonempty index.

```lean
instance splitNonempty (t : ℝ≥0) :
    Nonempty {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} :=
  ⟨⟨(t, 0), by simp⟩⟩
```

# The (min,plus) convolution

The _(min,plus) convolution_ $`g \ast h` (the _infimal convolution_) is
the dioid product of the embedded curves, read back into
$`\mathbb{R}_{\ge 0}`. Because the
product on $`\overline{\mathbb{R}}_{\ge 0}` is numeric addition and the
dioid supremum is the numeric infimum, the convolution at `t` is finite
(the split $`t + 0` gives $`g(t) + h(0)`), so the projection is exact.

*Definition:* $`(g \ast h)(t) = \big((\mathrm{emb}\,g \ast \mathrm{emb}\,h)(t)\big)\!\downarrow_{\mathbb{R}_{\ge 0}}`

```lean
noncomputable def minConv (g h : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    (conv (embMin g) (embMin h) t
      : MinPlusNN).toVal.toNNReal
```

The underlying $`\mathbb{R}_{\ge 0}^{\infty}` value of the dioid product
is the sum of the embedded values.

*Theorem:* $`\uparrow(\mathrm{emb}\,g(u) \otimes \mathrm{emb}\,h(s)) = g(u) + h(s)`

```lean
theorem embMin_mul (g h : ℝ≥0 → ℝ≥0) (u s : ℝ≥0) :
    ((embMin g u ⊗ₒ embMin h s : MinPlusNN) : ℝ≥0∞)
      = (g u : ℝ≥0∞) + (h s : ℝ≥0∞) := rfl
```

The dioid convolution unfolds to the numeric infimum over the splits:
the dioid supremum is the numeric infimum, and the product $`\otimes` is
numeric $`+`.

*Theorem:* $`\uparrow(g \ast h)(t) = \inf_{u + s = t} (g(u) + h(s))` in $`\mathbb{R}_{\ge 0}^{\infty}`

```lean
theorem conv_embMin_toE (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    ((conv (embMin g) (embMin h) t : MinPlusNN) : ℝ≥0∞)
      = ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞) := by
  rw [conv_apply]
  show (⨅ x : {x : MinPlusNN //
        ∃ u s, u + s = t ∧ x = embMin g u ⊗ₒ embMin h s},
        (x.val : ℝ≥0∞)) = _
  apply le_antisymm
  · refine le_iInf (fun p => ?_)
    refine iInf_le_of_le
      ⟨embMin g p.1.1 ⊗ₒ embMin h p.1.2,
        p.1.1, p.1.2, p.2, rfl⟩ ?_
    show ((embMin g p.1.1 ⊗ₒ embMin h p.1.2 : MinPlusNN)
        : ℝ≥0∞) ≤ _
    rw [embMin_mul]; push_cast; rfl
  · refine le_iInf (fun x => ?_)
    obtain ⟨u, s, hus, hx⟩ := x.2
    refine iInf_le_of_le ⟨(u, s), hus⟩ ?_
    rw [show (x.val : ℝ≥0∞)
          = ((embMin g u ⊗ₒ embMin h s : MinPlusNN)
              : ℝ≥0∞) from congrArg _ hx, embMin_mul]
    push_cast; rfl
```

Projecting back, the (min,plus) convolution is the expected real
infimum.

*Theorem:* $`(g \ast h)(t) = \inf_{u + s = t} (g(u) + h(s))`

```lean
theorem minConv_eq (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    minConv g h t
      = ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          (g p.1.1 + h p.1.2) := by
  rw [minConv, conv_embMin_toE,
    ← ENNReal.coe_iInf
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        g p.1.1 + h p.1.2),
    ENNReal.toNNReal_coe]
```

The (min,plus) convolution is _isotone_ in each curve: raising a curve
raises the convolution.

*Theorem:* $`g \le g' \implies A \ast g \le A \ast g'`

```lean
theorem minConv_mono_right (A : ℝ≥0 → ℝ≥0)
    {g g' : ℝ≥0 → ℝ≥0} (h : g ≤ g') :
    minConv A g ≤ minConv A g' := by
  intro t
  rw [minConv_eq, minConv_eq]
  refine ciInf_mono (OrderBot.bddBelow _) (fun p => ?_)
  gcongr
  exact h p.1.2
```

# The (max,plus) convolution

The _(max,plus) convolution_ $`g \mathbin{\overline{\ast}} h`
is the dioid product of the two embedded curves, read back into
$`\mathbb{R}_{\ge 0}`. It is the supremal mirror of the (min,plus)
convolution, over the same splits; convolving a curve with itself,
$`g \mathbin{\overline{\ast}} g` (the _super-convolution_),
generates the super-additive closure.

*Definition:* $`(g \mathbin{\overline{\ast}} h)(t) = \big((\mathrm{emb}_{\max}g \ast \mathrm{emb}_{\max}h)(t)\big)\!\downarrow_{\mathbb{R}_{\ge 0}}`

```lean
noncomputable def maxConv (g h : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    (conv (embMax g) (embMax h) t
      : MaxPlusNN).toVal.unbotD 0 |>.toNNReal
```

The underlying value of the dioid product is the sum of the embedded
values.

*Theorem:* $`\uparrow(\mathrm{emb}_{\max}g(a) \otimes \mathrm{emb}_{\max}h(b)) = g(a) + h(b)`

```lean
theorem embMax_mul (g h : ℝ≥0 → ℝ≥0) (a b : ℝ≥0) :
    ((embMax g a ⊗ₒ embMax h b : MaxPlusNN)
        : WithBot ℝ≥0∞)
      = (((g a : ℝ≥0∞) : WithBot ℝ≥0∞))
        + (((h b : ℝ≥0∞) : WithBot ℝ≥0∞)) := rfl
```

The dioid convolution unfolds to the supremum of
$`g(a) + h(b)` over the splits.

*Theorem:* $`\uparrow(g \mathbin{\overline{\ast}} h)(t) = \bigsqcup_{a + b = t} (g(a) + h(b))` in `WithBot ℝ≥0∞`

```lean
theorem conv_embMax_toW (g h : ℝ≥0 → ℝ≥0)
    (t : ℝ≥0) :
    ((conv (embMax g) (embMax h) t : MaxPlusNN)
        : WithBot ℝ≥0∞)
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          (((g p.1.1 + h p.1.2 : ℝ≥0)
            : ℝ≥0∞) : WithBot ℝ≥0∞) := by
  rw [conv_apply]
  show (⨆ x : {x : MaxPlusNN //
        ∃ u s, u + s = t ∧
          x = embMax g u ⊗ₒ embMax h s},
        (x.val : WithBot ℝ≥0∞)) = _
  apply le_antisymm
  · refine iSup_le (fun x => ?_)
    obtain ⟨u, s, hus, hx⟩ := x.2
    refine le_iSup_of_le ⟨(u, s), hus⟩ ?_
    rw [show (x.val : WithBot ℝ≥0∞)
          = ((embMax g u ⊗ₒ embMax h s
                : MaxPlusNN) : WithBot ℝ≥0∞)
            from congrArg _ hx, embMax_mul]
    push_cast; rfl
  · refine iSup_le (fun p => ?_)
    refine le_iSup_of_le
      ⟨embMax g p.1.1 ⊗ₒ embMax h p.1.2,
        p.1.1, p.1.2, p.2, rfl⟩ ?_
    show _ ≤ ((embMax g p.1.1 ⊗ₒ embMax h p.1.2
        : MaxPlusNN) : WithBot ℝ≥0∞)
    rw [embMax_mul]; push_cast; rfl
```

Projecting back, the (max,plus) convolution is the expected real
supremum,
provided the values are bounded so the supremum is finite.

*Theorem:* $`\uparrow(g \mathbin{\overline{\ast}} h)(t) = \bigsqcup_{a + b = t} (g(a) + h(b))` when finite

```lean
theorem maxConv_coe (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0)
    (hfin : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞)) ≠ ⊤) :
    ((maxConv g h t : ℝ≥0) : ℝ≥0∞)
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞) := by
  have hcoe : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        (((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞)
          : WithBot ℝ≥0∞))
      = (((⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞))
          : ℝ≥0∞) : WithBot ℝ≥0∞) :=
    (WithBot.coe_iSup (OrderTop.bddAbove _)).symm
  rw [maxConv, conv_embMax_toW, hcoe]
  rw [WithBot.unbotD_coe, ENNReal.coe_toNNReal hfin]
```

The (max,plus) convolution obeys an _unconditional_ upper bound: if
every
split term is below `c`, so is the result. No finiteness is needed —
when the dioid supremum is $`+\infty` the projection floors to `0`,
which is below `c` anyway, and otherwise the bound is the genuine
supremum's. This is the bound the strict-service proofs use.

*Theorem:* $`(\forall a + b = t,\ g(a) + h(b) \le c) \implies (g \mathbin{\overline{\ast}} h)(t) \le c`

```lean
theorem maxConv_le (g h : ℝ≥0 → ℝ≥0) (t c : ℝ≥0)
    (hsplit : ∀ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      g p.1.1 + h p.1.2 ≤ c) :
    maxConv g h t ≤ c := by
  rw [maxConv, conv_embMax_toW]
  have hcoe :
      (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        (((g p.1.1 + h p.1.2 : ℝ≥0)
          : ℝ≥0∞) : WithBot ℝ≥0∞))
      = (((⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞))
          : ℝ≥0∞) : WithBot ℝ≥0∞) :=
    (WithBot.coe_iSup (OrderTop.bddAbove _)).symm
  rw [hcoe, WithBot.unbotD_coe]
  have hb : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞))
        ≤ (c : ℝ≥0∞) :=
    iSup_le (fun p => by exact_mod_cast hsplit p)
  have := ENNReal.toNNReal_mono (by simp) hb
  simpa using this
```

Adding a constant absorbs into that bound, exactly as the supremum
absorption lemma did for an explicit $`\bigsqcup`: this is the shape the
strict-service-curve proofs invoke, with `c` a departure value.

*Theorem:* $`(\forall a + b = t,\ c + g(a) + g(b) \le y) \implies c + (g \mathbin{\overline{\ast}} g)(t) \le y`

```lean
theorem add_maxConv_le
    (g : ℝ≥0 → ℝ≥0) (t c y : ℝ≥0)
    (h : ∀ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      c + (g p.1.1 + g p.1.2) ≤ y) :
    c + maxConv g g t ≤ y := by
  have hcy : c ≤ y :=
    le_trans le_self_add (h ⟨(t, 0), by simp⟩)
  have hsup : maxConv g g t ≤ y - c :=
    maxConv_le g g t (y - c)
      (fun p => le_tsub_of_add_le_left (h p))
  calc c + maxConv g g t ≤ c + (y - c) := by gcongr
    _ = y := add_tsub_cancel_of_le hcy
```

# The (max,plus) convolution as a conjugated (min,plus) convolution

The _(max,plus)_ computation is not a separate world: it is the
_(min,plus)_ convolution _conjugated by negation_. The
order-reversing involution $`x \mapsto -x` is the isomorphism between
the two dioids, turning $`\max` into $`\min` and a sum into the
negated sum. Concretely, over the reals,
$$`\sup_{a + b = t}\big(g(a) + g(b)\big) = -\inf_{a + b = t}\big((-g(a)) + (-g(b))\big),`
the right-hand infimum being a (min,plus) convolution of $`-g`. We
record this duality as one theorem; the standalone _(max,plus)_ dioid
is kept as the computational engine, while this lemma is the honest
statement of _why_ it is the right one. The supremal conjugation
$`\sup g = -\inf(-g)` holds for any family bounded above.

*Theorem:* $`\sup_i g(i) = -\inf_i (-g(i))` for a family bounded above

```lean
theorem neg_ciInf_neg {ι : Type} [Nonempty ι]
    (g : ι → ℝ) (hbdd : BddAbove (Set.range g)) :
    (⨆ i, g i) = - ⨅ i, - g i := by
  have hbb : BddBelow (Set.range (fun i => - g i)) := by
    obtain ⟨c, hc⟩ := hbdd
    exact ⟨-c, by
      rintro _ ⟨i, rfl⟩; simpa using hc ⟨i, rfl⟩⟩
  apply le_antisymm
  · refine ciSup_le (fun i => ?_)
    rw [le_neg]; exact ciInf_le_of_le hbb i (le_refl _)
  · rw [neg_le]; refine le_ciInf (fun i => ?_)
    rw [le_neg, neg_neg]; exact le_ciSup hbdd i
```

*Theorem:* $`(g \mathbin{\overline{\ast}} g)(t) = -\inf_{a + b = t} ((-g(a)) + (-g(b)))`, when finite

```lean
theorem maxConv_eq_neg_iInf
    (g : ℝ≥0 → ℝ≥0) (t : ℝ≥0)
    (hfin : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((g p.1.1 + g p.1.2 : ℝ≥0) : ℝ≥0∞))
        ≠ ⊤) :
    ((maxConv g g t : ℝ≥0) : ℝ)
      = - ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
            (- ((g p.1.1 : ℝ) + (g p.1.2 : ℝ))) := by
  have hsc : ((maxConv g g t : ℝ≥0) : ℝ≥0∞)
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + g p.1.2 : ℝ≥0) : ℝ≥0∞) :=
    maxConv_coe g g t hfin
  have hbN : BddAbove (Set.range
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        (g p.1.1 + g p.1.2 : ℝ≥0))) := by
    refine ⟨maxConv g g t, ?_⟩
    rintro _ ⟨p, rfl⟩
    have hle :
        ((g p.1.1 + g p.1.2 : ℝ≥0) : ℝ≥0∞)
        ≤ ((maxConv g g t : ℝ≥0) : ℝ≥0∞) := by
      rw [hsc]
      exact le_iSup
        (fun q : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
          ((g q.1.1 + g q.1.2 : ℝ≥0)
            : ℝ≥0∞)) p
    exact_mod_cast hle
  have hr : maxConv g g t
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          (g p.1.1 + g p.1.2) := by
    rw [← ENNReal.coe_iSup hbN] at hsc
    exact_mod_cast hsc
  have hbR : BddAbove (Set.range
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        ((g p.1.1 + g p.1.2 : ℝ≥0) : ℝ))) := by
    obtain ⟨c, hc⟩ := hbN
    refine ⟨(c : ℝ), ?_⟩
    rintro _ ⟨p, rfl⟩
    exact_mod_cast hc ⟨p, rfl⟩
  simp only [← NNReal.coe_add]
  rw [← neg_ciInf_neg _ hbR,
    show (((maxConv g g t : ℝ≥0)) : ℝ)
        = ((⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
            (g p.1.1 + g p.1.2) : ℝ≥0) : ℝ)
        from congrArg _ hr,
    NNReal.coe_iSup]
```

# The real convolutions bridge to the dioid-backed operators

The dioid-backed `minConv` / `maxConv` are _defined_ by computing in a
dioid and projecting back. The direct numeric operators `minConvR` /
`maxConvR` on $`\mathbb{R}_{\ge 0}` (collected at the start of the
chapter) are the same convolutions on their own terms; here we bridge
each to its dioid-backed counterpart.

The direct definition agrees with the dioid-backed `minConv`: this is
exactly `minConv_eq`, read as an equality of functions.

*Theorem:* $`g \ast h = \mathrm{minConv}(g, h)`

```lean
theorem minConvR_eq_minConv (g h : ℝ≥0 → ℝ≥0) :
    minConvR g h = minConv g h := by
  funext t
  rw [minConvR, minConv_eq]
```

When the supremum is finite, the direct `maxConvR` agrees with the
dioid-backed `maxConv`.

*Theorem:* $`g \mathbin{\overline{\ast}} h = \mathrm{maxConv}(g, h)` at $`t`, when finite

```lean
theorem maxConvR_eq_maxConv
    (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0)
    (hfin : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞))
        ≠ ⊤) :
    maxConvR g h t = maxConv g h t := by
  have hbdd : BddAbove (Set.range
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        g p.1.1 + h p.1.2)) := by
    by_contra hub
    exact hfin (ENNReal.iSup_coe_eq_top.mpr hub)
  have h : ((maxConvR g h t : ℝ≥0) : ℝ≥0∞)
      = ((maxConv g h t : ℝ≥0) : ℝ≥0∞) := by
    rw [maxConvR, ENNReal.coe_iSup hbdd,
      maxConv_coe _ _ _ hfin]
  exact_mod_cast h
```

```lean
end DeepWiki
```
