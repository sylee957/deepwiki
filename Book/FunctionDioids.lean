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
convolution operators `minConvProj` / `maxConvProj` are read back from the
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

We define the _direct_ convolution operators on numeric functions — a
numeric infimum or supremum over the splits $`u + s = t`, with no
recourse to a dioid. The key observation is that every such operator
has the _same shape_: aggregate the codomain sum $`f(u) + g(s)` over
all splits $`u + s = t` of the argument. They differ only in the
codomain $`T` and in whether the aggregation is an infimum or a
supremum. We therefore define the shape _once_, generic over an
arbitrary domain with an addition (to form the splits) and a codomain
carrying both an addition (to combine the two values) and an infimum —
and dually a supremum.

Specialising the codomain then recovers each concrete convolution: the
domain is always the cumulative-curve time axis $`\mathbb{R}_{\ge 0}`,
and the codomain ranges over the scalar carriers — the extended reals
$`\mathbb{R} \cup \{\pm\infty\}`, the non-negative reals
$`\mathbb{R}_{\ge 0}`, and the extended non-negative reals
$`\overline{\mathbb{R}}_{\ge 0}` (`ℝ≥0∞`). No separate definition is
needed per carrier: a theorem about, say, the $`\overline{\mathbb{R}}_{\ge 0}`
convolution simply types its arguments as $`g, h : \mathbb{R}^{+} \to
\overline{\mathbb{R}}_{\ge 0}`, and `minConv g h` _is_ that operator.

*Definition:* the _(min,plus) convolution_ $`(f \ast g)(t) = \inf_{u + s = t}\,(f(u) + g(s))` over any codomain with $`\inf`

```lean
noncomputable def minConv
    {D T : Type*} [Add D] [Add T] [InfSet T]
    (f g : D → T) : D → T :=
  fun t =>
    ⨅ p : {p : D × D // p.1 + p.2 = t},
      f p.1.1 + g p.1.2
```

*Definition:* the _(max,plus) convolution_ $`(f \mathbin{\overline{\ast}} g)(t) = \sup_{u + s = t}\,(f(u) + g(s))` over any codomain with $`\sup`

```lean
noncomputable def maxConv
    {D T : Type*} [Add D] [Add T] [SupSet T]
    (f g : D → T) : D → T :=
  fun t =>
    ⨆ p : {p : D × D // p.1 + p.2 = t},
      f p.1.1 + g p.1.2
```

A caveat for the (max,plus) supremum over the _non-negative reals_
$`\mathbb{R}_{\ge 0}`: an unbounded supremum is not finite there, so the
direct `maxConv` floors to $`0`; the dioid-backed `maxConvProj` defined
later is the canonical operator over that carrier, and the two agree
wherever the supremum is finite.

The _deconvolution_ (the dual quotient) has its own generic shape: a
supremum, over all forward shifts $`s`, of the codomain _difference_
$`g(t + s) - h(s)`. It abstracts over a domain with an addition (to form
the shift) and a codomain carrying a subtraction and a supremum.

*Definition:* the _deconvolution_ $`(g \oslash h)(t) = \sup_{s}\,(g(t + s) - h(s))` over any codomain with $`-` and $`\sup`

```lean
noncomputable def deconv
    {D T : Type*} [Add D] [Sub T] [SupSet T]
    (g h : D → T) : D → T :=
  fun t => ⨆ s : D, g (t + s) - h s
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
      = minConv f g t := by
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
      = (↑(minConv f g) : FminBar) := by
  funext t
  apply MinPlusExt.ext
  exact conv_coe_min f g t
```

# The dual (max,plus) convolution

The construction dualizes verbatim to the _(max,plus)_ side, on the
same extended reals but through the order-dual carrier `MaxPlusExt`
(`WithBot (WithTop ℝ)`). The _(max,plus) convolution_ is `maxConv`
at this carrier — the numeric _supremum_ over the splits; the function
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
      = maxConv f g t := by
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
theorem conv_coe_max'
    (f g : ℝ≥0 → WithBot (WithTop ℝ)) :
    conv (↑f : FmaxBar) (↑g : FmaxBar)
      = (↑(maxConv f g) : FmaxBar) := by
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
it by conjunction. Non-decrease is just `Monotone`, so we reuse it
directly; the other two atoms are named here, generic over the domain
and codomain (the curves are valued in the scalar carriers, but the
properties need only a zero and an order).

*Definition:* $`f` is non-negative: $`\forall t,\ 0 \le f(t)`

```lean
def IsNonneg {D T : Type*} [Zero T] [LE T]
    (f : D → T) : Prop :=
  ∀ t, 0 ≤ f t
```

*Definition:* $`f` is null at the origin: $`f(0) = 0`

```lean
def IsNullAtOrigin {D T : Type*} [Zero D] [Zero T]
    (f : D → T) : Prop :=
  f 0 = 0
```

The third atom, _non-decrease_ — $`x \le y \implies f(x) \le f(y)` —
is exactly `Monotone f`, so we use the library predicate rather than
naming our own. The two coincide _definitionally_, not merely
logically — unfolding `Monotone` gives back the implication verbatim,
so the equivalence holds by `Iff.rfl`.

*Example:* `Monotone` _is_ the non-decrease atom

```lean
example {α β : Type*} [Preorder α] [Preorder β]
    (f : α → β) :
    Monotone f ↔ ∀ x y, x ≤ y → f x ≤ f y :=
  Iff.rfl
```

The textbook classes are conjunctions of these atoms:
$`\mathcal{F}^{+}` is `IsNonneg`; $`\mathcal{F}_0` is
`IsNonneg ∧ IsNullAtOrigin`; $`\mathcal{F}^{\uparrow}` is
`IsNonneg ∧ Monotone`; and $`\mathcal{F}_0^{\uparrow}` is all three.

## Stability under the minimum

Each atomic property passes through the pointwise minimum; a class,
being a conjunction of atoms, then inherits stability by conjunction.

*Theorem:* non-negativity is stable under $`\min`

```lean
theorem IsNonneg.min {D T : Type*} [LinearOrder T]
    [Zero T] {f g : D → T}
    (hf : IsNonneg f) (hg : IsNonneg g) :
    IsNonneg (fun t => min (f t) (g t)) :=
  fun t => le_min (hf t) (hg t)
```

*Theorem:* nullity at the origin is stable under $`\min`

```lean
theorem IsNullAtOrigin.min {D T : Type*} [Zero D]
    [LinearOrder T] [Zero T] {f g : D → T}
    (hf : IsNullAtOrigin f) (hg : IsNullAtOrigin g) :
    IsNullAtOrigin (fun t => min (f t) (g t)) := by
  show Min.min (f 0) (g 0) = 0
  rw [hf, hg, min_self]
```

For non-decrease there is nothing new to prove: the pointwise minimum
of two monotone functions is monotone, by the library's `Monotone.min`.

*Example:* non-decrease is stable under $`\min`

```lean
example {α β : Type*} [Preorder α] [LinearOrder β]
    {f g : α → β} (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun t => min (f t) (g t)) :=
  hf.min hg
```

## Stability under the pointwise sum

The classes are also closed under the ordinary _pointwise numeric
sum_ $`(f + g)(t) = f(t) + g(t)`. This is the top-absorbing addition
of $`\overline{\mathbb{R}}`, _not_ the dioid sum $`\oplus` (which is
the minimum); it plays no part in the sub-dioid builder below, but
$`\mathcal{F}^{\uparrow}` is stable under it all the same. Both atoms
pass through: a sum of non-negative values is non-negative, and the
sum of two non-decreasing functions is non-decreasing — the latter by
the library's `Monotone.add`.

*Theorem:* non-negativity is stable under the pointwise sum

```lean
theorem IsNonneg.add {D T : Type*}
    [_root_.AddCommMonoid T] [PartialOrder T]
    [IsOrderedAddMonoid T] {f g : D → T}
    (hf : IsNonneg f) (hg : IsNonneg g) :
    IsNonneg (fun t => f t + g t) := by
  intro t
  calc (0 : T) = 0 + 0 := by simp
    _ ≤ f t + g t := by gcongr; exacts [hf t, hg t]
```

*Example:* non-decrease is stable under the pointwise sum

```lean
example {α β : Type*} [Preorder α]
    [_root_.AddCommMonoid β] [PartialOrder β]
    [IsOrderedAddMonoid β]
    {f g : α → β} (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun t => f t + g t) :=
  hf.add hg
```

## Stability under the convolution

Each atom is likewise stable under the (min,plus) convolution
`minConv`. Non-negativity passes through because every split-sum
$`f(u) + g(s)` is non-negative, hence so is their infimum. Nullity at
the origin holds because the only split of $`0` is $`0 + 0`.

*Theorem:* non-negativity is stable under the convolution

```lean
theorem IsNonneg.conv {D T : Type*} [Add D]
    [_root_.AddCommMonoid T] [CompleteLattice T]
    [IsOrderedAddMonoid T] {f g : D → T}
    (hf : IsNonneg f) (hg : IsNonneg g) :
    IsNonneg (minConv f g) := by
  intro t
  simp only [minConv]
  refine le_iInf ?_
  rintro ⟨⟨u, s⟩, _⟩
  calc (0 : T) = 0 + 0 := by simp
    _ ≤ f u + g s := by gcongr; exacts [hf u, hg s]
```

*Theorem:* nullity at the origin is stable under the convolution

```lean
theorem IsNullAtOrigin.conv {D T : Type*}
    [_root_.AddCommMonoid D] [PartialOrder D]
    [CanonicallyOrderedAdd D]
    [_root_.AddZeroClass T] [CompleteLattice T]
    {f g : D → T}
    (hf : IsNullAtOrigin f) (hg : IsNullAtOrigin g) :
    IsNullAtOrigin (minConv f g) := by
  show minConv f g 0 = 0
  simp only [minConv]
  apply le_antisymm
  · exact iInf_le_of_le ⟨(0, 0), by simp⟩ (by
      simp [IsNullAtOrigin] at hf hg; simp [hf, hg])
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, (hus : u + s = 0)⟩
    obtain ⟨rfl, rfl⟩ := add_eq_zero.mp hus
    simp [IsNullAtOrigin] at hf hg; simp [hf, hg]
```

Non-decrease is the inf-convolution of non-decreasing functions: a
split of the larger argument is reduced to a split of the smaller one
by lowering the first coordinate to $`\min(u, x)`.

*Theorem:* non-decrease is stable under the convolution

```lean
theorem monotone_minConv {D T : Type*}
    [_root_.AddCommMonoid D] [LinearOrder D]
    [CanonicallyOrderedAdd D] [Sub D] [OrderedSub D]
    [_root_.AddCommMonoid T] [CompleteLattice T]
    [IsOrderedAddMonoid T] {f g : D → T}
    (hf : Monotone f) (hg : Monotone g) :
    Monotone (minConv f g) := by
  intro x y hxy
  simp only [minConv]
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
  · exact hf (min_le_left u x)
  · exact hg hs
```

# The non-decreasing closure

A function need not be non-decreasing, but it has a canonical
_non-decreasing closure_ $`f^{\uparrow}`: the least non-decreasing
function lying above $`f`. Its value at $`t` is the supremum of $`f`
over the whole initial segment up to $`t` — running the supremum over
all earlier arguments forces monotonicity while keeping the function
as low as possible. The segment is the order-ideal $`\{s : s \le t\}`.

This construction is _agnostic to both ends_: the domain need only be
an ordered type with a least element $`\bot` (so the initial segments
are nonempty), and the values need only live in a lattice where the
supremum over each segment exists. We develop it once, generically,
over any preorder-with-bottom domain and conditionally-complete-lattice
codomain, then read it on the carriers the book uses — the extended
reals here, and $`\mathbb{R}_{\ge 0}` (with domain $`\mathbb{R}^{+}`)
in the chapter on real curves. The closure indexes the supremum by the
order-ideal $`\{s : s \le t\}`, written as a subtype; that subtype is
always inhabited (it contains $`\bot`), so the supremum is over a
nonempty set.

*Definition:* $`\bot \in \{s : s \le t\}`, so the index is nonempty

```lean
instance subLeNonempty {D : Type*} [Preorder D]
    [OrderBot D] (t : D) :
    Nonempty {s : D // s ≤ t} :=
  ⟨⟨⊥, bot_le⟩⟩
```

*Definition:* $`f^{\uparrow}(t) = \sup_{s \le t} f(s)`, over any domain $`D` and codomain $`T`

```lean
noncomputable def ndClosure {D T : Type*}
    [Preorder D] [OrderBot D]
    [ConditionallyCompleteLattice T]
    (f : D → T) : D → T :=
  fun t => ⨆ s : {s : D // s ≤ t}, f s
```

Over a merely _conditionally_-complete lattice the supremum is genuine
only when the values are bounded on each initial segment. We name that
hypothesis; on a _complete_ lattice (such as the extended reals below)
it holds for free.

*Definition:* $`f` is bounded above on each initial segment

```lean
def ClosureBddAbove {D T : Type*} [Preorder D]
    [Preorder T] (f : D → T) : Prop :=
  ∀ t, BddAbove
    (Set.range (fun s : {s : D // s ≤ t} => f s))
```

The closure dominates the original function: $`t` itself lies in its
own initial segment, so $`f(t)` is one of the values entering the
supremum, hence below it (the bound keeps the supremum genuine).

*Theorem:* $`f \le f^{\uparrow}`

```lean
theorem le_ndClosure {D T : Type*}
    [Preorder D] [OrderBot D]
    [ConditionallyCompleteLattice T] (f : D → T)
    (hbdd : ClosureBddAbove f) (t : D) :
    f t ≤ ndClosure f t := by
  unfold ndClosure
  exact le_ciSup (hbdd t)
    (⟨t, le_refl t⟩ : {s // s ≤ t})
```

The closure is non-decreasing: a larger argument $`y \ge x` has a
wider initial segment, so its supremum can only grow. Each value
$`f(s)` from the smaller segment ($`s \le x \le y`) already appears
among those of the larger, hence sits below the larger supremum.

*Theorem:* $`f^{\uparrow}` is non-decreasing

```lean
theorem ndClosure_mono {D T : Type*}
    [Preorder D] [OrderBot D]
    [ConditionallyCompleteLattice T] (f : D → T)
    (hbdd : ClosureBddAbove f) :
    Monotone (ndClosure f) := by
  intro x y hxy
  unfold ndClosure
  refine ciSup_le (fun s => ?_)
  exact le_ciSup (hbdd y) ⟨s.1, s.2.trans hxy⟩
```

The closure is the _least_ such function: any non-decreasing $`g`
above $`f` already dominates it. For each $`s \le t` we have
$`f(s) \le g(s) \le g(t)` — the first step because $`g \ge f`, the
second because $`g` is non-decreasing — so $`g(t)` is an upper bound
of the values defining $`f^{\uparrow}(t)`, whence
$`f^{\uparrow}(t) \le g(t)`. (No boundedness is needed here: $`g(t)`
itself is the witnessing bound.)

*Theorem:* $`g` non-decreasing, $`g \ge f \implies g \ge f^{\uparrow}`

```lean
theorem ndClosure_le {D T : Type*}
    [Preorder D] [OrderBot D]
    [ConditionallyCompleteLattice T]
    {f g : D → T} (hg : Monotone g)
    (hfg : ∀ t, f t ≤ g t) (t : D) :
    ndClosure f t ≤ g t := by
  unfold ndClosure
  refine ciSup_le (fun s => ?_)
  exact (hfg s.1).trans (hg s.2)
```

On the _extended reals_ $`\mathbb{R} \cup \{\pm\infty\}` the lattice is
_complete_, so the boundedness hypothesis is vacuous and the closure
is unconditional. We read the generic construction there as $`f^{\uparrow}`.

*Definition:* the non-decreasing closure $`f^{\uparrow}` on $`\overline{\mathbb{R}}`

```lean
noncomputable abbrev fUp
    (f : ℝ≥0 → WithTop (WithBot ℝ)) :
    ℝ≥0 → WithTop (WithBot ℝ) :=
  ndClosure f
```

On a complete lattice every set is bounded above, so the boundedness
hypothesis is discharged once and reused.

*Theorem:* on $`\overline{\mathbb{R}}` the closure is unconditionally bounded

```lean
theorem fUp_bdd (f : ℝ≥0 → WithTop (WithBot ℝ)) :
    ClosureBddAbove f :=
  fun t => OrderTop.bddAbove _
```

*Theorem:* $`f \le f^{\uparrow}`

```lean
theorem le_fUp (f : ℝ≥0 → WithTop (WithBot ℝ))
    (t : ℝ≥0) : f t ≤ fUp f t :=
  le_ndClosure f (fUp_bdd f) t
```

*Theorem:* $`f^{\uparrow}` is non-decreasing

```lean
theorem monotone_fUp
    (f : ℝ≥0 → WithTop (WithBot ℝ)) :
    Monotone (fUp f) :=
  fun _ _ hxy => ndClosure_mono f (fUp_bdd f) hxy
```

*Theorem:* $`g \in \mathcal{F}^{\uparrow},\ g \ge f \implies g \ge f^{\uparrow}`

```lean
theorem fUp_le {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hg : Monotone g) (hfg : ∀ t, f t ≤ g t)
    (t : ℝ≥0) : fUp f t ≤ g t :=
  ndClosure_le hg hfg t
```

When $`f` is itself non-negative, the closure stays non-negative —
$`0 \le f(t) \le f^{\uparrow}(t)` — so a curve of $`\mathcal{F}^{+}`
has its closure back in $`\mathcal{F}^{\uparrow}`.

*Theorem:* $`f \in \mathcal{F}^{+} \implies f^{\uparrow} \in \mathcal{F}^{+}`

```lean
theorem fUp_isNonneg
    {f : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : IsNonneg f) : IsNonneg (fUp f) :=
  fun t => (hf t).trans (le_fUp f t)
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
underlying values, and the dioid product unwraps to `minConv`.

The classes are the subtypes of $`\mathcal{F}` cut out directly by the
atoms: $`\mathcal{F}^{+}` by non-negativity alone, and
$`\mathcal{F}^{\uparrow}` by the _conjunction_ of non-negativity and
monotonicity — written inline as the carving predicate, no named
composite.

*Definition:* $`\mathcal{F}^{+}` and $`\mathcal{F}^{\uparrow}` as subtypes

```lean
abbrev FPlus :=
  {f : FminBar // IsNonneg (fun t => (f t).toVal)}

abbrev FNondecr :=
  {f : FminBar //
    IsNonneg (fun t => (f t).toVal)
      ∧ Monotone (fun t => (f t).toVal)}
```

```lean
theorem coe_toVal (a : FminBar) :
    (↑(fun t => (a t).toVal) : FminBar) = a := by
  funext t; apply MinPlusExt.ext; rfl

theorem mul_toVal (a b : FminBar) (t : ℝ≥0) :
    ((a ⊗ₒ b) t).toVal
      = minConv (fun t => (a t).toVal)
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
      (fun f : FminBar => IsNonneg (fun t => (f t).toVal))
      where
  add ha hb := fun t => le_min (ha t) (hb t)
  mul {a b} ha hb := fun t => by
    show (0 : WithTop (WithBot ℝ)) ≤ ((a ⊗ₒ b) t).toVal
    rw [mul_toVal]; exact (IsNonneg.conv ha hb) t
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
        IsNonneg (fun t => (f t).toVal)
          ∧ Monotone (fun t => (f t).toVal))
      where
  add ha hb :=
    ⟨fun t => le_min (ha.1 t) (hb.1 t),
      fun _ _ hxy =>
        min_le_min (ha.2 hxy) (hb.2 hxy)⟩
  mul {a b} ha hb := by
    have hn := IsNonneg.conv ha.1 hb.1
    have hm := monotone_minConv ha.2 hb.2
    refine ⟨fun t => ?_, fun _ _ hxy => ?_⟩
    · show (0 : WithTop (WithBot ℝ)) ≤ ((a ⊗ₒ b) t).toVal
      rw [mul_toVal]; exact hn t
    · show ((a ⊗ₒ b) _).toVal ≤ ((a ⊗ₒ b) _).toVal
      rw [mul_toVal, mul_toVal]; exact hm hxy
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
      fun _ _ hxy =>
        le_iInf (fun i =>
          (iInf_le _ i).trans ((hF i).2 hxy))⟩
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
noncomputable def minConvProj (g h : ℝ≥0 → ℝ≥0) :
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
theorem minConvProj_eq (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    minConvProj g h t
      = ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          (g p.1.1 + h p.1.2) := by
  rw [minConvProj, conv_embMin_toE,
    ← ENNReal.coe_iInf
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        g p.1.1 + h p.1.2),
    ENNReal.toNNReal_coe]
```

The (min,plus) convolution is _isotone_ in each curve: raising a curve
raises the convolution.

*Theorem:* $`g \le g' \implies A \ast g \le A \ast g'`

```lean
theorem minConvProj_mono_right (A : ℝ≥0 → ℝ≥0)
    {g g' : ℝ≥0 → ℝ≥0} (h : g ≤ g') :
    minConvProj A g ≤ minConvProj A g' := by
  intro t
  rw [minConvProj_eq, minConvProj_eq]
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
noncomputable def maxConvProj (g h : ℝ≥0 → ℝ≥0) :
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
theorem maxConvProj_coe (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0)
    (hfin : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞)) ≠ ⊤) :
    ((maxConvProj g h t : ℝ≥0) : ℝ≥0∞)
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞) := by
  have hcoe : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        (((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞)
          : WithBot ℝ≥0∞))
      = (((⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞))
          : ℝ≥0∞) : WithBot ℝ≥0∞) :=
    (WithBot.coe_iSup (OrderTop.bddAbove _)).symm
  rw [maxConvProj, conv_embMax_toW, hcoe]
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
theorem maxConvProj_le (g h : ℝ≥0 → ℝ≥0) (t c : ℝ≥0)
    (hsplit : ∀ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      g p.1.1 + h p.1.2 ≤ c) :
    maxConvProj g h t ≤ c := by
  rw [maxConvProj, conv_embMax_toW]
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
theorem add_maxConvProj_le
    (g : ℝ≥0 → ℝ≥0) (t c y : ℝ≥0)
    (h : ∀ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      c + (g p.1.1 + g p.1.2) ≤ y) :
    c + maxConvProj g g t ≤ y := by
  have hcy : c ≤ y :=
    le_trans le_self_add (h ⟨(t, 0), by simp⟩)
  have hsup : maxConvProj g g t ≤ y - c :=
    maxConvProj_le g g t (y - c)
      (fun p => le_tsub_of_add_le_left (h p))
  calc c + maxConvProj g g t ≤ c + (y - c) := by gcongr
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
theorem maxConvProj_eq_neg_iInf
    (g : ℝ≥0 → ℝ≥0) (t : ℝ≥0)
    (hfin : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((g p.1.1 + g p.1.2 : ℝ≥0) : ℝ≥0∞))
        ≠ ⊤) :
    ((maxConvProj g g t : ℝ≥0) : ℝ)
      = - ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
            (- ((g p.1.1 : ℝ) + (g p.1.2 : ℝ))) := by
  have hsc : ((maxConvProj g g t : ℝ≥0) : ℝ≥0∞)
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + g p.1.2 : ℝ≥0) : ℝ≥0∞) :=
    maxConvProj_coe g g t hfin
  have hbN : BddAbove (Set.range
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        (g p.1.1 + g p.1.2 : ℝ≥0))) := by
    refine ⟨maxConvProj g g t, ?_⟩
    rintro _ ⟨p, rfl⟩
    have hle :
        ((g p.1.1 + g p.1.2 : ℝ≥0) : ℝ≥0∞)
        ≤ ((maxConvProj g g t : ℝ≥0) : ℝ≥0∞) := by
      rw [hsc]
      exact le_iSup
        (fun q : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
          ((g q.1.1 + g q.1.2 : ℝ≥0)
            : ℝ≥0∞)) p
    exact_mod_cast hle
  have hr : maxConvProj g g t
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
    show (((maxConvProj g g t : ℝ≥0)) : ℝ)
        = ((⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
            (g p.1.1 + g p.1.2) : ℝ≥0) : ℝ)
        from congrArg _ hr,
    NNReal.coe_iSup]
```

# The real convolutions bridge to the dioid-backed operators

The dioid-backed `minConvProj` / `maxConvProj` are _defined_ by computing in a
dioid and projecting back. The direct numeric operators `minConv` /
`maxConv` on $`\mathbb{R}_{\ge 0}` are the same convolutions on their
own terms; here we bridge each to its dioid-backed counterpart.

The direct definition agrees with the dioid-backed `minConvProj`: this is
exactly `minConvProj_eq`, read as an equality of functions.

*Theorem:* $`g \ast h = \mathrm{minConvProj}(g, h)`

```lean
theorem minConv_eq_minConvProj (g h : ℝ≥0 → ℝ≥0) :
    minConv g h = minConvProj g h := by
  funext t
  rw [minConv, minConvProj_eq]
```

When the supremum is finite, the direct `maxConv` agrees with the
dioid-backed `maxConvProj`.

*Theorem:* $`g \mathbin{\overline{\ast}} h = \mathrm{maxConvProj}(g, h)` at $`t`, when finite

```lean
theorem maxConv_eq_maxConvProj
    (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0)
    (hfin : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞))
        ≠ ⊤) :
    maxConv g h t = maxConvProj g h t := by
  have hbdd : BddAbove (Set.range
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        g p.1.1 + h p.1.2)) := by
    by_contra hub
    exact hfin (ENNReal.iSup_coe_eq_top.mpr hub)
  have h : ((maxConv g h t : ℝ≥0) : ℝ≥0∞)
      = ((maxConvProj g h t : ℝ≥0) : ℝ≥0∞) := by
    rw [maxConv, ENNReal.coe_iSup hbdd,
      maxConvProj_coe _ _ _ hfin]
  exact_mod_cast h
```

```lean
end DeepWiki
```
