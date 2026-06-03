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

# Subsets of the function class

Network calculus restricts to four subsets of real functions, defined
by _natural-order_ conditions on the values (non-negativity, nullity at
the origin, non-decrease). We state them as predicates on
$`\mathbb{R}^{+} \to \mathbb{R} \cup \{\pm\infty\}`.

$`\mathcal{F}^{+}` is the non-negative functions.

*Definition:* $`f \in \mathcal{F}^{+} \iff \forall t,\ 0 \le f(t)`

```lean
def isFPlus (f : ℝ≥0 → WithTop (WithBot ℝ)) : Prop :=
  ∀ t, 0 ≤ f t
```

$`\mathcal{F}_0` is the non-negative functions null at the origin.

*Definition:* $`f \in \mathcal{F}_0 \iff f \in \mathcal{F}^{+} \land f(0) = 0`

```lean
def isF0 (f : ℝ≥0 → WithTop (WithBot ℝ)) : Prop :=
  isFPlus f ∧ f 0 = 0
```

$`\mathcal{F}^{\uparrow}` is the non-negative, non-decreasing functions.

*Definition:* $`f \in \mathcal{F}^{\uparrow} \iff f \in \mathcal{F}^{+} \land (\forall x \le y,\ f(x) \le f(y))`

```lean
def isFNondecr (f : ℝ≥0 → WithTop (WithBot ℝ)) : Prop :=
  isFPlus f ∧ ∀ x y, x ≤ y → f x ≤ f y
```

$`\mathcal{F}_0^{\uparrow}` is their intersection: non-negative,
non-decreasing, null at the origin.

*Definition:* $`\mathcal{F}_0^{\uparrow} = \mathcal{F}_0 \cap \mathcal{F}^{\uparrow}`

```lean
def isF0Nondecr (f : ℝ≥0 → WithTop (WithBot ℝ)) : Prop :=
  isF0 f ∧ isFNondecr f
```

## Stability under the minimum

The pointwise minimum of two functions of each class stays in that
class: the bound $`0 \le \cdot`, nullity at the origin, and
monotonicity all pass through `min`.

*Theorem:* $`\mathcal{F}^{+}` is stable under $`\min`

```lean
theorem isFPlus.min {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : isFPlus f) (hg : isFPlus g) :
    isFPlus (fun t => min (f t) (g t)) :=
  fun t => le_min (hf t) (hg t)
```

*Theorem:* $`\mathcal{F}_0` is stable under $`\min`

```lean
theorem isF0.min {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : isF0 f) (hg : isF0 g) :
    isF0 (fun t => min (f t) (g t)) :=
  ⟨hf.1.min hg.1, by
    show Min.min (f 0) (g 0) = 0
    rw [hf.2, hg.2, min_self]⟩
```

*Theorem:* $`\mathcal{F}^{\uparrow}` is stable under $`\min`

```lean
theorem isFNondecr.min
    {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : isFNondecr f) (hg : isFNondecr g) :
    isFNondecr (fun t => min (f t) (g t)) :=
  ⟨hf.1.min hg.1, fun x y hxy =>
    min_le_min (hf.2 x y hxy) (hg.2 x y hxy)⟩
```

*Theorem:* $`\mathcal{F}_0^{\uparrow}` is stable under $`\min`

```lean
theorem isF0Nondecr.min
    {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : isF0Nondecr f) (hg : isF0Nondecr g) :
    isF0Nondecr (fun t => min (f t) (g t)) :=
  ⟨hf.1.min hg.1, hf.2.min hg.2⟩
```

## Stability under the convolution

The same classes are stable under the (min,plus) convolution
`minConvBar`. Non-negativity passes through because every split-sum
$`f(u) + g(s)` is non-negative, hence so is their infimum. Nullity at
the origin holds because the only split of $`0` is $`0 + 0`.
Monotonicity is the inf-convolution of non-decreasing functions: a
split of the larger argument is reduced to a split of the smaller one
by lowering one coordinate.

*Theorem:* $`\mathcal{F}^{+}` is stable under the convolution

```lean
theorem isFPlus.conv
    {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : isFPlus f) (hg : isFPlus g) :
    isFPlus (minConvBar f g) := by
  intro t
  rw [minConvBar]
  refine le_iInf ?_
  rintro ⟨⟨u, s⟩, _⟩
  calc (0 : WithTop (WithBot ℝ)) = 0 + 0 := by simp
    _ ≤ f u + g s := by gcongr; exacts [hf u, hg s]
```

*Theorem:* $`\mathcal{F}_0` is stable under the convolution

```lean
theorem isF0.conv
    {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : isF0 f) (hg : isF0 g) :
    isF0 (minConvBar f g) :=
  ⟨hf.1.conv hg.1, by
    rw [minConvBar]
    apply le_antisymm
    · exact iInf_le_of_le ⟨(0, 0), by simp⟩ (by
        simp [hf.2, hg.2])
    · refine le_iInf ?_
      rintro ⟨⟨u, s⟩, (hus : u + s = 0)⟩
      obtain ⟨rfl, rfl⟩ := add_eq_zero.mp hus
      simp [hf.2, hg.2]⟩
```

The monotonicity of the convolution: pushing a split of $`y` down to a
split of $`x \le y` by lowering the first coordinate to $`\min(u, x)`.

*Theorem:* $`f, g` non-decreasing $`\implies f \ast g` non-decreasing

```lean
theorem minConvBar_mono
    {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : ∀ x y, x ≤ y → f x ≤ f y)
    (hg : ∀ x y, x ≤ y → g x ≤ g y)
    {x y : ℝ≥0} (hxy : x ≤ y) :
    minConvBar f g x ≤ minConvBar f g y := by
  rw [minConvBar, minConvBar]
  refine le_iInf ?_
  rintro ⟨⟨u, s⟩, (hus : u + s = y)⟩
  refine iInf_le_of_le ⟨(min u x, x - min u x), by
    rw [add_tsub_cancel_of_le (min_le_right u x)]⟩ ?_
  have hs : x - min u x ≤ s := by
    rw [tsub_le_iff_right]
    rcases le_total u x with h | h
    · rw [min_eq_left h, add_comm, hus]; exact hxy
    · rw [min_eq_right h]; exact le_add_self
  gcongr
  · exact hf _ _ (min_le_left u x)
  · exact hg _ _ hs
```

*Theorem:* $`\mathcal{F}^{\uparrow}` is stable under the convolution

```lean
theorem isFNondecr.conv
    {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : isFNondecr f) (hg : isFNondecr g) :
    isFNondecr (minConvBar f g) :=
  ⟨hf.1.conv hg.1,
    fun _ _ hxy => minConvBar_mono hf.2 hg.2 hxy⟩
```

*Theorem:* $`\mathcal{F}_0^{\uparrow}` is stable under the convolution

```lean
theorem isF0Nondecr.conv
    {f g : ℝ≥0 → WithTop (WithBot ℝ)}
    (hf : isF0Nondecr f) (hg : isF0Nondecr g) :
    isF0Nondecr (minConvBar f g) :=
  ⟨hf.1.conv hg.1, hf.2.conv hg.2⟩
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

We read the predicates onto $`\mathcal{F}` through the `RbarMin`
wrapper, and record two bridges: $`\mathcal{F}` is the lift of its own
underlying values, and the dioid product unwraps to `minConvBar`.

```lean
def isFPlusF (f : FminBar) : Prop :=
  isFPlus (fun t => (f t).toB)

def isFNondecrF (f : FminBar) : Prop :=
  isFNondecr (fun t => (f t).toB)

theorem coe_toB (a : FminBar) :
    (↑(fun t => (a t).toB) : FminBar) = a := by
  funext t; apply RbarMin.ext; rfl

theorem mul_toB (a b : FminBar) (t : ℝ≥0) :
    ((a ⊗ₒ b) t).toB
      = minConvBar (fun t => (a t).toB)
          (fun t => (b t).toB) t := by
  show ((conv a b t : RbarMin) : WithTop (WithBot ℝ)) = _
  rw [← coe_toB a, ← coe_toB b]
  exact conv_coe_toB _ _ t
```

The unit (impulse) and zero (constant $`+\infty`) are non-negative and
non-decreasing; with the stability lemmas this gives the five closure
conditions.

*Definition:* $`\mathcal{F}^{+}` is a sub-complete-dioid

```lean
theorem isSubCompleteDioid_isFPlusF :
    IsSubCompleteDioid isFPlusF where
  add ha hb := fun t => le_min (ha t) (hb t)
  mul {a b} ha hb := fun t => by
    show (0 : WithTop (WithBot ℝ)) ≤ ((a ⊗ₒ b) t).toB
    rw [mul_toB]; exact (isFPlus.conv ha hb) t
  eps := fun _ => le_top
  one := fun t => by
    show (0 : WithTop (WithBot ℝ))
        ≤ ((convUnit t : RbarMin)).toB
    rcases eq_or_ne t 0 with h | h
    · rw [convUnit, if_pos h]; exact le_rfl
    · rw [convUnit, if_neg h]; exact le_top
  iSup F hF := fun t => le_iInf (fun i => hF i t)
```

*Definition:* $`\mathcal{F}^{\uparrow}` is a sub-complete-dioid

```lean
theorem isSubCompleteDioid_isFNondecrF :
    IsSubCompleteDioid isFNondecrF where
  add ha hb :=
    ⟨fun t => le_min (ha.1 t) (hb.1 t),
      fun x y hxy =>
        min_le_min (ha.2 x y hxy) (hb.2 x y hxy)⟩
  mul {a b} ha hb := by
    have h : isFNondecr
        (minConvBar (fun t => (a t).toB)
          (fun t => (b t).toB)) := isFNondecr.conv ha hb
    refine ⟨fun t => ?_, fun x y hxy => ?_⟩
    · show (0 : WithTop (WithBot ℝ)) ≤ ((a ⊗ₒ b) t).toB
      rw [mul_toB]; exact h.1 t
    · show ((a ⊗ₒ b) x).toB ≤ ((a ⊗ₒ b) y).toB
      rw [mul_toB, mul_toB]; exact h.2 x y hxy
  eps := ⟨fun _ => le_top, fun _ _ _ => le_top⟩
  one := by
    refine ⟨fun t => ?_, fun x y hxy => ?_⟩
    · show (0 : WithTop (WithBot ℝ))
          ≤ ((convUnit t : RbarMin)).toB
      rcases eq_or_ne t 0 with h | h
      · rw [convUnit, if_pos h]; exact le_rfl
      · rw [convUnit, if_neg h]; exact le_top
    · show ((convUnit x : RbarMin)).toB
          ≤ ((convUnit y : RbarMin)).toB
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
noncomputable instance :
    CompleteDioid {f : FminBar // isFPlusF f} :=
  isSubCompleteDioid_isFPlusF.toCompleteDioid

noncomputable instance :
    CompleteDioid {f : FminBar // isFNondecrF f} :=
  isSubCompleteDioid_isFNondecrF.toCompleteDioid
```

By contrast $`\mathcal{F}_0` and $`\mathcal{F}_0^{\uparrow}` are _not_
dioids: the closure condition `eps` would require the dioid zero
$`\varepsilon = +\infty` (the constant function) to be null at the
origin, but $`+\infty \ne 0`. The sub-complete-dioid builder does not
apply, faithfully reflecting that these sets lack the neutral.

```lean
end VerifiedWiki
```
