import VersoManual
import Book.Scalars

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The (min,plus) convolution and the function dioid" =>
The functions of network calculus map the non-negative reals into the
complete (min,plus) dioid $`\overline{\mathbb{R}}_{\min}`. They inherit
their algebra from that dioid: the sum is the pointwise minimum, and the
product is the _(min,plus) convolution_, the adaptation of the classical
convolution $`\int_x f(x)\,g(t-x)\,dx` to the $`(\min, +)` setting. This
chapter defines both and records the basic facts about the convolution.

```lean
namespace NetworkCalculus

open Algebra
open scoped Classical NNReal
```

# The (min,plus) functions

A _(min,plus) function_ maps the non-negative reals $`\mathbb{R}^{+}`
into the complete dioid $`\overline{\mathbb{R}}_{\min}` (`RbarMin`). The
set of them is written $`\mathcal{F}`.

*Definition:* $`\mathcal{F} = \{\, f : \mathbb{R}^{+} \to \overline{\mathbb{R}}_{\min} \,\}`

```lean
abbrev F := ℝ≥0 → RbarMin
```

The dioid sum is the _pointwise minimum_: the functions inherit
$`\oplus = \wedge` from $`\overline{\mathbb{R}}_{\min}` pointwise.

*Definition:* $`(f \wedge g)(t) = f(t) \oplus g(t)`

```lean
def pmin (f g : F) : F := fun t => f t ⊕ₒ g t
```

# The convolution

The _(min,plus) convolution_ $`f \ast g` is the dioid product on
$`\mathcal{F}`. Its value at $`t` is the dioid sum — the infimum, since
the order is reversed — over all ways of splitting $`t` into a sum
$`u + s`, of the product $`f(u) \otimes g(s)`:
$$`(f \ast g)(t) = \bigwedge_{u + s = t} f(u) \otimes g(s).`
We take the dioid supremum $`\bigsqcup` over the set of these products;
on $`\overline{\mathbb{R}}_{\min}` that supremum is exactly the numeric
infimum.

*Definition:* $`(f \ast g)(t) = \bigsqcup\,\{\, f(u) \otimes g(s) \mid u + s = t \,\}`

```lean
noncomputable def conv (f g : F) : F := fun t =>
  CompleteDioid.sSup
    { x | ∃ u s : ℝ≥0, u + s = t ∧ x = f u ⊗ₒ g s }

theorem conv_apply (f g : F) (t : ℝ≥0) :
    conv f g t
      = CompleteDioid.sSup
          { x | ∃ u s, u + s = t ∧ x = f u ⊗ₒ g s } :=
  rfl
```

# Two forms of the convolution

The decomposition $`u + s = t` of a non-negative real is the same as a
single $`s \le t` with $`u = t - s`. So the convolution has the
equivalent _single-variable_ form
$$`(f \ast g)(t) = \bigwedge_{0 \le s \le t} f(t - s) \otimes g(s).`

*Theorem:* $`(f \ast g)(t) = \bigsqcup\,\{\, f(t - s) \otimes g(s) \mid s \le t \,\}`

```lean
theorem conv_eq_sub (f g : F) (t : ℝ≥0) :
    conv f g t
      = CompleteDioid.sSup
          { x | ∃ s : ℝ≥0,
              s ≤ t ∧ x = f (t - s) ⊗ₒ g s } := by
  show CompleteDioid.sSup _ = CompleteDioid.sSup _
  congr 1
  ext x
  constructor
  · rintro ⟨u, s, hus, rfl⟩
    refine ⟨s, ?_, ?_⟩
    · rw [← hus]; exact le_add_self
    · rw [show t - s = u by rw [← hus]; simp]
  · rintro ⟨s, hst, rfl⟩
    refine ⟨t - s, s, ?_, rfl⟩
    rw [tsub_add_cancel_of_le hst]
```

# Commutativity

Because the product $`\otimes` on $`\overline{\mathbb{R}}_{\min}` is
commutative and the decomposition $`u + s = t` is symmetric under
swapping the two parts, the convolution is commutative.

*Theorem:* $`f \ast g = g \ast f`

```lean
theorem conv_comm (f g : F) : conv f g = conv g f := by
  funext t
  show CompleteDioid.sSup _ = CompleteDioid.sSup _
  congr 1
  ext x
  constructor
  · rintro ⟨u, s, hus, rfl⟩
    exact ⟨s, u, by rw [add_comm]; exact hus,
      CommSemiring.otimes_comm _ _⟩
  · rintro ⟨u, s, hus, rfl⟩
    exact ⟨s, u, by rw [add_comm]; exact hus,
      CommSemiring.otimes_comm _ _⟩
```

These are the defining facts of the (min,plus) convolution. Its
associativity, the distributivity over the pointwise minimum, and the
neutral element together make $`(\mathcal{F}, \wedge, \ast)` a dioid in
its own right — the _function dioid_ — built on top of the scalar
dioid $`\overline{\mathbb{R}}_{\min}`.

```lean
end NetworkCalculus
```
