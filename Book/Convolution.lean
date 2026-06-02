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
open scoped Classical NNReal Algebra.Bridge
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
    exact ⟨s, u, by rw [add_comm]; exact hus, mul_comm _ _⟩
  · rintro ⟨u, s, hus, rfl⟩
    exact ⟨s, u, by rw [add_comm]; exact hus,
      mul_comm _ _⟩
```

# Properties of the convolution

The convolution is commutative, associative, and distributes over the
pointwise minimum; it also commutes with adding a constant. Together
these make $`(\mathcal{F}, \wedge, \ast)` a dioid in its own right — the
_function dioid_ — built on top of the scalar dioid
$`\overline{\mathbb{R}}_{\min}`. The proofs rest on a few facts about
the dioid sum as a join, which we record first.

The dioid sum is the binary _join_ for $`\preceq`: each summand is below
the sum, and the sum is the least common upper bound.

```lean
section Join
variable {T : Type*} [Algebra.CompleteDioid T]
open Algebra

theorem le_oplus_left (a b : T) : a ≼ₒ a ⊕ₒ b := by
  show a ⊕ₒ (a ⊕ₒ b) = a ⊕ₒ b
  rw [← add_assoc, Dioid.oplus_idem]

theorem le_oplus_right (a b : T) : b ≼ₒ a ⊕ₒ b := by
  show b ⊕ₒ (a ⊕ₒ b) = a ⊕ₒ b
  rw [add_comm a b,
    ← add_assoc, Dioid.oplus_idem]

theorem oplus_le (a b c : T)
    (ha : a ≼ₒ c) (hb : b ≼ₒ c) : a ⊕ₒ b ≼ₒ c := by
  show (a ⊕ₒ b) ⊕ₒ c = c
  rw [add_assoc]
  show a ⊕ₒ (b ⊕ₒ c) = c
  rw [(by exact hb : b ⊕ₒ c = c)]; exact ha

theorem oplus_le_oplus {a b c d : T}
    (h1 : a ≼ₒ c) (h2 : b ≼ₒ d) : a ⊕ₒ b ≼ₒ c ⊕ₒ d :=
  oplus_le _ _ _ (le_trans h1 (le_oplus_left c d))
    (le_trans h2 (le_oplus_right c d))

end Join

open Algebra
```

Distributivity of the convolution over the pointwise minimum, by the
distributivity of $`\otimes` over $`\oplus` in the scalar dioid.

*Theorem:* $`f \ast (g \wedge h) = (f \ast g) \wedge (f \ast h)`

```lean
theorem conv_distrib (f g h : F) :
    conv f (pmin g h) = pmin (conv f g) (conv f h) := by
  funext t
  apply le_antisymm
  · rw [conv_apply]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    have hd : f u ⊗ₒ (pmin g h s)
        = (f u ⊗ₒ g s) ⊕ₒ (f u ⊗ₒ h s) :=
      left_distrib (f u) (g s) (h s)
    show f u ⊗ₒ (pmin g h s) ≼ₒ _
    rw [hd]
    refine oplus_le_oplus ?_ ?_
    · exact conv_apply f g t ▸
        CompleteDioid.le_sSup _ _ ⟨u, s, hus, rfl⟩
    · exact conv_apply f h t ▸
        CompleteDioid.le_sSup _ _ ⟨u, s, hus, rfl⟩
  · refine oplus_le _ _ _ ?_ ?_
    · rw [conv_apply]
      refine CompleteDioid.sSup_le _ _ ?_
      rintro x ⟨u, s, hus, rfl⟩
      rw [conv_apply]
      refine le_trans ?_ (CompleteDioid.le_sSup _
        (f u ⊗ₒ (pmin g h s)) ⟨u, s, hus, rfl⟩)
      exact mul_le_mul_left (le_oplus_left _ _) _
    · rw [conv_apply]
      refine CompleteDioid.sSup_le _ _ ?_
      rintro x ⟨u, s, hus, rfl⟩
      rw [conv_apply]
      refine le_trans ?_ (CompleteDioid.le_sSup _
        (f u ⊗ₒ (pmin g h s)) ⟨u, s, hus, rfl⟩)
      exact mul_le_mul_left (le_oplus_right _ _) _
```

Associativity. Both $`(f \ast g) \ast h` and $`f \ast (g \ast h)` are
the dioid sum, over all triple decompositions $`u + v + z = t`, of the
product $`f(u) \otimes g(v) \otimes h(z)`; the two associations of that
product agree by associativity of $`\otimes`.

*Definition:* the triple-decomposition value

```lean
noncomputable def triple (f g h : F) (t : ℝ≥0) : RbarMin :=
  CompleteDioid.sSup
    { x | ∃ u v z : ℝ≥0,
        u + v + z = t ∧ x = (f u ⊗ₒ g v) ⊗ₒ h z }
```

*Theorem:* $`((f \ast g) \ast h)(t) = \bigsqcup_{u+v+z=t} f(u) \otimes g(v) \otimes h(z)`

```lean
theorem conv_conv_eq_triple (f g h : F) (t : ℝ≥0) :
    conv (conv f g) h t = triple f g h t := by
  apply le_antisymm
  · rw [conv_apply]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨w, z, hwz, rfl⟩
    rw [conv_apply, Algebra.sSup_mul]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro y ⟨q, ⟨u, v, huv, rfl⟩, rfl⟩
    refine CompleteDioid.le_sSup _ _ ⟨u, v, z, ?_, rfl⟩
    rw [huv]; exact hwz
  · rw [triple]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, v, z, hsum, rfl⟩
    rw [conv_apply]
    refine le_trans ?_ (CompleteDioid.le_sSup _
      ((conv f g (u+v)) ⊗ₒ h z) ⟨u+v, z, hsum, rfl⟩)
    refine mul_le_mul_right ?_ _
    rw [conv_apply]
    exact CompleteDioid.le_sSup _ _ ⟨u, v, rfl, rfl⟩
```

*Theorem:* $`(f \ast (g \ast h))(t) = \bigsqcup_{u+v+z=t} f(u) \otimes g(v) \otimes h(z)`

```lean
theorem conv_conv_eq_triple' (f g h : F) (t : ℝ≥0) :
    conv f (conv g h) t = triple f g h t := by
  apply le_antisymm
  · rw [conv_apply]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, p, hup, rfl⟩
    rw [conv_apply, CompleteDioid.mul_sSup]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro y ⟨q, ⟨v, z, hvz, rfl⟩, rfl⟩
    refine CompleteDioid.le_sSup _ _ ⟨u, v, z, ?_, ?_⟩
    · rw [add_assoc, hvz]; exact hup
    · exact (mul_assoc (f u) (g v) (h z)).symm
  · rw [triple]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, v, z, hsum, rfl⟩
    rw [conv_apply]
    refine le_trans ?_ (CompleteDioid.le_sSup _
      (f u ⊗ₒ (conv g h (v+z)))
      ⟨u, v+z, by rw [← add_assoc]; exact hsum, rfl⟩)
    rw [mul_assoc]
    refine mul_le_mul_left ?_ _
    rw [conv_apply]
    exact CompleteDioid.le_sSup _ _ ⟨v, z, rfl, rfl⟩
```

*Theorem:* $`(f \ast g) \ast h = f \ast (g \ast h)`

```lean
theorem conv_assoc (f g h : F) :
    conv (conv f g) h = conv f (conv g h) := by
  funext t
  rw [conv_conv_eq_triple, conv_conv_eq_triple']
```

Addition by a constant. Adding a constant $`K` pointwise is, in the
scalar dioid, multiplying by $`K` (numeric addition is the dioid
product $`\otimes`); it slides through the convolution.

*Definition:* $`(f + K)(t) = f(t) \otimes K`

```lean
def addConst (f : F) (K : RbarMin) : F :=
  fun t => f t ⊗ₒ K
```

*Theorem:* $`(f \ast g) + K = f \ast (g + K)`

```lean
theorem conv_add_const (f g : F) (K : RbarMin) :
    addConst (conv f g) K = conv f (addConst g K) := by
  funext t
  show (conv f g t) ⊗ₒ K = _
  rw [conv_apply, conv_apply, Algebra.sSup_mul]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨u, s, hus, rfl⟩, rfl⟩
    exact ⟨u, s, hus, by
      show (f u ⊗ₒ g s) ⊗ₒ K = f u ⊗ₒ (addConst g K s)
      rw [show addConst g K s = g s ⊗ₒ K from rfl,
        mul_assoc]⟩
  · rintro ⟨u, s, hus, rfl⟩
    refine ⟨f u ⊗ₒ g s, ⟨u, s, hus, rfl⟩, ?_⟩
    show (f u ⊗ₒ g s) ⊗ₒ K = f u ⊗ₒ (addConst g K s)
    rw [show addConst g K s = g s ⊗ₒ K from rfl,
      mul_assoc]
```

With commutativity, associativity, distributivity over the minimum,
and the constant-shift law all established, $`(\mathcal{F}, \wedge,
\ast)` carries the full (min,plus) dioid structure inherited from
$`\overline{\mathbb{R}}_{\min}`.

```lean
end NetworkCalculus
```
