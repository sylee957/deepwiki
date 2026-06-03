import VersoManual
import Book.Scalars

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The (min,plus) convolution and the function dioid" =>
The functions of network calculus map the non-negative reals into a
complete (min,plus) dioid. For cumulative functions, the concrete
carrier is $`\overline{\mathbb{R}}_{\ge 0}`: ordinary non-negative
functions embed into this carrier, while $`+\infty` supplies the
neutral needed by the min-plus sum. The sum is the pointwise minimum,
and the product is the _(min,plus) convolution_, the adaptation of the
classical convolution $`\int_x f(x)\,g(t-x)\,dx` to the $`(\min, +)`
setting. This chapter defines both and records the basic facts about
the convolution.

```lean
namespace NetworkCalculus

open Algebra
open scoped Classical NNReal Algebra.Bridge
```

# The function dioid

A function dioid maps the non-negative reals $`\mathbb{R}^{+}` into
some complete dioid. We work over the bare function type
$`\mathbb{R}^{+} \to T` directly, equipping it with the convolution
algebra below rather than wrapping it in a name. The concrete min-plus
functions used in this book are the specialization to
$`\overline{\mathbb{R}}_{\ge 0}` (`RplusMin`), written $`\mathcal{F}`.

*Definition:* the concrete function space $`\mathcal{F} = \mathbb{R}^{+} \to \overline{\mathbb{R}}_{\ge 0}`

```lean
abbrev F := ℝ≥0 → RplusMin
```

The dioid sum is the _pointwise minimum_: the functions inherit
$`\oplus = \wedge` from $`\overline{\mathbb{R}}_{\ge 0}` pointwise.

*Definition:* $`(f \wedge g)(t) = f(t) \oplus g(t)`

```lean
def pmin {T : Type*} [CompleteDioid T]
    (f g : ℝ≥0 → T) : ℝ≥0 → T :=
  fun t => f t ⊕ₒ g t
```

# The convolution

The _(min,plus) convolution_ $`f \ast g` is the dioid product on
$`\mathcal{F}`. Its value at $`t` is the dioid sum — the infimum, since
the order is reversed — over all ways of splitting $`t` into a sum
$`u + s`, of the product $`f(u) \otimes g(s)`:
$$`(f \ast g)(t) = \bigwedge_{u + s = t} f(u) \otimes g(s).`
We take the dioid supremum $`\bigsqcup` over the set of these products;
on $`\overline{\mathbb{R}}_{\ge 0}` that supremum is exactly the numeric
infimum.

*Definition:* $`(f \ast g)(t) = \bigsqcup\,\{\, f(u) \otimes g(s) \mid u + s = t \,\}`

```lean
noncomputable def conv {T : Type*}
    [CompleteDioid T]
    (f g : ℝ≥0 → T) : ℝ≥0 → T := fun t =>
  CompleteDioid.sSup
    { x | ∃ u s : ℝ≥0, u + s = t ∧ x = f u ⊗ₒ g s }

theorem conv_apply {T : Type*} [CompleteDioid T]
    (f g : ℝ≥0 → T) (t : ℝ≥0) :
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
theorem conv_eq_sub {T : Type*} [CompleteDioid T]
    (f g : ℝ≥0 → T) (t : ℝ≥0) :
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

Because the product $`\otimes` on $`\overline{\mathbb{R}}_{\ge 0}` is
commutative and the decomposition $`u + s = t` is symmetric under
swapping the two parts, the convolution is commutative.

*Theorem:* $`f \ast g = g \ast f`

```lean
theorem conv_comm {T : Type*} [CompleteDioid T]
    (f g : ℝ≥0 → T) : conv f g = conv g f := by
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
$`\overline{\mathbb{R}}_{\ge 0}`. The proofs rest on a few facts about
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
theorem conv_distrib {T : Type*} [CompleteDioid T]
    (f g h : ℝ≥0 → T) :
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
noncomputable def triple {T : Type*} [CompleteDioid T]
    (f g h : ℝ≥0 → T) (t : ℝ≥0) : T :=
  CompleteDioid.sSup
    { x | ∃ u v z : ℝ≥0,
        u + v + z = t ∧ x = (f u ⊗ₒ g v) ⊗ₒ h z }
```

*Theorem:* $`((f \ast g) \ast h)(t) = \bigsqcup_{u+v+z=t} f(u) \otimes g(v) \otimes h(z)`

```lean
theorem conv_conv_eq_triple {T : Type*}
    [CompleteDioid T]
    (f g h : ℝ≥0 → T) (t : ℝ≥0) :
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
theorem conv_conv_eq_triple' {T : Type*}
    [CompleteDioid T]
    (f g h : ℝ≥0 → T) (t : ℝ≥0) :
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
theorem conv_assoc {T : Type*} [CompleteDioid T]
    (f g h : ℝ≥0 → T) :
    conv (conv f g) h = conv f (conv g h) := by
  funext t
  rw [conv_conv_eq_triple, conv_conv_eq_triple']
```

Addition by a constant. Adding a constant $`K` pointwise is, in the
scalar dioid, multiplying by $`K` (numeric addition is the dioid
product $`\otimes`); it slides through the convolution.

*Definition:* $`(f + K)(t) = f(t) \otimes K`

```lean
def addConst {T : Type*} [CompleteDioid T]
    (f : ℝ≥0 → T) (K : T) : ℝ≥0 → T :=
  fun t => f t ⊗ₒ K
```

*Theorem:* $`(f \ast g) + K = f \ast (g + K)`

```lean
theorem conv_add_const {T : Type*}
    [CompleteDioid T]
    (f g : ℝ≥0 → T) (K : T) :
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

# The function dioid instance

The lemmas above are the dioid laws for the convolution; assembling
them — together with the pointwise structure of the sum — exhibits the
function space $`\mathcal{F}` as a complete dioid in its own right. We
build that instance explicitly: a function type carries a stray
pointwise product from `Mathlib`, and the dioid product must instead be
the convolution.

The dioid sum is the pointwise minimum `pmin`; its laws are those of
$`T` applied at each point. The unit for the sum is the constant
$`\varepsilon` function.

*Definition:* the sum-neutral $`\varepsilon_{\mathcal{F}}(t) = \varepsilon`

```lean
def convZero {T : Type*} [CompleteDioid T] :
    ℝ≥0 → T := fun _ => εₒ
```

The unit for the convolution is the _impulse_: $`e` at time $`0`, and
$`\varepsilon` elsewhere.

*Definition:* the convolution unit $`\delta_0(t) = e` if $`t = 0`, else $`\varepsilon`

```lean
noncomputable def convUnit {T : Type*}
    [CompleteDioid T] : ℝ≥0 → T :=
  fun t => if t = 0 then eₒ else εₒ
```

The impulse is a two-sided identity for the convolution. The left
identity is proved directly from the definition; the right identity
follows by commutativity.

*Theorem:* $`\delta_0 \ast f = f` and $`f \ast \delta_0 = f`

```lean
theorem convUnit_left {T : Type*} [CompleteDioid T]
    (f : ℝ≥0 → T) : conv convUnit f = f := by
  funext t
  apply le_antisymm
  · rw [conv_apply]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    by_cases hu : u = 0
    · have hs : s = t := by
        rw [← hus, hu, zero_add]
      rw [convUnit, if_pos hu, hs]
      exact le_of_eq (MulMonoid.one_otimes (f t))
    · rw [convUnit, if_neg hu, Semiring.eps_otimes]
      exact bot_le
  · rw [conv_apply]
    refine CompleteDioid.le_sSup _ _
      ⟨0, t, by rw [zero_add], ?_⟩
    rw [convUnit, if_pos rfl]
    exact (MulMonoid.one_otimes (f t)).symm

theorem convUnit_right {T : Type*} [CompleteDioid T]
    (f : ℝ≥0 → T) : conv f convUnit = f := by
  rw [conv_comm, convUnit_left]
```

Convolving with the constant $`\varepsilon` collapses to $`\varepsilon`,
since $`\varepsilon` is absorbing for $`\otimes` and least for
$`\preceq`.

*Theorem:* $`\varepsilon_{\mathcal{F}} \ast f = \varepsilon_{\mathcal{F}}` and $`f \ast \varepsilon_{\mathcal{F}} = \varepsilon_{\mathcal{F}}`

```lean
theorem convZero_left {T : Type*} [CompleteDioid T]
    (f : ℝ≥0 → T) :
    conv convZero f = convZero := by
  funext t
  apply le_antisymm
  · rw [conv_apply]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    rw [show convZero u = εₒ from rfl,
      Semiring.eps_otimes]
    exact bot_le
  · exact bot_le

theorem convZero_right {T : Type*} [CompleteDioid T]
    (f : ℝ≥0 → T) :
    conv f convZero = convZero := by
  rw [conv_comm, convZero_left]
```

Right-distributivity is the mirror of `conv_distrib`, obtained by
commuting the convolution.

*Theorem:* $`(g \wedge h) \ast f = (g \ast f) \wedge (h \ast f)`

```lean
theorem conv_distrib_right {T : Type*}
    [CompleteDioid T] (f g h : ℝ≥0 → T) :
    conv (pmin g h) f = pmin (conv g f) (conv h f) := by
  rw [conv_comm, conv_distrib, conv_comm g f,
    conv_comm h f]
```

The pointwise supremum of a family of functions inherits the
least-upper-bound and lower-semi-continuity laws from $`T` pointwise.

*Definition:* $`\bigl(\bigsqcup_i f_i\bigr)(t) = \bigsqcup_i f_i(t)`

```lean
noncomputable def funSup {T : Type u}
    [CompleteDioid T] {ι : Type u}
    (F : ι → ℝ≥0 → T) : ℝ≥0 → T :=
  fun t => CompleteDioid.iSup (fun i => F i t)
```

Assembling the convolution laws with the pointwise sum and supremum
gives the instance. The sum, product, and unit are `pmin`, `conv`, and
the impulse; the dioid laws are the theorems above, applied pointwise
where the structure is pointwise.

*Definition:* $`(\mathcal{F}, \wedge, \ast)` is an `Algebra.CompleteDioid`

```lean
noncomputable instance funCompleteDioid
    {T : Type u} [CompleteDioid T] :
    CompleteDioid (ℝ≥0 → T) where
  add := pmin
  zero := convZero
  mul := conv
  one := convUnit
  oplus_assoc f g h := funext fun t => add_assoc _ _ _
  eps_oplus f := funext fun t => zero_add _
  oplus_eps f := funext fun t => add_zero _
  oplus_comm f g := funext fun t => add_comm _ _
  otimes_assoc := conv_assoc
  one_otimes := convUnit_left
  otimes_one := convUnit_right
  left_distrib := conv_distrib
  right_distrib f g h := conv_distrib_right h f g
  eps_otimes := convZero_left
  otimes_eps := convZero_right
  otimes_comm := conv_comm
  oplus_idem f := funext fun t => Dioid.oplus_idem _
  iSup := funSup
  le_iSup F i :=
    funext fun t => CompleteDioid.le_iSup (fun j => F j t) i
  iSup_le F b hb :=
    funext fun t =>
      CompleteDioid.iSup_le (fun i => F i t) (b t)
        (fun i => congrFun (hb i) t)
  mul_iSup a F := by
    funext t
    show conv a (funSup F) t
        = funSup (fun i => conv a (F i)) t
    rw [conv_apply]
    apply le_antisymm
    · refine CompleteDioid.sSup_le _ _ ?_
      rintro x ⟨u, s, hus, rfl⟩
      show a u ⊗ₒ funSup F s ≼ₒ _
      rw [show funSup F s
          = CompleteDioid.iSup (fun i => F i s) from rfl,
        CompleteDioid.mul_iSup]
      refine CompleteDioid.iSup_le _ _ ?_
      intro i
      refine le_trans ?_
        (CompleteDioid.le_iSup
          (fun i => conv a (F i) t) i)
      rw [conv_apply]
      exact CompleteDioid.le_sSup _ _ ⟨u, s, hus, rfl⟩
    · refine CompleteDioid.iSup_le _ _ ?_
      intro i
      show conv a (F i) t ≼ₒ _
      rw [conv_apply]
      refine CompleteDioid.sSup_le _ _ ?_
      rintro x ⟨u, s, hus, rfl⟩
      refine le_trans ?_
        (CompleteDioid.le_sSup _ _ ⟨u, s, hus, rfl⟩)
      show a u ⊗ₒ F i s ≼ₒ a u ⊗ₒ funSup F s
      rw [show funSup F s
          = CompleteDioid.iSup (fun i => F i s) from rfl]
      exact mul_le_mul_left
        (CompleteDioid.le_iSup (fun i => F i s) i) _
```

Now that the convolution is the dioid product, its _isotony_ is just
the isotony of the product over the dioid order $`\preceq`: raising
either factor raises the convolution. No special argument is needed —
it is `mul_le_mul_left` / `mul_le_mul_right` read through `conv`.

*Theorem:* $`g \preceq g' \implies f \ast g \preceq f \ast g'` and $`f \preceq f' \implies f \ast g \preceq f' \ast g`

```lean
theorem conv_le_conv_right {T : Type*}
    [CompleteDioid T] (f : ℝ≥0 → T)
    {g g' : ℝ≥0 → T} (h : g ≼ₒ g') :
    conv f g ≼ₒ conv f g' :=
  mul_le_mul_left h f

theorem conv_le_conv_left {T : Type*}
    [CompleteDioid T] {f f' : ℝ≥0 → T}
    (h : f ≼ₒ f') (g : ℝ≥0 → T) :
    conv f g ≼ₒ conv f' g :=
  mul_le_mul_right h g
```

```lean
end NetworkCalculus
```
