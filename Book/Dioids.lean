import VersoManual
import Mathlib.Algebra.Order.Kleene
import Mathlib.Order.CompleteLattice.Lemmas

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Dioids and complete dioids" =>
This chapter formalizes the algebra of _dioids_, the _canonical order_
they induce, the order properties and isotony, and the _complete dioid_
that adds completeness and lower semi-continuity.

All declarations live in the `NetworkCalculus` namespace.

```lean
namespace NetworkCalculus

open scoped Computability
-- `add_eq_sup : a + b = a ⊔ b`
```

# A dioid, defined from scratch

The tower below is a self-contained illustration: each layer is a
_bundled structure_ over a carrier $`T`, carrying the operations and
axioms as fields, with each layer extending the previous one. There is
no type-class resolution and hence no inheritance diamond — a value of
a layer is passed explicitly. The interface the rest of the book
actually builds on is `IdemDioid`, defined afterwards.

*Definition:* a _sum signature_ on a carrier $`T` is a binary
$`\oplus : T \times T \to T` with a neutral $`\varepsilon`.

```lean
namespace Algebra

structure Oplus (T : Type*) where
  oplus : T → T → T
  eps : T
```

*Definition:* a _product signature_ on $`T` is a binary
$`\otimes : T \times T \to T` with a neutral $`e`.

```lean
structure Otimes (T : Type*) extends Oplus T where
  otimes : T → T → T
  one : T
```

*Definition:* $`(T, \oplus, \varepsilon)` is a _monoid_:
$$`(a \oplus b) \oplus c = a \oplus (b \oplus c), \quad \varepsilon \oplus a = a, \quad a \oplus \varepsilon = a.`

```lean
structure AddMonoid (T : Type*) extends Oplus T where
  oplus_assoc : ∀ a b c,
    oplus (oplus a b) c = oplus a (oplus b c)
  eps_oplus : ∀ a, oplus eps a = a
  oplus_eps : ∀ a, oplus a eps = a
```

*Definition:* a _commutative_ monoid adds $`a \oplus b = b \oplus a`.

```lean
structure AddCommMonoid (T : Type*) extends
    AddMonoid T where
  oplus_comm : ∀ a b, oplus a b = oplus b a
```

*Definition:* $`(T, \otimes, e)` is a _monoid_:
$$`(a \otimes b) \otimes c = a \otimes (b \otimes c), \quad e \otimes a = a, \quad a \otimes e = a.`

```lean
structure MulMonoid (T : Type*) extends Otimes T where
  otimes_assoc : ∀ a b c,
    otimes (otimes a b) c = otimes a (otimes b c)
  one_otimes : ∀ a, otimes one a = a
  otimes_one : ∀ a, otimes a one = a
```

*Definition:* a _semi-ring_ is a commutative $`\oplus`-monoid and a $`\otimes`-monoid with
$$`a \otimes (b \oplus c) = (a \otimes b) \oplus (a \otimes c), \quad (a \oplus b) \otimes c = (a \otimes c) \oplus (b \otimes c),`
$$`\varepsilon \otimes a = \varepsilon, \quad a \otimes \varepsilon = \varepsilon.`

```lean
structure Semiring (T : Type*) extends
    AddCommMonoid T, MulMonoid T where
  left_distrib : ∀ a b c,
    otimes a (oplus b c) = oplus (otimes a b) (otimes a c)
  right_distrib : ∀ a b c,
    otimes (oplus a b) c = oplus (otimes a c) (otimes b c)
  eps_otimes : ∀ a, otimes eps a = eps
  otimes_eps : ∀ a, otimes a eps = eps
```

For readability we attach tagged infixes to a semi-ring: in a semi-ring
$`R` on $`T`, write `a +[R] b` for $`a \oplus b` and `a *[R] b` for
$`a \otimes b`. The tag records which semi-ring's operation is meant,
since the operation is a field of the value $`R` rather than resolved
by type class.

```lean
abbrev Semiring.add {T : Type*} (R : Semiring T)
    (a b : T) : T := R.oplus a b
abbrev Semiring.mul {T : Type*} (R : Semiring T)
    (a b : T) : T := R.otimes a b

notation:65 a:65 " +[" R "] " b:66 => Semiring.add R a b
notation:70 a:70 " *[" R "] " b:71 => Semiring.mul R a b
```

*Definition:* a _commutative semi-ring_ adds $`a \otimes b = b \otimes a`.

```lean
structure CommSemiring (T : Type*) extends
    Semiring T where
  otimes_comm : ∀ a b, otimes a b = otimes b a
```

*Definition:* a _dioid_ is a commutative semi-ring whose sum is idempotent, $`a \oplus a = a`.

```lean
structure Dioid (T : Type*) extends
    CommSemiring T where
  oplus_idem : ∀ a, oplus a a = a
```

*Theorem:* $`(a \oplus b) \otimes (c \oplus d) = (a \otimes c) \oplus (b \otimes c) \oplus (a \otimes d) \oplus (b \otimes d)`

```lean
theorem quaternary_distrib {T : Type*} (R : Semiring T)
    (a b c d : T) :
    (a +[R] b) *[R] (c +[R] d)
      = a *[R] c +[R] b *[R] c
        +[R] a *[R] d +[R] b *[R] d := by
  simp only [Semiring.add, Semiring.mul]
  have hexp :
      R.otimes (R.oplus a b) (R.oplus c d)
        = R.oplus (R.oplus (R.otimes a c) (R.otimes a d))
            (R.oplus (R.otimes b c) (R.otimes b d)) := by
    rw [R.right_distrib, R.left_distrib, R.left_distrib]
  rw [hexp]
  set p := R.otimes a c; set q := R.otimes b c
  set r := R.otimes a d; set s := R.otimes b d
  rw [R.oplus_assoc p q r, R.oplus_assoc p (R.oplus q r) s,
    R.oplus_assoc p r (R.oplus q s)]
  congr 1
  rw [R.oplus_comm q r, R.oplus_assoc r q s]
```

## The canonical order on a dioid

Every dioid carries a _canonical order_ read off from its sum: $`a` is
below $`b` exactly when adding $`a` to $`b` changes nothing. We write it
`a ≼[R] b`, tagged by the dioid $`R` whose order is meant.

*Definition:* $`a \preceq b \iff a \oplus b = b`

```lean
def Dioid.le {T : Type*} (R : Dioid T) (a b : T) :
    Prop := R.oplus a b = b

notation:50 a:50 " ≼[" R "] " b:51 => Dioid.le R a b
```

Reflexivity is exactly idempotency of the sum: $`a \oplus a = a`.

*Theorem:* $`a \preceq a`

```lean
theorem Dioid.le_refl {T : Type*} (R : Dioid T)
    (a : T) : a ≼[R] a :=
  R.oplus_idem a
```

Transitivity uses associativity to merge the two witnessing equations.

*Theorem:* $`a \preceq b \;\wedge\; b \preceq c \;\Rightarrow\; a \preceq c`

```lean
theorem Dioid.le_trans {T : Type*} (R : Dioid T)
    {a b c : T} (hab : a ≼[R] b) (hbc : b ≼[R] c) :
    a ≼[R] c := by
  show R.oplus a c = c
  calc R.oplus a c
      = R.oplus a (R.oplus b c) := by rw [hbc]
    _ = R.oplus (R.oplus a b) c := by
        rw [R.oplus_assoc]
    _ = R.oplus b c := by rw [hab]
    _ = c := hbc
```

Antisymmetry uses commutativity: the two equations exhibit $`a` and
$`b` as the same sum.

*Theorem:* $`a \preceq b \;\wedge\; b \preceq a \;\Rightarrow\; a = b`

```lean
theorem Dioid.le_antisymm {T : Type*} (R : Dioid T)
    {a b : T} (hab : a ≼[R] b) (hba : b ≼[R] a) :
    a = b := by
  have h1 : R.oplus a b = b := hab
  have h2 : R.oplus b a = a := hba
  rw [← h1, R.oplus_comm, h2]
```

The sum is _isotone_ in each argument: a smaller summand gives a
smaller sum.

*Theorem:* $`a \preceq b \;\Rightarrow\; a \oplus c \preceq b \oplus c`

```lean
theorem Dioid.add_le_add_right {T : Type*}
    (R : Dioid T) {a b : T} (h : a ≼[R] b) (c : T) :
    (R.oplus a c) ≼[R] (R.oplus b c) := by
  show R.oplus (R.oplus a c) (R.oplus b c)
    = R.oplus b c
  calc R.oplus (R.oplus a c) (R.oplus b c)
      = R.oplus (R.oplus a b) (R.oplus c c) := by
        rw [R.oplus_assoc, ← R.oplus_assoc c b c,
          R.oplus_comm c b, R.oplus_assoc b c c,
          ← R.oplus_assoc a b (R.oplus c c)]
    _ = R.oplus b c := by rw [h, R.oplus_idem]
```

*Theorem:* $`a \preceq b \;\Rightarrow\; c \oplus a \preceq c \oplus b`

```lean
theorem Dioid.add_le_add_left {T : Type*}
    (R : Dioid T) {a b : T} (h : a ≼[R] b) (c : T) :
    (R.oplus c a) ≼[R] (R.oplus c b) := by
  rw [R.oplus_comm c a, R.oplus_comm c b]
  exact Dioid.add_le_add_right R h c
```

The product is isotone in each argument, by distributivity.

*Theorem:* $`a \preceq b \;\Rightarrow\; a \otimes c \preceq b \otimes c`

```lean
theorem Dioid.mul_le_mul_right {T : Type*}
    (R : Dioid T) {a b : T} (h : a ≼[R] b) (c : T) :
    (R.otimes a c) ≼[R] (R.otimes b c) := by
  show R.oplus (R.otimes a c) (R.otimes b c)
    = R.otimes b c
  rw [← R.right_distrib, h]
```

*Theorem:* $`a \preceq b \;\Rightarrow\; c \otimes a \preceq c \otimes b`

```lean
theorem Dioid.mul_le_mul_left {T : Type*}
    (R : Dioid T) {a b : T} (h : a ≼[R] b) (c : T) :
    (R.otimes c a) ≼[R] (R.otimes c b) := by
  show R.oplus (R.otimes c a) (R.otimes c b)
    = R.otimes c b
  rw [← R.left_distrib, h]

end Algebra
```

# The working interface `IdemDioid`

The from-scratch tower above fixes the meaning of a dioid; for the rest
of the book we work with it through a single type class, `IdemDioid`,
so that carriers can be registered as instances and the algebraic
notation $`+`, $`*`, $`0`, $`1`, $`\sqcup` is available directly. It is
the dioid as an _idempotent commutative semiring_: a commutative
semiring whose sum is idempotent, with the canonical order
$`a \preceq b \iff a + b = b` and $`a + b = a \sqcup b`.

*Definition:* `IdemDioid α` is the type class of idempotent commutative semirings on $`\alpha`, with $`\oplus = {+}`, $`\otimes = {*}`, $`\mathbf{0} = 0`, $`\mathbf{1} = 1`, and order $`a \preceq b \iff a + b = b`. The carriers of later chapters target it.

```lean
abbrev IdemDioid (α : Type*) := IdemCommSemiring α
```

*Definition:* `ofCommSemiring` builds an `IdemDioid` from a commutative semiring whose sum is idempotent, deriving the canonical order from idempotency.

```lean
namespace IdemDioid

abbrev ofCommSemiring {α : Type*} [CommSemiring α]
    (add_idem : ∀ a : α, a + a = a) : IdemDioid α :=
  { IdemSemiring.ofSemiring add_idem with
    mul_comm := mul_comm }

end IdemDioid
```

# The canonical order

*Theorem:* $`a \preceq b \iff a \oplus b = b`

```lean
namespace Dioid

theorem le_iff_add_eq_right
    {α : Type*} [IdemDioid α] {a b : α} :
    a ≤ b ↔ a + b = b :=
  add_eq_right_iff_le.symm
```

# Order relation and isotony

*Theorem:* $`a \preceq a` (reflexivity)

```lean
theorem le_refl' {α : Type*} [IdemDioid α] (a : α) :
    a ≤ a :=
  le_iff_add_eq_right.mpr (add_idem a)
```

*Theorem:* $`a \preceq b \;\wedge\; b \preceq c \;\Rightarrow\; a \preceq c` (transitivity)

```lean
theorem le_trans' {α : Type*} [IdemDioid α] {a b c : α}
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [le_iff_add_eq_right] at hab hbc ⊢
  calc a + c = a + (b + c) := by rw [hbc]
    _ = (a + b) + c := by rw [add_assoc]
    _ = b + c := by rw [hab]
    _ = c := hbc
```

*Theorem:* $`a \preceq b \;\wedge\; b \preceq a \;\Rightarrow\; a = b` (antisymmetry)

```lean
theorem le_antisymm' {α : Type*} [IdemDioid α] {a b : α}
    (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rw [le_iff_add_eq_right] at hab hba
  rw [← hab, add_comm, hba]
```

*Theorem:* $`a \preceq b \;\Rightarrow\; a \oplus c \preceq b \oplus c` (isotony of $`\oplus`)

```lean
theorem add_le_add_right'
    {α : Type*} [IdemDioid α] {a b : α}
    (h : a ≤ b) (c : α) : a + c ≤ b + c := by
  rw [le_iff_add_eq_right] at h ⊢
  calc (a + c) + (b + c)
      = (a + b) + (c + c) := by ac_rfl
    _ = b + c := by rw [h, add_idem]
```

*Theorem:* $`a \preceq b \;\Rightarrow\; c \oplus a \preceq c \oplus b`

```lean
theorem add_le_add_left'
    {α : Type*} [IdemDioid α] {a b : α}
    (h : a ≤ b) (c : α) : c + a ≤ c + b := by
  rw [add_comm c, add_comm c]
  exact add_le_add_right' h c
```

*Theorem:* $`a \preceq b \;\Rightarrow\; a \otimes c \preceq b \otimes c` (isotony of $`\otimes`)

```lean
theorem mul_le_mul_right'
    {α : Type*} [IdemDioid α] {a b : α}
    (h : a ≤ b) (c : α) : a * c ≤ b * c := by
  rw [le_iff_add_eq_right] at h ⊢
  rw [← add_mul, h]
```

*Theorem:* $`a \preceq b \;\Rightarrow\; c \otimes a \preceq c \otimes b`

```lean
theorem mul_le_mul_left'
    {α : Type*} [IdemDioid α] {a b : α}
    (h : a ≤ b) (c : α) : c * a ≤ c * b := by
  rw [le_iff_add_eq_right] at h ⊢
  rw [← mul_add, h]
```

```lean
end Dioid
```

# The complete dioid

*Definition:* a _complete dioid_ is an idempotent commutative semiring that is a complete lattice for $`\preceq`, with $`\otimes` lower semi-continuous: $`a \otimes \bigsqcup_{b \in s} b = \bigsqcup_{b \in s} a \otimes b`.

```lean
class CompleteDioid (α : Type*) extends
    IdemCommSemiring α, CompleteLattice α where
  mul_sSup : ∀ (a : α) (s : Set α),
    a * sSup s = ⨆ b ∈ s, a * b
```

*Theorem:* $`\Bigl(\bigsqcup_{b \in s} b\Bigr) \otimes a = \bigsqcup_{b \in s} b \otimes a`

```lean
namespace CompleteDioid

theorem sSup_mul {α : Type*} [CompleteDioid α]
    (a : α) (s : Set α) :
    sSup s * a = ⨆ b ∈ s, b * a := by
  rw [mul_comm, mul_sSup]; simp_rw [mul_comm a]
```

*Theorem:* $`a \otimes \bigsqcup_i g(i) = \bigsqcup_i a \otimes g(i)`

```lean
theorem mul_iSup {α : Type*} [CompleteDioid α]
    {ι : Sort*} (a : α) (g : ι → α) :
    a * ⨆ i, g i = ⨆ i, a * g i := by
  rw [← sSup_range, mul_sSup, iSup_range]
```

*Theorem:* $`\Bigl(\bigsqcup_i g(i)\Bigr) \otimes a = \bigsqcup_i g(i) \otimes a`

```lean
theorem iSup_mul {α : Type*} [CompleteDioid α]
    {ι : Sort*} (g : ι → α) (a : α) :
    (⨆ i, g i) * a = ⨆ i, g i * a := by
  rw [← sSup_range, sSup_mul, iSup_range]
```

*Theorem:* $`a \otimes (b \sqcup c) = (a \otimes b) \sqcup (a \otimes c)`

```lean
theorem mul_sup {α : Type*} [CompleteDioid α]
    (a b c : α) :
    a * (b ⊔ c) = a * b ⊔ a * c := by
  have h1 : (⨆ i : Bool, cond i b c) = b ⊔ c := by
    simp [iSup_bool_eq]
  have h2 :
      (⨆ i : Bool, a * cond i b c)
        = a * b ⊔ a * c := by
    simp [iSup_bool_eq]
  rw [← h1, mul_iSup, h2]
```

*Theorem:* $`(b \sqcup c) \otimes a = (b \otimes a) \sqcup (c \otimes a)`

```lean
theorem sup_mul {α : Type*} [CompleteDioid α]
    (a b c : α) :
    (b ⊔ c) * a = b * a ⊔ c * a := by
  have h1 : (⨆ i : Bool, cond i b c) = b ⊔ c := by
    simp [iSup_bool_eq]
  have h2 :
      (⨆ i : Bool, cond i b c * a)
        = b * a ⊔ c * a := by
    simp [iSup_bool_eq]
  rw [← h1, iSup_mul, h2]

end CompleteDioid
```

```lean
end NetworkCalculus
```
