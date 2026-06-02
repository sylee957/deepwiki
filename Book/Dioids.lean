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

The tower below is a self-contained illustration built as a chain of
_type classes_ over a carrier $`T`. The operations are recovered by
instance resolution, so the glyphs $`\oplus` and $`\otimes` need no
tag — we write them `⊕ₒ` and `⊗ₒ`. Each layer extends the previous
one, and the idempotency that distinguishes a dioid is added as a
single field on top of a commutative semi-ring, so no inheritance
diamond arises. The interface the rest of the book actually builds on
is `IdemDioid`, defined afterwards.

*Definition:* a _sum signature_ on a carrier $`T` is a binary
$`\oplus : T \times T \to T` with a neutral $`\varepsilon`.

```lean
namespace Algebra

class Oplus (T : Type*) where
  oplus : T → T → T
  eps : T

class Otimes (T : Type*) where
  otimes : T → T → T
  one : T

scoped infixl:65 " ⊕ₒ " => Oplus.oplus
scoped infixl:70 " ⊗ₒ " => Otimes.otimes
scoped notation "εₒ" => Oplus.eps
scoped notation "eₒ" => Otimes.one
```

*Definition:* a _product signature_ on $`T` is a binary
$`\otimes : T \times T \to T` with a neutral $`e`.

*Definition:* $`(T, \oplus, \varepsilon)` is a _monoid_:
$$`(a \oplus b) \oplus c = a \oplus (b \oplus c), \quad \varepsilon \oplus a = a, \quad a \oplus \varepsilon = a.`

```lean
class AddMonoid (T : Type*) extends Oplus T where
  oplus_assoc : ∀ a b c : T,
    (a ⊕ₒ b) ⊕ₒ c = a ⊕ₒ (b ⊕ₒ c)
  eps_oplus : ∀ a : T, εₒ ⊕ₒ a = a
  oplus_eps : ∀ a : T, a ⊕ₒ εₒ = a
```

*Definition:* a _commutative_ monoid adds $`a \oplus b = b \oplus a`.

```lean
class AddCommMonoid (T : Type*) extends AddMonoid T where
  oplus_comm : ∀ a b : T, a ⊕ₒ b = b ⊕ₒ a
```

*Definition:* $`(T, \otimes, e)` is a _monoid_:
$$`(a \otimes b) \otimes c = a \otimes (b \otimes c), \quad e \otimes a = a, \quad a \otimes e = a.`

```lean
class MulMonoid (T : Type*) extends Otimes T where
  otimes_assoc : ∀ a b c : T,
    (a ⊗ₒ b) ⊗ₒ c = a ⊗ₒ (b ⊗ₒ c)
  one_otimes : ∀ a : T, eₒ ⊗ₒ a = a
  otimes_one : ∀ a : T, a ⊗ₒ eₒ = a
```

*Definition:* a _semi-ring_ is a commutative $`\oplus`-monoid and a $`\otimes`-monoid with
$$`a \otimes (b \oplus c) = (a \otimes b) \oplus (a \otimes c), \quad (a \oplus b) \otimes c = (a \otimes c) \oplus (b \otimes c),`
$$`\varepsilon \otimes a = \varepsilon, \quad a \otimes \varepsilon = \varepsilon.`

```lean
class Semiring (T : Type*) extends
    AddCommMonoid T, MulMonoid T where
  left_distrib : ∀ a b c : T,
    a ⊗ₒ (b ⊕ₒ c) = a ⊗ₒ b ⊕ₒ a ⊗ₒ c
  right_distrib : ∀ a b c : T,
    (a ⊕ₒ b) ⊗ₒ c = a ⊗ₒ c ⊕ₒ b ⊗ₒ c
  eps_otimes : ∀ a : T, εₒ ⊗ₒ a = εₒ
  otimes_eps : ∀ a : T, a ⊗ₒ εₒ = εₒ
```

*Definition:* a _commutative semi-ring_ adds $`a \otimes b = b \otimes a`.

```lean
class CommSemiring (T : Type*) extends Semiring T where
  otimes_comm : ∀ a b : T, a ⊗ₒ b = b ⊗ₒ a
```

*Definition:* a _dioid_ is a commutative semi-ring whose sum is idempotent, $`a \oplus a = a`.

```lean
class Dioid (T : Type*) extends CommSemiring T where
  oplus_idem : ∀ a : T, a ⊕ₒ a = a
```

*Theorem:* $`(a \oplus b) \otimes (c \oplus d) = (a \otimes c) \oplus (b \otimes c) \oplus (a \otimes d) \oplus (b \otimes d)`

```lean
theorem quaternary_distrib {T : Type*} [Semiring T]
    (a b c d : T) :
    (a ⊕ₒ b) ⊗ₒ (c ⊕ₒ d)
      = a ⊗ₒ c ⊕ₒ b ⊗ₒ c ⊕ₒ a ⊗ₒ d ⊕ₒ b ⊗ₒ d := by
  have hexp : (a ⊕ₒ b) ⊗ₒ (c ⊕ₒ d)
      = (a ⊗ₒ c ⊕ₒ a ⊗ₒ d) ⊕ₒ (b ⊗ₒ c ⊕ₒ b ⊗ₒ d) := by
    rw [Semiring.right_distrib, Semiring.left_distrib,
      Semiring.left_distrib]
  rw [hexp]
  set p := a ⊗ₒ c; set q := b ⊗ₒ c
  set r := a ⊗ₒ d; set s := b ⊗ₒ d
  rw [AddMonoid.oplus_assoc p q r,
    AddMonoid.oplus_assoc p (q ⊕ₒ r) s,
    AddMonoid.oplus_assoc p r (q ⊕ₒ s)]
  congr 1
  rw [AddCommMonoid.oplus_comm q r,
    AddMonoid.oplus_assoc r q s]
```

## The canonical order on a dioid

Every dioid carries a _canonical order_ read off from its sum: $`a` is
below $`b` exactly when adding $`a` to $`b` changes nothing. We write it
`a ≼ₒ b`; the dioid is recovered by instance resolution.

*Definition:* $`a \preceq b \iff a \oplus b = b`

```lean
def le {T : Type*} [Dioid T] (a b : T) : Prop :=
  a ⊕ₒ b = b

scoped infix:50 " ≼ₒ " => le
```

Reflexivity is exactly idempotency of the sum: $`a \oplus a = a`.

*Theorem:* $`a \preceq a`

```lean
theorem le_refl {T : Type*} [Dioid T] (a : T) :
    a ≼ₒ a :=
  Dioid.oplus_idem a
```

Transitivity uses associativity to merge the two witnessing equations.

*Theorem:* $`a \preceq b \;\wedge\; b \preceq c \;\Rightarrow\; a \preceq c`

```lean
theorem le_trans {T : Type*} [Dioid T] {a b c : T}
    (hab : a ≼ₒ b) (hbc : b ≼ₒ c) : a ≼ₒ c := by
  show a ⊕ₒ c = c
  calc a ⊕ₒ c
      = a ⊕ₒ (b ⊕ₒ c) := by rw [hbc]
    _ = (a ⊕ₒ b) ⊕ₒ c := by
        rw [AddMonoid.oplus_assoc]
    _ = b ⊕ₒ c := by rw [hab]
    _ = c := hbc
```

Antisymmetry uses commutativity: the two equations exhibit $`a` and
$`b` as the same sum.

*Theorem:* $`a \preceq b \;\wedge\; b \preceq a \;\Rightarrow\; a = b`

```lean
theorem le_antisymm {T : Type*} [Dioid T] {a b : T}
    (hab : a ≼ₒ b) (hba : b ≼ₒ a) : a = b := by
  have h1 : a ⊕ₒ b = b := hab
  rw [← h1, AddCommMonoid.oplus_comm, hba]
```

The sum is _isotone_ in each argument: a smaller summand gives a
smaller sum.

*Theorem:* $`a \preceq b \;\Rightarrow\; a \oplus c \preceq b \oplus c`

```lean
theorem add_le_add_right {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (a ⊕ₒ c) ≼ₒ (b ⊕ₒ c) := by
  show (a ⊕ₒ c) ⊕ₒ (b ⊕ₒ c) = b ⊕ₒ c
  calc (a ⊕ₒ c) ⊕ₒ (b ⊕ₒ c)
      = (a ⊕ₒ b) ⊕ₒ (c ⊕ₒ c) := by
        rw [AddMonoid.oplus_assoc,
          ← AddMonoid.oplus_assoc c b c,
          AddCommMonoid.oplus_comm c b,
          AddMonoid.oplus_assoc b c c,
          ← AddMonoid.oplus_assoc a b (c ⊕ₒ c)]
    _ = b ⊕ₒ c := by rw [h, Dioid.oplus_idem]
```

*Theorem:* $`a \preceq b \;\Rightarrow\; c \oplus a \preceq c \oplus b`

```lean
theorem add_le_add_left {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (c ⊕ₒ a) ≼ₒ (c ⊕ₒ b) := by
  rw [AddCommMonoid.oplus_comm c a,
    AddCommMonoid.oplus_comm c b]
  exact add_le_add_right h c
```

The product is isotone in each argument, by distributivity.

*Theorem:* $`a \preceq b \;\Rightarrow\; a \otimes c \preceq b \otimes c`

```lean
theorem mul_le_mul_right {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (a ⊗ₒ c) ≼ₒ (b ⊗ₒ c) := by
  show (a ⊗ₒ c) ⊕ₒ (b ⊗ₒ c) = b ⊗ₒ c
  rw [← Semiring.right_distrib, h]
```

*Theorem:* $`a \preceq b \;\Rightarrow\; c \otimes a \preceq c \otimes b`

```lean
theorem mul_le_mul_left {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (c ⊗ₒ a) ≼ₒ (c ⊗ₒ b) := by
  show (c ⊗ₒ a) ⊕ₒ (c ⊗ₒ b) = c ⊗ₒ b
  rw [← Semiring.left_distrib, h]
```

## A complete dioid from scratch

A dioid is _complete_ when every subset of the carrier has a least
upper bound for the canonical order $`\preceq`, and the product is
_lower semi-continuous_: it commutes with these suprema. We add the
supremum $`\bigsqcup` as a field `sSup`, the two laws making it a least
upper bound, and lower semi-continuity
$$`a \otimes \bigsqcup_{b \in s} b = \bigsqcup_{b \in s} a \otimes b.`

*Definition:* a _complete dioid_ adds $`\bigsqcup : \mathcal{P}(T) \to T` with
$$`a \in s \Rightarrow a \preceq \textstyle\bigsqcup s, \qquad (\forall a \in s,\ a \preceq b) \Rightarrow \textstyle\bigsqcup s \preceq b,`
$$`a \otimes \textstyle\bigsqcup s = \textstyle\bigsqcup\,\{\,a \otimes b \mid b \in s\,\}.`

```lean
class CompleteDioid (T : Type*) extends Dioid T where
  sSup : Set T → T
  le_sSup : ∀ (s : Set T) (a : T), a ∈ s →
    le a (sSup s)
  sSup_le : ∀ (s : Set T) (b : T),
    (∀ a ∈ s, le a b) → le (sSup s) b
  mul_sSup : ∀ (a : T) (s : Set T),
    a ⊗ₒ sSup s = sSup ((fun b => a ⊗ₒ b) '' s)
```

Lower semi-continuity holds on the right as well, by commutativity of
the product.

*Theorem:* $`\Bigl(\bigsqcup_{b \in s} b\Bigr) \otimes a = \bigsqcup_{b \in s} b \otimes a`

```lean
theorem sSup_mul {T : Type*} [CompleteDioid T]
    (a : T) (s : Set T) :
    (CompleteDioid.sSup s) ⊗ₒ a
      = CompleteDioid.sSup ((fun b => b ⊗ₒ a) '' s) := by
  rw [CommSemiring.otimes_comm, CompleteDioid.mul_sSup]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, CommSemiring.otimes_comm y a⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, CommSemiring.otimes_comm a y⟩
```

The binary join is the supremum of a two-element set, and the product
distributes over it — the finite shadow of lower semi-continuity.

*Definition:* $`a \sqcup b := \bigsqcup \{a, b\}`

```lean
def sup {T : Type*} [CompleteDioid T] (a b : T) : T :=
  CompleteDioid.sSup {a, b}
```

*Theorem:* $`a \otimes (b \sqcup c) = (a \otimes b) \sqcup (a \otimes c)`

```lean
theorem mul_sup {T : Type*} [CompleteDioid T]
    (a b c : T) :
    a ⊗ₒ sup b c = sup (a ⊗ₒ b) (a ⊗ₒ c) := by
  unfold sup
  rw [CompleteDioid.mul_sSup]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨b, Or.inl rfl, rfl⟩
    · exact ⟨c, Or.inr rfl, rfl⟩
```

## The top element

A complete dioid has a _greatest element_ $`\top`, the sum of all the
elements of the carrier:
$$`\top = \bigsqcup_{x} x.`
We take it as the supremum of the universal set, written `⊤ₒ[T]`.

*Definition:* $`\top = \bigsqcup_{x \in T} x`

```lean
def top (T : Type*) [CompleteDioid T] : T :=
  CompleteDioid.sSup Set.univ

scoped notation:max "⊤ₒ[" T "]" => top T
```

Being the supremum of everything, $`\top` lies above every element.

*Theorem:* $`a \preceq \top`

```lean
theorem le_top {T : Type*} [CompleteDioid T] (a : T) :
    a ≼ₒ ⊤ₒ[T] :=
  CompleteDioid.le_sSup Set.univ a (Set.mem_univ a)
```

Hence $`\top` is _absorbing for the sum_: adding anything to it changes
nothing.

*Theorem:* $`\top \oplus a = \top`

```lean
theorem top_oplus {T : Type*} [CompleteDioid T] (a : T) :
    ⊤ₒ[T] ⊕ₒ a = ⊤ₒ[T] := by
  have h : a ⊕ₒ ⊤ₒ[T] = ⊤ₒ[T] := le_top a
  rw [AddCommMonoid.oplus_comm, h]
```

Since the zero $`\varepsilon` is absorbing for the product, multiplying
$`\top` by $`\varepsilon` on either side collapses to $`\varepsilon`.

*Theorem:* $`\varepsilon \otimes \top = \top \otimes \varepsilon = \varepsilon`

```lean
theorem eps_otimes_top {T : Type*} [CompleteDioid T] :
    εₒ ⊗ₒ ⊤ₒ[T] = εₒ :=
  Semiring.eps_otimes (top T)

theorem top_otimes_eps {T : Type*} [CompleteDioid T] :
    ⊤ₒ[T] ⊗ₒ εₒ = εₒ :=
  Semiring.otimes_eps (top T)
```

## The two orders agree

A complete dioid now carries _two_ ways to compare elements. The
_algebraic_ order $`\preceq` comes from the sum, $`a \preceq b \iff a
\oplus b = b`. The _lattice_ order comes from the supremum: $`a` is
below $`b` when the least upper bound of $`\{a, b\}` is $`b`. These must
coincide for the structure to be consistent, and they do — a direct
consequence of the least-upper-bound laws.

First, the supremum of a pair _is_ the binary sum: adjoining the two
upper-bound facts to idempotency pins $`\bigsqcup\{a, b\} = a \oplus b`.

*Theorem:* $`\bigsqcup \{a, b\} = a \oplus b`

```lean
theorem sSup_pair {T : Type*} [CompleteDioid T]
    (a b : T) : CompleteDioid.sSup {a, b} = a ⊕ₒ b := by
  apply le_antisymm
  · refine CompleteDioid.sSup_le _ _ ?_
    intro x hx
    rcases hx with hx | hx
    · show x ⊕ₒ (a ⊕ₒ b) = a ⊕ₒ b
      rw [hx, ← AddMonoid.oplus_assoc, Dioid.oplus_idem]
    · rw [Set.mem_singleton_iff] at hx
      show x ⊕ₒ (a ⊕ₒ b) = a ⊕ₒ b
      rw [hx, AddCommMonoid.oplus_comm a b,
        ← AddMonoid.oplus_assoc, Dioid.oplus_idem]
  · have ha := CompleteDioid.le_sSup ({a, b} : Set T) a
      (by simp)
    have hb := CompleteDioid.le_sSup ({a, b} : Set T) b
      (by simp)
    show (a ⊕ₒ b) ⊕ₒ CompleteDioid.sSup {a, b}
      = CompleteDioid.sSup {a, b}
    rw [AddMonoid.oplus_assoc, hb, ha]
```

Hence the lattice order — $`\bigsqcup\{a, b\} = b` — is exactly the
algebraic order $`a \preceq b`.

*Theorem:* $`a \preceq b \iff \bigsqcup \{a, b\} = b`

```lean
theorem le_iff_sSup_pair {T : Type*} [CompleteDioid T]
    {a b : T} :
    a ≼ₒ b ↔ CompleteDioid.sSup {a, b} = b := by
  rw [sSup_pair]; rfl

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
