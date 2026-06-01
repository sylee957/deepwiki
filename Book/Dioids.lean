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

*Definition:* the sum $`\oplus : D \times D \to D` with neutral $`\varepsilon`.

```lean
namespace Algebra

class Oplus (D : Type*) where
  oplus : D → D → D
  eps : D
```

*Definition:* the product $`\otimes : D \times D \to D` with neutral $`e`.

```lean
class Otimes (D : Type*) where
  otimes : D → D → D
  one : D
```

We attach local infixes `+ₒ`, `*ₒ` for the two operations.

```lean
section
local infixl:65 " +ₒ " => Oplus.oplus
local infixl:70 " *ₒ " => Otimes.otimes
```

*Definition:* $`(D, \oplus, \varepsilon)` is a _monoid_:
$$`(a \oplus b) \oplus c = a \oplus (b \oplus c), \quad \varepsilon \oplus a = a, \quad a \oplus \varepsilon = a.`

```lean
class AddMonoid (D : Type*) extends Oplus D where
  oplus_assoc : ∀ a b c : D, (a +ₒ b) +ₒ c = a +ₒ (b +ₒ c)
  eps_oplus : ∀ a : D, Oplus.eps +ₒ a = a
  oplus_eps : ∀ a : D, a +ₒ Oplus.eps = a
```

*Definition:* a _commutative_ monoid adds $`a \oplus b = b \oplus a`.

```lean
class AddCommMonoid (D : Type*) extends AddMonoid D where
  oplus_comm : ∀ a b : D, a +ₒ b = b +ₒ a
```

*Definition:* an _idempotent_ commutative monoid adds $`a \oplus a = a`.

```lean
class AddIdemCommMonoid (D : Type*) extends
    AddCommMonoid D where
  oplus_idem : ∀ a : D, a +ₒ a = a
```

*Definition:* $`(D, \otimes, e)` is a _monoid_:
$$`(a \otimes b) \otimes c = a \otimes (b \otimes c), \quad e \otimes a = a, \quad a \otimes e = a.`

```lean
class MulMonoid (D : Type*) extends Otimes D where
  otimes_assoc :
    ∀ a b c : D, (a *ₒ b) *ₒ c = a *ₒ (b *ₒ c)
  one_otimes : ∀ a : D, Otimes.one *ₒ a = a
  otimes_one : ∀ a : D, a *ₒ Otimes.one = a
```

*Definition:* a _semi-ring_ is a commutative $`\oplus`-monoid and a $`\otimes`-monoid with
$$`a \otimes (b \oplus c) = (a \otimes b) \oplus (a \otimes c), \quad (a \oplus b) \otimes c = (a \otimes c) \oplus (b \otimes c),`
$$`\varepsilon \otimes a = \varepsilon, \quad a \otimes \varepsilon = \varepsilon.`

```lean
class Semiring (D : Type*) extends
    AddCommMonoid D, MulMonoid D where
  left_distrib :
    ∀ a b c : D, a *ₒ (b +ₒ c) = a *ₒ b +ₒ a *ₒ c
  right_distrib :
    ∀ a b c : D, (a +ₒ b) *ₒ c = a *ₒ c +ₒ b *ₒ c
  eps_otimes : ∀ a : D, Oplus.eps *ₒ a = Oplus.eps
  otimes_eps : ∀ a : D, a *ₒ Oplus.eps = Oplus.eps
```

*Definition:* a _commutative semi-ring_ adds $`a \otimes b = b \otimes a`.

```lean
class CommSemiring (D : Type*) extends Semiring D where
  otimes_comm : ∀ a b : D, a *ₒ b = b *ₒ a
```

*Definition:* a _dioid_ is a commutative semi-ring whose sum is idempotent, $`a \oplus a = a`.

```lean
class Dioid (D : Type*) extends
    CommSemiring D, AddIdemCommMonoid D
```

*Theorem:* $`(a \oplus b) \otimes (c \oplus d) = (a \otimes c) \oplus (b \otimes c) \oplus (a \otimes d) \oplus (b \otimes d)`

```lean
theorem quaternary_distrib {D : Type*} [Semiring D]
    (a b c d : D) :
    (a +ₒ b) *ₒ (c +ₒ d)
      = a *ₒ c +ₒ b *ₒ c +ₒ a *ₒ d +ₒ b *ₒ d := by
  set p := a *ₒ c; set q := b *ₒ c
  set r := a *ₒ d; set s := b *ₒ d
  have hexp :
      (a +ₒ b) *ₒ (c +ₒ d) = (p +ₒ r) +ₒ (q +ₒ s) := by
    rw [Semiring.right_distrib, Semiring.left_distrib,
      Semiring.left_distrib]
  rw [hexp, AddMonoid.oplus_assoc p q r,
    AddMonoid.oplus_assoc p (q +ₒ r) s,
    AddMonoid.oplus_assoc p r (q +ₒ s)]
  congr 1
  rw [AddCommMonoid.oplus_comm q r,
    AddMonoid.oplus_assoc r q s]

end

end Algebra
```

# The Mathlib interface `IdemDioid`

*Definition:* `IdemDioid α` $`:=` Mathlib's `IdemCommSemiring α` (idempotent commutative semiring), with $`\oplus = {+}`, $`\otimes = {*}`, $`\mathbf{0} = 0`, $`\mathbf{1} = 1`, and order $`a \preceq b \iff a + b = b`, $`a + b = a \sqcup b`. The carriers of later chapters target it.

```lean
abbrev IdemDioid (α : Type*) := IdemCommSemiring α
```

*Definition:* `ofCommSemiring` builds an `IdemDioid` from a commutative semiring with idempotent sum, deriving the order via `IdemSemiring.ofSemiring`.

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
