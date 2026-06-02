import VersoManual
import Book.Signatures
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Semi-rings and the dioid" =>
On top of the monoids of the previous chapter, this chapter adds the
distributive structure: the semi-ring, its commutative refinement, and
the _dioid_ — a commutative semi-ring whose sum is idempotent. Each
layer is again paired with a bridge to the corresponding `Mathlib`
structure. The order a dioid induces, and complete dioids, follow in
the next chapters.

```lean
namespace NetworkCalculus

namespace Algebra

open scoped Bridge
```

# The semi-ring

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

```lean
namespace Bridge

scoped instance instSemiring
    {T : Type*} [Semiring T] : _root_.Semiring T where
  toAddCommMonoid := instAddCommMonoid
  toMonoid := instMulMonoid
  left_distrib := Semiring.left_distrib
  right_distrib := Semiring.right_distrib
  zero_mul := Semiring.eps_otimes
  mul_zero := Semiring.otimes_eps

end Bridge
```

*Theorem:* $`(a \oplus b) \otimes (c \oplus d) = (a \otimes c) \oplus (b \otimes c) \oplus (a \otimes d) \oplus (b \otimes d)`

```lean
example {T : Type*} [Semiring T]
    (a b c d : T) :
    (a ⊕ₒ b) ⊗ₒ (c ⊕ₒ d)
      = (a ⊗ₒ c) ⊕ₒ (b ⊗ₒ c) ⊕ₒ (a ⊗ₒ d) ⊕ₒ (b ⊗ₒ d) := by
  have hexp : (a ⊕ₒ b) ⊗ₒ (c ⊕ₒ d)
      = (a ⊗ₒ c ⊕ₒ a ⊗ₒ d) ⊕ₒ (b ⊗ₒ c ⊕ₒ b ⊗ₒ d) := by
    rw [right_distrib, left_distrib, left_distrib]
  rw [hexp,
    add_assoc (a ⊗ₒ c) (b ⊗ₒ c) (a ⊗ₒ d),
    add_assoc (a ⊗ₒ c)
      (b ⊗ₒ c ⊕ₒ a ⊗ₒ d) (b ⊗ₒ d),
    add_assoc (a ⊗ₒ c) (a ⊗ₒ d)
      (b ⊗ₒ c ⊕ₒ b ⊗ₒ d)]
  congr 1
  rw [add_comm (b ⊗ₒ c) (a ⊗ₒ d),
    add_assoc (a ⊗ₒ d) (b ⊗ₒ c) (b ⊗ₒ d)]
```

# The commutative semi-ring

*Definition:* a _commutative semi-ring_ adds $`a \otimes b = b \otimes a`.

```lean
class CommSemiring (T : Type*) extends Semiring T where
  otimes_comm : ∀ a b : T, a ⊗ₒ b = b ⊗ₒ a
```

```lean
namespace Bridge

scoped instance instCommSemiring
    {T : Type*} [CommSemiring T] :
    _root_.CommSemiring T where
  toSemiring := instSemiring
  mul_comm := CommSemiring.otimes_comm

scoped instance instMulCommMonoid
    {T : Type*} [CommSemiring T] :
    _root_.CommMonoid T where
  toMonoid := instMulMonoid
  mul_comm := CommSemiring.otimes_comm

end Bridge
```

# The dioid

*Definition:* a _dioid_ is a commutative semi-ring whose sum is idempotent, $`a \oplus a = a`.

```lean
class Dioid (T : Type*) extends CommSemiring T where
  oplus_idem : ∀ a : T, a ⊕ₒ a = a
```

```lean
end Algebra
```

```lean
end NetworkCalculus
```
