import Book.Signatures
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel

/-! # Dioids
Semirings, commutative semirings, and the idempotent dioid,
built on the abstract `Bridge` tower over Mathlib. -/

namespace DeepWiki

namespace Algebra

open scoped Bridge

/-- Abstract semiring over the `Bridge` tower (`⊕ₒ`, `⊗ₒ`, `εₒ`). -/
class Semiring (T : Type*) extends
    AddCommMonoid T, MulMonoid T where
  left_distrib : ∀ a b c : T,
    a ⊗ₒ (b ⊕ₒ c) = a ⊗ₒ b ⊕ₒ a ⊗ₒ c
  right_distrib : ∀ a b c : T,
    (a ⊕ₒ b) ⊗ₒ c = a ⊗ₒ c ⊕ₒ b ⊗ₒ c
  eps_otimes : ∀ a : T, εₒ ⊗ₒ a = εₒ
  otimes_eps : ∀ a : T, a ⊗ₒ εₒ = εₒ

namespace Bridge

/-- `Algebra.Semiring` yields a Mathlib `Semiring`. -/
scoped instance instSemiring
    {T : Type*} [Semiring T] : _root_.Semiring T where
  toAddCommMonoid := instAddCommMonoid
  toMonoid := instMulMonoid
  left_distrib := Semiring.left_distrib
  right_distrib := Semiring.right_distrib
  zero_mul := Semiring.eps_otimes
  mul_zero := Semiring.otimes_eps

end Bridge

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

/-- Semiring with commutative product `⊗ₒ`. -/
class CommSemiring (T : Type*) extends Semiring T where
  otimes_comm : ∀ a b : T, a ⊗ₒ b = b ⊗ₒ a

namespace Bridge

/-- `Algebra.CommSemiring` yields a Mathlib `CommSemiring`. -/
scoped instance instCommSemiring
    {T : Type*} [CommSemiring T] :
    _root_.CommSemiring T where
  toSemiring := instSemiring
  mul_comm := CommSemiring.otimes_comm

/-- The product `⊗ₒ` forms a Mathlib `CommMonoid`. -/
scoped instance instMulCommMonoid
    {T : Type*} [CommSemiring T] :
    _root_.CommMonoid T where
  toMonoid := instMulMonoid
  mul_comm := CommSemiring.otimes_comm

end Bridge

/-- A dioid: commutative semiring with idempotent sum `⊕ₒ`. -/
class Dioid (T : Type*) extends CommSemiring T where
  oplus_idem : ∀ a : T, a ⊕ₒ a = a

end Algebra

end DeepWiki
