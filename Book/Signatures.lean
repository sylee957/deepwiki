import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Order.Kleene

/-! Abstract dioid signature tower (`⊕ₒ`/`⊗ₒ`) with scoped `Bridge`
instances mapping each class onto its Mathlib counterpart. -/

namespace DeepWiki

namespace Algebra

/-- Additive structure: a carrier with `⊕ₒ` and identity `εₒ`. -/
class Oplus (T : Type*) extends AddZero T

/-- Multiplicative structure: a carrier with `⊗ₒ` and unit `eₒ`. -/
class Otimes (T : Type*) extends MulOne T

/-- Dioid sum `a ⊕ₒ b`. -/
scoped notation:65 a:65 " ⊕ₒ " b:66 =>
  @HAdd.hAdd _ _ _
    (@instHAdd _ Oplus.toAddZero.toAdd) a b
/-- Additive identity `εₒ`. -/
scoped notation:max "εₒ" =>
  @Zero.zero _ Oplus.toAddZero.toZero
/-- Dioid product `a ⊗ₒ b`. -/
scoped notation:70 a:70 " ⊗ₒ " b:71 =>
  @HMul.hMul _ _ _
    (@instHMul _ Otimes.toMulOne.toMul) a b
/-- Multiplicative unit `eₒ`. -/
scoped notation:max "eₒ" =>
  @One.one _ Otimes.toMulOne.toOne

/-- Additive monoid over `⊕ₒ`: associative with identity `εₒ`. -/
class AddMonoid (T : Type*) extends Oplus T where
  oplus_assoc : ∀ a b c : T,
    (a ⊕ₒ b) ⊕ₒ c = a ⊕ₒ (b ⊕ₒ c)
  eps_oplus : ∀ a : T, εₒ ⊕ₒ a = a
  oplus_eps : ∀ a : T, a ⊕ₒ εₒ = a

namespace Bridge

/-- Bridge: `Algebra.AddMonoid` to Mathlib's `AddMonoid`. -/
scoped instance instAddMonoid
    {T : Type*} [AddMonoid T] : _root_.AddMonoid T where
  toAddZero := AddMonoid.toOplus.toAddZero
  add_assoc := AddMonoid.oplus_assoc
  zero_add := AddMonoid.eps_oplus
  add_zero := AddMonoid.oplus_eps
  nsmul n a := n.rec 0 (fun _ acc => acc + a)

end Bridge

/-- Multiplicative monoid over `⊗ₒ`: associative with unit `eₒ`. -/
class MulMonoid (T : Type*) extends Otimes T where
  otimes_assoc : ∀ a b c : T,
    (a ⊗ₒ b) ⊗ₒ c = a ⊗ₒ (b ⊗ₒ c)
  one_otimes : ∀ a : T, eₒ ⊗ₒ a = a
  otimes_one : ∀ a : T, a ⊗ₒ eₒ = a

namespace Bridge

/-- Bridge: `Algebra.MulMonoid` to Mathlib's `Monoid`. -/
scoped instance instMulMonoid
    {T : Type*} [MulMonoid T] : _root_.Monoid T where
  toMulOne := MulMonoid.toOtimes.toMulOne
  mul_assoc := MulMonoid.otimes_assoc
  one_mul := MulMonoid.one_otimes
  mul_one := MulMonoid.otimes_one
  npow n a := n.rec 1 (fun _ acc => acc * a)

end Bridge

/-- Commutative additive monoid: `⊕ₒ` is commutative. -/
class AddCommMonoid (T : Type*) extends AddMonoid T where
  oplus_comm : ∀ a b : T, a ⊕ₒ b = b ⊕ₒ a

namespace Bridge

/-- Bridge: `Algebra.AddCommMonoid` to Mathlib's `AddCommMonoid`. -/
scoped instance instAddCommMonoid
    {T : Type*} [AddCommMonoid T] :
    _root_.AddCommMonoid T where
  toAddMonoid := instAddMonoid
  add_comm := AddCommMonoid.oplus_comm

end Bridge

end Algebra

end DeepWiki
