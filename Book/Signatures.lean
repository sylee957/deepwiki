import VersoManual
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Order.Kleene

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Signatures and monoids" =>
The dioid tower begins with the bare _operation signatures_ — a sum
$`\oplus` and a product $`\otimes`, each with a neutral — and the
monoid layers over them. This chapter builds the signatures, the
additive and multiplicative monoids and the commutative monoid, each
paired with a _bridge_ exhibiting it as the corresponding `Mathlib`
structure. The semi-ring and dioid layers continue in the next chapter.

All declarations live in the `NetworkCalculus` namespace.

```lean
namespace NetworkCalculus
```

# Operation signatures

The tower is built as a chain of _type classes_ over a carrier $`T`.
The operations are recovered by instance resolution, so the glyphs
$`\oplus` and $`\otimes` need no tag — we write them `⊕ₒ` and `⊗ₒ`.

*Definition:* a _sum signature_ on a carrier $`T` is a binary
$`\oplus : T \times T \to T` with a neutral $`\varepsilon`.

```lean
namespace Algebra

class Oplus (T : Type*) extends AddZero T

class Otimes (T : Type*) extends MulOne T

scoped notation:65 a:65 " ⊕ₒ " b:66 =>
  @HAdd.hAdd _ _ _
    (@instHAdd _ Oplus.toAddZero.toAdd) a b
scoped notation:max "εₒ" =>
  @Zero.zero _ Oplus.toAddZero.toZero
scoped notation:70 a:70 " ⊗ₒ " b:71 =>
  @HMul.hMul _ _ _
    (@instHMul _ Otimes.toMulOne.toMul) a b
scoped notation:max "eₒ" =>
  @One.one _ Otimes.toMulOne.toOne
```

Each signature bundles `Mathlib`'s lawless `Add`/`Zero` (`AddZero`) and
`Mul`/`One` (`MulOne`), so $`\oplus, \varepsilon` are literally the
addition and its neutral and $`\otimes, e` the multiplication and its
unit. The glyphs $`\oplus, \varepsilon, \otimes, e` are notation for
$`+, 0, *, 1`, restricted to carriers of the signatures; the monoid
bridges below only add the laws.

*Definition:* a _product signature_ on $`T` is a binary
$`\otimes : T \times T \to T` with a neutral $`e`.

# The monoid

## The additive monoid

*Definition:* $`(T, \oplus, \varepsilon)` is a _monoid_:
$$`(a \oplus b) \oplus c = a \oplus (b \oplus c), \quad \varepsilon \oplus a = a, \quad a \oplus \varepsilon = a.`

```lean
class AddMonoid (T : Type*) extends Oplus T where
  oplus_assoc : ∀ a b c : T,
    (a ⊕ₒ b) ⊕ₒ c = a ⊕ₒ (b ⊕ₒ c)
  eps_oplus : ∀ a : T, εₒ ⊕ₒ a = a
  oplus_eps : ∀ a : T, a ⊕ₒ εₒ = a
```

```lean
namespace Bridge

scoped instance instAddMonoid
    {T : Type*} [AddMonoid T] : _root_.AddMonoid T where
  toAddZero := AddMonoid.toOplus.toAddZero
  add_assoc := AddMonoid.oplus_assoc
  zero_add := AddMonoid.eps_oplus
  add_zero := AddMonoid.oplus_eps
  nsmul n a := n.rec 0 (fun _ acc => acc + a)

end Bridge
```

## The multiplicative monoid

The product carries the same monoid structure, over the $`\otimes`
signature with neutral $`e`.

*Definition:* $`(T, \otimes, e)` is a _monoid_:
$$`(a \otimes b) \otimes c = a \otimes (b \otimes c), \quad e \otimes a = a, \quad a \otimes e = a.`

```lean
class MulMonoid (T : Type*) extends Otimes T where
  otimes_assoc : ∀ a b c : T,
    (a ⊗ₒ b) ⊗ₒ c = a ⊗ₒ (b ⊗ₒ c)
  one_otimes : ∀ a : T, eₒ ⊗ₒ a = a
  otimes_one : ∀ a : T, a ⊗ₒ eₒ = a
```

```lean
namespace Bridge

scoped instance instMulMonoid
    {T : Type*} [MulMonoid T] : _root_.Monoid T where
  toMulOne := MulMonoid.toOtimes.toMulOne
  mul_assoc := MulMonoid.otimes_assoc
  one_mul := MulMonoid.one_otimes
  mul_one := MulMonoid.otimes_one
  npow n a := n.rec 1 (fun _ acc => acc * a)

end Bridge
```

# The commutative monoid

*Definition:* a _commutative_ monoid adds $`a \oplus b = b \oplus a`.

```lean
class AddCommMonoid (T : Type*) extends AddMonoid T where
  oplus_comm : ∀ a b : T, a ⊕ₒ b = b ⊕ₒ a
```

```lean
namespace Bridge

scoped instance instAddCommMonoid
    {T : Type*} [AddCommMonoid T] :
    _root_.AddCommMonoid T where
  toAddMonoid := instAddMonoid
  add_comm := AddCommMonoid.oplus_comm

end Bridge
```

```lean
end Algebra
```

```lean
end NetworkCalculus
```
