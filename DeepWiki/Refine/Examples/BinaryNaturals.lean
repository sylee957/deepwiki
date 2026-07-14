import DeepWiki.Refine.ProofTransfer

/-! # Unary and binary natural-number representation example

Canonical binary numerals give a computation-oriented natural-number carrier.  Its zero,
successor, and conversions to and from `Nat` form an equivalent natural-number interface, so the
usual dependent eliminator transfers to the binary carrier. -/

namespace DeepWiki.Refine

universe u v w

/-- A canonical positive binary numeral, with its most significant bit represented recursively. -/
inductive BinaryPositive where
  /-- The positive numeral one. -/
  | one
  /-- Append a low zero bit. -/
  | bit0 (digits : BinaryPositive)
  /-- Append a low one bit. -/
  | bit1 (digits : BinaryPositive)
  deriving DecidableEq, Repr

namespace BinaryPositive

/-- Read a positive binary numeral as a unary natural number. -/
def toNat : BinaryPositive → Nat
  | .one => 1
  | .bit0 digits => 2 * digits.toNat
  | .bit1 digits => 2 * digits.toNat + 1

/-- Every positive binary numeral denotes a positive natural number. -/
theorem toNat_pos (value : BinaryPositive) : 0 < value.toNat := by
  induction value with
  | one => simp [toNat]
  | bit0 digits ih =>
      simp only [toNat]
      omega
  | bit1 digits ih =>
      simp only [toNat]
      omega

/-- Binary successor on positive numerals. -/
def succ : BinaryPositive → BinaryPositive
  | .one => .bit0 .one
  | .bit0 digits => .bit1 digits
  | .bit1 digits => .bit0 digits.succ

/-- Reading a positive binary successor agrees with unary successor. -/
theorem toNat_succ (value : BinaryPositive) : value.succ.toNat = Nat.succ value.toNat := by
  induction value with
  | one => rfl
  | bit0 digits => rfl
  | bit1 digits ih =>
      simp only [succ, toNat, ih]
      omega

/-- Addition on canonical positive binary numerals. -/
def add : BinaryPositive → BinaryPositive → BinaryPositive
  | .one, right => right.succ
  | .bit0 left, .one => .bit1 left
  | .bit1 left, .one => .bit0 left.succ
  | .bit0 left, .bit0 right => .bit0 (add left right)
  | .bit0 left, .bit1 right => .bit1 (add left right)
  | .bit1 left, .bit0 right => .bit1 (add left right)
  | .bit1 left, .bit1 right => .bit0 (add left right).succ

/-- Reading binary positive addition agrees with unary addition. -/
@[simp] theorem toNat_add (left right : BinaryPositive) :
    (add left right).toNat = left.toNat + right.toNat := by
  induction left generalizing right with
  | one => cases right <;> simp [add, toNat, toNat_succ] <;> omega
  | bit0 left ih => cases right <;> simp [add, toNat, ih] <;> omega
  | bit1 left ih => cases right <;> simp [add, toNat, toNat_succ, ih] <;> omega

/-- Multiplication on canonical positive binary numerals. -/
def mul : BinaryPositive → BinaryPositive → BinaryPositive
  | .one, right => right
  | .bit0 left, right => .bit0 (mul left right)
  | .bit1 left, right => add (.bit0 (mul left right)) right

/-- Reading binary positive multiplication agrees with unary multiplication. -/
@[simp] theorem toNat_mul (left right : BinaryPositive) :
    (mul left right).toNat = left.toNat * right.toNat := by
  induction left generalizing right with
  | one => simp [mul, toNat]
  | bit0 left ih => simp [mul, toNat, ih, Nat.mul_assoc]
  | bit1 left ih => simp [mul, toNat, ih, Nat.add_mul, Nat.mul_assoc]

/-- Unary reading distinguishes canonical positive binary numerals. -/
theorem toNat_injective : Function.Injective BinaryPositive.toNat := by
  intro left right equality
  induction left generalizing right with
  | one =>
      cases right with
      | one => rfl
      | bit0 digits =>
          have positive := digits.toNat_pos
          simp only [toNat] at equality
          omega
      | bit1 digits =>
          have positive := digits.toNat_pos
          simp only [toNat] at equality
          omega
  | bit0 left ih =>
      cases right with
      | one =>
          have positive := left.toNat_pos
          simp only [toNat] at equality
          omega
      | bit0 right =>
          apply congrArg BinaryPositive.bit0
          apply ih
          simp only [toNat] at equality
          omega
      | bit1 right =>
          simp only [toNat] at equality
          omega
  | bit1 left ih =>
      cases right with
      | one =>
          have positive := left.toNat_pos
          simp only [toNat] at equality
          omega
      | bit0 right =>
          simp only [toNat] at equality
          omega
      | bit1 right =>
          apply congrArg BinaryPositive.bit1
          apply ih
          simp only [toNat] at equality
          omega

/-- Decide strict order directly on canonical positive binary numerals. -/
def ltb : BinaryPositive → BinaryPositive → Bool
  | .one, .one => false
  | .one, .bit0 _ => true
  | .one, .bit1 _ => true
  | .bit0 _, .one => false
  | .bit1 _, .one => false
  | .bit0 left, .bit0 right => ltb left right
  | .bit1 left, .bit1 right => ltb left right
  | .bit0 left, .bit1 right => if left == right then true else ltb left right
  | .bit1 left, .bit0 right => if left == right then false else ltb left right

/-- Binary positive comparison returns true exactly when the unary readings are strictly ordered. -/
@[simp] theorem ltb_eq_true_iff (left right : BinaryPositive) :
    ltb left right = true ↔ left.toNat < right.toNat := by
  induction left generalizing right with
  | one =>
      cases right with
      | one => simp [ltb, toNat]
      | bit0 right =>
          have positive := right.toNat_pos
          simp [ltb, toNat]
          omega
      | bit1 right =>
          have positive := right.toNat_pos
          simp [ltb, toNat]
          omega
  | bit0 left ih =>
      cases right with
      | one =>
          have positive := left.toNat_pos
          simp [ltb, toNat]
          omega
      | bit0 right => simpa [ltb, toNat] using ih right
      | bit1 right =>
          by_cases heq : left = right
          · subst right
            simp [ltb, toNat]
          · have hneNat : left.toNat ≠ right.toNat := fun equality =>
              heq (toNat_injective equality)
            simp [ltb, toNat, heq, ih]
            omega
  | bit1 left ih =>
      cases right with
      | one => simp [ltb, toNat]
      | bit0 right =>
          by_cases heq : left = right
          · subst right
            simp [ltb, toNat]
          · simp [ltb, toNat, heq, ih]
            omega
      | bit1 right => simpa [ltb, toNat] using ih right

end BinaryPositive

/-- A canonical binary representation of nonnegative natural numbers. -/
inductive BinaryNat where
  /-- The binary representation of zero. -/
  | zero
  /-- A positive binary numeral viewed as a nonnegative numeral. -/
  | pos (value : BinaryPositive)
  deriving DecidableEq, Repr

namespace BinaryNat

/-- Read a binary natural number as a unary natural number. -/
def toNat : BinaryNat → Nat
  | .zero => 0
  | .pos value => value.toNat

/-- Successor on canonical binary natural numbers. -/
def succ : BinaryNat → BinaryNat
  | .zero => .pos .one
  | .pos value => .pos value.succ

/-- The canonical binary representation of one. -/
def one : BinaryNat :=
  .pos .one

/-- Reading binary zero produces unary zero. -/
@[simp] theorem toNat_zero : BinaryNat.zero.toNat = 0 :=
  rfl

/-- Reading binary successor agrees with unary successor. -/
@[simp] theorem toNat_succ (value : BinaryNat) : value.succ.toNat = Nat.succ value.toNat := by
  cases value with
  | zero => rfl
  | pos value => exact value.toNat_succ

/-- Reading binary one produces unary one. -/
@[simp] theorem toNat_one : one.toNat = 1 :=
  rfl

/-- Unary reading distinguishes canonical binary natural numbers. -/
theorem toNat_injective : Function.Injective BinaryNat.toNat := by
  intro left right equality
  cases left with
  | zero =>
      cases right with
      | zero => rfl
      | pos value =>
          have positive := value.toNat_pos
          simp only [toNat] at equality
          omega
  | pos left =>
      cases right with
      | zero =>
          have positive := left.toNat_pos
          simp only [toNat] at equality
          omega
      | pos right =>
          apply congrArg BinaryNat.pos
          exact BinaryPositive.toNat_injective equality

/-- Decide strict order directly on canonical binary natural numbers. -/
def ltb : BinaryNat → BinaryNat → Bool
  | .zero, .zero => false
  | .zero, .pos _ => true
  | .pos _, .zero => false
  | .pos left, .pos right => left.ltb right

/-- Binary natural comparison returns true exactly when the unary readings are strictly ordered. -/
@[simp] theorem ltb_eq_true_iff (left right : BinaryNat) :
    ltb left right = true ↔ left.toNat < right.toNat := by
  cases left with
  | zero =>
      cases right with
      | zero => simp [ltb, toNat]
      | pos right =>
          have positive := right.toNat_pos
          simp [ltb, toNat]
          omega
  | pos left =>
      cases right <;> simp [ltb, toNat]

/-- Encode a unary natural number as a canonical binary natural number. -/
def ofNat : Nat → BinaryNat
  | 0 => .zero
  | n + 1 => (ofNat n).succ

/-- Encoding unary zero produces binary zero. -/
@[simp] theorem ofNat_zero : ofNat 0 = .zero :=
  rfl

/-- Encoding unary successor agrees with binary successor. -/
@[simp] theorem ofNat_succ (n : Nat) : ofNat (Nat.succ n) = (ofNat n).succ :=
  rfl

/-- Unary decoding is a left inverse of binary encoding. -/
@[simp] theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ofNat_succ, toNat_succ, ih]

/-- Binary encoding is a left inverse of unary decoding. -/
@[simp] theorem ofNat_toNat (value : BinaryNat) : ofNat value.toNat = value := by
  apply BinaryNat.toNat_injective
  exact toNat_ofNat value.toNat

/-- Multiplication of canonical binary natural numbers. -/
def mul : BinaryNat → BinaryNat → BinaryNat
  | .zero, _ => .zero
  | _, .zero => .zero
  | .pos left, .pos right => .pos (left.mul right)

/-- Reading binary multiplication agrees with unary multiplication. -/
@[simp] theorem toNat_mul (left right : BinaryNat) :
    (mul left right).toNat = left.toNat * right.toNat := by
  cases left <;> cases right <;> simp [mul, toNat]

/-- The product of a list of canonical binary natural numbers. -/
def listProduct : List BinaryNat → BinaryNat
  | [] => one
  | value :: values => mul value (listProduct values)

/-- Reading a binary list product agrees with the unary list product. -/
@[simp] theorem toNat_listProduct (values : List BinaryNat) :
    (listProduct values).toNat = (values.map toNat).prod := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [listProduct, toNat_mul, List.map_cons, List.prod_cons, ih]

/-- Unary and canonical binary natural numbers are equivalent. -/
def natEquiv : Nat ≃ BinaryNat where
  toFun := ofNat
  invFun := toNat
  left_inv := toNat_ofNat
  right_inv := ofNat_toNat

end BinaryNat

/-- The standard unary natural-number interface. -/
def unaryNatSignature : NatSignature where
  Carrier := Nat
  zero := 0
  succ := Nat.succ

/-- The canonical binary natural-number interface. -/
def binaryNatSignature : NatSignature where
  Carrier := BinaryNat
  zero := .zero
  succ := BinaryNat.succ

/-- Unary-to-binary conversion is an equivalence of natural-number interfaces. -/
def unaryBinaryNatSignatureEquiv : NatSignatureEquiv unaryNatSignature binaryNatSignature where
  carrier := BinaryNat.natEquiv
  map_zero := rfl
  map_succ := BinaryNat.ofNat_succ

/-- The usual dependent eliminator for unary natural numbers. -/
def unaryNatEliminator : unaryNatSignature.Eliminator.{0, u} := by
  intro P hzero hsucc n
  induction n with
  | zero => exact hzero
  | succ n ih => exact hsucc n ih

/-- The unary eliminator transferred across the unary-to-binary interface equivalence. -/
def binaryNatEliminator : binaryNatSignature.Eliminator.{0, u} :=
  unaryBinaryNatSignatureEquiv.eliminator unaryNatEliminator

/-- Binary elimination recovers unary elimination from decoding compatibility and round-trip identity. -/
def unaryNatEliminatorOfBinary
    (eliminate : binaryNatSignature.Eliminator.{0, u}) :
    unaryNatSignature.Eliminator.{0, u} := by
  intro P hzero hsucc n
  have result : P (BinaryNat.toNat (BinaryNat.ofNat n)) :=
    eliminate (fun value => P value.toNat) hzero
      (fun value ih => BinaryNat.toNat_succ value ▸ hsucc value.toNat ih)
      (BinaryNat.ofNat n)
  simpa using result

example {P : BinaryNat → Sort u} (hzero : P .zero)
    (hsucc : ∀ n, P n → P n.succ) : ∀ n, P n :=
  binaryNatEliminator P hzero hsucc

example : BinaryNat.toNat BinaryNat.zero = 0 :=
  BinaryNat.toNat_zero

example (n : BinaryNat) : BinaryNat.toNat n.succ = Nat.succ (BinaryNat.toNat n) :=
  BinaryNat.toNat_succ n

example (n : Nat) : BinaryNat.toNat (BinaryNat.ofNat n) = n :=
  BinaryNat.toNat_ofNat n

example (eliminate : binaryNatSignature.Eliminator.{0, u}) :
    unaryNatSignature.Eliminator.{0, u} :=
  unaryNatEliminatorOfBinary eliminate

end DeepWiki.Refine
