import DeepWiki.ComputableAlgebra.PolyEngine

/-! # Representation-independent computable fractions

`CFrac F P` is the minimal fraction-representation interface: `F` stores a numerator and a nonzero
denominator in polynomial representation `P`. `PolyFrac P` is the canonical proof-carrying builder used
by the dense and sparse specializations. -/

namespace DeepWiki.SymbolicIntegration

universe u

/-- A computable fraction representation `F` backed by polynomial representation `P`. -/
class CFrac (F : (α : Type u) → [CField α] → Type u)
    (P : outParam (Type u → Type u)) [CPoly P] [CPolyEngine P] where
  /-- Read the stored numerator and denominator. -/
  toPair : {α : Type u} → [CField α] → F α → P α × P α
  /-- Build a fraction from a numerator and a denominator certified nonzero. -/
  ofPair : {α : Type u} → [CField α] → (num den : P α) →
    CPolyEngine.cisZero den = false → F α
  /-- Reading a constructed fraction returns the supplied pair. -/
  toPair_ofPair : ∀ {α : Type u} [CField α] (num den : P α)
    (h : CPolyEngine.cisZero den = false), toPair (ofPair num den h) = (num, den)
  /-- Every represented fraction stores a denominator certified nonzero. -/
  den_nonzero_impl : ∀ {α : Type u} [CField α] (x : F α),
    CPolyEngine.cisZero (toPair x).2 = false

/-- Canonical proof-carrying fractions over a polynomial representation `P`. -/
structure PolyFrac (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] where
  /-- Stored numerator polynomial. -/
  num : P α
  /-- Stored denominator polynomial. -/
  den : P α
  /-- The stored denominator is nonzero according to the polynomial engine. -/
  den_nonzero : CPolyEngine.cisZero den = false

/-- `PolyFrac P` implements the `CFrac` interface by structure projection and construction. -/
instance instCFracPolyFrac {P : Type u → Type u} [CPoly P] [CPolyEngine P] :
    CFrac (PolyFrac P) P where
  toPair x := (x.num, x.den)
  ofPair num den h := ⟨num, den, h⟩
  toPair_ofPair _ _ _ := rfl
  den_nonzero_impl x := x.den_nonzero

namespace CFrac

variable {F : (α : Type u) → [CField α] → Type u}
variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CFrac F P]

/-- The numerator polynomial stored by a represented fraction. -/
def num {α : Type u} [CField α] (x : F α) : P α := (CFrac.toPair x).1

/-- The denominator polynomial stored by a represented fraction. -/
def den {α : Type u} [CField α] (x : F α) : P α := (CFrac.toPair x).2

/-- Build a represented fraction from numerator and certified-nonzero denominator polynomials. -/
def ofFraction {α : Type u} [CField α] (num den : P α)
    (h : CPolyEngine.cisZero den = false) : F α :=
  CFrac.ofPair num den h

/-- Build a represented fraction when the denominator passes the executable nonzero test. -/
def ofFraction? {α : Type u} [CField α] (num den : P α) : Option (F α) :=
  if h : CPolyEngine.cisZero den = false then some (CFrac.ofPair num den h) else none

/-- `ofFraction?` returns the certified fraction when the denominator is nonzero. -/
@[simp] theorem ofFraction?_eq_some {α : Type u} [CField α] (num den : P α)
    (h : CPolyEngine.cisZero den = false) :
    ofFraction? (F := F) num den = some (ofFraction num den h) := by
  simp [ofFraction?, h, ofFraction]

/-- `ofFraction?` rejects a denominator recognized as zero. -/
@[simp] theorem ofFraction?_eq_none {α : Type u} [CField α] (num den : P α)
    (h : CPolyEngine.cisZero den = true) : ofFraction? (F := F) num den = none := by
  simp [ofFraction?, h]

/-- The numerator of a constructed represented fraction is the supplied numerator. -/
@[simp] theorem num_ofFraction {α : Type u} [CField α] (a b : P α)
    (h : CPolyEngine.cisZero b = false) : num (ofFraction (F := F) a b h) = a := by
  rw [num, ofFraction, CFrac.toPair_ofPair]

/-- The denominator of a constructed represented fraction is the supplied denominator. -/
@[simp] theorem den_ofFraction {α : Type u} [CField α] (a b : P α)
    (h : CPolyEngine.cisZero b = false) : den (ofFraction (F := F) a b h) = b := by
  rw [den, ofFraction, CFrac.toPair_ofPair]

/-- A represented fraction's stored denominator passes its polynomial engine's nonzero test. -/
theorem den_nonzero {α : Type u} [CField α] (x : F α) :
    CPolyEngine.cisZero (den x) = false :=
  CFrac.den_nonzero_impl x

end CFrac

end DeepWiki.SymbolicIntegration
