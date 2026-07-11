import DeepWiki.ComputableAlgebra.PolyEngineCore

/-! # Representation-independent computable fractions

`CFrac F P` is the minimal fraction-representation interface: `F` stores a numerator and a nonzero
denominator in polynomial representation `P`. Concrete proof-carrying carriers live in the dense and
sparse representation modules. -/

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

/-- Laws for a `CFrac` representation's pair reader and certified constructor. -/
class LawfulCFrac (F : (α : Type u) → [CField α] → Type u)
    (P : outParam (Type u → Type u)) [CPoly P] [CPolyEngine P] [CFrac F P] : Prop where
  /-- Reading a constructed fraction returns the supplied pair. -/
  toPair_ofPair : ∀ {α : Type u} [CField α] (num den : P α)
    (h : CPolyEngine.cisZero den = false),
      CFrac.toPair (CFrac.ofPair (F := F) num den h) = (num, den)
  /-- Every represented fraction stores a denominator certified nonzero. -/
  den_nonzero_impl : ∀ {α : Type u} [CField α] (x : F α),
    CPolyEngine.cisZero (CFrac.toPair (F := F) x).2 = false
  /-- Rebuilding a represented fraction from its stored pair returns that fraction. -/
  ofPair_toPair : ∀ {α : Type u} [CField α] (x : F α),
    CFrac.ofPair (F := F) (CFrac.toPair x).1 (CFrac.toPair x).2 (den_nonzero_impl x) = x

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
    [LawfulCFrac F P] (h : CPolyEngine.cisZero b = false) : CFrac.num (ofFraction (F := F) a b h) = a := by
  rw [CFrac.num, ofFraction, LawfulCFrac.toPair_ofPair]

/-- The denominator of a constructed represented fraction is the supplied denominator. -/
@[simp] theorem den_ofFraction {α : Type u} [CField α] (a b : P α)
    [LawfulCFrac F P] (h : CPolyEngine.cisZero b = false) : CFrac.den (ofFraction (F := F) a b h) = b := by
  rw [CFrac.den, ofFraction, LawfulCFrac.toPair_ofPair]

/-- A represented fraction's stored denominator passes its polynomial engine's nonzero test. -/
theorem den_nonzero {α : Type u} [CField α] [LawfulCFrac F P] (x : F α) :
    CPolyEngine.cisZero (CFrac.den x) = false :=
  LawfulCFrac.den_nonzero_impl x

/-- Construction respects equality of certified numerator-denominator pairs. -/
private theorem ofPair_pair_congr {α : Type u} [CField α] (p q : P α × P α)
    (hp : CPolyEngine.cisZero p.2 = false) (hq : CPolyEngine.cisZero q.2 = false)
    (h : p = q) : CFrac.ofPair (F := F) p.1 p.2 hp = CFrac.ofPair (F := F) q.1 q.2 hq := by
  cases h
  rfl

/-- A represented fraction is determined by its stored numerator-denominator pair. -/
theorem ext {α : Type u} [CField α] {x y : F α}
    [LawfulCFrac F P] (h : CFrac.toPair x = CFrac.toPair y) : x = y := by
  calc
    x = CFrac.ofPair (CFrac.toPair x).1 (CFrac.toPair x).2 (LawfulCFrac.den_nonzero_impl x) :=
      (LawfulCFrac.ofPair_toPair x).symm
    _ = CFrac.ofPair (CFrac.toPair y).1 (CFrac.toPair y).2 (LawfulCFrac.den_nonzero_impl y) := by
      exact ofPair_pair_congr _ _ (LawfulCFrac.den_nonzero_impl x) (LawfulCFrac.den_nonzero_impl y) h
    _ = y := LawfulCFrac.ofPair_toPair y

/-- Rebuilding a fraction through the public readers is the identity. -/
@[simp] theorem ofFraction_num_den {α : Type u} [CField α] [LawfulCFrac F P] (x : F α) :
    ofFraction (F := F) (CFrac.num x) (CFrac.den x) (den_nonzero x) = x := by
  exact LawfulCFrac.ofPair_toPair x

end CFrac

end DeepWiki.SymbolicIntegration
