import DeepWiki.ComputableAlgebra.PolyEuclidean
import DeepWiki.ComputableAlgebra.PolyEngine
import DeepWiki.ComputableAlgebra.PolyReprGcd

/-! # Representation-independent gcd-derived polynomial algorithms

Fraction-pair normalization and polynomial lcm select gcd and division through capability classes. -/

namespace DeepWiki.SymbolicIntegration

namespace CPoly

/-- Reduce a represented fraction pair to a monic-denominator form through selected gcd and division. -/
def normalizeFracPair {P : Type → Type} [CPoly P] [CPolyEngine P]
    [CPolyGcd P] [CPolyEuclidean P] {α : Type} [CField α]
    (num den : P α) : P α × P α :=
  if CPolyEngine.cisZero num then (CPoly.czero, CPoly.one)
  else
    let g := CPolyGcd.compute num den
    let num' := CPolyEuclidean.div num g
    let den' := CPolyEuclidean.div den g
    let s := CField.inv (CPolyEngine.clead den')
    (CPolyEngine.scale s num', CPolyEngine.scale s den')

/-- A zero numerator normalizes to the represented fraction `0/1`. -/
@[simp] theorem normalizeFracPair_of_cisZero {P : Type → Type} [CPoly P] [CPolyEngine P]
    [CPolyGcd P] [CPolyEuclidean P] {α : Type} [CField α] (num den : P α)
    (h : CPolyEngine.cisZero num = true) :
    normalizeFracPair num den = (CPoly.czero, CPoly.one) := by
  simp [normalizeFracPair, h]

/-- A numerator recognized as zero normalizes to `0/1`. -/
@[simp] theorem normalizeFracPair_of_isZero {P : Type → Type} [CPoly P] [CPolyEngine P]
    [CPolyGcd P] [CPolyEuclidean P] (num den : P ℚ)
    (h : CPolyEngine.cisZero num = true) :
    normalizeFracPair num den = (CPoly.czero, CPoly.one) := by
  simp [normalizeFracPair, h]

/-- Compute a monic polynomial lcm through the selected gcd and Euclidean-division capabilities. -/
def lcm {P : Type → Type} [CPoly P] [CPolyEngine P]
    [CPolyGcd P] [CPolyEuclidean P] {α : Type} [CField α] (p q : P α) : P α :=
  if CPolyEngine.cisZero p || CPolyEngine.cisZero q then CPoly.czero
  else CPolyEngine.cmonic
    (CPolyEuclidean.div (CPolyEngine.mul p q) (CPolyGcd.compute p q))

/-- The selected polynomial lcm is zero when its left input is zero. -/
@[simp] theorem lcm_eq_zero_of_left {P : Type → Type} [CPoly P] [CPolyEngine P]
    [CPolyGcd P] [CPolyEuclidean P] {α : Type} [CField α] (p q : P α)
    (h : CPolyEngine.cisZero p = true) : lcm p q = CPoly.czero := by
  simp [lcm, h]

/-- The selected polynomial lcm is zero when its right input is zero. -/
@[simp] theorem lcm_eq_zero_of_right {P : Type → Type} [CPoly P] [CPolyEngine P]
    [CPolyGcd P] [CPolyEuclidean P] {α : Type} [CField α] (p q : P α)
    (h : CPolyEngine.cisZero q = true) : lcm p q = CPoly.czero := by
  simp [lcm, h]

/-- A left input recognized as zero makes the selected lcm zero. -/
@[simp] theorem lcm_of_left_isZero {P : Type → Type} [CPoly P] [CPolyEngine P]
    [CPolyGcd P] [CPolyEuclidean P] {α : Type} [CField α] (p q : P α)
    (h : CPolyEngine.cisZero p = true) : lcm p q = CPoly.czero := by
  simp [lcm, h]

/-- A right input recognized as zero makes the selected lcm zero. -/
@[simp] theorem lcm_of_right_isZero {P : Type → Type} [CPoly P] [CPolyEngine P]
    [CPolyGcd P] [CPolyEuclidean P] {α : Type} [CField α] (p q : P α)
    (h : CPolyEngine.cisZero q = true) : lcm p q = CPoly.czero := by
  simp [lcm, h]

end CPoly

end DeepWiki.SymbolicIntegration
