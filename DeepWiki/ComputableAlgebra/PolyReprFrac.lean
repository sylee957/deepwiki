import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.ComputableAlgebra.PolyReprDivisionDegree
import DeepWiki.ComputableAlgebra.PolyReprGcd
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Representation-generic raw fraction algorithms

`RawFrac α P` is the single raw numerator/denominator pair used by the fraction layer. This module adds
gcd reduction and `RatFunc` denotation to the representation-independent arithmetic from `Fraction.lean`.
The former parallel `GFrac` structure and arithmetic are retired. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

/-- An unchecked numerator/denominator pair retained only at algorithm boundaries. -/
abbrev RawFrac (α : Type u) (P : Type u → Type u := DensePoly) := P α × P α

namespace RawFrac

variable {P : Type u → Type u} [CPoly P] {α : Type u}

/-- Multiply two unchecked raw fraction pairs componentwise. -/
def mul [CPolyEngine P] [CField α] (x y : RawFrac α P) : RawFrac α P :=
  (CPolyEngine.mul x.1 y.1, CPolyEngine.mul x.2 y.2)

/-- Reduce a raw fraction to lowest terms by dividing numerator and denominator by their gcd. -/
def reduce [CPolyGcd P] [CField α] (x : RawFrac α P) : RawFrac α P :=
  let g : P α := CPolyGcd.compute (P := P) (α := α) x.1 x.2
  ⟨(CPoly.cdivmod x.1 g).1, (CPoly.cdivmod x.2 g).1⟩

section Denote

variable [CField α] [CFieldSpec.{u,v} α]

/-- Denotation of a raw represented fraction into `RatFunc`. -/
noncomputable def toRatFunc (x : RawFrac α P) : RatFunc (CRingSpec.R α) :=
  algebraMap (CRingSpec.R α)[X] (RatFunc (CRingSpec.R α)) (CPoly.toPoly x.1) /
    algebraMap (CRingSpec.R α)[X] (RatFunc (CRingSpec.R α)) (CPoly.toPoly x.2)

/-- Raw fraction multiplication realizes multiplication in `RatFunc`. -/
theorem toRatFunc_mul [CPolyEngine P] [LawfulCPolyEngine.{u,v} P] (x y : RawFrac α P) :
    toRatFunc (mul x y) = toRatFunc x * toRatFunc y := by
  simp only [toRatFunc, mul, LawfulCPolyEngine.toPoly_mul, map_mul]
  rw [div_mul_div_comm]

/-- Gcd reduction preserves a raw fraction's value when its denominator is nonzero. -/
theorem toRatFunc_reduce [CPolyGcd P] [LawfulCPolyGcd.{u,v} P]
    (x : RawFrac α P) (hden : ¬ CPoly.cisZero x.2 = true) :
    toRatFunc (reduce x) = toRatFunc x := by
  let g : P α := CPolyGcd.compute (P := P) (α := α) x.1 x.2
  have hG := LawfulCPolyGcd.compute_isGCD' (P := P) x.1 x.2
  have hgn : CPoly.toPoly g ∣ CPoly.toPoly x.1 := by simpa [g] using hG.1
  have hgd : CPoly.toPoly g ∣ CPoly.toPoly x.2 := by simpa [g] using hG.2.1
  have hg : ¬ CPoly.cisZero g = true := fun hz => by
    have hzero : CPoly.toPoly g = 0 :=
      (CPoly.cisZero_iff _).mp hz
    have hden0 : CPoly.toPoly x.2 = 0 := by
      apply zero_dvd_iff.mp
      rw [← hzero]
      exact hgd
    exact hden ((CPoly.cisZero_iff _).mpr hden0)
  have hgne : CPoly.toPoly g ≠ 0 := fun h =>
    hg ((CPoly.cisZero_iff _).mpr h)
  have hnum := CPoly.toPoly_mul_cdiv_of_dvd x.1 g hg hgn
  have hden' := CPoly.toPoly_mul_cdiv_of_dvd x.2 g hg hgd
  have hc : algebraMap (CRingSpec.R α)[X] (RatFunc (CRingSpec.R α))
      (CPoly.toPoly g) ≠ 0 :=
    (map_ne_zero_iff _
      (IsFractionRing.injective (CRingSpec.R α)[X] (RatFunc (CRingSpec.R α)))).mpr hgne
  simp only [toRatFunc, reduce]
  rw [hnum, hden', map_mul, map_mul, mul_div_mul_left _ _ hc]

end Denote

end RawFrac

end DeepWiki.SymbolicIntegration
