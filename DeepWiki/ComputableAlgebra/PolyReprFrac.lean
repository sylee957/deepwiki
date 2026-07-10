import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.ComputableAlgebra.PolyReprDivisionDegree
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

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] {α : Type u}

/-- Multiply two unchecked raw fraction pairs componentwise. -/
def mul [CField α] (x y : RawFrac α P) : RawFrac α P :=
  (CPolyEngine.mul x.1 y.1, CPolyEngine.mul x.2 y.2)

/-- Reduce a raw fraction to lowest terms by dividing numerator and denominator by their gcd. -/
def reduce [CField α] (x : RawFrac α P) : RawFrac α P :=
  let g := CPoly.cgcd x.1 x.2
  ⟨(CPoly.cdivmod x.1 g).1, (CPoly.cdivmod x.2 g).1⟩

section Denote

variable [LawfulCPolyEngine.{u,v} P] [CField α] [CFieldSpec.{u,v} α]

/-- Denotation of a raw represented fraction into `RatFunc`. -/
noncomputable def toRatFunc (x : RawFrac α P) : RatFunc (CRingSpec.R α) :=
  algebraMap (CRingSpec.R α)[X] (RatFunc (CRingSpec.R α)) (CPoly.toPoly x.1) /
    algebraMap (CRingSpec.R α)[X] (RatFunc (CRingSpec.R α)) (CPoly.toPoly x.2)

/-- Raw fraction multiplication realizes multiplication in `RatFunc`. -/
theorem toRatFunc_mul (x y : RawFrac α P) :
    toRatFunc (mul x y) = toRatFunc x * toRatFunc y := by
  simp only [toRatFunc, mul, LawfulCPolyEngine.toPoly_mul, map_mul]
  rw [div_mul_div_comm]

omit [CPolyEngine P] [LawfulCPolyEngine P] in
/-- Gcd reduction preserves a raw fraction's value when its denominator is nonzero. -/
theorem toRatFunc_reduce (x : RawFrac α P) (hden : ¬ CPoly.cisZero x.2 = true) :
    toRatFunc (reduce x) = toRatFunc x := by
  have hgn := (CPoly.cgcd_dvd x.1 x.2).1
  have hgd := (CPoly.cgcd_dvd x.1 x.2).2
  have hg : ¬ CPoly.cisZero (CPoly.cgcd x.1 x.2) = true := fun hz => by
    rw [(CPoly.cisZero_iff _).mp hz, zero_dvd_iff] at hgd
    exact hden ((CPoly.cisZero_iff _).mpr hgd)
  have hgne : CPoly.toPoly (CPoly.cgcd x.1 x.2) ≠ 0 := fun h =>
    hg ((CPoly.cisZero_iff _).mpr h)
  have hnum := CPoly.toPoly_mul_cdiv_of_dvd x.1 (CPoly.cgcd x.1 x.2) hg hgn
  have hden' := CPoly.toPoly_mul_cdiv_of_dvd x.2 (CPoly.cgcd x.1 x.2) hg hgd
  have hc : algebraMap (CRingSpec.R α)[X] (RatFunc (CRingSpec.R α))
      (CPoly.toPoly (CPoly.cgcd x.1 x.2)) ≠ 0 :=
    (map_ne_zero_iff _
      (IsFractionRing.injective (CRingSpec.R α)[X] (RatFunc (CRingSpec.R α)))).mpr hgne
  simp only [toRatFunc, reduce]
  rw [hnum, hden', map_mul, map_mul, mul_div_mul_left _ _ hc]

end Denote

end RawFrac

/-! ### Dense and sparse execution of the same raw fraction algorithms -/

example :
    RawFrac.mul (([1, 1], [1]) : RawFrac ℚ) (([1], [0, 1]) : RawFrac ℚ) = ([1, 1], [0, 1]) := by
  native_decide

example :
    (CPoly.cdeg (RawFrac.reduce (([-1, 0, 1], [-1, 1]) : RawFrac ℚ)).1,
      CPoly.cdeg (RawFrac.reduce (([-1, 0, 1], [-1, 1]) : RawFrac ℚ)).2) = (1, 0) := by
  native_decide

example :
    let x : RawFrac ℚ CPoly.SparsePoly :=
      (CPoly.SparsePoly.ofList [(0, 1), (1, 1)], CPoly.SparsePoly.ofList [(0, 1)])
    let y : RawFrac ℚ CPoly.SparsePoly :=
      (CPoly.SparsePoly.ofList [(0, 1)], CPoly.SparsePoly.ofList [(1, 1)])
    (CPolyEngine.cdeg (RawFrac.mul x y).1, CPolyEngine.cdeg (RawFrac.mul x y).2) = (1, 1) := by
  native_decide

end DeepWiki.SymbolicIntegration
