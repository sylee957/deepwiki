import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.ComputableAlgebra.FracReprDense
import DeepWiki.ComputableAlgebra.FracReprSparse
import DeepWiki.ComputableAlgebra.PolyEuclidean
import DeepWiki.ComputableAlgebra.PolyEuclideanDense
import DeepWiki.ComputableAlgebra.PolyReprGcd

/-! # Representation-independent fraction reduction

`CFrac.reduce` cancels the selected polynomial gcd from a represented fraction through the abstract gcd
and Euclidean-division capabilities. Its denotation theorem is shared by dense and sparse fractions. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

namespace CFrac

variable {F : (α : Type u) → [CField α] → Type u}
variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CFrac F P]

/-- The selected common factor of a represented fraction's numerator and denominator. -/
def reduceGcd {α : Type u} [CField α] [CPolyGcd P α] (a : F α) : P α :=
  CPolyGcd.compute (num a) (den a)

/-- The selected common factor divides both stored fraction polynomials. -/
theorem toPoly_reduceGcd_dvd [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α]
    [CFieldSpec.{u,v} α] (a : F α) :
    CPoly.toPoly (reduceGcd a) ∣ CPoly.toPoly (num a) ∧
      CPoly.toPoly (reduceGcd a) ∣ CPoly.toPoly (den a) := by
  exact ⟨(LawfulCPolyGcd.compute_isGCD' (num a) (den a)).1,
    (LawfulCPolyGcd.compute_isGCD' (num a) (den a)).2.1⟩

/-- A represented fraction's selected common factor denotes a nonzero polynomial. -/
theorem toPoly_reduceGcd_ne_zero [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α]
    [CFieldSpec.{u,v} α] (a : F α) :
    CPoly.toPoly (reduceGcd a) ≠ 0 := by
  have hden : CPoly.toPoly (den a) ≠ 0 := toPoly_den_ne_zero_generic a
  intro hg
  exact hden (eq_zero_of_zero_dvd (hg ▸ (toPoly_reduceGcd_dvd a).2))

/-- The numerator after cancelling the selected common factor. -/
def reduceNum {α : Type u} [CField α] [CPolyGcd P α] [CPolyEuclidean P]
    (a : F α) : P α :=
  CPolyEuclidean.div (num a) (reduceGcd a)

/-- The denominator after cancelling the selected common factor. -/
def reduceDen {α : Type u} [CField α] [CPolyGcd P α] [CPolyEuclidean P]
    (a : F α) : P α :=
  CPolyEuclidean.div (den a) (reduceGcd a)

/-- Cancel the selected polynomial gcd and scale the result to a monic denominator. -/
def reduceMonic {α : Type u} [CField α] [CPolyGcd P α] [CPolyEuclidean P]
    (a : F α) : F α :=
  let num1 := reduceNum a
  let den1 := CPolyEngine.cnorm (reduceDen a)
  if CPolyEngine.cisZero den1 then a
  else
    let c := CField.inv (CPolyEngine.clead den1)
    let num2 := CPolyEngine.scale c num1
    let den2 := CPolyEngine.scale c den1
    if h : CPolyEngine.cisZero den2 = false then ofFraction num2 den2 h else a

/-- Read a polynomial-valued represented fraction through selected Euclidean division. -/
def polynomialQuotient [CPolyEuclidean P]
    {α : Type u} [CField α] (a : F α) : P α :=
  CPolyEuclidean.div (num a) (den a)

/-- An exactly divisible represented fraction is reconstructed by its polynomial quotient. -/
theorem toPoly_polynomialQuotient_mul [LawfulCPolyEngine.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a : F α)
    (hdvd : CPoly.toPoly (den a) ∣ CPoly.toPoly (num a)) :
    CPoly.toPoly (polynomialQuotient a) * CPoly.toPoly (den a) =
      CPoly.toPoly (num a) := by
  simpa only [polynomialQuotient, mul_comm] using
    (LawfulCPolyEuclidean.div_exact (num a) (den a)
      (toPoly_den_ne_zero_generic a) hdvd).symm

/-- Exact cancellation reconstructs the stored numerator. -/
theorem toPoly_reduceNum_mul [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P]
    [CFieldSpec.{u,v} α] (a : F α) :
    CPoly.toPoly (reduceNum a) * CPoly.toPoly (reduceGcd a) =
      CPoly.toPoly (num a) := by
  simpa only [reduceNum, mul_comm] using
    (LawfulCPolyEuclidean.div_exact (num a) (reduceGcd a)
      (toPoly_reduceGcd_ne_zero a) (toPoly_reduceGcd_dvd a).1).symm

/-- Exact cancellation reconstructs the stored denominator. -/
theorem toPoly_reduceDen_mul [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P]
    [CFieldSpec.{u,v} α] (a : F α) :
    CPoly.toPoly (reduceDen a) * CPoly.toPoly (reduceGcd a) =
      CPoly.toPoly (den a) := by
  simpa only [reduceDen, mul_comm] using
    (LawfulCPolyEuclidean.div_exact (den a) (reduceGcd a)
      (toPoly_reduceGcd_ne_zero a) (toPoly_reduceGcd_dvd a).2).symm

/-- The reduced denominator passes the representation's executable nonzero test. -/
theorem cisZero_reduceDen [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P]
    [CFieldSpec.{u,v} α] (a : F α) :
    CPolyEngine.cisZero (reduceDen a) = false := by
  rw [Bool.eq_false_iff, Ne, LawfulCPolyEngine.cisZero_iff]
  intro hz
  apply toPoly_den_ne_zero_generic a
  rw [← toPoly_reduceDen_mul a, hz, zero_mul]

/-- Cancel the selected polynomial gcd from a represented fraction. -/
def reduce {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] {α : Type u} [CField α] [CPolyGcd P α]
    [CPolyEuclidean P] [CFrac F P] (a : F α) : F α :=
  if h : CPolyEngine.cisZero (CFrac.reduceDen a) = false then
    CFrac.ofFraction (CFrac.reduceNum a) (CFrac.reduceDen a) h
  else a

/-- `CFrac.reduce` preserves the represented fraction's rational-function value. -/
@[denote] theorem toRatFunc_reduce
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CFrac F P]
    [CFieldSpec.{u,v} α] (a : F α) :
    CFrac.toRatFunc (CFrac.reduce a) = CFrac.toRatFunc a := by
  let G := CFrac.am α (CPoly.toPoly (CFrac.reduceGcd a))
  let Nq := CFrac.am α (CPoly.toPoly (CFrac.reduceNum a))
  let Dq := CFrac.am α (CPoly.toPoly (CFrac.reduceDen a))
  let N := CFrac.am α (CPoly.toPoly (CFrac.num a))
  let D := CFrac.am α (CPoly.toPoly (CFrac.den a))
  have hnum : Nq * G = N := by
    simp only [Nq, G, N, ← map_mul]
    exact congrArg _ (CFrac.toPoly_reduceNum_mul a)
  have hden : Dq * G = D := by
    simp only [Dq, G, D, ← map_mul]
    exact congrArg _ (CFrac.toPoly_reduceDen_mul a)
  have hGne : G ≠ 0 := CFrac.am_ne_zero (CFrac.toPoly_reduceGcd_ne_zero a)
  have hDne : D ≠ 0 := CFrac.am_ne_zero (CFrac.toPoly_den_ne_zero_generic a)
  have hDqne : Dq ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hden
    exact hDne hden.symm
  rw [CFrac.reduce, dif_pos (CFrac.cisZero_reduceDen a), CFrac.toRatFunc_ofFraction,
    CFrac.toRatFunc_eq_div]
  change Nq / Dq = N / D
  rw [div_eq_div_iff hDqne hDne, ← hnum, ← hden]
  ring

/-- The lawful reduced fraction stores the selected quotient numerator. -/
@[simp] theorem num_reduce
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CFrac F P]
    [CFieldSpec.{u,v} α] (a : F α) :
    num (reduce a) = reduceNum a := by
  rw [reduce, dif_pos (cisZero_reduceDen a), num_ofFraction]

/-- The lawful reduced fraction stores the selected quotient denominator. -/
@[simp] theorem den_reduce
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CFrac F P]
    [CFieldSpec.{u,v} α] (a : F α) :
    den (reduce a) = reduceDen a := by
  rw [reduce, dif_pos (cisZero_reduceDen a), den_ofFraction]

/-- `CFrac.reduce` preserves the represented fraction's Boolean zero test. -/
theorem isZero_reduce
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CFrac F P]
    [CFieldSpec.{u,v} α] (a : F α) :
    isZero (reduce a) = isZero a := by
  apply Bool.eq_iff_iff.mpr
  rw [isZero_iff_toRatFunc, isZero_iff_toRatFunc, toRatFunc_reduce]

/-- Monic-denominator reduction preserves the represented rational-function value. -/
@[denote] theorem toRatFunc_reduceMonic
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CFrac F P]
    [CFieldSpec.{u,v} α] (a : F α) :
    toRatFunc (reduceMonic a) = toRatFunc a := by
  rw [reduceMonic]
  split <;> rename_i hden1
  · rfl
  · dsimp only
    split <;> rename_i hden2
    · rw [toRatFunc_ofFraction]
      rw [LawfulCPolyEngine.toPoly_scale, LawfulCPolyEngine.toPoly_scale,
        LawfulCPolyEngine.toPoly_cnorm, map_mul, map_mul]
      let c := am α (Polynomial.C (CRingSpec.toR
        (CField.inv (CPolyEngine.clead (CPolyEngine.cnorm (reduceDen a))))))
      let Nq := am α (CPoly.toPoly (reduceNum a))
      let Dq := am α (CPoly.toPoly (reduceDen a))
      change c * Nq / (c * Dq) = toRatFunc a
      have hcCoeff : CRingSpec.toR
          (CField.inv (CPolyEngine.clead (CPolyEngine.cnorm (reduceDen a)))) ≠ 0 := by
        change CFieldSpec.toK
            (CField.inv (CPolyEngine.clead (CPolyEngine.cnorm (reduceDen a)))) ≠ 0
        rw [CFieldSpec.toK_inv]
        apply inv_ne_zero
        change CRingSpec.toR
          (CPolyEngine.clead (CPolyEngine.cnorm (reduceDen a))) ≠ 0
        rw [LawfulCPolyEngine.toR_clead_eq_leadingCoeff,
          LawfulCPolyEngine.toPoly_cnorm]
        exact Polynomial.leadingCoeff_ne_zero.mpr (by
          intro hz
          apply hden1
          exact (LawfulCPolyEngine.cisZero_iff
            (CPolyEngine.cnorm (reduceDen a))).mpr (by
              rw [LawfulCPolyEngine.toPoly_cnorm, hz]))
      have hc : c ≠ 0 := am_ne_zero (Polynomial.C_ne_zero.mpr hcCoeff)
      rw [mul_div_mul_left _ _ hc]
      have hreduce := toRatFunc_reduce a
      rw [reduce, dif_pos (cisZero_reduceDen a), toRatFunc_ofFraction] at hreduce
      exact hreduce
    · rfl

/-- Monic-denominator reduction preserves the represented fraction's Boolean zero test. -/
theorem isZero_reduceMonic
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CFrac F P]
    [CFieldSpec.{u,v} α] (a : F α) :
    isZero (reduceMonic a) = isZero a := by
  apply Bool.eq_iff_iff.mpr
  rw [isZero_iff_toRatFunc, isZero_iff_toRatFunc, toRatFunc_reduceMonic]

end CFrac

/-! Both dense and sparse specializations resolve the same reducer and denotation law. -/

example {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a : DenseFrac α) :
    CFrac.toRatFunc (CFrac.reduce a) = CFrac.toRatFunc a :=
  CFrac.toRatFunc_reduce a

example {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a : DenseFrac α) :
    CFrac.toRatFunc (CFrac.reduceMonic a) = CFrac.toRatFunc a :=
  CFrac.toRatFunc_reduceMonic a

example {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a : SparseFrac α) :
    CFrac.toRatFunc (CFrac.reduce a) = CFrac.toRatFunc a :=
  CFrac.toRatFunc_reduce a

example {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a : SparseFrac α) :
    CFrac.toRatFunc (CFrac.reduceMonic a) = CFrac.toRatFunc a :=
  CFrac.toRatFunc_reduceMonic a

example {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a : SparseFrac α)
    (hdvd : CPoly.toPoly (CFrac.den a) ∣ CPoly.toPoly (CFrac.num a)) :
    CPoly.toPoly (CFrac.polynomialQuotient a) * CPoly.toPoly (CFrac.den a) =
      CPoly.toPoly (CFrac.num a) :=
  CFrac.toPoly_polynomialQuotient_mul a hdvd

end DeepWiki.SymbolicIntegration
