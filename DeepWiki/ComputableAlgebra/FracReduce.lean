import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.ComputableAlgebra.PolyEuclidean
import DeepWiki.ComputableAlgebra.PolyReprGcd

/-! # Representation-independent fraction reduction

`qReduce` cancels the selected polynomial gcd from a represented fraction through the abstract gcd
and Euclidean-division capabilities. Its denotation theorem is shared by dense and sparse fractions. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

namespace CFrac

variable {F : (α : Type u) → [CField α] → Type u}
variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CFrac F P]

/-- The selected common factor of a represented fraction's numerator and denominator. -/
def reduceGcd [CPolyGcd P] {α : Type u} [CField α] (a : F α) : P α :=
  CPolyGcd.compute (num a) (den a)

/-- The selected common factor divides both stored fraction polynomials. -/
theorem toPoly_reduceGcd_dvd [LawfulCPolyEngine.{u,v} P]
    [CPolyGcd P] [LawfulCPolyGcd.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a : F α) :
    CPoly.toPoly (reduceGcd a) ∣ CPoly.toPoly (num a) ∧
      CPoly.toPoly (reduceGcd a) ∣ CPoly.toPoly (den a) := by
  exact ⟨(LawfulCPolyGcd.compute_isGCD' (num a) (den a)).1,
    (LawfulCPolyGcd.compute_isGCD' (num a) (den a)).2.1⟩

/-- A represented fraction's selected common factor denotes a nonzero polynomial. -/
theorem toPoly_reduceGcd_ne_zero [LawfulCPolyEngine.{u,v} P]
    [CPolyGcd P] [LawfulCPolyGcd.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a : F α) :
    CPoly.toPoly (reduceGcd a) ≠ 0 := by
  have hden : CPoly.toPoly (den a) ≠ 0 := toPoly_den_ne_zero_generic a
  intro hg
  exact hden (eq_zero_of_zero_dvd (hg ▸ (toPoly_reduceGcd_dvd a).2))

/-- The numerator after cancelling the selected common factor. -/
def reduceNum [CPolyGcd P] [CPolyEuclidean P]
    {α : Type u} [CField α] (a : F α) : P α :=
  CPolyEuclidean.div (num a) (reduceGcd a)

/-- The denominator after cancelling the selected common factor. -/
def reduceDen [CPolyGcd P] [CPolyEuclidean P]
    {α : Type u} [CField α] (a : F α) : P α :=
  CPolyEuclidean.div (den a) (reduceGcd a)

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
    [CPolyGcd P] [LawfulCPolyGcd.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a : F α) :
    CPoly.toPoly (reduceNum a) * CPoly.toPoly (reduceGcd a) =
      CPoly.toPoly (num a) := by
  simpa only [reduceNum, mul_comm] using
    (LawfulCPolyEuclidean.div_exact (num a) (reduceGcd a)
      (toPoly_reduceGcd_ne_zero a) (toPoly_reduceGcd_dvd a).1).symm

/-- Exact cancellation reconstructs the stored denominator. -/
theorem toPoly_reduceDen_mul [LawfulCPolyEngine.{u,v} P]
    [CPolyGcd P] [LawfulCPolyGcd.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a : F α) :
    CPoly.toPoly (reduceDen a) * CPoly.toPoly (reduceGcd a) =
      CPoly.toPoly (den a) := by
  simpa only [reduceDen, mul_comm] using
    (LawfulCPolyEuclidean.div_exact (den a) (reduceGcd a)
      (toPoly_reduceGcd_ne_zero a) (toPoly_reduceGcd_dvd a).2).symm

/-- The reduced denominator passes the representation's executable nonzero test. -/
theorem cisZero_reduceDen [LawfulCPolyEngine.{u,v} P]
    [CPolyGcd P] [LawfulCPolyGcd.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a : F α) :
    CPolyEngine.cisZero (reduceDen a) = false := by
  rw [Bool.eq_false_iff, Ne, LawfulCPolyEngine.cisZero_iff]
  intro hz
  apply toPoly_den_ne_zero_generic a
  rw [← toPoly_reduceDen_mul a, hz, zero_mul]

end CFrac

/-- Cancel the selected polynomial gcd from a represented fraction. -/
def qReduce {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    [CPolyGcd P] [LawfulCPolyGcd.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CFrac F P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a : F α) : F α :=
  CFrac.ofFraction (CFrac.reduceNum a) (CFrac.reduceDen a) (CFrac.cisZero_reduceDen a)

/-- `qReduce` preserves the represented fraction's rational-function value. -/
@[denote] theorem toRatFunc_qReduce
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    [CPolyGcd P] [LawfulCPolyGcd.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CFrac F P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a : F α) :
    CFrac.toRatFunc (qReduce a) = CFrac.toRatFunc a := by
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
  rw [qReduce, CFrac.toRatFunc_ofFraction, CFrac.toRatFunc_eq_div]
  change Nq / Dq = N / D
  rw [div_eq_div_iff hDqne hDne, ← hnum, ← hden]
  ring

namespace CFrac

/-- `qReduce` preserves the represented fraction's Boolean zero test. -/
theorem isZero_qReduce
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    [CPolyGcd P] [LawfulCPolyGcd.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P] [CFrac F P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a : F α) :
    isZero (qReduce a) = isZero a := by
  apply Bool.eq_iff_iff.mpr
  rw [isZero_iff_toRatFunc, isZero_iff_toRatFunc, toRatFunc_qReduce]

end CFrac

/-! The sparse specialization resolves the same reducer and denotation law without a dense adapter. -/

example {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a : SparseFrac α) :
    CFrac.toRatFunc (qReduce a) = CFrac.toRatFunc a :=
  toRatFunc_qReduce a

example {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a : SparseFrac α)
    (hdvd : CPoly.toPoly (CFrac.den a) ∣ CPoly.toPoly (CFrac.num a)) :
    CPoly.toPoly (CFrac.polynomialQuotient a) * CPoly.toPoly (CFrac.den a) =
      CPoly.toPoly (CFrac.num a) :=
  CFrac.toPoly_polynomialQuotient_mul a hdvd

end DeepWiki.SymbolicIntegration
