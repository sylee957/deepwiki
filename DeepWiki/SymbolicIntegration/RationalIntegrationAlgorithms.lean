import DeepWiki.SymbolicIntegration.RationalIntegration
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Algebra.Polynomial.Degree.Units

/-! # Rational-function integration algorithms — functional form (Bronstein §2.1–§2.2)
The book's integration *algorithms* (Bernoulli, Hermite, Horowitz–Ostrogradsky, Rothstein–Trager,
Lazard–Rioboo–Trager) are formalized as ordinary functional Lean `def`s over `K[X]` paired with a
correctness theorem, rather than via an operational-semantics interpreter. This file starts the
shared kernel: the extended-Euclidean **Diophantine solver** `aB + bC = c` for coprime `a, b`, the
inner step of partial-fraction (§2.1) and Hermite (§2.2) reduction. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open Classical in
/-- **Diophantine solver** (the extended-Euclidean inner step of §2.1/§2.2): for `a, b ∈ K[X]`,
return `(B, C)` with `a·B + b·C = c` whenever `a, b` are coprime, computed from the Bézout
coefficients `gcdA/gcdB` scaled by the inverse of the (constant, unit) `gcd a b`. -/
noncomputable def diophantineSolve (a b c : K[X]) : K[X] × K[X] :=
  (c * EuclideanDomain.gcdA a b * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹,
   c * EuclideanDomain.gcdB a b * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹)

open Classical in
/-- **Correctness of `diophantineSolve`**: for coprime `a, b`, the returned pair `(B, C)` solves the
Bézout/Diophantine equation `a·B + b·C = c`. -/
theorem diophantineSolve_spec {a b : K[X]} (hab : IsCoprime a b) (c : K[X]) :
    a * (diophantineSolve a b c).1 + b * (diophantineSolve a b c).2 = c := by
  have hg : IsUnit (EuclideanDomain.gcd a b) := EuclideanDomain.gcd_isUnit_iff.mpr hab
  have hdeg : (EuclideanDomain.gcd a b).natDegree = 0 := natDegree_eq_zero_of_isUnit hg
  have hgC : EuclideanDomain.gcd a b = C ((EuclideanDomain.gcd a b).coeff 0) :=
    eq_C_of_natDegree_eq_zero hdeg
  have hr0 : (EuclideanDomain.gcd a b).coeff 0 ≠ 0 := fun h =>
    hg.ne_zero (by rw [hgC, h, map_zero])
  simp only [diophantineSolve]
  have step : a * (c * EuclideanDomain.gcdA a b * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹)
        + b * (c * EuclideanDomain.gcdB a b * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹)
      = c * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹
        * (a * EuclideanDomain.gcdA a b + b * EuclideanDomain.gcdB a b) := by ring
  rw [step, ← EuclideanDomain.gcd_eq_gcd_ab, mul_assoc]
  nth_rewrite 2 [hgC]
  rw [← map_mul, inv_mul_cancel₀ hr0, map_one, mul_one]

end DeepWiki.SymbolicIntegration
