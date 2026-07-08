import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic
import DeepWiki.SymbolicIntegration.Core.Polynomial.Basic

/-! # Polynomial Diophantine solvers

Extended-Euclidean Bézout solvers and their degree-reduced variant for
polynomial identities.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open Classical in
/-- Extended-Euclidean solver returning cofactors for `a * B + b * C = c` when `a` and `b` are coprime. -/
noncomputable def diophantineSolve (a b c : K[X]) : K[X] × K[X] :=
  (c * EuclideanDomain.gcdA a b * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹,
   c * EuclideanDomain.gcdB a b * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹)

open Classical in
/-- For coprime `a` and `b`, `diophantineSolve a b c` solves `a * B + b * C = c`. -/
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

open Classical in
/-- Diophantine solver whose first cofactor is reduced modulo `b`. -/
noncomputable def diophantineSolveReduced (a b c : K[X]) : K[X] × K[X] :=
  ((diophantineSolve a b c).1 % b,
   (diophantineSolve a b c).2 + ((diophantineSolve a b c).1 / b) * a)

open Classical in
/-- For coprime `a` and `b`, `diophantineSolveReduced a b c` still solves `a * B + b * C = c`. -/
theorem diophantineSolveReduced_spec {a b : K[X]} (hab : IsCoprime a b) (c : K[X]) :
    a * (diophantineSolveReduced a b c).1 + b * (diophantineSolveReduced a b c).2 = c := by
  have hbase := diophantineSolve_spec hab c
  simp only [diophantineSolveReduced]
  have hdm : b * ((diophantineSolve a b c).1 / b) + (diophantineSolve a b c).1 % b
      = (diophantineSolve a b c).1 := EuclideanDomain.div_add_mod _ b
  linear_combination hbase + a * hdm

open Classical in
/-- The first cofactor returned by `diophantineSolveReduced` has degree below `b.degree` when `b ≠ 0`. -/
theorem diophantineSolveReduced_fst_degree_lt {a b : K[X]} (hb : b ≠ 0) (c : K[X]) :
    (diophantineSolveReduced a b c).1.degree < b.degree := by
  simp only [diophantineSolveReduced]
  exact Polynomial.degree_mod_lt _ hb

end DeepWiki.SymbolicIntegration
