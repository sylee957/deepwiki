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

/-- The Bézout cofactor `Cᵢ` of `Dᵢ'` in `Dᵢ'·Cᵢ + Dᵢ·(…) = 1`, so `Cᵢ·Dᵢ' ≡ 1 (mod Dᵢ)`. -/
noncomputable def bezoutDeriv (Di : K[X]) : K[X] :=
  (diophantineSolve (derivative Di) Di 1).1

/-- The `Cᵢ` congruence: for `IsCoprime Dᵢ' Dᵢ`, `(bezoutDeriv Di * derivative Di) %ₘ Di = 1 %ₘ Di`. -/
theorem bezoutDeriv_mul_derivative_modByMonic (Di : K[X]) (hDi : Di.Monic)
    (hcop : IsCoprime (derivative Di) Di) :
    (bezoutDeriv Di * derivative Di) %ₘ Di = (1 : K[X]) %ₘ Di := by
  have hspec := diophantineSolve_spec hcop (1 : K[X])
  have hkey : bezoutDeriv Di * derivative Di
      = (1 : K[X]) - Di * (diophantineSolve (derivative Di) Di 1).2 := by
    rw [bezoutDeriv]; linear_combination hspec
  rw [hkey, sub_modByMonic, self_mul_modByMonic hDi, sub_zero]

/-- `Cᵢ(α)·Dᵢ'(α) = 1` at a root `α` of the monic `Dᵢ` (so `Cᵢ(α) = 1/Dᵢ'(α)`). -/
theorem bezoutDeriv_mul_derivative_eval {Di : K[X]} {α : K} (hDi : Di.Monic)
    (hα : Di.eval α = 0) (hcop : IsCoprime (derivative Di) Di) :
    (bezoutDeriv Di).eval α * (derivative Di).eval α = 1 := by
  have h := bezoutDeriv_mul_derivative_modByMonic Di hDi hcop
  have := congrArg (fun p => p.eval α) h
  simpa [eval_modByMonic_of_root hDi hα, Polynomial.eval_mul] using this

end DeepWiki.SymbolicIntegration
