import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.RatFunc.Basic
import DeepWiki.SymbolicIntegration.RationalFunctionDerivative
import DeepWiki.SymbolicIntegration.DifferentialAlgebra

/-! # Partial-fraction / residue decomposition (simple-root case)
For `A` of degree `< #s` and distinct points `s`, with `D = ∏_{α∈s}(X−α)`, the residue decomposition
`A/D = ∑_{α∈s} (A(α)/D'(α)) / (X−α)`, and its consequences for the logarithmic part of `∫ A/D`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-- Residue decomposition: for `deg A < #s` and `D = ∏_{α∈s}(X−α)`,
`A = ∑_{α∈s} (A(α)/D'(α))·(D/(X−α))`. -/
theorem eq_sum_residue_mul_nodal_div {K : Type*} [Field K] (s : Finset K) (A : K[X])
    (hA : A.degree < s.card) :
    A = ∑ α ∈ s, C (A.eval α / eval α (derivative (Lagrange.nodal s id)))
          * (Lagrange.nodal s id / (X - C α)) := by
  classical
  conv_lhs => rw [Lagrange.eq_interpolate (Set.injOn_id _) hA, Lagrange.interpolate_eq_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hd : eval i (derivative (Lagrange.nodal s id)) = ∏ j ∈ s.erase i, (i - j) := by
    have h := Lagrange.eval_nodal_derivative_eval_node_eq (s := s) (v := (id : K → K)) hi
    rw [Lagrange.eval_nodal] at h; simpa using h
  have hdiv : Lagrange.nodal s id / (X - C i) = ∏ j ∈ s.erase i, (X - C j) := by
    have h := Lagrange.nodal_erase_eq_nodal_div (s := s) (v := (id : K → K)) hi
    rw [Lagrange.nodal_eq] at h; simpa using h.symm
  simp only [id_eq]
  rw [hd, hdiv]

/-- Partial fraction in `K(x)`: for `deg A < #s` and `D = ∏_{α∈s}(X−α)`,
`A/D = ∑_{α∈s} (A(α)/D'(α))/(X−α)`. -/
theorem ratFunc_eq_sum_residue_div {K : Type*} [Field K] (s : Finset K) (A : K[X])
    (hA : A.degree < s.card) :
    (algebraMap K[X] (RatFunc K) A) / (algebraMap K[X] (RatFunc K) (Lagrange.nodal s id))
      = ∑ α ∈ s, algebraMap K[X] (RatFunc K)
            (C (A.eval α / eval α (derivative (Lagrange.nodal s id))))
          / algebraMap K[X] (RatFunc K) (X - C α) := by
  classical
  have hinj := RatFunc.algebraMap_injective K
  have hD0 : algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr Lagrange.nodal_ne_zero
  rw [div_eq_iff hD0, Finset.sum_mul]
  conv_lhs => rw [eq_sum_residue_mul_nodal_div s A hA, map_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hdvd : (X - C α) ∣ Lagrange.nodal s id := by
    rw [Lagrange.nodal_eq]; exact Finset.dvd_prod_of_mem _ hα
  have hXα : algebraMap K[X] (RatFunc K) (X - C α) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (X_sub_C_ne_zero α)
  have heq : algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
      = algebraMap K[X] (RatFunc K) (X - C α)
        * algebraMap K[X] (RatFunc K) (Lagrange.nodal s id / (X - C α)) := by
    rw [← map_mul, EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero α) hdvd]
  rw [map_mul, heq]
  field_simp

open scoped Differential in
/-- Integral: modeling `log(X−α)` by `L α` with `(L α)′ = 1/(X−α)`,
`(∑_{α∈s} (A(α)/D'(α))·L α)′ = A/D`. -/
theorem deriv_sum_residue_log {K : Type*} [Field K] (s : Finset K) (A : K[X])
    (hA : A.degree < s.card) (L : K → RatFunc K)
    (hL : ∀ α ∈ s, (L α)′ = (algebraMap K[X] (RatFunc K) (X - C α))⁻¹) :
    (∑ α ∈ s, algebraMap K[X] (RatFunc K)
          (C (A.eval α / eval α (derivative (Lagrange.nodal s id)))) * L α)′
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) := by
  rw [map_sum, ratFunc_eq_sum_residue_div s A hA]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hc : (algebraMap K[X] (RatFunc K)
      (C (A.eval α / eval α (derivative (Lagrange.nodal s id)))))′ = 0 := by
    rw [show (algebraMap K[X] (RatFunc K) _)′ = ratFuncDeriv _ from rfl,
      ratFuncDeriv_algebraMap, derivative_C, map_zero]
  rw [deriv_const_mul _ hc, hL α hα, ← div_eq_mul_inv]

open scoped Differential in
/-- Logarithmic part as a `logDeriv` sum: for `D = ∏_{α∈s}(X−α)` and `deg A < #s`,
`A/D = ∑_{α∈s} (A(α)/D'(α)) · logDeriv(X−α)`. -/
theorem ratFunc_eq_sum_residue_logDeriv {K : Type*} [Field K] (s : Finset K) (A : K[X])
    (hA : A.degree < s.card) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
      = ∑ α ∈ s, algebraMap K[X] (RatFunc K)
          (C (A.eval α / eval α (derivative (Lagrange.nodal s id))))
            * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C α)) := by
  rw [ratFunc_eq_sum_residue_div s A hA]
  refine Finset.sum_congr rfl fun α hα => ?_
  have ht : (algebraMap K[X] (RatFunc K) (X - C α))′ = 1 := by
    rw [show (algebraMap K[X] (RatFunc K) _)′ = ratFuncDeriv _ from rfl, ratFuncDeriv_algebraMap,
      derivative_sub, derivative_X, derivative_C, sub_zero, map_one]
  rw [Differential.logDeriv, ht, div_eq_mul_one_div]

open Classical in
open scoped Differential in
/-- Residue-grouped log sum: `A/D = ∑_{a} a · logDeriv(∏_{α : res(α)=a}(X−α))` over the distinct
residues `a = A(α)/D'(α)`. -/
theorem ratFunc_eq_sum_residue_grouped {K : Type*} [Field K] (s : Finset K) (A : K[X])
    (hA : A.degree < s.card) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
      = ∑ a ∈ s.image (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id))),
          algebraMap K[X] (RatFunc K) (C a)
            * Differential.logDeriv (algebraMap K[X] (RatFunc K)
                (∏ α ∈ s.filter (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id)) = a),
                  (X - C α))) := by
  set res : K → K := fun α => A.eval α / eval α (derivative (Lagrange.nodal s id)) with hres
  rw [ratFunc_eq_sum_residue_logDeriv s A hA,
    ← Finset.sum_fiberwise_of_maps_to (g := res) (t := s.image res)
      (fun α hα => Finset.mem_image_of_mem _ hα)
      (f := fun α => algebraMap K[X] (RatFunc K) (C (res α))
        * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C α)))]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hne : ∀ α ∈ s.filter (fun α => res α = a),
      algebraMap K[X] (RatFunc K) (X - C α) ≠ 0 :=
    fun α _ => (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero α)
  have hlog := logDeriv_prod_zpow (s.filter (fun α => res α = a))
    (fun α => algebraMap K[X] (RatFunc K) (X - C α)) (fun _ => 1) hne
  simp only [zpow_one, Int.cast_one, one_mul] at hlog
  rw [map_prod, hlog, Finset.mul_sum]
  exact Finset.sum_congr rfl fun α hα => by rw [(Finset.mem_filter.mp hα).2]

end DeepWiki.SymbolicIntegration
