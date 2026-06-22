import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.RatFunc.Basic
import DeepWiki.SymbolicIntegration.RationalFunctionDerivative
import DeepWiki.SymbolicIntegration.DifferentialFields

/-! # The Bernoulli partial-fraction / residue decomposition (Bronstein §2.1, simple-root case)
For a polynomial `A` of degree `< n` and `n` distinct points `s`, with `D = ∏_{α∈s}(X−α)` (squarefree,
so simple roots), the residue (Lagrange) decomposition is
`A = ∑_{α∈s} (A(α)/D'(α)) · (D/(X−α))`, i.e. dividing by `D`, the partial fraction
`A/D = ∑_{α∈s} (A(α)/D'(α)) / (X−α)` — the `∑_{α|D(α)=0}` sum underlying Bernoulli's algorithm (and the
Rothstein–Trager logarithmic part). Built from Mathlib's Lagrange interpolation (`nodal`, `nodalWeight`,
`basis`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-- **Bernoulli residue decomposition** (§2.1): for `A` of degree `< #s` and distinct points `s`,
with `D = ∏_{α∈s}(X−α) = Lagrange.nodal s id`, `A = ∑_{α∈s} (A(α)/D'(α))·(D/(X−α))`. Dividing by `D`
gives the simple-root partial fraction `A/D = ∑_{α∈s} (A(α)/D'(α))/(X−α)`; the coefficient
`A(α)/D'(α)` is the residue of `A/D` at `α`. -/
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

/-- **Bernoulli partial fraction in `K(x)`** (§2.1, eq 2.3 simple-root case): for `A` of degree `< #s`
and distinct `s`, with `D = ∏_{α∈s}(X−α)`, the rational function decomposes as
`A/D = ∑_{α∈s} (A(α)/D'(α))/(X−α)` — the sum over the roots of `D`, residue `A(α)/D'(α)` at each.
Since each `1/(X−α)` is a logarithmic derivative, `∫ A/D = ∑_{α∈s} (A(α)/D'(α))·log(X−α)`. -/
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
/-- **Bernoulli integral** (§2.1): `∫ A/D = ∑_{α∈s} (A(α)/D'(α))·log(X−α)` for squarefree
`D = ∏_{α∈s}(X−α)` and `deg A < #s`. Modeling `log(X−α)` by `L α` with `(L α)′ = 1/(X−α)`, the
derivative of `∑_{α∈s} (A(α)/D'(α))·L α` is the integrand `A/D` — by the partial fraction
`ratFunc_eq_sum_residue_div`, since each residue `A(α)/D'(α)` is a constant. -/
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

end DeepWiki.SymbolicIntegration
