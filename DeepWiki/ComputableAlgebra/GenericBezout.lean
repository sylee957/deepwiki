import DeepWiki.ComputableAlgebra.PolyInterpolateSparse
import DeepWiki.ComputableAlgebra.PolyEngine
import DeepWiki.Algebra.PolynomialMatrixDegree
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Generic Bézout cofactors, resultant, and selected interpolation

The representation-selected interpolation implementations live in `PolyInterpolateDense` and
`PolyInterpolateSparse`; this module supplies seed resultants. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The seed-generic abstract Rothstein-Trager resultant `R(z) = res_t(d, a - z*Dd)` -/

variable {K : Type*} [Field K]

/-- Seed-generic Rothstein-Trager resultant `R(z) = res_t(D, A - z*Dd) ∈ K[z]`: `D`, `A`, and `Dd`
lifted to `(K[z])[t]` and eliminating `t`, with formal `t`-degrees `(deg D, deg D)`. -/
noncomputable def rtResultantSeed (A D Dd : K[X]) : K[X] :=
  Polynomial.resultant (D.map (C : K →+* K[X]))
    (A.map (C : K →+* K[X]) - C Polynomial.X * Dd.map (C : K →+* K[X]))
    D.natDegree D.natDegree

/-- `(rtResultantSeed A D Dd).eval c = res_t(D, A - c*Dd)`: specialization at `z = c`. -/
theorem rtResultantSeed_eval (A D Dd : K[X]) (c : K) :
    (rtResultantSeed A D Dd).eval c
      = Polynomial.resultant D (A - C c * Dd) D.natDegree D.natDegree := by
  have hcomp : (Polynomial.evalRingHom c).comp (C : K →+* K[X]) = RingHom.id K := by
    ext k; simp
  show Polynomial.evalRingHom c (rtResultantSeed A D Dd) = _
  rw [rtResultantSeed, ← Polynomial.resultant_map_map]
  congr 1
  · rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C, hcomp,
      Polynomial.map_id]
    simp

/-- Restatement: the seed-generic abstract RT-resultant specializes at `z = c` to the parameter
resultant `res_t(D, A - c*Dd)`. -/
example (A D Dd : K[X]) (c : K) :
    (rtResultantSeed A D Dd).eval c
      = Polynomial.resultant D (A - C c * Dd) D.natDegree D.natDegree :=
  rtResultantSeed_eval A D Dd c

open Polynomial in
/-- `(rtResultantSeed A D Dd).natDegree ≤ D.natDegree`: degree in `z` bounded by `deg D`. -/
theorem natDegree_rtResultantSeed_le (A D Dd : K[X]) :
    (rtResultantSeed A D Dd).natDegree ≤ D.natDegree := by
  rw [rtResultantSeed, resultant]
  refine le_trans (natDegree_det_le_sum_col _
    (fun j => j.addCases (fun _ => 1) (fun _ => 0)) ?_) ?_
  · intro i j
    rw [Polynomial.sylvester, Matrix.of_apply]
    refine j.addCases (fun j₁ => ?_) (fun j₁ => ?_)
    · simp only [Fin.addCases_left]
      split_ifs with h
      · exact natDegree_coeff_map_sub_C_X_mul_map_le_one A Dd _
      · simp
    · simp only [Fin.addCases_right]
      split_ifs with h
      · rw [Polynomial.coeff_map, Polynomial.natDegree_C]
      · simp
  · rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
    rw [Finset.sum_eq_zero (fun i _ => by rw [Fin.addCases_right])]
    omega

end DeepWiki.SymbolicIntegration
