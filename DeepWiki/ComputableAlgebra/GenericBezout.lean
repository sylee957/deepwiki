import DeepWiki.ComputableAlgebra.PolyInterpolateDense
import DeepWiki.ComputableAlgebra.PolyEngine
import DeepWiki.Algebra.PolynomialMatrixDegree
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Generic Bézout cofactors, resultant, and selected interpolation

The dense Lagrange implementation lives in `PolyInterpolateDense`; this module supplies its
representation-selected `CPoly.interpolate` wrapper, generic denotation satellites, and seed
resultants. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### Representation-selected interpolation output -/

namespace CPoly

universe u v

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
  {α : Type u} [CField α]

/-- Lagrange interpolation with its coefficient polynomial stored in representation `P`. -/
def interpolate (pts : List (α × α)) : P α :=
  CPolyEngine.ofCoeffList (DensePoly.cinterpolate pts)

/-- Dense selected interpolation is definitionally the existing dense interpolation algorithm. -/
@[simp] theorem interpolate_dense_eq (pts : List (α × α)) :
    interpolate (P := DensePoly) pts = DensePoly.cinterpolate pts := rfl

variable [CFieldSpec.{u,v} α] [LawfulCPolyEngine.{u,v} P]

/-- Selected interpolation denotes the same polynomial as the coefficient-list implementation. -/
@[denote] theorem toPoly_interpolate (pts : List (α × α)) :
    toPoly (interpolate (P := P) pts) = DensePoly.toPoly (DensePoly.cinterpolate pts) := by
  rw [interpolate, LawfulCPolyEngine.toPoly_ofCoeffList]

open scoped Classical in
/-- Selected interpolation evaluates to the sampled value at each distinct node. -/
theorem eval_toPoly_interpolate (pts : List (α × α))
    (hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup)
    {zk yk : α} (hmem : (zk, yk) ∈ pts) :
    (toPoly (interpolate (P := P) pts)).eval (CFieldSpec.toK zk) = CFieldSpec.toK yk := by
  rw [toPoly_interpolate]
  exact DensePoly.eval_toPolyG_cinterpolateG pts hnodup hmem

/-- A nonempty selected interpolant has degree strictly below the number of sample points. -/
theorem degree_toPoly_interpolate_lt (pts : List (α × α)) (hne : pts ≠ []) :
    (toPoly (interpolate (P := P) pts)).degree < (pts.length : WithBot ℕ) := by
  rw [toPoly_interpolate]
  exact DensePoly.degree_toPolyG_cinterpolateG_lt pts hne

end CPoly

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
