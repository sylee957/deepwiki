import DeepWiki.SymbolicIntegration.Computable.FractionFieldDeriv
import DeepWiki.SymbolicIntegration.MonomialExtensions

/-! # Linear-factor support for residue matching

Reusable facts about the linear factor `X - C α`: its monomial log-derivative, root evaluation of
`implicitDeriv`, and the `divByMonic` quotient formulas used by residue-match decompositions. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

namespace ResidueMatchTower

variable {K : Type*} [Field K] [Differential K]

/-- The monomial log-derivative of a linear factor: over `extendDeriv (implicitDeriv v)`,
`D(t−α)/(t−α) = algebraMap(v − C α′) / algebraMap(t − α)` in `RatFunc K`. -/
theorem extendDeriv_implicitDeriv_logDeriv_X_sub_C [Algebra ℚ K] (v : K[X]) (α : K) :
    extendDeriv (Differential.implicitDeriv v) (algebraMap K[X] (RatFunc K) (X - C α))
        / algebraMap K[X] (RatFunc K) (X - C α)
      = algebraMap K[X] (RatFunc K) (v - C (α′)) / algebraMap K[X] (RatFunc K) (X - C α) := by
  rw [extendDeriv_logDeriv, implicitDeriv_X_sub_C]

/-- `eval` of `mapCoeffs d` at a root of `d`: for `d(α) = 0`,
`(mapCoeffs d)(α) = −d′(α)·α′` over a differential field `K`. -/
theorem eval_mapCoeffs_of_isRoot (d : K[X]) (α : K) (hα : d.eval α = 0) :
    (Differential.mapCoeffs d).eval α = -((derivative d).eval α * α′) := by
  have h := Differential.deriv_aeval_eq (A := K) (R := K) α d
  simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] at h
  rw [hα] at h
  rw [show (0 : K)′ = 0 from map_zero _] at h
  linear_combination -h

/-- The absorption identity at a simple root: for `d(α) = 0`, the monomial derivative
`Dd = implicitDeriv v d` evaluates to `(Dd)(α) = d′(α)·(v(α) − α′)`. -/
theorem eval_implicitDeriv_of_isRoot (v d : K[X]) (α : K) (hα : d.eval α = 0) :
    (Differential.implicitDeriv v d).eval α = (derivative d).eval α * (v.eval α - α′) := by
  rw [Differential.implicitDeriv]
  simp only [Derivation.add_apply, Derivation.coe_smul, Pi.smul_apply, smul_eq_mul,
    Derivation.coe_restrictScalars, derivative'_apply, eval_add, eval_mul]
  rw [eval_mapCoeffs_of_isRoot d α hα]
  ring

omit [Differential K] in
/-- Polynomial over a linear factor splits off its quotient and a simple pole: in `RatFunc K`,
`algebraMap p / algebraMap (X − C α) =
  algebraMap(p /ₘ (X − C α)) + algebraMap(C(p.eval α))/algebraMap(X − C α)`. -/
theorem algebraMap_div_X_sub_C_split (p : K[X]) (α : K) :
    algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) (X - C α)
      = algebraMap K[X] (RatFunc K) (p /ₘ (X - C α))
        + algebraMap K[X] (RatFunc K) (C (p.eval α)) / algebraMap K[X] (RatFunc K) (X - C α) := by
  have hsplit : (p : K[X]) = (X - C α) * (p /ₘ (X - C α)) + C (p.eval α) := by
    have := modByMonic_add_div p (X - C α)
    rw [modByMonic_X_sub_C_eq_C_eval] at this
    linear_combination -this
  have hXα : algebraMap K[X] (RatFunc K) (X - C α) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero α)
  have hmap : algebraMap K[X] (RatFunc K) p
      = algebraMap K[X] (RatFunc K) (X - C α) * algebraMap K[X] (RatFunc K) (p /ₘ (X - C α))
        + algebraMap K[X] (RatFunc K) (C (p.eval α)) := by
    rw [← map_mul, ← map_add]; exact congrArg _ hsplit
  rw [hmap]
  field_simp

omit [Differential K] in
/-- The hyperexp polynomial part is the constant `C b`:
`(C b·X − C e) /ₘ (X − C a) = C b` over a field. -/
theorem divByMonic_C_mul_X_sub_C (b e a : K) :
    (C b * X - C e) /ₘ (X - C a) = C b := by
  refine (div_modByMonic_unique (C b) (C (b * a - e)) (monic_X_sub_C a) ⟨?_, ?_⟩).1
  · rw [map_sub, map_mul]; ring
  · rw [degree_X_sub_C]
    exact lt_of_le_of_lt degree_C_le (by decide)

/-! ### Axiom audit -/

#print axioms ResidueMatchTower.extendDeriv_implicitDeriv_logDeriv_X_sub_C
#print axioms ResidueMatchTower.eval_mapCoeffs_of_isRoot
#print axioms ResidueMatchTower.eval_implicitDeriv_of_isRoot
#print axioms ResidueMatchTower.algebraMap_div_X_sub_C_split
#print axioms ResidueMatchTower.divByMonic_C_mul_X_sub_C

end ResidueMatchTower

end DeepWiki.SymbolicIntegration
