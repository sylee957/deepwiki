import DeepWiki.SymbolicIntegration.RationalIntegration
import DeepWiki.SymbolicIntegration.Residues
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory
import DeepWiki.Algebra.SubresultantSpec

/-! # Rothstein-Trager resultant primitives

Resultant and residue-gcd kernels for rational logarithmic terms.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- The Rothstein-Trager resultant `resultant_x(D, A - t * D')` as a polynomial in `t`. -/
noncomputable def rtResultant (A D : K[X]) : K[X] :=
  Polynomial.resultant (D.map (C : K →+* K[X]))
    (A.map (C : K →+* K[X]) - C Polynomial.X * (derivative D).map (C : K →+* K[X]))
    D.natDegree (D.natDegree - 1)

/-- The Rothstein–Trager second operand's coefficient at `deg D − 1` is nonzero — it
carries the `t`-linear term `−lc(D′)·t` (characteristic zero). -/
theorem rtResultant_operand_coeff_ne_zero [CharZero K] (A D : K[X])
    (hAD : A.natDegree < D.natDegree) :
    (A.map (C : K →+* K[X])
        - C Polynomial.X * (derivative D).map (C : K →+* K[X])).coeff (D.natDegree - 1)
      ≠ 0 := by
  have hD0 : D ≠ 0 := fun h => by simp [h] at hAD
  have hdne : (derivative D).coeff (D.natDegree - 1) ≠ 0 := by
    have he : D.natDegree - 1 + 1 = D.natDegree := by omega
    rw [Polynomial.coeff_derivative, he]
    refine mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hD0) ?_
    exact_mod_cast Nat.succ_ne_zero (D.natDegree - 1)
  rw [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C_mul,
    Polynomial.coeff_map]
  intro h
  have hX : Polynomial.X * C ((derivative D).coeff (D.natDegree - 1))
      = C (A.coeff (D.natDegree - 1)) := (sub_eq_zero.mp h).symm
  have hdeg := congrArg Polynomial.natDegree hX
  rw [Polynomial.natDegree_mul Polynomial.X_ne_zero
      (fun hc => hdne (by simpa [Polynomial.C_eq_zero] using hc)),
    Polynomial.natDegree_X, Polynomial.natDegree_C, Polynomial.natDegree_C] at hdeg
  omega

/-- The exact degree of the Rothstein–Trager second operand: for `deg A < deg D` in
characteristic zero, `deg_x (A.map C − C X · (D′).map C) = deg D − 1` — the top coefficient
carries the nonzero `t`-linear term `−lc(D′)·t`. -/
theorem natDegree_rtResultant_operand [CharZero K] (A D : K[X])
    (hAD : A.natDegree < D.natDegree) :
    (A.map (C : K →+* K[X])
        - C Polynomial.X * (derivative D).map (C : K →+* K[X])).natDegree
      = D.natDegree - 1 := by
  have hD0 : D ≠ 0 := fun h => by simp [h] at hAD
  have hupper : (A.map (C : K →+* K[X])
      - C Polynomial.X * (derivative D).map (C : K →+* K[X])).natDegree
        ≤ D.natDegree - 1 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective]
      omega
    · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective]
      exact Polynomial.natDegree_derivative_le D
  exact le_antisymm hupper
    (Polynomial.le_natDegree_of_ne_zero (rtResultant_operand_coeff_ne_zero A D hAD))

/-- Evaluating `rtResultant A D` at `a` gives `resultant_x(D, A - C a * D')`. -/
theorem rtResultant_eval (A D : K[X]) (a : K) :
    (rtResultant A D).eval a
      = Polynomial.resultant D (A - C a * derivative D) D.natDegree (D.natDegree - 1) := by
  have hcomp : (Polynomial.evalRingHom a).comp (C : K →+* K[X]) = RingHom.id K := by
    ext k; simp
  show Polynomial.evalRingHom a (rtResultant A D) = _
  rw [rtResultant, ← Polynomial.resultant_map_map]
  congr 1
  · rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C, hcomp,
      Polynomial.map_id]
    simp

open Classical in
/-- The residue gcd `gcd(D, A - C a * D')`. -/
noncomputable def rtLogGcd (A D : K[X]) (a : K) : K[X] :=
  gcd D (A - C a * derivative D)

open Classical in
/-- At a simple `D`-root, `rtLogGcd A D a` vanishes exactly when the residue of `A / D` is `a`. -/
theorem rtLogGcd_isRoot_iff (A D : K[X]) (a α : K) (hα : (derivative D).eval α ≠ 0) :
    (rtLogGcd A D a).IsRoot α ↔ (D.IsRoot α ∧ A.eval α / (derivative D).eval α = a) :=
  isRoot_gcd_iff_residue A D a α hα

/-- For separable `D`, roots of `rtResultant A D` are residues of `A / D`. -/
theorem rtResultant_eval_eq_zero_iff [IsAlgClosed K] (A D : K[X]) (hD : D.Separable) (a : K)
    (hdeg : (A - C a * derivative D).natDegree = D.natDegree - 1) :
    (rtResultant A D).eval a = 0 ↔ ∃ α, D.IsRoot α ∧ A.eval α / (derivative D).eval α = a := by
  rw [rtResultant_eval, ← hdeg, ← residue_iff_resultant_eq_zero A D hD a]

/-- `rtResultant A D` evaluates to a leading-coefficient factor times the product over roots of `D`. -/
theorem rtResultant_eval_eq_prod_roots [IsAlgClosed K] (A D : K[X]) (a : K)
    (hA : A.natDegree < D.natDegree) :
    (rtResultant A D).eval a
      = D.leadingCoeff ^ (D.natDegree - 1) *
        (D.roots.map (fun α => A.eval α - a * (derivative D).eval α)).prod := by
  have hg : (A - C a * derivative D).natDegree ≤ D.natDegree - 1 :=
    (natDegree_sub_le _ _).trans
      (max_le (by omega) ((natDegree_C_mul_le _ _).trans (natDegree_derivative_le D)))
  rw [rtResultant_eval, Polynomial.resultant_eq_prod_eval D (A - C a * derivative D)
    (D.natDegree - 1) hg (IsAlgClosed.splits D)]
  exact congrArg (D.leadingCoeff ^ (D.natDegree - 1) * ·)
    (congrArg Multiset.prod (Multiset.map_congr rfl (fun α _ => by simp [eval_sub, eval_mul, eval_C])))

end DeepWiki.SymbolicIntegration
