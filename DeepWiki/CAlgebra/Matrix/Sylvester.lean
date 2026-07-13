import DeepWiki.CAlgebra.Matrix.Dense
import DeepWiki.CAlgebra.PolyBridge.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Computable Sylvester matrix

`sylvester p q m n` is the computable `DenseMatrix` whose Mathlib bridge is
`Polynomial.sylvester`: the first `m` columns hold `q` shifted, the last `n` hold `p` shifted. This is
the matrix whose determinant is the resultant (Phase 3c). -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

/-- Computable Sylvester matrix of `p, q` with block widths `m` (for `p`) and `n` (for `q`). -/
def sylvester (p q : DensePoly R) (m n : Nat) : DenseMatrix R :=
  DenseMatrix.ofFn (m + n) (m + n) fun i j =>
    if j < m then (if j ≤ i ∧ i ≤ j + n then q.coeff (i - j) else 0)
    else (if (j - m) ≤ i ∧ i ≤ (j - m) + m then p.coeff (i - (j - m)) else 0)

/-- The computable Sylvester matrix bridges to Mathlib's `Polynomial.sylvester`. -/
theorem toMatrix_sylvester (p q : DensePoly R) (m n : Nat) :
    (sylvester p q m n).toMatrix (m + n) (m + n)
      = (toPolynomial p).sylvester (toPolynomial q) m n := by
  ext i j
  induction j using Fin.addCases with
  | left jl =>
      rw [DenseMatrix.toMatrix_apply, sylvester,
        DenseMatrix.entry_ofFn _ _ _ _ _ i.isLt (Fin.castAdd n jl).isLt,
        Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
      simp only [Fin.val_castAdd, jl.isLt, if_true, Set.mem_Icc, coeff_toPolynomial]
  | right jr =>
      rw [DenseMatrix.toMatrix_apply, sylvester,
        DenseMatrix.entry_ofFn _ _ _ _ _ i.isLt (Fin.natAdd m jr).isLt,
        Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
      have hm : ¬ (m + (jr : ℕ) < m) := by omega
      simp only [Fin.val_natAdd, hm, if_false, Nat.add_sub_cancel_left, Set.mem_Icc,
        coeff_toPolynomial]

end DeepWiki.CAlgebra
