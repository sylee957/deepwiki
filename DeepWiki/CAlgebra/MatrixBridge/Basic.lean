import DeepWiki.CAlgebra.Matrix.Sylvester
import DeepWiki.CAlgebra.PolyBridge.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Mathlib bridge for the matrix layer

The Mathlib correspondence for `DenseMatrix`: `toMatrix` into `Matrix (Fin n) (Fin m) R`, the
Sylvester-matrix bridge to `Polynomial.sylvester`, and `resultant` (the Sylvester determinant)
bridged to `Polynomial.resultant`. Kept out of the `Matrix/` core so those stay
correspondence-free. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

namespace DenseMatrix

variable {R : Type u} [Zero R]

/-- Bridge to a Mathlib matrix of dimensions `n × m`: the entry function read through `Fin`. -/
def toMatrix (M : DenseMatrix R) (n m : Nat) : Matrix (Fin n) (Fin m) R :=
  Matrix.of fun i j => M.entry i j

/-- `toMatrix` reads entries through the dense `entry` function. -/
@[simp] theorem toMatrix_apply (M : DenseMatrix R) (n m : Nat) (i : Fin n) (j : Fin m) :
    M.toMatrix n m i j = M.entry i j := rfl

/-- The Mathlib bridge of an `ofFn` matrix is the entry function itself. -/
@[simp] theorem toMatrix_ofFn (n m : Nat) (f : Nat → Nat → R) (i : Fin n) (j : Fin m) :
    (ofFn n m f).toMatrix n m i j = f i j := by
  rw [toMatrix_apply, entry_ofFn n m f i j i.isLt j.isLt]

end DenseMatrix

variable {R : Type u} [CommRing R] [DecidableEq R]

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

/-- The resultant of `p, q`: the determinant of the Sylvester matrix. -/
def resultant (p q : DensePoly R) (m n : Nat) : R :=
  ((sylvester p q m n).toMatrix (m + n) (m + n)).det

/-- The computable resultant bridges to Mathlib's `Polynomial.resultant`. -/
theorem toPolynomial_resultant (p q : DensePoly R) (m n : Nat) :
    resultant p q m n = (toPolynomial p).resultant (toPolynomial q) m n := by
  rw [resultant, toMatrix_sylvester]
  rfl

/-- Validation: the computable resultant equals the Mathlib resultant of the bridged polynomials. -/
example (p q : DensePoly R) (m n : Nat) :
    resultant p q m n = Polynomial.resultant (toPolynomial p) (toPolynomial q) m n :=
  toPolynomial_resultant p q m n

end DeepWiki.CAlgebra
