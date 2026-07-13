import Mathlib.Data.Matrix.Basic

/-! # Computable dense matrices (Hex-style carrier)

`DenseMatrix R` stores a matrix as a list of rows. `entry` reads a coefficient (out-of-range → `0`),
and `toMatrix` bridges to a Mathlib `Matrix (Fin n) (Fin m) R` of chosen dimensions, agreeing
entrywise by definition. This is the carrier the Bareiss fraction-free determinant (Phase 3b) and the
Sylvester resultant (Phase 3c) are built on. -/

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [Zero R]

/-- Computable dense matrix: `data` is the list of rows (each a list of entries). -/
structure DenseMatrix (R : Type u) where
  /-- The rows of the matrix, top to bottom. -/
  data : List (List R)

namespace DenseMatrix

/-- The number of stored rows. -/
def nrows (M : DenseMatrix R) : Nat := M.data.length

/-- The stored width of row `i` (0 when out of range). -/
def rowLen (M : DenseMatrix R) (i : Nat) : Nat := (M.data.getD i []).length

/-- Entry `(i, j)`, defaulting to `0` outside the stored data. -/
def entry (M : DenseMatrix R) (i j : Nat) : R := (M.data.getD i []).getD j (0 : R)

/-- Build a `DenseMatrix` from an entry function on `n × m` indices. -/
def ofFn (n m : Nat) (f : Nat → Nat → R) : DenseMatrix R :=
  ⟨(List.range n).map (fun i => (List.range m).map (fun j => f i j))⟩

@[simp] theorem entry_ofFn (n m : Nat) (f : Nat → Nat → R) (i j : Nat) (hi : i < n) (hj : j < m) :
    (ofFn n m f).entry i j = f i j := by
  simp only [entry, ofFn, List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some, List.getElem?_map]
  rw [List.getElem?_range hj]
  simp

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

end DeepWiki.CAlgebra
