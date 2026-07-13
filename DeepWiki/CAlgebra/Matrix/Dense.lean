import Mathlib.Data.List.Basic
import Mathlib.Algebra.GroupWithZero.Defs

/-! # Computable dense matrices (`DenseMatrix`) — carrier

`DenseMatrix R` stores a matrix as a list of rows; `entry` reads a coefficient (out-of-range → `0`)
and `ofFn` builds one from an entry function. Its Mathlib correspondence (`toMatrix` into
`Matrix (Fin n) (Fin m) R`) lives in `MatrixBridge/Basic.lean`, keeping this core correspondence-free. -/

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

end DenseMatrix

end DeepWiki.CAlgebra
