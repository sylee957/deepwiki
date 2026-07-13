import DeepWiki.CAlgebra.Matrix.Dense
import DeepWiki.CAlgebra.Poly.Operations

/-! # Computable Sylvester matrix — carrier

`sylvester p q m n` is the `DenseMatrix` whose first `m` columns hold `q` shifted and last `n` hold
`p` shifted — the matrix whose determinant is the resultant. Its Mathlib correspondence
(`toMatrix_sylvester`) and the resultant live in `MatrixBridge/Basic.lean`. -/

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

/-- Computable Sylvester matrix of `p, q` with block widths `m` (for `p`) and `n` (for `q`). -/
def sylvester (p q : DensePoly R) (m n : Nat) : DenseMatrix R :=
  DenseMatrix.ofFn (m + n) (m + n) fun i j =>
    if j < m then (if j ≤ i ∧ i ≤ j + n then q.coeff (i - j) else 0)
    else (if (j - m) ≤ i ∧ i ≤ (j - m) + m then p.coeff (i - (j - m)) else 0)

end DeepWiki.CAlgebra
