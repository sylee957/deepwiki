import DeepWiki.ComputableAlgebra.PolyResultantDense
import DeepWiki.ComputableAlgebra.PolySubresultant
import DeepWiki.ComputableAlgebra.PolyInterpolateDense
import DeepWiki.ComputableAlgebra.PolyInterpolateSparse

/-! # Computable determinant + subresultant (L1 of the computable-LRT build)

`CPolySubresultant.det` is a generic `[CField α]` cofactor-expansion determinant on a row-list matrix.
`CPolySubresultant` selects the representation-independent Sylvester-submatrix algorithm, which builds one polynomial column
`Σ_i (scalar cofactor det)·tⁱ`, mirroring the abstract
`DeepWiki.SymbolicIntegration.subresultant`. Foundation for the symbolic (root-free) LRT log part — see
`docs/computable-lrt.md`. Validated by `ccompute`; abstract `toPoly` correctness layered later. -/

namespace DeepWiki.SymbolicIntegration

universe u

namespace DensePoly

variable {α : Type u} [CField α]

/-- The Sylvester matrix of `p` (degree-`< n` slots) and `q` (degree-`< m` slots) as an `(m+n)×(m+n)`
row-list matrix: `m` shifted rows of `p`'s coefficients then `n` shifted rows of `q`'s (coefficients low to
high within a row, padded with zeros). Used for the resultant/subresultant. -/
private def cSylvesterRows (p q : DensePoly α) (n m : ℕ) : List (List α) :=
  let pc : List α := (cnorm p)
  let qc : List α := (cnorm q)
  let width := m + n
  let shiftRow (coeffs : List α) (k : ℕ) : List α :=
    (List.replicate k CCommRing.zero ++ coeffs ++ List.replicate width CCommRing.zero).take width
  (List.range m).map (fun i => shiftRow pc i) ++ (List.range n).map (fun i => shiftRow qc i)

end DensePoly

/-! ### Validation (`ccompute`) -/

open DensePoly

/-- `det [[1,2],[3,4]] = −2` over `ℚ`. -/
theorem subresultantDet_two_by_two : CPolySubresultant.det ([[1, 2], [3, 4]] : List (List ℚ)) = -2 := by ccompute

/-- `det [[2,0,1],[1,3,2],[0,1,1]] = 3` over `ℚ` (cofactor expansion). -/
theorem subresultantDet_three_by_three :
    CPolySubresultant.det ([[2, 0, 1], [1, 3, 2], [0, 1, 1]] : List (List ℚ)) = 3 := by ccompute

/-- **`CPolySubresultant.det ∘ cSylvesterRows` computes the resultant** (up to the standard `(-1)^{deg p·deg q}` sign):
here `Res(t²−1, t+2) = 3` matches the selected resultant with the even sign — validating the Sylvester
construction against the lawful dense resultant. -/
private theorem subresultantDet_cSylvesterRows_eq_resultant :
    CPolySubresultant.det (cSylvesterRows ([-1, 0, 1] : DensePoly ℚ) ([2, 1] : DensePoly ℚ) 2 1)
      = CPolyResultant.compute ([-1, 0, 1] : DensePoly ℚ) ([2, 1] : DensePoly ℚ) := by ccompute

/-- The **0-th subresultant is the resultant** (constant polynomial): `S₀(t²−1, t+2) = [3]` — the full
`bSylvester` determinant, matching the selected dense resultant. -/
theorem subresultantDefault_zero :
    CPolySubresultant.default ([-1, 0, 1] : DensePoly ℚ) ([2, 1] : DensePoly ℚ) 2 1 0
      = [CPolyResultant.compute ([-1, 0, 1] : DensePoly ℚ) ([2, 1] : DensePoly ℚ)] := by ccompute

/-- The **degree-1 subresultant of `(t²−1, t+2)` is `t+2`** (`= q`, since `deg q = 1`): `S₁ = [2,1]`. -/
theorem subresultantDefault_one :
    CPolySubresultant.default ([-1, 0, 1] : DensePoly ℚ) ([2, 1] : DensePoly ℚ) 2 1 1 = [2, 1] := by ccompute

/-- The selected sparse implementation computes the same degree-one subresultant. -/
theorem subresultantCompute_sparse_one :
    CPolySubresultant.compute
      (CPoly.SparsePoly.ofList [(0, -1), (2, 1)] : CPoly.SparsePoly ℚ)
      (CPoly.SparsePoly.ofList [(0, 2), (1, 1)]) 2 1 1 =
        CPoly.SparsePoly.ofList [(0, 2), (1, 1)] := by
  ccompute

/-- **L2a — parametric = scalar at a point.** `S₁(z,t)` of `(t²−1, t − z·2t)` is `(1−2z)·t`; evaluated at
`z = 2` (a sample point) it equals the *scalar* subresultant `S₁(t²−1, −3t)` (`= −3t`). The interpolation is
exact at the sample nodes — validating the root-free parametric log-argument. -/
theorem CPolySubresultant.parametric_eval :
    (CPolySubresultant.parametric ([-1, 0, 1] : DensePoly ℚ) ([0, 1] : DensePoly ℚ)
        ([0, 2] : DensePoly ℚ) 2 1 1).map
        (fun zp => ceval zp (2 : ℚ))
      = (cnorm (CPolySubresultant.default ([-1, 0, 1] : DensePoly ℚ)
          (csub ([0, 1] : DensePoly ℚ) (cscale (2 : ℚ) ([0, 2] : DensePoly ℚ))) 2 1 1) : List ℚ) := by
  ccompute

/-- Parametric subresultants also run with sparse inner-polynomial storage. -/
theorem CPolySubresultant.parametric_sparse :
    CPolySubresultant.parametric (Q := CPoly.SparsePoly)
      (CPoly.SparsePoly.ofList [(0, -1), (2, 1)] : CPoly.SparsePoly ℚ)
      (CPoly.SparsePoly.ofList [(1, 1)])
      (CPoly.SparsePoly.ofList [(1, 2)]) 2 1 1 =
        [CPoly.SparsePoly.ofList [], CPoly.SparsePoly.ofList [(0, 1), (1, -2)]] := by
  ccompute

end DeepWiki.SymbolicIntegration
