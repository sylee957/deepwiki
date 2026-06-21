import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

/-! # Subresultants (Bronstein §1.4, Definition 1.4.2)
The `j`-th subresultant `Sⱼ(A,B)` of `A` (degree `n`) and `B` (degree `m`) is built from the
Sylvester matrix by deleting the last `j` rows of each of the `A`- and `B`-blocks and summing the
determinants of the `(m+n−2j)`-square submatrices `ⱼSᵢ` (one per `0 ≤ i ≤ j`) against `xⁱ`. We use
Bronstein's row layout (`m` shifted rows of `A`, then `n` shifted rows of `B`) so the deletion
recipe applies verbatim. The `0`-th subresultant is the resultant (`subresultant_zero`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R]

/-- **Sylvester matrix** (§1.4, Bronstein layout): `m` shifted rows of `A` (degree `n`) followed by
`n` shifted rows of `B` (degree `m`), size `(m+n)×(m+n)`. Row `i < m` is `A` shifted by `i`; row
`m ≤ i` is `B` shifted by `i − m`. -/
def bSylvester (A B : R[X]) (n m : ℕ) : Matrix (Fin (m + n)) (Fin (m + n)) R :=
  .of fun i l =>
    if (i : ℕ) < m then
      (if (i : ℕ) ≤ (l : ℕ) ∧ (l : ℕ) ≤ (i : ℕ) + n then A.coeff (n + i - l) else 0)
    else
      (if (i : ℕ) - m ≤ (l : ℕ) ∧ (l : ℕ) ≤ (i : ℕ) then B.coeff ((i : ℕ) - l) else 0)

/-- Row selector for `ⱼSᵢ`: keep `A`-rows `0..m−j−1` then `B`-rows `m..m+n−j−1` (delete the last
`j` rows of each block). -/
def subRow (n m j : ℕ) : Fin (m + n - 2 * j) → Fin (m + n) :=
  fun t => ⟨if (t : ℕ) < m - j then (t : ℕ) else (t : ℕ) + j, by have := t.isLt; split <;> omega⟩

/-- Column selector for `ⱼSᵢ`: keep the first `m+n−2j−1` columns plus column `m+n−i−j−1`. -/
def subCol (n m j i : ℕ) : Fin (m + n - 2 * j) → Fin (m + n) :=
  fun s => ⟨if (s : ℕ) < m + n - 2 * j - 1 then (s : ℕ) else m + n - i - j - 1,
    by have := s.isLt; split <;> omega⟩

/-- **Definition 1.4.2**: the `j`-th *subresultant* `Sⱼ(A,B) = ∑_{i=0}^{j} det(ⱼSᵢ)·xⁱ ∈ R[x]`,
where `ⱼSᵢ` is the `(m+n−2j)`-square submatrix of the Sylvester matrix selected by `subRow`/`subCol`. -/
noncomputable def subresultant (A B : R[X]) (n m j : ℕ) : R[X] :=
  ∑ i ∈ Finset.range (j + 1),
    C ((bSylvester A B n m).submatrix (subRow n m j) (subCol n m j i)).det * X ^ i

/-- For `j = 0` the row/column selectors are the identity. -/
theorem subRow_zero (n m : ℕ) : subRow n m 0 = id := by
  funext t; apply Fin.ext; simp only [subRow, Nat.sub_zero, Nat.add_zero, ite_self, id_eq]

theorem subCol_zero (n m : ℕ) : subCol n m 0 0 = id := by
  funext s; apply Fin.ext
  have := s.isLt
  simp only [subCol, Nat.mul_zero, Nat.sub_zero, id_eq]
  split
  · rfl
  · omega

/-- **The `0`-th subresultant is the resultant** (§1.4): `S₀(A,B) = det(Sylvester(A,B))` (as a
constant polynomial), since the `j = 0` submatrix is the full Sylvester matrix. -/
theorem subresultant_zero (A B : R[X]) (n m : ℕ) :
    subresultant A B n m 0 = C (bSylvester A B n m).det := by
  rw [subresultant, Finset.sum_range_one, subRow_zero, subCol_zero, Matrix.submatrix_id_id,
    pow_zero, mul_one]

end DeepWiki.SymbolicIntegration
