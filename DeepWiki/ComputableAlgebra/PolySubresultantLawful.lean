import DeepWiki.ComputableAlgebra.LinearAlgebraRatCorrect
import DeepWiki.ComputableAlgebra.ListDet
import DeepWiki.ComputableAlgebra.PolySubresultant
import DeepWiki.Algebra.SubresultantSpec

/-! # `toPoly (CPolySubresultant.default …) = subresultant …` (L4b, the subresultant certification)

The computable Sylvester-submatrix subresultant `CPolySubresultant.default` computes Mathlib's abstract
`DeepWiki.SymbolicIntegration.subresultant` under the `toPoly` bridge. Built from the `toK`-determinant
homomorphism `CPolySubresultant.toK_det_eq_matrix_det` plus the index correspondence
`bSylvesterRows`/`subRowIdx`/`subColIdx` ↔ `bSylvester`/`subRow`/`subCol`. This is the last purely
computational bridge of the root-free LRT log part. -/

namespace DeepWiki.SymbolicIntegration

open Polynomial Matrix

universe u v

/-- Denotation law for a representation-selected executable subresultant. -/
class LawfulCPolySubresultant (P : Type u → Type u) [CPoly P] [CPolySubresultant P] : Prop where
  /-- The selected computation denotes the abstract Sylvester-submatrix subresultant. -/
  compute_spec : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (p q : P α) (n m j : ℕ),
      CPoly.toPoly (CPolySubresultant.compute p q n m j) =
        subresultant (CPoly.toPoly p) (CPoly.toPoly q) n m j

namespace CPolySubresultant

variable {P : Type u → Type u} [CPoly P]
  {α : Type u} [CField α] [CFieldSpec.{u,v} α]

open CFieldSpec

/-! ### Determinant denotation bridge -/

/-- `toK` commutes with the selected cofactor-expansion determinant recursion. -/
@[denote] theorem toK_detAux : ∀ (n : ℕ) (M : List (List α)),
    toK (CPolySubresultant.detAux n M) = listDetn n (M.map (fun r => r.map toK)) := by
  intro n
  induction n with
  | zero => intro M; simp [CPolySubresultant.detAux, listDetn, CFieldSpec.toK_one]
  | succ n ih =>
    intro M
    cases M with
    | nil => simp [CPolySubresultant.detAux, listDetn, CFieldSpec.toK_one]
    | cons row rest =>
      rw [CPolySubresultant.detAux, List.map_cons, listDetn, toK_foldl_add,
        CFieldSpec.toK_zero, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp]
      have hminor : (rest.map (fun r => r.take j ++ r.drop (j + 1))).map (fun r => r.map toK)
          = (rest.map (fun r => r.map toK)).map (fun r => r.take j ++ r.drop (j + 1)) := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro r _
        simp only [Function.comp, List.map_append, List.map_take, List.map_drop]
      by_cases hpar : j % 2 = 0
      · simp only [if_pos hpar, CFieldSpec.toK_mul, ih, hminor, ← getD_map_toK]
      · simp only [if_neg hpar, CFieldSpec.toK_neg, CFieldSpec.toK_mul, ih, hminor, ← getD_map_toK]

/-- `toK` maps the selected determinant to the list determinant. -/
@[denote] theorem toK_det (M : List (List α)) :
    toK (CPolySubresultant.det M) = listDetn M.length (M.map (fun r => r.map toK)) := by
  rw [CPolySubresultant.det, toK_detAux]

/-- The selected determinant denotes Mathlib's matrix determinant for a well-formed square matrix. -/
theorem toK_det_eq_matrix_det (M : List (List α)) (n : ℕ) (hlen : M.length = n)
    (hrows : ∀ r ∈ M, r.length = n) :
    toK (CPolySubresultant.det M) = (matrixOfList (M.map (fun r => r.map toK)) n).det := by
  have hlen' : (M.map (fun r => r.map toK)).length = n := by rw [List.length_map]; exact hlen
  have hrows' : ∀ r ∈ (M.map (fun r => r.map toK)), r.length = n := by
    intro r hr; rw [List.mem_map] at hr; obtain ⟨s, hs, rfl⟩ := hr
    rw [List.length_map]; exact hrows s hs
  rw [toK_det, hlen, listDetn_eq_det n (M.map (fun r => r.map toK)) hlen' hrows']

/-! ### List-read helpers -/

/-- Reading a mapped list at an in-bounds index commutes with the map. -/
private theorem getD_map_of_lt {β γ : Type*} (g : β → γ) (l : List β) (r : ℕ) (db : β) (dg : γ)
    (h : r < l.length) : (l.map g).getD r dg = g (l.getD r db) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- `(List.range N).getD r 0 = r` for `r < N`. -/
private theorem getD_range_of_lt {r N : ℕ} (h : r < N) : (List.range N).getD r 0 = r := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_range h]; rfl

/-! ### Index-selector reads -/

private theorem subRowIdx_length (n m j : ℕ) : (subRowIdx n m j).length = m + n - 2 * j := by
  simp [subRowIdx]

private theorem subColIdx_length (n m j i : ℕ) : (subColIdx n m j i).length = m + n - 2 * j := by
  simp [subColIdx]

/-- The computable row selector reads as the abstract `subRow`'s value. -/
private theorem subRowIdx_getD (n m j : ℕ) (t : Fin (m + n - 2 * j)) :
    (subRowIdx n m j).getD (t : ℕ) 0 = (subRow n m j t : ℕ) := by
  rw [subRowIdx, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range t.isLt]
  simp [subRow]

/-- The computable column selector reads as the abstract `subCol`'s value. -/
private theorem subColIdx_getD (n m j i : ℕ) (s : Fin (m + n - 2 * j)) :
    (subColIdx n m j i).getD (s : ℕ) 0 = (subCol n m j i s : ℕ) := by
  rw [subColIdx, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range s.isLt]
  simp [subCol]

/-! ### The Sylvester-matrix entry correspondence -/

/-- `bSylvesterRows` reads as the abstract `bSylvester`. Entry `(RR, CC)` of the computable Sylvester
matrix, read through `toK`, equals the abstract `bSylvester (toPoly p) (toPoly q) n m` entry. -/
private theorem toK_bSylvesterRows_getD (p q : P α) (n m : ℕ) {RR CC : ℕ}
    (hR : RR < m + n) (hC : CC < m + n) :
    toK (((bSylvesterRows p q n m).getD RR []).getD CC CCommRing.zero)
      = bSylvester (CPoly.toPoly p) (CPoly.toPoly q) n m ⟨RR, hR⟩ ⟨CC, hC⟩ := by
  rw [bSylvesterRows]
  simp only [bSylvester, Matrix.of_apply]
  by_cases hRm : RR < m
  · -- `A`-block row
    rw [DensePoly.getD_append_left _ _ _ _ (by rw [List.length_map, List.length_range]; exact hRm),
      getD_map_of_lt _ _ _ (0 : ℕ) _ (by rw [List.length_range]; exact hRm), getD_range_of_lt hRm,
      getD_map_of_lt _ _ _ (0 : ℕ) _ (by simp only [List.length_range]; omega),
      getD_range_of_lt hC, if_pos hRm]
    by_cases hcond : RR ≤ CC ∧ CC ≤ RR + n
    · rw [if_pos hcond, if_pos hcond]
      simpa only [toR_eq_toK] using (CPoly.coeff_toPoly p (n + RR - CC)).symm
    · rw [if_neg hcond, if_neg hcond, CFieldSpec.toK_zero]
  · -- `B`-block row
    have hRm' : m ≤ RR := by omega
    rw [DensePoly.getD_append_right _ _ _ _ (by rw [List.length_map, List.length_range]; exact hRm'),
      List.length_map, List.length_range,
      getD_map_of_lt _ _ _ (0 : ℕ) _ (by rw [List.length_range]; omega), getD_range_of_lt (by omega),
      getD_map_of_lt _ _ _ (0 : ℕ) _ (by simp only [List.length_range]; omega),
      getD_range_of_lt hC, show m + (RR - m) = RR from by omega, if_neg hRm]
    by_cases hcond : RR - m ≤ CC ∧ CC ≤ RR
    · rw [if_pos hcond, if_pos hcond]
      simpa only [toR_eq_toK] using (CPoly.coeff_toPoly q (RR - CC)).symm
    · rw [if_neg hcond, if_neg hcond, CFieldSpec.toK_zero]

/-! ### The submatrix correspondence and the subresultant identity -/

/-- The computable Sylvester submatrix maps to the abstract one. After `toK`, `matrixOfList` of the
computable submatrix equals `(bSylvester …).submatrix (subRow …) (subCol …)`. -/
private theorem matrixOfList_submatrix (p q : P α) (n m j i : ℕ) :
    matrixOfList ((submatrix (bSylvesterRows p q n m) (subRowIdx n m j) (subColIdx n m j i)).map
        (fun row => row.map toK)) (m + n - 2 * j)
      = (bSylvester (CPoly.toPoly p) (CPoly.toPoly q) n m).submatrix
          (subRow n m j) (subCol n m j i) := by
  ext r c
  have hr : (r : ℕ) < (subRowIdx n m j).length := by rw [subRowIdx_length]; exact r.isLt
  have hc : (c : ℕ) < (subColIdx n m j i).length := by rw [subColIdx_length]; exact c.isLt
  simp only [matrixOfList, Matrix.of_apply, Matrix.submatrix_apply]
  rw [submatrix,
    getD_map_of_lt (fun row => row.map toK) _ _ ([] : List α) _ (by rwa [List.length_map]),
    getD_map_of_lt toK _ _ CCommRing.zero _ (by
      rw [getD_map_of_lt _ _ _ (0 : ℕ) _ hr, List.length_map]; exact hc),
    getD_map_of_lt _ _ _ (0 : ℕ) _ hr, getD_map_of_lt _ _ _ (0 : ℕ) _ hc,
    subRowIdx_getD n m j r, subColIdx_getD n m j i c,
    toK_bSylvesterRows_getD p q n m (subRow n m j r).isLt (subCol n m j i c).isLt]

/-- The default subresultant certification. `toPoly (default p q n m j) = subresultant (toPoly p)
(toPoly q) n m j`: the computable Sylvester-submatrix subresultant computes Mathlib's abstract
subresultant. -/
@[denote] theorem toPoly_default (p q : P α) (n m j : ℕ) :
    CPoly.toPoly (default p q n m j) =
      subresultant (CPoly.toPoly p) (CPoly.toPoly q) n m j := by
  ext k
  rw [CPoly.coeff_toPoly, subresultant, Polynomial.finsetSum_coeff, default,
    CPoly.coeff_ofFn]
  by_cases hk : k < j + 1
  · rw [if_pos hk]
    simp only [toR_eq_toK, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range, hk, if_pos]
    rw [CPolySubresultant.toK_det_eq_matrix_det _ (m + n - 2 * j)
        (by rw [submatrix, List.length_map, subRowIdx_length])
        (by
          intro row hrow
          rw [submatrix, List.mem_map] at hrow
          obtain ⟨s, _, rfl⟩ := hrow
          rw [List.length_map, subColIdx_length]),
      matrixOfList_submatrix]
  · rw [if_neg hk, CRingSpec.toR_zero]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_range, hk, if_false]

end CPolySubresultant

namespace LawfulCPolySubresultant

variable {P : Type u → Type u} [CPoly P] [CPolySubresultant P]
  [LawfulCPolySubresultant.{u,v} P]

/-- Universe-explicit projection of the selected subresultant's denotation law. -/
theorem compute_spec' {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (p q : P α) (n m j : ℕ) :
    CPoly.toPoly (CPolySubresultant.compute p q n m j) =
      subresultant (CPoly.toPoly p) (CPoly.toPoly q) n m j := by
  exact @LawfulCPolySubresultant.compute_spec P inferInstance inferInstance inferInstance α
    inferInstance (inferInstance : CFieldSpec.{u,v} α) p q n m j

end LawfulCPolySubresultant

/-- The dense generic implementation satisfies the abstract subresultant law. -/
instance instLawfulCPolySubresultantDense : LawfulCPolySubresultant DensePoly where
  compute_spec := by
    intro α _ _ p q n m j
    rw [CPolySubresultant.compute_dense_eq]
    exact CPolySubresultant.toPoly_default p q n m j

/-- The sparse generic implementation satisfies the abstract subresultant law. -/
instance instLawfulCPolySubresultantSparse : LawfulCPolySubresultant CPoly.SparsePoly where
  compute_spec := by
    intro α _ _ p q n m j
    rw [CPolySubresultant.compute_sparse_eq]
    exact CPolySubresultant.toPoly_default p q n m j

end DeepWiki.SymbolicIntegration
