import DeepWiki.SymbolicIntegration.Engine.Subresultant
import DeepWiki.SymbolicIntegration.Engine.LinearSolveCorrect
import DeepWiki.SymbolicIntegration.Subresultants

/-! # `toPoly (cSubresultant …) = subresultant …` (L4b, the subresultant certification)

The computable Sylvester-submatrix subresultant `cSubresultant` computes Mathlib's abstract
`DeepWiki.SymbolicIntegration.subresultant` under the `toPoly` bridge. Built from the `toK`-determinant
homomorphism `toK_cDetG_eq_det` (Subresultant.lean) plus the index correspondence
`cBSylvesterRows`/`cSubRowIdx`/`cSubColIdx` ↔ `bSylvester`/`subRow`/`subCol`. This is the last purely
computational bridge of the root-free LRT log part. -/

namespace DeepWiki.SymbolicIntegration

open Polynomial Matrix

namespace CPoly

variable {α : Type*} [CField α] [CFieldSpec α]

open CFieldSpec

/-! ### List-read helpers -/

/-- Reading a mapped list at an in-bounds index commutes with the map. -/
theorem getD_map_of_lt {β γ : Type*} (g : β → γ) (l : List β) (r : ℕ) (db : β) (dg : γ)
    (h : r < l.length) : (l.map g).getD r dg = g (l.getD r db) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- `(List.range N).getD r 0 = r` for `r < N`. -/
theorem getD_range_of_lt {r N : ℕ} (h : r < N) : (List.range N).getD r 0 = r := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_range h]; rfl

/-! ### Index-selector reads -/

theorem cSubRowIdx_length (n m j : ℕ) : (cSubRowIdx n m j).length = m + n - 2 * j := by
  simp [cSubRowIdx]

theorem cSubColIdx_length (n m j i : ℕ) : (cSubColIdx n m j i).length = m + n - 2 * j := by
  simp [cSubColIdx]

/-- The computable row selector reads as the abstract `subRow`'s value. -/
theorem cSubRowIdx_getD (n m j : ℕ) (t : Fin (m + n - 2 * j)) :
    (cSubRowIdx n m j).getD (t : ℕ) 0 = (subRow n m j t : ℕ) := by
  rw [cSubRowIdx, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range t.isLt]
  simp [subRow]

/-- The computable column selector reads as the abstract `subCol`'s value. -/
theorem cSubColIdx_getD (n m j i : ℕ) (s : Fin (m + n - 2 * j)) :
    (cSubColIdx n m j i).getD (s : ℕ) 0 = (subCol n m j i s : ℕ) := by
  rw [cSubColIdx, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range s.isLt]
  simp [subCol]

/-! ### The Sylvester-matrix entry correspondence -/

/-- `cBSylvesterRows` reads as the abstract `bSylvester`. Entry `(RR, CC)` of the computable Sylvester
matrix, read through `toK`, equals the abstract `bSylvester (toPoly p) (toPoly q) n m` entry. -/
theorem toK_cBSylvesterRows_getD (p q : CPoly α) (n m : ℕ) {RR CC : ℕ}
    (hR : RR < m + n) (hC : CC < m + n) :
    toK (((cBSylvesterRows p q n m).getD RR []).getD CC CField.zero)
      = bSylvester (toPoly p) (toPoly q) n m ⟨RR, hR⟩ ⟨CC, hC⟩ := by
  rw [cBSylvesterRows]
  simp only [bSylvester, Matrix.of_apply]
  by_cases hRm : RR < m
  · -- `A`-block row
    rw [getD_append_left _ _ _ _ (by rw [List.length_map, List.length_range]; exact hRm),
      getD_map_of_lt _ _ _ (0 : ℕ) _ (by rw [List.length_range]; exact hRm), getD_range_of_lt hRm,
      getD_map_of_lt _ _ _ (0 : ℕ) _ (by simp only [List.length_range]; omega),
      getD_range_of_lt hC, if_pos hRm]
    by_cases hcond : RR ≤ CC ∧ CC ≤ RR + n
    · rw [if_pos hcond, if_pos hcond, toK_cnormG_getD]
    · rw [if_neg hcond, if_neg hcond, CFieldSpec.toK_zero]
  · -- `B`-block row
    have hRm' : m ≤ RR := by omega
    rw [getD_append_right _ _ _ _ (by rw [List.length_map, List.length_range]; exact hRm'),
      List.length_map, List.length_range,
      getD_map_of_lt _ _ _ (0 : ℕ) _ (by rw [List.length_range]; omega), getD_range_of_lt (by omega),
      getD_map_of_lt _ _ _ (0 : ℕ) _ (by simp only [List.length_range]; omega),
      getD_range_of_lt hC, show m + (RR - m) = RR from by omega, if_neg hRm]
    by_cases hcond : RR - m ≤ CC ∧ CC ≤ RR
    · rw [if_pos hcond, if_pos hcond, toK_cnormG_getD]
    · rw [if_neg hcond, if_neg hcond, CFieldSpec.toK_zero]

/-! ### The submatrix correspondence and the subresultant identity -/

/-- The computable Sylvester submatrix maps to the abstract one. After `toK`, `matrixOfList` of the
computable submatrix equals `(bSylvester …).submatrix (subRow …) (subCol …)`. -/
theorem matrixOfList_cSubmatrix (p q : CPoly α) (n m j i : ℕ) :
    matrixOfList ((cSubmatrix (cBSylvesterRows p q n m) (cSubRowIdx n m j) (cSubColIdx n m j i)).map
        (fun row => row.map toK)) (m + n - 2 * j)
      = (bSylvester (toPoly p) (toPoly q) n m).submatrix (subRow n m j) (subCol n m j i) := by
  ext r c
  have hr : (r : ℕ) < (cSubRowIdx n m j).length := by rw [cSubRowIdx_length]; exact r.isLt
  have hc : (c : ℕ) < (cSubColIdx n m j i).length := by rw [cSubColIdx_length]; exact c.isLt
  simp only [matrixOfList, Matrix.of_apply, Matrix.submatrix_apply]
  rw [cSubmatrix,
    getD_map_of_lt (fun row => row.map toK) _ _ ([] : List α) _ (by rwa [List.length_map]),
    getD_map_of_lt toK _ _ CField.zero _ (by
      rw [getD_map_of_lt _ _ _ (0 : ℕ) _ hr, List.length_map]; exact hc),
    getD_map_of_lt _ _ _ (0 : ℕ) _ hr, getD_map_of_lt _ _ _ (0 : ℕ) _ hc,
    cSubRowIdx_getD n m j r, cSubColIdx_getD n m j i c,
    toK_cBSylvesterRows_getD p q n m (subRow n m j r).isLt (subCol n m j i c).isLt]

/-- The subresultant certification. `toPoly (cSubresultant p q n m j) = subresultant (toPoly p)
(toPoly q) n m j`: the computable Sylvester-submatrix subresultant computes Mathlib's abstract
subresultant. -/
@[denote] theorem toPolyG_cSubresultantG (p q : CPoly α) (n m j : ℕ) :
    toPoly (cSubresultant p q n m j) = subresultant (toPoly p) (toPoly q) n m j := by
  rw [toPolyG_eq_sum_range, subresultant, cSubresultant, List.length_map, List.length_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  congr 1
  rw [getD_map_of_lt _ _ _ (0 : ℕ) _ (by rw [List.length_range]; exact hi), getD_range_of_lt hi]
  congr 1
  simp only [toR_eq_toK]
  rw [toK_cDetG_eq_det _ (m + n - 2 * j)
      (by rw [cSubmatrix, List.length_map, cSubRowIdx_length])
      (by
        intro row hrow
        rw [cSubmatrix, List.mem_map] at hrow
        obtain ⟨s, _, rfl⟩ := hrow
        rw [List.length_map, cSubColIdx_length]),
    matrixOfList_cSubmatrix]

end CPoly

end DeepWiki.SymbolicIntegration
