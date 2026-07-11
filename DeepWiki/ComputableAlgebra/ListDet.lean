import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Generic list-matrix determinant = `Matrix.det`

`listDetn` is the cofactor-expansion determinant on a row-list matrix over a `CommRing`; `listDetn_eq_det`
proves it equals `Matrix.det` of the corresponding `Fin n × Fin n` matrix. The bridge lets the computable
`CPolySubresultant.det`/`default` be certified against the abstract Sylvester-determinant subresultant. -/

namespace DeepWiki.SymbolicIntegration

open Matrix

variable {R : Type*} [CommRing R]

/-- Cofactor-expansion determinant on a row-list matrix (dimension-indexed), over a `CommRing`. Expands
along row 0: `Σⱼ (−1)ʲ · M[0][j] · det(minorⱼ)`. -/
def listDetn : ℕ → List (List R) → R
  | 0, _ => 1
  | _ + 1, [] => 1
  | n + 1, row :: rest =>
    ((List.range (n + 1)).map (fun j =>
      let aij := row.getD j 0
      let minor := rest.map (fun r => r.take j ++ r.drop (j + 1))
      let term := aij * listDetn n minor
      if j % 2 = 0 then term else -term)).foldl (· + ·) 0

/-- The `Fin n × Fin n` matrix read off a row-list. -/
def matrixOfList (M : List (List R)) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  .of fun i j => (M.getD i []).getD j 0

end DeepWiki.SymbolicIntegration

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R]

/-- Column-deletion index lemma. For a list `L` of length `n+1`, deleting column `j` (`take j ++
drop (j+1)`) reads at index `k < n` as `L` at `if k < j then k else k+1` — the `Fin.succAbove` skip. -/
theorem getD_take_append_drop (L : List R) (n j k : ℕ) (hL : L.length = n + 1) (hk : k < n) :
    (L.take j ++ L.drop (j + 1)).getD k 0 = L.getD (if k < j then k else k + 1) 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rcases lt_or_ge k j with hkj | hkj
  · rw [if_pos hkj,
      List.getElem?_append_left (by rw [List.length_take]; omega), List.getElem?_take_of_lt hkj]
  · rw [if_neg (by omega), List.getElem?_append_right (by rw [List.length_take]; omega),
      List.length_take, List.getElem?_drop]
    congr 2
    omega

/-- The minor of a row-list matrix is the `Fin.succ`/`succAbove` submatrix. Deleting row 0 (via `rest`)
and column `j` (via `take j ++ drop (j+1)`) from `matrixOfList (row :: rest) (n+1)` gives exactly
`.submatrix Fin.succ j.succAbove`. -/
theorem matrixOfList_minor (n : ℕ) (row : List R) (rest : List (List R))
    (hrest_len : rest.length = n) (hrest_rows : ∀ r ∈ rest, r.length = n + 1) (j : Fin (n + 1)) :
    matrixOfList (rest.map (fun r => r.take (j : ℕ) ++ r.drop ((j : ℕ) + 1))) n
      = (matrixOfList (row :: rest) (n + 1)).submatrix Fin.succ j.succAbove := by
  ext i' k
  have hi : (i' : ℕ) < rest.length := by rw [hrest_len]; exact i'.isLt
  have hmem : rest.getD (i' : ℕ) [] ∈ rest := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi
  have hLlen : (rest.getD (i' : ℕ) []).length = n + 1 := hrest_rows _ hmem
  have hmap : (rest.map (fun r => r.take (j : ℕ) ++ r.drop ((j : ℕ) + 1))).getD (i' : ℕ) []
      = (rest.getD (i' : ℕ) []).take (j : ℕ) ++ (rest.getD (i' : ℕ) []).drop ((j : ℕ) + 1) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  simp only [matrixOfList, Matrix.submatrix_apply, Matrix.of_apply, Fin.val_succ,
    List.getD_cons_succ, hmap]
  rw [getD_take_append_drop _ n _ _ hLlen k.isLt]
  congr 1
  rcases lt_or_ge (k : ℕ) (j : ℕ) with hkj | hkj
  · rw [if_pos hkj,
      Fin.succAbove_of_castSucc_lt j k (by rw [Fin.lt_def]; exact hkj),
      Fin.val_castSucc]
  · rw [if_neg (by omega),
      Fin.succAbove_of_le_castSucc j k (by rw [Fin.le_def, Fin.val_castSucc]; exact hkj),
      Fin.val_succ]

/-- `listDetn` computes `Matrix.det`. For a well-formed `n × n` row-list `M`, the cofactor-expansion
`listDetn n M` equals `(matrixOfList M n).det`. Proved by induction on `n` via `Matrix.det_succ_row_zero`
and the minor correspondence `matrixOfList_minor`. This bridge certifies the computable
determinant against Mathlib's abstract determinant. -/
theorem listDetn_eq_det : ∀ (n : ℕ) (M : List (List R)), M.length = n → (∀ r ∈ M, r.length = n) →
    listDetn n M = (matrixOfList M n).det := by
  have foldl_sum : ∀ (g : ℕ → R) (m : ℕ),
      List.foldl (· + ·) 0 ((List.range m).map g) = ∑ j : Fin m, g (j : ℕ) := by
    intro g m
    have h1 : List.foldl (· + ·) 0 ((List.range m).map g) = ∑ i ∈ Finset.range m, g i := by
      induction m with
      | zero => simp
      | succ k ih =>
        rw [List.range_succ, List.map_append, List.foldl_append, Finset.sum_range_succ, ih]; simp
    rw [h1, ← Fin.sum_univ_eq_sum_range]
  intro n
  induction n with
  | zero => intro M _ _; simp [listDetn, Matrix.det_fin_zero]
  | succ n ih =>
    intro M hlen hrows
    obtain ⟨row, rest, rfl⟩ : ∃ row rest, M = row :: rest := by
      cases M with
      | nil => simp at hlen
      | cons a l => exact ⟨a, l, rfl⟩
    have hrest_len : rest.length = n := by simpa using hlen
    have hrest_rows : ∀ r ∈ rest, r.length = n + 1 := fun r hr => hrows r (List.mem_cons_of_mem _ hr)
    rw [listDetn, foldl_sum, Matrix.det_succ_row_zero]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    have hM0j : (matrixOfList (row :: rest) (n + 1)) 0 j = row.getD (j : ℕ) 0 := by
      simp [matrixOfList]
    have hminlen : (rest.map (fun r => r.take (j : ℕ) ++ r.drop ((j : ℕ) + 1))).length = n := by
      rw [List.length_map]; exact hrest_len
    have hminrows : ∀ r ∈ (rest.map (fun r => r.take (j : ℕ) ++ r.drop ((j : ℕ) + 1))), r.length = n := by
      intro r hr
      rw [List.mem_map] at hr
      obtain ⟨s, hs, rfl⟩ := hr
      rw [List.length_append, List.length_take, List.length_drop, hrest_rows s hs]
      have := j.isLt; omega
    rw [hM0j, ← matrixOfList_minor n row rest hrest_len hrest_rows j, ← ih _ hminlen hminrows]
    rcases Nat.even_or_odd (j : ℕ) with he | ho
    · rw [if_pos (Nat.even_iff.mp he), he.neg_one_pow]; ring
    · rw [if_neg (by rw [Nat.odd_iff] at ho; omega), ho.neg_one_pow]; ring

end DeepWiki.SymbolicIntegration
