import DeepWiki.SymbolicIntegration.Engine.FuelFreeResultant
import DeepWiki.SymbolicIntegration.Engine.Tower.Integrate
import DeepWiki.ComputableAlgebra.ListDet
import DeepWiki.ComputableAlgebra.PolySubresultant

/-! # Computable determinant + subresultant (L1 of the computable-LRT build)

`CPolySubresultant.det` is a generic `[CField α]` cofactor-expansion determinant on a row-list matrix.
`CPolySubresultant` selects the representation-independent Sylvester-submatrix algorithm, which builds one polynomial column
`Σ_i (scalar cofactor det)·tⁱ`, mirroring the abstract
`DeepWiki.SymbolicIntegration.subresultant`. Foundation for the symbolic (root-free) LRT log part — see
`docs/computable-lrt.md`. Validated by `native_decide`; abstract `toPoly` correctness layered later. -/

namespace DeepWiki.SymbolicIntegration

universe u

namespace DensePoly

variable {α : Type u} [CField α]

/-- The Sylvester matrix of `p` (degree-`< n` slots) and `q` (degree-`< m` slots) as an `(m+n)×(m+n)`
row-list matrix: `m` shifted rows of `p`'s coefficients then `n` shifted rows of `q`'s (coefficients low to
high within a row, padded with zeros). Used for the resultant/subresultant. -/
def cSylvesterRows (p q : DensePoly α) (n m : ℕ) : List (List α) :=
  let pc : List α := (cnorm p)
  let qc : List α := (cnorm q)
  let width := m + n
  let shiftRow (coeffs : List α) (k : ℕ) : List α :=
    (List.replicate k CCommRing.zero ++ coeffs ++ List.replicate width CCommRing.zero).take width
  (List.range m).map (fun i => shiftRow pc i) ++ (List.range n).map (fun i => shiftRow qc i)

end DensePoly

namespace CPolySubresultant

variable {α : Type u} [CField α]

/-! ### `toK`-determinant homomorphism (L4b): certifying the selected default against `Matrix.det` -/

section Spec

variable [CFieldSpec α]

open CFieldSpec

/-- **`toK` is a determinant homomorphism.** `toK (CPolySubresultant.detAux n M) = listDetn n (M.map (map toK))` — the
computable cofactor determinant maps to the generic-`CommRing` determinant over `K`. -/
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

/-- `toK (CPolySubresultant.det M) = listDetn M.length (M.map (map toK))`. -/
@[denote] theorem toK_det (M : List (List α)) :
    toK (CPolySubresultant.det M) = listDetn M.length (M.map (fun r => r.map toK)) := by
  rw [CPolySubresultant.det, toK_detAux]

/-- **`CPolySubresultant.det` computes `Matrix.det`.** For a well-formed `n × n` row-list `M`, the computable determinant
`toK (CPolySubresultant.det M)` equals `(matrixOfList (M.map (map toK)) n).det` — the full bridge from the computable
cofactor determinant to Mathlib's abstract determinant over `K`. -/
theorem toK_det_eq_matrix_det (M : List (List α)) (n : ℕ) (hlen : M.length = n)
    (hrows : ∀ r ∈ M, r.length = n) :
    toK (CPolySubresultant.det M) = (matrixOfList (M.map (fun r => r.map toK)) n).det := by
  have hlen' : (M.map (fun r => r.map toK)).length = n := by rw [List.length_map]; exact hlen
  have hrows' : ∀ r ∈ (M.map (fun r => r.map toK)), r.length = n := by
    intro r hr; rw [List.mem_map] at hr; obtain ⟨s, hs, rfl⟩ := hr
    rw [List.length_map]; exact hrows s hs
  rw [toK_det, hlen, listDetn_eq_det n (M.map (fun r => r.map toK)) hlen' hrows']

end Spec

end CPolySubresultant

/-- Dense polynomials use the representation-independent Sylvester-submatrix implementation. -/
instance instCPolySubresultantDense : CPolySubresultant DensePoly where
  compute := CPolySubresultant.default

/-- Sparse polynomials use the representation-independent Sylvester-submatrix implementation. -/
instance instCPolySubresultantSparse : CPolySubresultant CPoly.SparsePoly where
  compute := CPolySubresultant.default

namespace CPolySubresultant

/-- **The parametric subresultant `Sⱼ(z,t)`** of `Dstar` and `A − z·Dd`: a polynomial in `t`
whose coefficients are dense polynomials in the residue `z`, computed root-free by interpolation of
the selected scalar subresultant at `z = 0,1,…,n+m`. -/
def parametric {α : Type u} [CField α] {P Q : Type u → Type u}
    [CPoly P] [CPolyEngine P] [CPolySubresultant P] [CPoly Q] [CPolyEngine Q]
    (Dstar A Dd : P α) (n m j : ℕ) : List (Q α) :=
  let N := n + m + 1
  (List.range (j + 1)).map (fun k =>
    CPoly.interpolate ((List.range N).map (fun jj =>
      let c := CField.natCast jj
      (c, CPoly.coeff
        (CPolySubresultant.compute Dstar
          (CPolyEngine.sub A (CPolyEngine.scale c Dd)) n m j) k))))

/-- Dense subresultant selection unfolds to the representation-independent default. -/
@[simp] theorem compute_dense_eq {α : Type*} [CField α] (p q : DensePoly α) (n m j : ℕ) :
    CPolySubresultant.compute p q n m j = CPolySubresultant.default p q n m j := rfl

/-- Sparse subresultant selection unfolds to the generic implementation. -/
@[simp] theorem compute_sparse_eq {α : Type*} [CField α]
    (p q : CPoly.SparsePoly α) (n m j : ℕ) :
    CPolySubresultant.compute p q n m j = CPolySubresultant.default p q n m j := rfl

end CPolySubresultant

/-! ### Validation (`native_decide`) -/

open DensePoly

/-- `det [[1,2],[3,4]] = −2` over `ℚ`. -/
theorem subresultantDet_two_by_two : CPolySubresultant.det ([[1, 2], [3, 4]] : List (List ℚ)) = -2 := by native_decide

/-- `det [[2,0,1],[1,3,2],[0,1,1]] = 3` over `ℚ` (cofactor expansion). -/
theorem subresultantDet_three_by_three :
    CPolySubresultant.det ([[2, 0, 1], [1, 3, 2], [0, 1, 1]] : List (List ℚ)) = 3 := by native_decide

/-- **`CPolySubresultant.det ∘ cSylvesterRows` computes the resultant** (up to the standard `(-1)^{deg p·deg q}` sign):
here `Res(t²−1, t+2) = 3` matches `cresultantWf` with the even sign — validating the Sylvester construction
against the proven `cresultantWf`. -/
theorem subresultantDet_cSylvesterRows_eq_resultant :
    CPolySubresultant.det (cSylvesterRows ([-1, 0, 1] : DensePoly ℚ) ([2, 1] : DensePoly ℚ) 2 1)
      = cresultantWf ([-1, 0, 1] : DensePoly ℚ) ([2, 1] : DensePoly ℚ) := by native_decide

/-- The **0-th subresultant is the resultant** (constant polynomial): `S₀(t²−1, t+2) = [3]` — the full
`bSylvester` determinant, matching `cresultantWf`. -/
theorem subresultantDefault_zero :
    CPolySubresultant.default ([-1, 0, 1] : DensePoly ℚ) ([2, 1] : DensePoly ℚ) 2 1 0
      = [cresultantWf ([-1, 0, 1] : DensePoly ℚ) ([2, 1] : DensePoly ℚ)] := by native_decide

/-- The **degree-1 subresultant of `(t²−1, t+2)` is `t+2`** (`= q`, since `deg q = 1`): `S₁ = [2,1]`. -/
theorem subresultantDefault_one :
    CPolySubresultant.default ([-1, 0, 1] : DensePoly ℚ) ([2, 1] : DensePoly ℚ) 2 1 1 = [2, 1] := by native_decide

/-- The selected sparse implementation computes the same degree-one subresultant. -/
theorem subresultantCompute_sparse_one :
    CPolySubresultant.compute
      (CPoly.SparsePoly.ofList [(0, -1), (2, 1)] : CPoly.SparsePoly ℚ)
      (CPoly.SparsePoly.ofList [(0, 2), (1, 1)]) 2 1 1 =
        CPoly.SparsePoly.ofList [(0, 2), (1, 1)] := by
  native_decide

/-- **L2a — parametric = scalar at a point.** `S₁(z,t)` of `(t²−1, t − z·2t)` is `(1−2z)·t`; evaluated at
`z = 2` (a sample point) it equals the *scalar* subresultant `S₁(t²−1, −3t)` (`= −3t`). The interpolation is
exact at the sample nodes — validating the root-free parametric log-argument. -/
theorem CPolySubresultant.parametric_eval :
    (CPolySubresultant.parametric ([-1, 0, 1] : DensePoly ℚ) ([0, 1] : DensePoly ℚ)
        ([0, 2] : DensePoly ℚ) 2 1 1).map
        (fun zp => ceval zp (2 : ℚ))
      = (cnorm (CPolySubresultant.default ([-1, 0, 1] : DensePoly ℚ)
          (csub ([0, 1] : DensePoly ℚ) (cscale (2 : ℚ) ([0, 2] : DensePoly ℚ))) 2 1 1) : List ℚ) := by
  native_decide

/-- Parametric subresultants also run with sparse inner-polynomial storage. -/
theorem CPolySubresultant.parametric_sparse :
    CPolySubresultant.parametric (Q := CPoly.SparsePoly)
      (CPoly.SparsePoly.ofList [(0, -1), (2, 1)] : CPoly.SparsePoly ℚ)
      (CPoly.SparsePoly.ofList [(1, 1)])
      (CPoly.SparsePoly.ofList [(1, 2)]) 2 1 1 =
        [CPoly.SparsePoly.ofList [], CPoly.SparsePoly.ofList [(0, 1), (1, -2)]] := by
  native_decide

end DeepWiki.SymbolicIntegration
