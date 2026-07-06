import DeepWiki.SymbolicIntegration.Computable.FuelFreeResultant
import DeepWiki.SymbolicIntegration.Computable.Tower.Integrate
import DeepWiki.SymbolicIntegration.Computable.ListDet

/-! # Computable determinant + subresultant (L1 of the computable-LRT build)

`cDetGn` is a generic `[CField α]` cofactor-expansion determinant on a row-list matrix; `cSubresultantG`
builds the subresultant of two `CPolyG α` polynomials as the Sylvester-submatrix determinant with one
polynomial column (`Σ_i (scalar cofactor det)·tⁱ`), mirroring the abstract
`DeepWiki.SymbolicIntegration.subresultant`. Foundation for the symbolic (root-free) LRT log part — see
`docs/computable-lrt.md`. Validated by `native_decide`; abstract `toPolyG` correctness layered later. -/

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α]

/-- **Generic cofactor-expansion determinant** on a row-list matrix, dimension-indexed for termination.
`cDetGn n M` expands `M` (assumed `n × n`) along its first row: `Σ_j (−1)ʲ · M[0][j] · det(minorⱼ)`. -/
def cDetGn : ℕ → List (List α) → α
  | 0, _ => CField.one
  | _ + 1, [] => CField.one
  | n + 1, row :: rest =>
    ((List.range (n + 1)).map (fun j =>
      let aij := row.getD j CField.zero
      let minor := rest.map (fun r => r.take j ++ r.drop (j + 1))
      let term := CField.mul aij (cDetGn n minor)
      if j % 2 = 0 then term else CField.neg term)).foldl CField.add CField.zero

/-- Determinant of a square row-list matrix (`cDetGn` at its own row-count). -/
def cDetG (M : List (List α)) : α := cDetGn M.length M

/-- The Sylvester matrix of `p` (degree-`< n` slots) and `q` (degree-`< m` slots) as an `(m+n)×(m+n)`
row-list matrix: `m` shifted rows of `p`'s coefficients then `n` shifted rows of `q`'s (coefficients low to
high within a row, padded with zeros). Used for the resultant/subresultant. -/
def cSylvesterRows (p q : CPolyG α) (n m : ℕ) : List (List α) :=
  let pc : List α := (cnormG p)
  let qc : List α := (cnormG q)
  let width := m + n
  let shiftRow (coeffs : List α) (k : ℕ) : List α :=
    (List.replicate k CField.zero ++ coeffs ++ List.replicate width CField.zero).take width
  (List.range m).map (fun i => shiftRow pc i) ++ (List.range n).map (fun i => shiftRow qc i)

/-- The **exact `bSylvester` matrix** (matching `DeepWiki.SymbolicIntegration.bSylvester`): `m` `A`-rows then
`n` `B`-rows, entry `(i,l) = A.coeff(n+i−l)` (`i≤l≤i+n`) resp. `B.coeff(i−l)` (`i−m≤l≤i`), coefficients
high-to-low. -/
def cBSylvesterRows (p q : CPolyG α) (n m : ℕ) : List (List α) :=
  let pc : List α := cnormG p
  let qc : List α := cnormG q
  let width := m + n
  let arow (i : ℕ) : List α := (List.range width).map (fun l =>
    if i ≤ l ∧ l ≤ i + n then pc.getD (n + i - l) CField.zero else CField.zero)
  let brow (i : ℕ) : List α := (List.range width).map (fun l =>
    if i - m ≤ l ∧ l ≤ i then qc.getD (i - l) CField.zero else CField.zero)
  (List.range m).map (fun i => arow i) ++ (List.range n).map (fun jj => brow (m + jj))

/-- Row-index selector `subRow n m j` (delete the last `j` rows of each Sylvester block). -/
def cSubRowIdx (n m j : ℕ) : List ℕ :=
  (List.range (m + n - 2 * j)).map (fun t => if t < m - j then t else t + j)

/-- Column-index selector `subCol n m j i` (first `m+n−2j−1` columns plus column `m+n−i−j−1`). -/
def cSubColIdx (n m j i : ℕ) : List ℕ :=
  (List.range (m + n - 2 * j)).map (fun s => if s < m + n - 2 * j - 1 then s else m + n - i - j - 1)

/-- Extract the submatrix of `M` on the given row/column index lists. -/
def cSubmatrix (M : List (List α)) (rows cols : List ℕ) : List (List α) :=
  rows.map (fun r => cols.map (fun c => (M.getD r []).getD c CField.zero))

/-- **The `j`-th subresultant polynomial** `Sⱼ(p,q) = Σ_{i=0}^{j} det(ⱼSᵢ)·tⁱ` (coefficients low-to-high),
mirroring `DeepWiki.SymbolicIntegration.subresultant p q n m j`. The symbolic (root-free) LRT log arguments
are these. -/
def cSubresultantG (p q : CPolyG α) (n m j : ℕ) : CPolyG α :=
  (List.range (j + 1)).map (fun i =>
    cDetG (cSubmatrix (cBSylvesterRows p q n m) (cSubRowIdx n m j) (cSubColIdx n m j i)))

/-- **The parametric subresultant `Sⱼ(z,t)`** of `Dstar` and `A − z·Dd` — the symbolic RT log argument, a
polynomial in `t` whose coefficients are polynomials in the residue `z`, **computed without roots** by
interpolation in `z` (`cSubresultantG` at `z = 0,1,…,n+m` per `t`-coefficient, then `cinterpolateG`). Output:
`List (CPolyG α)`, the `z`-polynomial coefficient of each `tᵏ` (`k = 0..j`). -/
def cSubresultantParam (Dstar A Dd : CPolyG α) (n m j : ℕ) : List (CPolyG α) :=
  let N := n + m + 1
  (List.range (j + 1)).map (fun k =>
    cinterpolateG ((List.range N).map (fun jj =>
      let c := cnatCastG jj
      (c, ((cSubresultantG Dstar (csubG A (cscaleG c Dd)) n m j : CPolyG α) : List α).getD k
        CField.zero))))

/-! ### `toK`-determinant homomorphism (L4b): certifying `cDetG` against `Matrix.det` -/

section Spec

variable [CFieldSpec α]

open CFieldSpec

/-- `toK` reads a `CField.zero`-defaulted `getD` through `map toK`. -/
theorem getD_map_toK (l : List α) (j : ℕ) :
    (l.map toK).getD j 0 = toK (l.getD j CField.zero) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[j]? with
  | none => simp [CFieldSpec.toK_zero]
  | some a => simp

/-- **`toK` is a determinant homomorphism.** `toK (cDetGn n M) = listDetn n (M.map (map toK))` — the
computable cofactor determinant maps to the generic-`CommRing` determinant over `K`. -/
theorem toK_cDetGn : ∀ (n : ℕ) (M : List (List α)),
    toK (cDetGn n M) = listDetn n (M.map (fun r => r.map toK)) := by
  intro n
  induction n with
  | zero => intro M; simp [cDetGn, listDetn, CFieldSpec.toK_one]
  | succ n ih =>
    intro M
    cases M with
    | nil => simp [cDetGn, listDetn, CFieldSpec.toK_one]
    | cons row rest =>
      rw [cDetGn, List.map_cons, listDetn, toK_foldl_add, CFieldSpec.toK_zero, List.map_map]
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

/-- `toK (cDetG M) = listDetn M.length (M.map (map toK))`. -/
theorem toK_cDetG (M : List (List α)) :
    toK (cDetG M) = listDetn M.length (M.map (fun r => r.map toK)) := by
  rw [cDetG, toK_cDetGn]

/-- **`cDetG` computes `Matrix.det`.** For a well-formed `n × n` row-list `M`, the computable determinant
`toK (cDetG M)` equals `(matrixOfList (M.map (map toK)) n).det` — the full bridge from the computable
cofactor determinant to Mathlib's abstract determinant over `K`. -/
theorem toK_cDetG_eq_det (M : List (List α)) (n : ℕ) (hlen : M.length = n)
    (hrows : ∀ r ∈ M, r.length = n) :
    toK (cDetG M) = (matrixOfList (M.map (fun r => r.map toK)) n).det := by
  have hlen' : (M.map (fun r => r.map toK)).length = n := by rw [List.length_map]; exact hlen
  have hrows' : ∀ r ∈ (M.map (fun r => r.map toK)), r.length = n := by
    intro r hr; rw [List.mem_map] at hr; obtain ⟨s, hs, rfl⟩ := hr
    rw [List.length_map]; exact hrows s hs
  rw [toK_cDetG, hlen, listDetn_eq_det n (M.map (fun r => r.map toK)) hlen' hrows']

end Spec

end CPolyG

/-! ### Validation (`native_decide`) -/

open CPolyG

/-- `det [[1,2],[3,4]] = −2` over `ℚ`. -/
theorem cDetG_two_by_two : cDetG ([[1, 2], [3, 4]] : List (List ℚ)) = -2 := by native_decide

/-- `det [[2,0,1],[1,3,2],[0,1,1]] = 3` over `ℚ` (cofactor expansion). -/
theorem cDetG_three_by_three :
    cDetG ([[2, 0, 1], [1, 3, 2], [0, 1, 1]] : List (List ℚ)) = 3 := by native_decide

/-- **`cDetG ∘ cSylvesterRows` computes the resultant** (up to the standard `(-1)^{deg p·deg q}` sign):
here `Res(t²−1, t+2) = 3` matches `cresultantWf` with the even sign — validating the Sylvester construction
against the proven `cresultantWf`. -/
theorem cDetG_cSylvesterRows_eq_resultant :
    cDetG (cSylvesterRows ([-1, 0, 1] : CPolyG ℚ) ([2, 1] : CPolyG ℚ) 2 1)
      = cresultantWf ([-1, 0, 1] : CPolyG ℚ) ([2, 1] : CPolyG ℚ) := by native_decide

/-- The **0-th subresultant is the resultant** (constant polynomial): `S₀(t²−1, t+2) = [3]` — the full
`bSylvester` determinant, matching `cresultantWf`. -/
theorem cSubresultantG_zero :
    cSubresultantG ([-1, 0, 1] : CPolyG ℚ) ([2, 1] : CPolyG ℚ) 2 1 0
      = [cresultantWf ([-1, 0, 1] : CPolyG ℚ) ([2, 1] : CPolyG ℚ)] := by native_decide

/-- The **degree-1 subresultant of `(t²−1, t+2)` is `t+2`** (`= q`, since `deg q = 1`): `S₁ = [2,1]`. -/
theorem cSubresultantG_one :
    cSubresultantG ([-1, 0, 1] : CPolyG ℚ) ([2, 1] : CPolyG ℚ) 2 1 1 = [2, 1] := by native_decide

/-- **L2a — parametric = scalar at a point.** `S₁(z,t)` of `(t²−1, t − z·2t)` is `(1−2z)·t`; evaluated at
`z = 2` (a sample point) it equals the *scalar* subresultant `S₁(t²−1, −3t)` (`= −3t`). The interpolation is
exact at the sample nodes — validating the root-free parametric log-argument. -/
theorem cSubresultantParam_eval :
    (cSubresultantParam ([-1, 0, 1] : CPolyG ℚ) ([0, 1] : CPolyG ℚ) ([0, 2] : CPolyG ℚ) 2 1 1).map
        (fun zp => cHornerG zp (2 : ℚ))
      = (cnormG (cSubresultantG ([-1, 0, 1] : CPolyG ℚ)
          (csubG ([0, 1] : CPolyG ℚ) (cscaleG (2 : ℚ) ([0, 2] : CPolyG ℚ))) 2 1 1) : List ℚ) := by
  native_decide

end DeepWiki.SymbolicIntegration
