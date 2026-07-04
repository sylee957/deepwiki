import DeepWiki.SymbolicIntegration.Computable.FuelFreeResultant

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

end DeepWiki.SymbolicIntegration
