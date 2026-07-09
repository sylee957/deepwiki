import DeepWiki.ComputableAlgebra.PolyReprDegree
import DeepWiki.ComputableAlgebra.ListDet

/-! # Toward a generic computable resultant (Sylvester determinant)

`listDetn` (in `ListDet.lean`) is a cofactor-expansion determinant over a Mathlib `CommRing`. A
*computable* resultant must expand over the interface coefficient `[CCommRing α]` (whose ops reduce under
`native_decide`), so this file mirrors `listDetn` as `clistDetn` on `CCommRing`, with `toR_clistDetn`
bridging it to `listDetn` over the denotation ring. The Sylvester matrix + resultant proper (matching
`Polynomial.sylvester` / `Polynomial.resultant`, using `resultant_map_map`) build on this. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.CPolyRepr

variable {α : Type u} [CCommRing α]

/-- Cofactor-expansion determinant on a row-list matrix over `CCommRing` (the computable, reducing
analogue of `listDetn`): expand along row 0 with alternating signs. -/
def clistDetn : ℕ → List (List α) → α
  | 0, _ => CCommRing.one
  | _ + 1, [] => CCommRing.one
  | n + 1, row :: rest =>
    ((List.range (n + 1)).map (fun j =>
      let aij := row.getD j CCommRing.zero
      let minor := rest.map (fun r => r.take j ++ r.drop (j + 1))
      let term := CCommRing.mul aij (clistDetn n minor)
      if j % 2 = 0 then term else CCommRing.neg term)).foldl CCommRing.add CCommRing.zero

section Bridge
variable [CRingSpec α]

/-- `toR` carries a `CCommRing.add`-`foldl` to the Mathlib `+`-`foldl` of the images. -/
theorem toR_foldl_add (L : List α) (acc : α) :
    CRingSpec.toR (L.foldl CCommRing.add acc)
      = (L.map CRingSpec.toR).foldl (· + ·) (CRingSpec.toR acc) := by
  induction L generalizing acc with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, CRingSpec.toR_add]

/-- Mapping `toR` over the matrix commutes with the minor (delete-column) operation. -/
theorem map_minor_comm (rest : List (List α)) (j : ℕ) :
    (rest.map (fun r => r.take j ++ r.drop (j + 1))).map (fun row => row.map CRingSpec.toR)
      = (rest.map (fun row => row.map CRingSpec.toR)).map (fun r => r.take j ++ r.drop (j + 1)) := by
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro r _
  simp only [Function.comp_apply, List.map_append, List.map_take, List.map_drop]

/-- `toR (row.getD j 0) = (row.map toR).getD j 0`. -/
theorem toR_getD (row : List α) (j : ℕ) :
    CRingSpec.toR (row.getD j CCommRing.zero) = (row.map CRingSpec.toR).getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases row[j]? with
  | none => simp [CRingSpec.toR_zero]
  | some a => rfl

/-- **The determinant bridge:** `toR (clistDetn n M) = listDetn n (M.map (map toR))` — the computable
determinant denotes the Mathlib `listDetn` (hence, via `listDetn_eq_det`, `Matrix.det`). -/
theorem toR_clistDetn : ∀ (n : ℕ) (M : List (List α)),
    CRingSpec.toR (clistDetn n M) = listDetn n (M.map (fun row => row.map CRingSpec.toR))
  | 0, _ => by rw [clistDetn, listDetn, CRingSpec.toR_one]
  | _ + 1, [] => by rw [clistDetn, List.map_nil, listDetn, CRingSpec.toR_one]
  | n + 1, row :: rest => by
    rw [clistDetn, List.map_cons, listDetn, toR_foldl_add, CRingSpec.toR_zero, List.map_map]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply]
    have hminor : CRingSpec.toR (clistDetn n (rest.map (fun r => r.take j ++ r.drop (j + 1))))
        = listDetn n ((rest.map (fun row => row.map CRingSpec.toR)).map
          (fun r => r.take j ++ r.drop (j + 1))) := by
      rw [toR_clistDetn n, map_minor_comm]
    split_ifs with hpar
    · rw [CRingSpec.toR_mul, toR_getD, hminor]
    · rw [CRingSpec.toR_neg, CRingSpec.toR_mul, toR_getD, hminor]

end Bridge

/-- `clistDetn` reduces: the 2×2 determinant `|1 2; 3 4| = -2`. -/
example : clistDetn 2 ([[1, 2], [3, 4]] : List (List ℚ)) = -2 := by native_decide
/-- `clistDetn` reduces: a 3×3 determinant `|2 0 1; 1 3 2; 0 1 1| = 3`. -/
example : clistDetn 3 ([[2, 0, 1], [1, 3, 2], [0, 1, 1]] : List (List ℚ)) = 3 := by native_decide

/-! ### The Sylvester matrix and the computable resultant

`cSylvester p q m n` is the `(m+n)×(m+n)` Sylvester coefficient matrix (rows = shifted coefficient
strips of `q` then `p`), matching `Polynomial.sylvester`'s column layout; `cResultant p q` is its
`clistDetn`. Validated by `native_decide` against known resultants (`res(x−1,x−2) = −1` for coprime,
`res(x²−1,x−1) = 0` for a common factor). The abstract bridge `toR (cResultant p q) =
Polynomial.resultant (toPoly p) (toPoly q)` (via `toR_clistDetn` + `listDetn_eq_det` +
`Polynomial.resultant_map_map`) is the remaining piece. -/

variable {P : Type u → Type u} [CPolyRepr P]

/-- The `(m+n)×(m+n)` Sylvester coefficient matrix of `p, q` (as a row-list). -/
def cSylvester (p q : P α) (m n : ℕ) : List (List α) :=
  (List.range (m + n)).map (fun i =>
    (List.range (m + n)).map (fun j =>
      if j < m then (if j ≤ i ∧ i ≤ j + n then coeff q (i - j) else CCommRing.zero)
      else (if (j - m) ≤ i ∧ i ≤ (j - m) + m then coeff p (i - (j - m)) else CCommRing.zero)))

/-- The computable resultant: the determinant of the Sylvester matrix (default degrees `cdeg`). -/
def cResultant (p q : P α) : α := clistDetn (cdeg p + cdeg q) (cSylvester p q (cdeg p) (cdeg q))

/-- `cResultant` reduces: `res(x − 1, x − 2) = −1` (coprime ⇒ nonzero). -/
example : cResultant ([-1, 1] : List ℚ) [-2, 1] = -1 := by native_decide
/-- `cResultant` reduces: `res(x² − 1, x − 1) = 0` (common factor ⇒ zero). -/
example : cResultant ([-1, 0, 1] : List ℚ) [-1, 1] = 0 := by native_decide

/-- The resultant of `p` with its derivative (the discriminant up to the leading factor): it vanishes
exactly when `p` has a repeated factor. -/
def cResultantDeriv (p : P α) : α := cResultant p (cderiv p)

/-- `cResultantDeriv` reduces: `x² − 1` is squarefree, so `res(p, p') ≠ 0`. -/
example : cResultantDeriv ([-1, 0, 1] : List ℚ) ≠ 0 := by native_decide
/-- `cResultantDeriv` reduces: `(x − 1)²` has a repeated factor, so `res(p, p') = 0`. -/
example : cResultantDeriv ([1, -2, 1] : List ℚ) = 0 := by native_decide

end DeepWiki.SymbolicIntegration.CPolyRepr
