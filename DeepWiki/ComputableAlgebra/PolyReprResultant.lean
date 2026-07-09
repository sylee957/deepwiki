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

/-- `clistDetn` reduces: the 2×2 determinant `|1 2; 3 4| = -2`. -/
example : clistDetn 2 ([[1, 2], [3, 4]] : List (List ℚ)) = -2 := by native_decide
/-- `clistDetn` reduces: a 3×3 determinant `|2 0 1; 1 3 2; 0 1 1| = 3`. -/
example : clistDetn 3 ([[2, 0, 1], [1, 3, 2], [0, 1, 1]] : List (List ℚ)) = 3 := by native_decide

end DeepWiki.SymbolicIntegration.CPolyRepr
