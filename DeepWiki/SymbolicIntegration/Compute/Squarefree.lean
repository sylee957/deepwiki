import DeepWiki.SymbolicIntegration.Compute.RtResultant

/-! # Computable squarefree factorization over `ℚ`
The Yun-style factorizer `csqfreeFactor` emits monic squarefree factors with their multiplicities.
-/

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-- Squarefree factorization `csqfreeFactor fuel p = [(Q₁,1),(Q₂,2),…]` into monic squarefree
parts `Qᵢ` of multiplicity `i`, `p = c·∏ᵢ Qᵢ^i`; fuel-bounded. -/
def csqfreeFactor (fuel : ℕ) (p : DensePoly ℚ) : List (DensePoly ℚ × ℕ) :=
  let p := cnorm p
  let (g, _, _) := DensePoly.cgcdWf p (cderiv p)
  let b1 := DensePoly.cdivWf p g
  let d1 := csub (DensePoly.cdivWf (cderiv p) g) (cderiv b1)
  let rec go : ℕ → DensePoly ℚ → DensePoly ℚ → ℕ → List (DensePoly ℚ × ℕ)
    | 0, _, _, _ => []
    | fo + 1, b, d, i =>
      if b.length ≤ 1 then []   -- `b` constant: no factors of multiplicity at least `i` remain.
      else
        let (q, _, _) := DensePoly.cgcdWf b d
        let q := cmonic q
        let b' := DensePoly.cdivWf b q
        let d' := csub (DensePoly.cdivWf d q) (cderiv b')
        let rest := go fo b' d' (i + 1)
        if q.length ≤ 1 then rest else (q, i) :: rest
  go fuel b1 d1 1

end Compute

end DeepWiki.SymbolicIntegration
