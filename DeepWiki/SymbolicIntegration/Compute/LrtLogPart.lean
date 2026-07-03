import DeepWiki.SymbolicIntegration.Compute.Subresultant

/-! # Computable squarefree factorization and logarithmic-part assembly
`csqfreeFactor` squarefree-factors a `CPoly` over `ℚ`; `lrtLogPart` assembles the `(Qᵢ, Sᵢ)`
pairs describing `∫A/D` as a sum of logarithms. -/

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-- Squarefree factorization `csqfreeFactor fuel p = [(Q₁,1),(Q₂,2),…]` into monic squarefree
parts `Qᵢ` of multiplicity `i`, `p = c·∏ᵢ Qᵢ^i`; fuel-bounded. -/
def csqfreeFactor (fuel : ℕ) (p : CPoly) : List (CPoly × ℕ) :=
  let p := cnorm p
  let (g, _, _) := cgcdExt fuel p (cderiv p)
  let b1 := cdiv fuel p g
  let d1 := csub (cdiv fuel (cderiv p) g) (cderiv b1)
  let rec go : ℕ → CPoly → CPoly → ℕ → List (CPoly × ℕ)
    | 0, _, _, _ => []
    | fo + 1, b, d, i =>
      if b.length ≤ 1 then []   -- `b` constant ⇒ no factors of multiplicity ≥ i remain
      else
        let (q, _, _) := cgcdExt fuel b d
        let q := cmonic q
        let b' := cdiv fuel b q
        let d' := csub (cdiv fuel d q) (cderiv b')
        let rest := go fo b' d' (i + 1)
        if q.length ≤ 1 then rest else (q, i) :: rest
  go fuel b1 d1 1

/-- Logarithmic part of `∫A/D`: `lrtLogPart fuel A D` returns the `(Qᵢ, Sᵢ)` pairs meaning
`∫A/D = ∑ᵢ ∑_{Qᵢ(a)=0} a·log(Sᵢ(a,x))`, for squarefree `D`. -/
def lrtLogPart (fuel : ℕ) (A D : CPoly) : List (CPoly × BPoly) :=
  let R := rtResultantCompute fuel A D
  (csqfreeFactor fuel R).map (fun (Qi, i) => (Qi, lrtGcdCompute fuel i Qi A D))

end Compute

end DeepWiki.SymbolicIntegration
