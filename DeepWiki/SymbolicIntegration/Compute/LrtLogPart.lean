import DeepWiki.SymbolicIntegration.Compute.Subresultant

/-! # Yun squarefree factorization and the LRT logarithmic-part assembly

The concrete `Compute`-layer squarefree factorization `csqfreeFactor` (Yun's recurrence over
`ℚ[x]`) and the Lazard–Rioboo–Trager log-part assembly `lrtLogPart`, which combines the
Rothstein–Trager resultant, Yun factorization, and per-multiplicity subresultant gcds into the
list of `(Qᵢ, Sᵢ)` pairs describing `∫A/D` as a sum of logarithms. -/

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-- **Yun squarefree factorization** `csqfreeFactor fuel p = [(Q₁,1),(Q₂,2),…]`: the distinct-degree
factorization of a `CPoly` over `ℚ` (char 0) into monic squarefree parts `Qᵢ` of multiplicity `i`,
`p = c·∏ᵢ Qᵢ^i` (units dropped). Yun's recurrence on `g = gcd(p, p')`: with `b₁ = p/g`, `d₁ = p'/g − b₁'`,
each step yields `Qᵢ = gcd(bᵢ, dᵢ)`, `bᵢ₊₁ = bᵢ/Qᵢ`, `dᵢ₊₁ = dᵢ/Qᵢ − bᵢ₊₁'`. Constant `Qᵢ`
(multiplicity-`i` absent) are dropped. Fuel-bounded (one step per multiplicity). -/
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

/-- **The assembled LRT logarithmic part** of `∫A/D`: `lrtLogPart fuel A D` returns the list of
`(Qᵢ, Sᵢ)` pairs meaning `∫A/D = ∑ᵢ ∑_{Qᵢ(a)=0} a·log(Sᵢ(a,x))`, where `(Qᵢ, i)` are the Yun
squarefree factors of the RT resultant `R = res_x(D, A − t·D')` and `Sᵢ = lrtGcdCompute fuel i Qᵢ A D`
the monic-in-`x` log argument at multiplicity `i`. (Assumes `D` squarefree — pure log part, no
Hermite reduction.) -/
def lrtLogPart (fuel : ℕ) (A D : CPoly) : List (CPoly × BPoly) :=
  let R := rtResultantCompute fuel A D
  (csqfreeFactor fuel R).map (fun (Qi, i) => (Qi, lrtGcdCompute fuel i Qi A D))

end Compute

end DeepWiki.SymbolicIntegration
