import DeepWiki.SymbolicIntegration.Engine.Subresultant
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv

/-! # The symbolic root-free LRT log part `cLrtLogArgG`

For a reduced integrand `hNum/Dstar` (`Dstar` squarefree), the Lazard–Rioboo–Trager log part is, for each
squarefree factor `Rᵢ(z)` (multiplicity `i`) of the residue resultant `R(z) = Res_t(Dstar, hNum − z·D Dstar)`,
the term `Σ_{Rᵢ(c)=0} c·log(Sᵢ(c,t))`, where `Sᵢ(z,t)` is the degree-`i` subresultant. `cLrtLogArgG` emits
the symbolic pairs `[(Rᵢ, Sᵢ)]` without computing roots. -/

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- `cLrtLogArgG Dt hNum Dstar = [(Rᵢ, Sᵢ)]`: for each non-constant squarefree
factor `Rᵢ` (multiplicity `i`) of the residue resultant `R(z) = Res_t(Dstar, hNum − z·D Dstar)`, the log
argument `Sᵢ(z,t)`. When `i = deg Dstar` (the residue's fiber is *all* poles — a single pure log `c·D(Dstar)/Dstar`)
the argument is `Dstar` itself; otherwise it is the parametric degree-`i` subresultant `Sᵢ(z,t)`.
Root-free residues stay implicit as the roots of `Rᵢ`. -/
def cLrtLogArgG (Dt hNum Dstar : CPolyG α) : List (CPolyG α × List (CPolyG α)) :=
  let Dd := cmonomialDeriv Dt Dstar
  let R := cResidueResultantTowerGWf Dt hNum Dstar
  let n := cdegG Dstar
  let m := cdegG Dd
  (cSqfreeYunFFGWf R).zipIdx.filterMap (fun (Ri, idx) =>
    let i := idx + 1
    if (cnormG Ri : List α).length ≤ 1 then none
    else if i = n then some (Ri, Dstar.map (fun c => ([c] : CPolyG α)))
    else some (Ri, cSubresultantParam Dstar hNum Dd n m i))

end CPolyG

end DeepWiki.SymbolicIntegration

/-! ### Validation (`native_decide`) — the symbolic log part of `∫ 1/(t²−1)` over `ℚ(t)` -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-- The residue resultant of `1/(t²−1)` is `R(z) = 1 − 4z²` (roots `±1/2` — the residues). -/
theorem cResidueResultant_invT2m1 :
    cResidueResultantTowerGWf ([1] : CPolyG ℚ) [1] [-1, 0, 1] = [1, 0, -4] := by native_decide

/-- The root-free LRT log part of `∫ 1/(t²−1)`: one pair `(z²−1/4, S₁)` — the residue minimal polynomial
`Rᵢ = z²−1/4` (residues `±1/2` stay *implicit*) and the parametric subresultant `S₁(z,t) = 1 − 2z·t`
(`t`-coefficients `[[1], [0,−2]]`). Evaluating `S₁` at the residues gives the actual log arguments
`1∓t = ∓(t∓1)`. No roots were computed. -/
theorem cLrtLogArg_invT2m1 :
    cLrtLogArgG ([1] : CPolyG ℚ) [1] [-1, 0, 1] = [([-1/4, 0, 1], [[1], [0, -2]])] := by native_decide

/-- The pure-log case `∫ 1/t = log t`: residue 1 has multiplicity `deg Dstar`, so the log
argument is `Dstar = t` (`[[0],[1]]`). -/
theorem cLrtLogArg_invT_pureLog :
    (cLrtLogArgG ([1] : CPolyG ℚ) [1] [0, 1]).map (·.2) = [[[0], [1]]] := by native_decide

/-- The pure-log case `∫ 2t/(t²+1) = log(t²+1)`: residue 1 has multiplicity `deg Dstar`,
so the log argument is `Dstar = t²+1` (`[[1],[0],[1]]`). -/
theorem cLrtLogArg_invT2p1_pureLog :
    (cLrtLogArgG ([1] : CPolyG ℚ) [0, 2] [1, 0, 1]).map (·.2) = [[[1], [0], [1]]] := by native_decide

end DeepWiki.SymbolicIntegration
