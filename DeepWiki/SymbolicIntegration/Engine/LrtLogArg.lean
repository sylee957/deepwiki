import DeepWiki.ComputableAlgebra.PolySubresultant
import DeepWiki.ComputableAlgebra.PolyInterpolateDense
import DeepWiki.ComputableAlgebra.PolyInterpolateSparse
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv

/-! # The symbolic root-free LRT log part `cLrtLogArg`

For a reduced integrand `hNum/Dstar` (`Dstar` squarefree), the Lazard–Rioboo–Trager log part is, for each
squarefree factor `Rᵢ(z)` (multiplicity `i`) of the residue resultant `R(z) = Res_t(Dstar, hNum − z·D Dstar)`,
the term `Σ_{Rᵢ(c)=0} c·log(Sᵢ(c,t))`, where `Sᵢ(z,t)` is the degree-`i` subresultant. `cLrtLogArg` emits
the symbolic pairs `[(Rᵢ, Sᵢ)]` without computing roots. -/

namespace DeepWiki.SymbolicIntegration

universe u

namespace CPoly

/-- Embed every represented coefficient of `p` as a constant polynomial in the same representation. -/
def coefficientConstants {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CCommRing α] (p : P α) : List (P α) :=
  (CPoly.coeffs p (CPoly.degBound p)).map fun c => CPolyEngine.ofCoeffList [c]

/-- Representation-independent root-free LRT log terms selected through squarefree, resultant,
subresultant, and interpolation capabilities. -/
def lrtLogArg {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    [CPolyInterpolate P] [CPolyResultant P] [CPolySubresultant P]
    {α : Type u} [CField α] [CDiffField α] [CPolySquarefree P α]
    (Dt hNum Dstar : P α) : List (P α × List (P α)) :=
  let Dd := CPolyEngine.monomialDeriv Dt Dstar
  let R : P α := CPoly.residueResultantTower Dt hNum Dstar
  let n := CPolyEngine.cdeg Dstar
  let m := CPolyEngine.cdeg Dd
  (CPoly.squarefreeYun R).zipIdx.filterMap fun (Ri, idx) =>
    let i := idx + 1
    if CPoly.degBound (CPolyEngine.cnorm Ri) ≤ 1 then none
    else if i = n then some (Ri, coefficientConstants Dstar)
    else some (Ri, CPolySubresultant.parametric Dstar hNum Dd n m i)

end CPoly

namespace DensePoly

/-- The generic coefficient-to-constant-polynomial embedding specializes to dense list mapping. -/
@[simp] theorem coefficientConstants_dense_eq {α : Type*} [CCommRing α] (p : DensePoly α) :
    CPoly.coefficientConstants p = p.map (fun c => ([c] : DensePoly α)) := by
  simp only [CPoly.coefficientConstants]
  congr 1
  apply List.ext_get
  · rw [CPoly.coeffs_length]
    rfl
  · intro n h₁ h₂
    simp [CPoly.coeffs, h₂]

/-- The generic normalized degree bound specializes to normalized dense-list length. -/
@[simp] theorem degBound_cnorm_dense_eq {α : Type*} [CCommRing α] (p : DensePoly α) :
    CPoly.degBound (CPolyEngine.cnorm p) = (cnorm p : List α).length := rfl

variable {α : Type*} [CField α] [CDiffField α] [CPolySquarefree DensePoly α]
  [CPolyResultant DensePoly] [CPolySubresultant DensePoly]

/-- `cLrtLogArg Dt hNum Dstar = [(Rᵢ, Sᵢ)]`: for each non-constant squarefree
factor `Rᵢ` (multiplicity `i`) of the residue resultant `R(z) = Res_t(Dstar, hNum − z·D Dstar)`, the log
argument `Sᵢ(z,t)`. When `i = deg Dstar` (the residue's fiber is *all* poles — a single pure log `c·D(Dstar)/Dstar`)
the argument is `Dstar` itself; otherwise it is the parametric degree-`i` subresultant `Sᵢ(z,t)`.
Root-free residues stay implicit as the roots of `Rᵢ`. -/
def cLrtLogArg (Dt hNum Dstar : DensePoly α) : List (DensePoly α × List (DensePoly α)) :=
  CPoly.lrtLogArg Dt hNum Dstar

end DensePoly

end DeepWiki.SymbolicIntegration

/-! ### Validation (`ccompute`) — the symbolic log part of `∫ 1/(t²−1)` over `ℚ(t)` -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-- The residue resultant of `1/(t²−1)` is `R(z) = 1 − 4z²` (roots `±1/2` — the residues). -/
theorem cResidueResultant_invT2m1 :
    cResidueResultantTower ([1] : DensePoly ℚ) [1] [-1, 0, 1] = [1, 0, -4] := by ccompute

/-- The root-free LRT log part of `∫ 1/(t²−1)`: one pair `(z²−1/4, S₁)` — the residue minimal polynomial
`Rᵢ = z²−1/4` (residues `±1/2` stay *implicit*) and the parametric subresultant `S₁(z,t) = 1 − 2z·t`
(`t`-coefficients `[[1], [0,−2]]`). Evaluating `S₁` at the residues gives the actual log arguments
`1∓t = ∓(t∓1)`. No roots were computed. -/
theorem cLrtLogArg_invT2m1 :
    cLrtLogArg ([1] : DensePoly ℚ) [1] [-1, 0, 1] = [([-1/4, 0, 1], [[1], [0, -2]])] := by ccompute

/-- The pure-log case `∫ 1/t = log t`: residue 1 has multiplicity `deg Dstar`, so the log
argument is `Dstar = t` (`[[0],[1]]`). -/
theorem cLrtLogArg_invT_pureLog :
    (cLrtLogArg ([1] : DensePoly ℚ) [1] [0, 1]).map (·.2) = [[[0], [1]]] := by ccompute

/-- The pure-log case `∫ 2t/(t²+1) = log(t²+1)`: residue 1 has multiplicity `deg Dstar`,
so the log argument is `Dstar = t²+1` (`[[1],[0],[1]]`). -/
theorem cLrtLogArg_invT2p1_pureLog :
    (cLrtLogArg ([1] : DensePoly ℚ) [0, 2] [1, 0, 1]).map (·.2) = [[[1], [0], [1]]] := by ccompute

/-- Sparse storage executes the same root-free LRT kernel for `∫ 1/(t²−1)`. -/
example :
    (CPoly.lrtLogArg
      (CPoly.SparsePoly.ofList [(0, 1)] : CPoly.SparsePoly ℚ)
      (CPoly.SparsePoly.ofList [(0, 1)])
      (CPoly.SparsePoly.ofList [(0, -1), (2, 1)])).map
        (fun p => (CPolyEngine.cdeg p.1, p.2.map CPolyEngine.cdeg)) = [(2, [0, 1])] := by
  ccompute

end DeepWiki.SymbolicIntegration
