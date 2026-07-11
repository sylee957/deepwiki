import DeepWiki.SymbolicIntegration.Engine.LrtLogArg
import DeepWiki.SymbolicIntegration.Engine.Hermite.ValuationTower

/-! # The symbolic (root-free) LRT reduced integrator `cIntegrateReducedLrt` (L3)

Combines the Hermite rational part (`cHermiteReduceTower`) with the symbolic Lazard–Rioboo–Trager log part
(`cLrtLogArg`) into a `LrtResult`: a rational function plus a list of symbolic log terms `(Rᵢ, Sᵢ)`, each
denoting `Σ_{Rᵢ(c)=0} c·log(Sᵢ(c,t))`. **No residues are computed** — this is the root-finding-free reduced
integrator. See `docs/computable-lrt.md`. -/

namespace DeepWiki.SymbolicIntegration

universe u

/-- A symbolic-residue reduced-integration result: a rational part `gnum/gden` plus symbolic log terms
`[(Rᵢ, Sᵢ)]`, each denoting `Σ_{Rᵢ(c)=0} c·log(Sᵢ(c,t))`, in polynomial representation `P` (dense by
default). -/
structure LrtResult (α : Type u) [CField α] (P : Type u → Type u := DensePoly) where
  /-- The Hermite rational part `(gnum, gden)`. -/
  rational : P α × P α
  /-- Symbolic log terms `[(Rᵢ, Sᵢ)]`: residue minimal polynomial `Rᵢ` and parametric log argument `Sᵢ(z,t)`
  (a `t`-polynomial with `z`-polynomial coefficients). -/
  logs : List (P α × List (P α))

namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α] [CPolySquarefree DensePoly α]
  [CPolyResultant DensePoly] [CPolySubresultant DensePoly]

/-- **The symbolic root-free LRT reduced integrator.** Hermite rational part + symbolic LRT log part. For
`a/d` (reduced, normal), returns the rational antiderivative and the symbolic log terms — no roots. -/
def cIntegrateReducedLrt (Dt a d : DensePoly α) : LrtResult α :=
  let H := cHermiteReduceTower Dt a d
  ⟨(H.1.1, H.1.2), cLrtLogArg Dt H.2.1 H.2.2⟩

end DensePoly

/-! ### Validation (`ccompute`) -/

namespace DensePoly

open scoped Classical

/-- `∫ 1/(t²−1)` over `ℚ(t)`: the Hermite part is trivial (squarefree denominator), and the LRT log part is
the single symbolic term `(z²−1/4, S₁)` with `S₁(z,t) = 1 − 2z·t`. Root-free. -/
theorem cIntegrateReducedLrtG_invT2m1 :
    (cIntegrateReducedLrt ([1] : DensePoly ℚ) [1] [-1, 0, 1]).logs
      = [([-1/4, 0, 1], [[1], [0, -2]])] := by ccompute

end DensePoly

end DeepWiki.SymbolicIntegration
