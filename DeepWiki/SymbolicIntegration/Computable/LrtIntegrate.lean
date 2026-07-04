import DeepWiki.SymbolicIntegration.Computable.LrtLogArg
import DeepWiki.SymbolicIntegration.Computable.HermiteValuationTower

/-! # The symbolic (root-free) LRT reduced integrator `cIntegrateReducedLrtG` (L3)

Combines the Hermite rational part (`cHermiteReduceTowerGWf`) with the symbolic Lazard–Rioboo–Trager log part
(`cLrtLogArgG`) into a `LrtResultG`: a rational function plus a list of symbolic log terms `(Rᵢ, Sᵢ)`, each
denoting `Σ_{Rᵢ(c)=0} c·log(Sᵢ(c,t))`. **No residues are computed** — this is the root-finding-free reduced
integrator. See `docs/computable-lrt.md`. -/

namespace DeepWiki.SymbolicIntegration

open Compute

/-- A symbolic-residue reduced-integration result: a rational part `gnum/gden` plus symbolic log terms
`[(Rᵢ, Sᵢ)]`, each denoting `Σ_{Rᵢ(c)=0} c·log(Sᵢ(c,t))`. -/
structure LrtResultG (α : Type*) [CField α] where
  /-- The Hermite rational part `(gnum, gden)`. -/
  rational : CPolyG α × CPolyG α
  /-- Symbolic log terms `[(Rᵢ, Sᵢ)]`: residue minimal polynomial `Rᵢ` and parametric log argument `Sᵢ(z,t)`
  (a `t`-polynomial with `z`-polynomial coefficients). -/
  logs : List (CPolyG α × List (CPolyG α))

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- **The symbolic root-free LRT reduced integrator.** Hermite rational part + symbolic LRT log part. For
`a/d` (reduced, normal), returns the rational antiderivative and the symbolic log terms — no roots. -/
def cIntegrateReducedLrtG (Dt a d : CPolyG α) : LrtResultG α :=
  let H := cHermiteReduceTowerGWf Dt a d
  ⟨(H.1.1, H.1.2), cLrtLogArgG Dt H.2.1 H.2.2⟩

end CPolyG

/-! ### Validation (`native_decide`) -/

namespace CPolyG

open scoped Classical

/-- `∫ 1/(t²−1)` over `ℚ(t)`: the Hermite part is trivial (squarefree denominator), and the LRT log part is
the single symbolic term `(z²−1/4, S₁)` with `S₁(z,t) = 1 − 2z·t`. Root-free. -/
theorem cIntegrateReducedLrtG_invT2m1 :
    (cIntegrateReducedLrtG ([1] : CPolyG ℚ) [1] [-1, 0, 1]).logs
      = [([-1/4, 0, 1], [[1], [0, -2]])] := by native_decide

end CPolyG

end DeepWiki.SymbolicIntegration
