import DeepWiki.SymbolicIntegration.Engine.LrtLogArg
import DeepWiki.SymbolicIntegration.Engine.Hermite.ValuationTower

/-! # The symbolic (root-free) LRT reduced integrator `cIntegrateReducedLrt` (L3)

Combines the Hermite rational part (`cHermiteReduceTower`) with the symbolic Lazard–Rioboo–Trager log part
(`cLrtLogArg`) into a `LrtResultG`: a rational function plus a list of symbolic log terms `(Rᵢ, Sᵢ)`, each
denoting `Σ_{Rᵢ(c)=0} c·log(Sᵢ(c,t))`. **No residues are computed** — this is the root-finding-free reduced
integrator. See `docs/computable-lrt.md`. -/

namespace DeepWiki.SymbolicIntegration


/-- A symbolic-residue reduced-integration result: a rational part `gnum/gden` plus symbolic log terms
`[(Rᵢ, Sᵢ)]`, each denoting `Σ_{Rᵢ(c)=0} c·log(Sᵢ(c,t))`. -/
structure LrtResultG (α : Type*) [CField α] where
  /-- The Hermite rational part `(gnum, gden)`. -/
  rational : CPoly α × CPoly α
  /-- Symbolic log terms `[(Rᵢ, Sᵢ)]`: residue minimal polynomial `Rᵢ` and parametric log argument `Sᵢ(z,t)`
  (a `t`-polynomial with `z`-polynomial coefficients). -/
  logs : List (CPoly α × List (CPoly α))

namespace CPoly

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- **The symbolic root-free LRT reduced integrator.** Hermite rational part + symbolic LRT log part. For
`a/d` (reduced, normal), returns the rational antiderivative and the symbolic log terms — no roots. -/
def cIntegrateReducedLrt (Dt a d : CPoly α) : LrtResultG α :=
  let H := cHermiteReduceTower Dt a d
  ⟨(H.1.1, H.1.2), cLrtLogArg Dt H.2.1 H.2.2⟩

end CPoly

/-! ### Validation (`native_decide`) -/

namespace CPoly

open scoped Classical

/-- `∫ 1/(t²−1)` over `ℚ(t)`: the Hermite part is trivial (squarefree denominator), and the LRT log part is
the single symbolic term `(z²−1/4, S₁)` with `S₁(z,t) = 1 − 2z·t`. Root-free. -/
theorem cIntegrateReducedLrtG_invT2m1 :
    (cIntegrateReducedLrt ([1] : CPoly ℚ) [1] [-1, 0, 1]).logs
      = [([-1/4, 0, 1], [[1], [0, -2]])] := by native_decide

end CPoly

end DeepWiki.SymbolicIntegration
