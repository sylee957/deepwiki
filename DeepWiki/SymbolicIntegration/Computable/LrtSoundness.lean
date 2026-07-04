import DeepWiki.SymbolicIntegration.Computable.LrtIntegrate
import DeepWiki.SymbolicIntegration.Computable.IntegrateTowerCorrectG

/-! # Symbolic-log soundness for the root-free LRT reduced integrator (G5, pass P1)

`IsIntegralResultLrtG` — the soundness contract for `cIntegrateReducedLrtG`'s **symbolic** log part
`[(Rᵢ, Sᵢ)]`, denoting `Σᵢ Σ_{Rᵢ(c)=0} c·(Δ Sᵢ(c,t))/Sᵢ(c,t)`. To handle **algebraic** residues without
building a `Differential (AlgebraicClosure K)` instance, it is stated over an arbitrary differential
extension `E` of `K = CFieldSpec.K α` in which every `Rᵢ` splits (the descent vehicle): `extendDeriv` /
`Differential.implicitDeriv` are already generic over any such `E`. See `docs/g5-lrt-soundness.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

section Ext

variable {E : Type*} [Field E] [Algebra (CFieldSpec.K α) E]

/-- Base-change of a `K`-polynomial to `RatFunc E` (`K = CFieldSpec.K α`). -/
noncomputable def amGExt (p : (CFieldSpec.K α)[X]) : RatFunc E :=
  algebraMap E[X] (RatFunc E) (p.map (algebraMap (CFieldSpec.K α) E))

/-- The symbolic log argument `Sᵢ` (a list of `z`-polynomials, one per `t`-power) evaluated at a residue
`c ∈ E`: the `E[t]` polynomial `Σₖ (Sᵢ[k] at z=c)·tᵏ`. -/
noncomputable def evalLrtArg (Si : List (CPolyG α)) (c : E) : E[X] :=
  (Si.zipIdx.map (fun p =>
    C ((toPolyG p.1).eval₂ (algebraMap (CFieldSpec.K α) E) c) * X ^ p.2)).sum

variable [Differential E] [Algebra ℚ E]

/-- The `E`-tower derivation on `RatFunc E`: `extendDeriv` of `implicitDeriv (Dt base-changed to E)`. The
generic (any differential extension `E`) analogue of `towerFractionFieldDerivG`. -/
noncomputable def towerDerivExt (Dt : CPolyG α) : Derivation ℤ (RatFunc E) (RatFunc E) :=
  extendDeriv (Differential.implicitDeriv ((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E)))

/-- The **algebraic residue sum** over `E`: `Σᵢ Σ_{c ∈ roots(Rᵢ in E)} c·(Δ Sᵢ(c,t))/Sᵢ(c,t)` — the honest
denotation of the symbolic LRT log part, summing over the residues (roots of each `Rᵢ`) in `E`. -/
noncomputable def logResidueSumLrtG (Dt : CPolyG α)
    (logs : List (CPolyG α × List (CPolyG α))) : RatFunc E :=
  (logs.map (fun p =>
    (((toPolyG p.1).map (algebraMap (CFieldSpec.K α) E)).roots.map (fun c =>
      algebraMap E (RatFunc E) c
        * (towerDerivExt Dt (algebraMap E[X] (RatFunc E) (evalLrtArg p.2 c))
            / algebraMap E[X] (RatFunc E) (evalLrtArg p.2 c)))).sum)).sum

end Ext

/-- **Symbolic-log soundness for the LRT reduced result.** Over **any** differential extension `E` of `K =
CFieldSpec.K α` in which every residue polynomial `Rᵢ` splits, the `E`-tower derivative of the rational part
plus the algebraic residue sum equals `anum/aden` (base-changed to `E`). The `E`-quantification + splitting
hypothesis is the descent vehicle (instantiate `E` at a splitting field to prove; injectivity of the base
change gives the `K`-level statement). This is the root-free analogue of `IsIntegralResultG` handling
algebraic residues. -/
def IsIntegralResultLrtG (Dt anum aden : CPolyG α) (res : LrtResultG α) : Prop :=
  ∀ (E : Type*) [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
    [DifferentialAlgebra (CFieldSpec.K α) E],
    (∀ p ∈ res.logs,
      Polynomial.Splits ((toPolyG p.1).map (algebraMap (CFieldSpec.K α) E))) →
    (towerDerivExt Dt (amGExt (toPolyG res.rational.1) / amGExt (toPolyG res.rational.2))
          + logResidueSumLrtG Dt res.logs : RatFunc E)
      = amGExt (toPolyG anum) / amGExt (toPolyG aden)

end DeepWiki.SymbolicIntegration
