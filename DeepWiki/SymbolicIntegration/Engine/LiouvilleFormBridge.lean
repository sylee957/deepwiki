import DeepWiki.SymbolicIntegration.Engine.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Engine.Hermite.TowerStep
import DeepWiki.SymbolicIntegration.Engine.IntegrationSpec

/-! # Bridge: the computable log-residue sum is a sum of logarithmic derivatives

`logResidueSumG` (the engine's log-part residue sum) equals `Σ_{(c,v)} c · (Δ(amG v) / amG v)` — a sum of
constant-coefficient **logarithmic derivatives** with respect to the tower derivation `Δ =
towerFractionFieldDerivG Dt`. This is the abstract Liouville form `Σ cᵢ · logDeriv uᵢ` (Mathlib's `logDeriv x =
x′/x`), spelled with the tower derivation directly — the generic `Differential (RatFunc K)` instance is only
available on the concrete tower, so the tower-derivation spelling keeps this lemma generic over `α`.

This is bridge piece (2) toward the completeness descent `descendGenuineLrt` (see `LrtCompleteness.lean`):
it exhibits the computable log part in the abstract Liouville form, so the in-project Liouville/residue
criterion (`isLiouville_logExtension_uncond`, `ratFunc_logarithmFree_iff_residues_zero`) can be applied. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- **`IsIntegralResultG` is the explicit Liouville form.** The formal integral identity is exactly
`Δ(g) + Σ_{(c,v)} c·(Δ(amG v)/amG v) = a/d` — a rational-part derivative plus a constant-coefficient
logarithmic-derivative sum, `Δ = towerFractionFieldDerivG Dt`. This exhibits the engine's soundness predicate
directly in the abstract Liouville form (the shape `ratFunc_liouville`/`isLiouville_logExtension_uncond`
consume), the entry point for the completeness descent. -/
theorem isIntegralResultG_iff_liouvilleForm (Dt anum aden : CPolyG α) (res : IntegralResultG α) :
    IsIntegralResultG Dt anum aden res ↔
      towerFractionFieldDerivG Dt (amG α (toPolyG res.rational.1) / amG α (toPolyG res.rational.2))
        + (res.logs.map (fun cv => amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG anum) / amG α (toPolyG aden) := by
  unfold IsIntegralResultG
  rw [logResidueSumG_eq_logDeriv_sum]

end DeepWiki.SymbolicIntegration
