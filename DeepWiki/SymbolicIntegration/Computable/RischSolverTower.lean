import DeepWiki.SymbolicIntegration.Computable.RischTowerPrimitive
import DeepWiki.SymbolicIntegration.Computable.Tower.CarrierRec

/-! # The tower-step recursion connector (`qEmbedNumG`)

The `num/1 ∈ QFunNZG β` embedding used to reassemble a recursed coefficient after integrating it in the
coefficient field `QFunNZG β = β(s)` (carrier derivation `Ds = [1]`, `s` an independent variable).

The generic polynomial-part coefficient recursion is now the **degree-raising** `cIntegratePrimPolyDegRaiseG`
(`LimitedIntegrateSingle.lean`, Bronstein `IntegratePrimitivePolynomial`, Thm 5.8.1) with telescoping soundness
`cIntegratePrimPolyDegRaiseG_sound` — it **supersedes** the former fixed-degree top-down recursion
`cLimitedIntegratePolyRatG` (retired here; it was the `c = 0` special case, unable to emit the degree-raising
`c·tᵐ⁺¹/(m+1)` term). See `docs/tower-limited-integration.md`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-- Embed a polynomial as a fraction `num/1 ∈ QFunNZG β`. -/
def qEmbedNumG {β : Type*} [CField β] [CFieldDomain β] (num : CPolyG β) : QFunNZG β :=
  ⟨(num, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

end DeepWiki.SymbolicIntegration
