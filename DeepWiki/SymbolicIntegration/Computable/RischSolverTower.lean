import DeepWiki.SymbolicIntegration.Computable.RischTowerPrimitive
import DeepWiki.SymbolicIntegration.Computable.Tower.CarrierRec

/-! # Tower-step recursion connector

The `num/1 ∈ QFunNZG β` embedding used to reassemble a recursed coefficient after
integrating it in the coefficient field `QFunNZG β = β(s)`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-- Embed a polynomial as a fraction `num/1 ∈ QFunNZG β`. -/
def qEmbedNumG {β : Type*} [CField β] [CFieldDomain β] (num : CPolyG β) : QFunNZG β :=
  ⟨(num, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

end DeepWiki.SymbolicIntegration
