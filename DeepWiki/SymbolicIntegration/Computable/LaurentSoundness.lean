import DeepWiki.SymbolicIntegration.Computable.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.LaurentCore
import DeepWiki.SymbolicIntegration.Computable.RischFieldSpec

/-! # Laurent integrator soundness (M1: the derivation kernel)

Toward discharging the hyperexp assembler's `hLaurField`: the base↔tower derivation bridge on polynomial
images and the hyperexponential power rule `D(tᵏ) = k·η·tᵏ`. See `docs/laurent-soundness.md`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- **The tower derivative of a polynomial image is the image of `cmonomialDeriv`**:
`D_tower(⟦p⟧) = ⟦cmonomialDeriv Dt p⟧`. Grounds every Laurent-term computation at the polynomial level
(`extendDeriv_algebraMap` + `toPolyG_cmonomialDeriv`). -/
theorem towerFractionFieldDerivG_amG_poly (Dt p : CPolyG α) :
    towerFractionFieldDerivG Dt (amG α (toPolyG p)) = amG α (toPolyG (cmonomialDeriv Dt p)) := by
  rw [towerFractionFieldDerivG, extendDeriv_algebraMap, toPolyG_cmonomialDeriv]

end DeepWiki.SymbolicIntegration
