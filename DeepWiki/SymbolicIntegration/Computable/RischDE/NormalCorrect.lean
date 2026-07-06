import DeepWiki.SymbolicIntegration.Computable.RischDE.Structural
import DeepWiki.SymbolicIntegration.Computable.RischDE.TowerGcdWitnessWf

/-! # `toPolyG` reading helpers for the recursive RDE residual

Two generic `toPolyG` reading lemmas consumed by the RDE normalization development. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG GBPolyCore

section Helpers

variable {β : Type*} [CField β] [CFieldSpec β]

/-- `cisZeroG p = false` gives `toPolyG p ≠ 0` — the contrapositive of `cisZeroG_iff`. -/
theorem toPolyG_ne_zero_of_cisZeroG_false {p : CPolyG β} (h : CPolyG.cisZeroG p = false) :
    toPolyG p ≠ 0 := by
  intro h0
  rw [(CPolyG.cisZeroG_iff p).mpr h0] at h
  exact absurd h (by simp)

end Helpers

end DeepWiki.SymbolicIntegration
