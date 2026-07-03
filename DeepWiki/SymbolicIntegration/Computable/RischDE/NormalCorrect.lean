import DeepWiki.SymbolicIntegration.Computable.RischDE.Structural
import DeepWiki.SymbolicIntegration.Computable.RischDE.TowerGcdWitnessWf

/-! # Reducing the recursive RDE residual to its weak-normalization crux

Discharges the provable clauses of `RischDESuccessResidual` for the recursive instance
(`Dt = [CField.one]`) — denominator-nonzero from the `QFunNZG β` subtype, `hyden` from the solve
guard, `hprim` from the gcd witness — and reduces `hdvdB`/`hdvdC` to two product-divisibilities
(`fden ∣ dₙh`, `gden ∣ dₙh²`), the weak-normalization precondition on the RDE input. The remainder
is bundled as `RischDESuccessResidualCrux`, with the field identity `crischDESolve_field_of_crux`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG GBPolyCore

/-! The fuel'd RDE-residual crux + Hprim + divisibility development that once lived here was retired with
the fuel-free switch (`Tower/RischDEInstance.lean`); its fuel-free replacements live in
`RischDE/TowerGcdWitnessWf.lean` and `RischDE/Structural.lean`. Only these two generic `toPolyG` reading
helpers remain, consumed by `RischDE/SolveNorm.lean`. -/

section Helpers

variable {β : Type*} [CField β] [CFieldSpec β]

/-- `cisZeroG p = false` gives `toPolyG p ≠ 0` — the contrapositive of `cisZeroG_iff`. -/
theorem toPolyG_ne_zero_of_cisZeroG_false {p : CPolyG β} (h : CPolyG.cisZeroG p = false) :
    toPolyG p ≠ 0 := by
  intro h0
  rw [(CPolyG.cisZeroG_iff p).mpr h0] at h
  exact absurd h (by simp)

/-- `toPolyG [CField.one] = 1`: the constant `[1]` reads as the polynomial `1`. -/
theorem toPolyG_cone_eq_one : toPolyG ([CField.one] : CPolyG β) = 1 := by
  rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]

end Helpers

end DeepWiki.SymbolicIntegration
