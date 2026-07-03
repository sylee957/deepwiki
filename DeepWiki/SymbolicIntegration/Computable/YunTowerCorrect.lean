import DeepWiki.SymbolicIntegration.Computable.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Computable.FieldGcd
import DeepWiki.SymbolicIntegration.Computable.SplitFactorWfCorrect
import DeepWiki.SymbolicIntegration.Computable.LogPartTowerSoundness

/-! # Abstract correctness of the fuel-free Yun factorization `cSqfreeYunFFGWf`

The computable Yun loop `cSqfreeYunFFGgoWf` mirrors the abstract `yunLoopAbs`
(`HermiteCorrectness.yunLoopAbs`) step for step: each emits the monic gcd of the working pair and
recurses on the deflated pair `(b/gcd, d/gcd − (b/gcd)′)`. This file establishes the per-step bridges
through `toPolyG`, reducing to the gcd frontier `GcdFFCorrect` (unconditional at `ℚ`). -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]

omit [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α] in
/-- `cmonicG` realizes `normalize` through `toPolyG`: `toPolyG (cmonicG q) = normalize (toPolyG q)`.
The monic associate of `toPolyG q` is its normalization. -/
theorem toPolyG_cmonicG_eq_normalize (q : CPolyG α) :
    toPolyG (cmonicG q) = normalize (toPolyG q) := by
  by_cases hq : toPolyG q = 0
  · have hcm : toPolyG (cmonicG q) = 0 := by
      have := associated_toPolyG_cmonicG q
      rwa [hq, associated_zero_iff_eq_zero] at this
    rw [hcm, hq, normalize_zero]
  · have hmonic : (toPolyG (cmonicG q)).Monic := monic_toPolyG_cmonicG q hq
    have hassoc : Associated (toPolyG (cmonicG q)) (toPolyG q) := associated_toPolyG_cmonicG q
    rw [← hmonic.normalize_eq_self, normalize_eq_normalize_iff_associated.mpr hassoc]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- The emitted Yun factor denotes the exact (monic) gcd: under the gcd frontier,
`toPolyG (cmonicG (cgcdFFCoreWf b d)) = gcd (toPolyG b) (toPolyG d)`. -/
theorem toPolyG_yunEmit_eq_gcd (hgcd : GcdFFCorrect (α := α)) (b d : CPolyG α) :
    toPolyG (cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)) = gcd (toPolyG b) (toPolyG d) := by
  rw [toPolyG_cmonicG_eq_normalize, normalize_eq_normalize_iff_associated.mpr (hgcd b d),
    normalize_gcd]

end DeepWiki.SymbolicIntegration
