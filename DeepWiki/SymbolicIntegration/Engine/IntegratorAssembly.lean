import DeepWiki.SymbolicIntegration.Engine.UnifiedFuelFree
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.NormalCore
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.Special
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.FullSoundness
import DeepWiki.ComputableAlgebra.PolyEuclideanDense
import DeepWiki.SymbolicIntegration.Engine.FuelFreeDiophantine
import DeepWiki.SymbolicIntegration.Engine.LogPartTowerSoundness
import DeepWiki.SymbolicIntegration.Engine.Hermite.TowerStep
import DeepWiki.SymbolicIntegration.Engine.Hermite.ValuationTower
import DeepWiki.SymbolicIntegration.Engine.OneShotAssembly
import DeepWiki.SymbolicIntegration.Engine.Hermite.Reduction
import DeepWiki.SymbolicIntegration.Engine.Hermite.ReductionRealization
import DeepWiki.SymbolicIntegration.Engine.ResidueLogPart
import DeepWiki.SymbolicIntegration.Engine.Assemble

/-! # The generic one-level Risch assembler

This file defines concrete canonical-split accessors (`crPoly`/…) and their reconstruction theorem.
-/

namespace DeepWiki.SymbolicIntegration

open DensePoly
open CFrac Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CPolySplitFactor DensePoly α] [Algebra ℚ (CFieldSpec.K α)]

/-- From `a = q·d + r`, `d = dₛ·dₙ`, and `b·dₙ + c·dₛ = r`, the pieces recombine:
`q + b/dₛ + c/dₙ = a/d`. -/
private theorem canonicalRepFast_field_identity {K : Type*} [Field K] (a d q r dn ds b c : K[X])
    (hd : d ≠ 0) (hdn : dn ≠ 0) (hds : ds ≠ 0)
    (hadiv : a = q * d + r) (hsplit : d = ds * dn) (hbcr : b * dn + c * ds = r) :
    (algebraMap K[X] (RatFunc K) q)
        + algebraMap K[X] (RatFunc K) b / algebraMap K[X] (RatFunc K) ds
        + algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) dn
      = algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) d := by
  set A := algebraMap K[X] (RatFunc K) with hA
  have hAd : A d ≠ 0 := RatFunc.algebraMap_ne_zero hd
  have hAdn : A dn ≠ 0 := RatFunc.algebraMap_ne_zero hdn
  have hAds : A ds ≠ 0 := RatFunc.algebraMap_ne_zero hds
  have hAa : A a = A q * (A ds * A dn) + (A b * A dn + A c * A ds) := by
    rw [hadiv, hsplit, ← hbcr]; push_cast [hA]; ring
  rw [show A d = A ds * A dn by rw [hsplit, map_mul]]
  rw [eq_div_iff (mul_ne_zero hAds hAdn), hAa]
  field_simp
  ring

/-- Polynomial part `fₚ` of `canonicalRepresentationFast Dt a d`. -/
abbrev crPoly (Dt a d : DensePoly α) : DensePoly α := (canonicalRepresentationFast Dt a d).1
/-- Special-part numerator `b` of the canonical split. -/
abbrev crSpecNum (Dt a d : DensePoly α) : DensePoly α := (canonicalRepresentationFast Dt a d).2.1.1
/-- Special-part denominator `dₛ` of the canonical split. -/
abbrev crSpecDen (Dt a d : DensePoly α) : DensePoly α := (canonicalRepresentationFast Dt a d).2.1.2
/-- Normal-part numerator `cₙ` of the canonical split. -/
abbrev crNormNum (Dt a d : DensePoly α) : DensePoly α := (canonicalRepresentationFast Dt a d).2.2.1
/-- Normal-part denominator `dₙ` of the canonical split. -/
abbrev crNormDen (Dt a d : DensePoly α) : DensePoly α := (canonicalRepresentationFast Dt a d).2.2.2
omit [CDiffFieldSpec α] [CRischField α] [Algebra ℚ (CFieldSpec.K α)] in
/-- Canonical split pieces recombine as `⟦fₚ⟧ + ⟦b/dₛ⟧ + ⟦cₙ/dₙ⟧ = ⟦a/d⟧`. -/
theorem canonicalReconstruction (Dt a d : DensePoly α)
    (hd : toPoly d ≠ 0)
    (hdn : toPoly (crNormDen Dt a d) ≠ 0)
    (hds : toPoly (crSpecDen Dt a d) ≠ 0)
    (hsplit : toPoly d = toPoly (crSpecDen Dt a d) * toPoly (crNormDen Dt a d))
    (hgdeg : (toPoly (CPolyEuclidean.gcdExt (crNormDen Dt a d) (crSpecDen Dt a d)).1).natDegree = 0)
    (hgne : toPoly (CPolyEuclidean.gcdExt (crNormDen Dt a d) (crSpecDen Dt a d)).1 ≠ 0) :
    fieldFrac (crPoly Dt a d) [CCommRing.one]
        + fieldFrac (crSpecNum Dt a d) (crSpecDen Dt a d)
        + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d)
      = fieldFrac a d := by
  set qr := CPolyEuclidean.divmod a d with hqr
  set sn := CPoly.splitFactor Dt d with hsn
  set uw := CPoly.bezoutOne sn.1 sn.2 with huw
  set bc := CPoly.extendedEuclideanSplit sn.1 sn.2 qr.2 uw.1 uw.2 with hbc
  have hcanon : canonicalRepresentationFast Dt a d = (qr.1, (bc.1, sn.2), (bc.2, sn.1)) := by
    rw [canonicalRepresentationFast, ← hqr, ← hsn, ← huw, ← hbc]
  simp only [crPoly, crSpecNum, crSpecDen, crNormNum, crNormDen, fieldFrac, hcanon] at hdn hds hsplit hgdeg hgne ⊢
  have hcnd : cnorm d ≠ [] := fun h => hd ((cisZeroG_iff d).mp (by simp [cisZero, h]))
  have hcns : cnorm sn.2 ≠ [] := fun h => hds ((cisZeroG_iff sn.2).mp (by simp [cisZero, h]))
  have hbez : toPoly uw.1 * toPoly sn.1 + toPoly uw.2 * toPoly sn.2 = 1 :=
    toPolyG_bezoutOne sn.1 sn.2 hgdeg hgne
  have hadiv : toPoly a = toPoly qr.1 * toPoly d + toPoly qr.2 :=
    toPolyG_divmod a d hcnd
  have hbcr : toPoly bc.1 * toPoly sn.1 + toPoly bc.2 * toPoly sn.2 = toPoly qr.2 :=
    toPolyG_extendedEuclideanSplit sn.1 sn.2 qr.2 uw.1 uw.2 hcns hbez
  have hone : am α (toPoly ([CCommRing.one] : DensePoly α)) = 1 := by
    simp only [denote]
    simp
  rw [hone, div_one]
  exact canonicalRepFast_field_identity (toPoly a) (toPoly d) (toPoly qr.1) (toPoly qr.2)
    (toPoly sn.1) (toPoly sn.2) (toPoly bc.1) (toPoly bc.2) hd hdn hds hadiv hsplit hbcr

end DeepWiki.SymbolicIntegration
