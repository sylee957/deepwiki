import DeepWiki.SymbolicIntegration.Engine.RischLevelConvert
import DeepWiki.SymbolicIntegration.Engine.Tower.CarrierRec
import DeepWiki.SymbolicIntegration.Engine.Tower.RecursiveElementary

/-! # Finite compositional Risch towers

A selected Risch level packages its executable operation with soundness, genuine-log, and relative
completeness contracts. A finite dense tower is built recursively; each successor receives the
immediately lower certified stage, which exposes the canonical coefficient adapter. Sparse levels
are adapters of dense stages, never separate tower algorithms.
-/

namespace DeepWiki.SymbolicIntegration

variable {n : ℕ}

/-- A selected dense Risch level and its semantic contracts at a fixed fraction-tower depth. -/
structure DenseRischStage (n : ℕ) where
  /-- Executable level solver selected at this depth. -/
  level : CRischLevel DensePoly (DenseFracTower n)
  /-- Semantic domain selected for this level. -/
  domain : RischLevelDomain DensePoly (DenseFracTower n)
  /-- Denotational soundness of the selected level. -/
  lawful : LawfulCRischLevel level domain
  /-- Genuine Liouville logarithms of successful outputs. -/
  genuine : let _ : LawfulCRischLevel level domain := lawful
    LawfulGenuineCRischLevel level domain
  /-- Relative completeness on the selected semantic domain. -/
  complete : let _ : LawfulCRischLevel level domain := lawful
    CompleteCRischLevel level domain

/-- A selected sparse Risch level and its transported semantic contracts at a fixed depth. -/
structure SparseRischStage (n : ℕ) where
  /-- Executable sparse level solver selected at this depth. -/
  level : CRischLevel CPoly.SparsePoly (DenseFracTower n)
  /-- Semantic sparse domain selected for this level. -/
  domain : RischLevelDomain CPoly.SparsePoly (DenseFracTower n)
  /-- Denotational soundness of the selected sparse level. -/
  lawful : LawfulCRischLevel level domain
  /-- Genuine Liouville logarithms of successful sparse outputs. -/
  genuine : let _ : LawfulCRischLevel level domain := lawful
    LawfulGenuineCRischLevel level domain
  /-- Relative completeness on the selected sparse semantic domain. -/
  complete : let _ : LawfulCRischLevel level domain := lawful
    CompleteCRischLevel level domain

/-- The recursive elementary coefficient domain induced by a certified lower dense Risch level. -/
def DenseRischStage.coefficientDomain (S : DenseRischStage n) :
    RecursiveElementaryDomain (α := DenseFrac (DenseFracTower n)) :=
  recursiveElementaryOfRischLevelCompositionalDomain S.domain

/-- The lower selected level supplies a complete certificate-checked coefficient adapter. -/
theorem DenseRischStage.coefficient_complete (S : DenseRischStage n) :
    CompleteCRecursiveElementaryIntegrator (recursiveElementaryOfRischLevel S.level)
      S.coefficientDomain := by
  letI : LawfulCRischLevel S.level S.domain := S.lawful
  letI : LawfulGenuineCRischLevel S.level S.domain := S.genuine
  letI : CompleteCRischLevel S.level S.domain := S.complete
  exact completeCRecursiveElementaryIntegratorOfRischLevelCompositional S.level S.domain

/-- Convert a certified dense level into its certified sparse adapter. -/
noncomputable def DenseRischStage.toSparse (S : DenseRischStage n) : SparseRischStage n := by
  letI : LawfulCRischLevel S.level S.domain := S.lawful
  letI : LawfulGenuineCRischLevel S.level S.domain := S.genuine
  letI : CompleteCRischLevel S.level S.domain := S.complete
  let sparseLevel := convertRischLevel (Q := CPoly.SparsePoly) S.level
  let sparseDomain := convertRischLevelDomain (Q := CPoly.SparsePoly) S.domain
  letI : LawfulCRischLevel sparseLevel sparseDomain := inferInstance
  letI : LawfulGenuineCRischLevel sparseLevel sparseDomain := inferInstance
  letI : CompleteCRischLevel sparseLevel sparseDomain := inferInstance
  exact ⟨sparseLevel, sparseDomain, inferInstance, inferInstance, inferInstance⟩

/-- A finite dense tower is built from a base stage by a successor constructor that receives the
immediately lower certified stage. -/
structure DenseRischTowerScheme where
  /-- Certified selected level at the constant base. -/
  base : DenseRischStage 0
  /-- Build the next selected level from the immediately lower certified level. -/
  step : ∀ n, DenseRischStage n → DenseRischStage (n + 1)

/-- The certified dense stage selected by a tower scheme at depth `n`. -/
def DenseRischTowerScheme.stage (T : DenseRischTowerScheme) : (n : ℕ) → DenseRischStage n
  | 0 => T.base
  | n + 1 => T.step n (T.stage n)

/-- Induction over the finite tower exposes soundness at every selected depth. -/
theorem DenseRischTowerScheme.stage_lawful (T : DenseRischTowerScheme) (n : ℕ) :
    LawfulCRischLevel (T.stage n).level (T.stage n).domain := by
  induction n with
  | zero => exact T.base.lawful
  | succ n _ => exact (T.step n (T.stage n)).lawful

/-- Induction over the finite tower exposes genuine logarithms at every selected depth. -/
theorem DenseRischTowerScheme.stage_genuine (T : DenseRischTowerScheme) (n : ℕ) :
    let _ : LawfulCRischLevel (T.stage n).level (T.stage n).domain := T.stage_lawful n
    LawfulGenuineCRischLevel (T.stage n).level (T.stage n).domain := by
  induction n with
  | zero => exact T.base.genuine
  | succ n _ => exact (T.step n (T.stage n)).genuine

/-- Induction over the finite tower exposes relative completeness at every selected depth. -/
theorem DenseRischTowerScheme.stage_complete (T : DenseRischTowerScheme) (n : ℕ) :
    let _ : LawfulCRischLevel (T.stage n).level (T.stage n).domain := T.stage_lawful n
    CompleteCRischLevel (T.stage n).level (T.stage n).domain := by
  induction n with
  | zero => exact T.base.complete
  | succ n _ => exact (T.step n (T.stage n)).complete

/-- The selected sparse stage at every finite depth is the adapter of the dense selected stage. -/
noncomputable def DenseRischTowerScheme.sparseStage (T : DenseRischTowerScheme) (n : ℕ) : SparseRischStage n :=
  (T.stage n).toSparse

end DeepWiki.SymbolicIntegration
