import DeepWiki.SymbolicIntegration.Engine.Tower.Deriv
import DeepWiki.SymbolicIntegration.Core.Differential.FractionFieldDeriv

/-! # Global-recursive represented-fraction tower instances

For every lawful `CFrac F P`, `CFieldSpec.K (F α) = RatFunc (CFieldSpec.K α)`. The abstract structures
needed by the Risch tower therefore iterate uniformly through dense and sparse fraction representations. -/

namespace DeepWiki.SymbolicIntegration

universe u v

/-- `CharZero` iterates through every lawful represented-fraction tower. -/
noncomputable instance instCharZeroKCFrac
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P] [CFrac F P] [LawfulCFrac F P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P]
    [CharZero (CFieldSpec.K α)] : CharZero (CFieldSpec.K (F α)) :=
  inferInstanceAs (CharZero (RatFunc (CFieldSpec.K α)))

/-- `Algebra ℚ` iterates through every lawful represented-fraction tower. -/
noncomputable instance instAlgebraQKCFrac
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P] [CFrac F P] [LawfulCFrac F P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CFieldDomain α P]
    [Algebra ℚ (CFieldSpec.K α)] : Algebra ℚ (CFieldSpec.K (F α)) :=
  inferInstanceAs (Algebra ℚ (RatFunc (CFieldSpec.K α)))

/-- `CDiffFieldSpec` iterates through every lawful represented-fraction tower. -/
noncomputable instance instCDiffFieldSpecCFracRec
    {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P] [CFrac F P] [LawfulCFrac F P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
    [CFieldDomain α P] [Algebra ℚ (CFieldSpec.K α)] : CDiffFieldSpec (F α) where
  diffK := fractionFieldDifferential
    (Differential.implicitDeriv (CPoly.toPoly (CPoly.one : P α)))
  toK_cderiv a := by
    show CFrac.toRatFunc (CFrac.towerDerivCFracWith (CPoly.one : P α) a)
      = @Differential.deriv _ _ (fractionFieldDifferential
          (Differential.implicitDeriv (CPoly.toPoly (CPoly.one : P α)))) (CFrac.toRatFunc a)
    rw [CFrac.toRatFunc_towerDerivCFracWith (CPoly.one : P α) a]
    rfl

/-- A carrier together with the lawful computable field and differential dictionaries needed by a
dense represented-fraction tower step. -/
structure DenseTowerCarrier where
  /-- The executable carrier at this tower depth. -/
  Carrier : Type
  /-- Computable field operations on the carrier. -/
  cfield : CField Carrier
  /-- Denotation of the computable field into a mathematical field. -/
  cfieldSpec : @CFieldSpec Carrier cfield
  /-- Computable derivation on the carrier. -/
  cdiffField : @CDiffField Carrier cfield
  /-- Rational-algebra structure on the denotation field. -/
  algebraQ : let _ : CField Carrier := cfield
    let _ : CFieldSpec Carrier := cfieldSpec
    Algebra ℚ (CFieldSpec.K Carrier)
  /-- Characteristic-zero law on the denotation field. -/
  charZero : let _ : CField Carrier := cfield
    let _ : CFieldSpec Carrier := cfieldSpec
    CharZero (CFieldSpec.K Carrier)
  /-- Denotational differential-field contract on the carrier. -/
  cdiffFieldSpec : @CDiffFieldSpec Carrier cfield cfieldSpec cdiffField

/-- The constant-field base of the dense recursive fraction tower. -/
noncomputable def denseTowerBase : DenseTowerCarrier where
  Carrier := ℚ
  cfield := inferInstance
  cfieldSpec := inferInstance
  cdiffField := inferInstance
  algebraQ := inferInstanceAs (Algebra ℚ ℚ)
  charZero := inferInstanceAs (CharZero ℚ)
  cdiffFieldSpec := inferInstance

/-- Extend a packaged carrier by one dense represented-fraction level. -/
noncomputable def DenseTowerCarrier.step (T : DenseTowerCarrier) : DenseTowerCarrier := by
  letI : CField T.Carrier := T.cfield
  letI : CFieldSpec T.Carrier := T.cfieldSpec
  letI : CDiffField T.Carrier := T.cdiffField
  letI : Algebra ℚ (CFieldSpec.K T.Carrier) := T.algebraQ
  letI : CharZero (CFieldSpec.K T.Carrier) := T.charZero
  letI : CDiffFieldSpec T.Carrier := T.cdiffFieldSpec
  exact {
    Carrier := DenseFrac T.Carrier
    cfield := inferInstance
    cfieldSpec := inferInstance
    cdiffField := inferInstance
    algebraQ := inferInstance
    charZero := inferInstance
    cdiffFieldSpec := inferInstance
  }

/-- The packaged dense represented-fraction carrier obtained after `n` recursive tower steps. -/
noncomputable def denseTowerCarrier : ℕ → DenseTowerCarrier
  | 0 => denseTowerBase
  | n + 1 => (denseTowerCarrier n).step

/-- The executable dense represented-fraction carrier at tower depth `n`. -/
abbrev DenseFracTower (n : ℕ) : Type := (denseTowerCarrier n).Carrier

/-- The depth-indexed dense tower carries computable field operations. -/
noncomputable instance instCFieldDenseFracTower (n : ℕ) : CField (DenseFracTower n) :=
  (denseTowerCarrier n).cfield

/-- The depth-indexed dense tower carries a lawful field denotation. -/
noncomputable instance instCFieldSpecDenseFracTower (n : ℕ) : CFieldSpec (DenseFracTower n) :=
  (denseTowerCarrier n).cfieldSpec

/-- The depth-indexed dense tower carries a computable derivation. -/
noncomputable instance instCDiffFieldDenseFracTower (n : ℕ) : CDiffField (DenseFracTower n) :=
  (denseTowerCarrier n).cdiffField

/-- The denotation field at every dense tower depth is a `ℚ`-algebra. -/
noncomputable instance instAlgebraQDenseFracTower (n : ℕ) :
    Algebra ℚ (CFieldSpec.K (DenseFracTower n)) :=
  (denseTowerCarrier n).algebraQ

/-- The denotation field at every dense tower depth has characteristic zero. -/
noncomputable instance instCharZeroDenseFracTower (n : ℕ) :
    CharZero (CFieldSpec.K (DenseFracTower n)) :=
  (denseTowerCarrier n).charZero

/-- The depth-indexed dense tower derivation satisfies its denotational contract. -/
noncomputable instance instCDiffFieldSpecDenseFracTower (n : ℕ) :
    CDiffFieldSpec (DenseFracTower n) :=
  (denseTowerCarrier n).cdiffFieldSpec

/-- Tower depth zero is the constant field `ℚ`. -/
theorem denseFracTower_zero : DenseFracTower 0 = ℚ := rfl

/-- A successor tower depth is one dense represented-fraction extension of the preceding depth. -/
theorem denseFracTower_succ (n : ℕ) :
    DenseFracTower (n + 1) = DenseFrac (DenseFracTower n) := rfl

/-- The semantic field of a successor dense tower carrier is the preceding rational-function field. -/
theorem denseFracTower_K_succ (n : ℕ) :
    CFieldSpec.K (DenseFracTower (n + 1)) = RatFunc (CFieldSpec.K (DenseFracTower n)) := rfl

/-- The canonical embedding of one dense-tower denotation field into its successor. -/
noncomputable def denseFracTowerKStep (n : ℕ) :
    CFieldSpec.K (DenseFracTower n) →+* CFieldSpec.K (DenseFracTower (n + 1)) := by
  change CFieldSpec.K (DenseFracTower n) →+* RatFunc (CFieldSpec.K (DenseFracTower n))
  exact RatFunc.C

/-- The generic differential-denotation square resolves recursively at depth two for sparse fractions. -/
theorem sparseFrac_recursive_toK_cderiv (x : SparseFrac (SparseFrac ℚ)) :
    CFieldSpec.toK (CDiffField.cderiv x) = Differential.deriv (CFieldSpec.toK x) :=
  CDiffFieldSpec.toK_cderiv x

end DeepWiki.SymbolicIntegration
