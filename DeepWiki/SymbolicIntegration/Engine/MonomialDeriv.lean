import DeepWiki.ComputableAlgebra.PolyEuclideanDense
import DeepWiki.ComputableAlgebra.PolyEngine
import DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors

/-! # Computable monomial derivation

`CDiffField`/`CDiffFieldSpec` (the computable coefficient derivation and its bridge) and the monomial
derivation `CPolyEngine.monomialDeriv Dt p = (coefficientwise cderiv of p) + (dp/dt)·Dt` realizing Mathlib's
`Differential.implicitDeriv`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

universe u v

/-! ### Computable derivation on the coefficient field -/

/-- Computable coefficient derivation: a `[CField α]` with one computable operation `cderiv : α → α`. -/
class CDiffField (α : Type*) [CField α] where
  /-- Computable derivation on coefficients. -/
  cderiv : α → α

/-- Bridge for `[CDiffField α]`: a Mathlib `Differential (CFieldSpec.K α)` certifying
`toK (cderiv a) = (toK a)′`. -/
class CDiffFieldSpec (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] where
  /-- The genuine Mathlib differential structure on `K = CFieldSpec.K α`. -/
  diffK : Differential (CFieldSpec.K α)
  /-- `cderiv` is intertwined with the field derivation `′` through `toK`. -/
  toK_cderiv : ∀ a,
    CFieldSpec.toK (CDiffField.cderiv a) = @Differential.deriv _ _ diffK (CFieldSpec.toK a)

/-- An explicitly selected computable derivation on a represented coefficient field.

Unlike the legacy `[CDiffField α]` instance, this is a value. A tower can therefore select a
different successor derivation at every level without asking Lean to globally choose one. -/
structure CFieldDerivation (α : Type*) [CField α] where
  /-- Computable derivative on represented coefficients. -/
  cderiv : α → α

namespace CFieldDerivation

/-- View the legacy implicit coefficient derivation as an explicit derivation dictionary. -/
def ofCDiffField (α : Type*) [CField α] [CDiffField α] : CFieldDerivation α :=
  ⟨CDiffField.cderiv⟩

end CFieldDerivation

/-- Semantic law for an explicit computable coefficient derivation and selected mathematical differential. -/
class LawfulCFieldDerivation (α : Type*) [CField α] [CFieldSpec α]
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α)) where
  /-- The computable derivative commutes with the coefficient-field denotation. -/
  toK_cderiv : ∀ a,
    CFieldSpec.toK (derivation.cderiv a) = @Differential.deriv _ _ diffK (CFieldSpec.toK a)

namespace LawfulCFieldDerivation

/-- The legacy `CDiffFieldSpec` law supplies the law for its explicit compatibility dictionary. -/
@[reducible] noncomputable def ofCDiffField (α : Type*) [CField α] [CFieldSpec α] [CDiffField α]
    [CDiffFieldSpec α] :
    LawfulCFieldDerivation α (CFieldDerivation.ofCDiffField α) CDiffFieldSpec.diffK where
  toK_cderiv := CDiffFieldSpec.toK_cderiv

end LawfulCFieldDerivation

/-- Expose `Differential (CFieldSpec.K α)` as an instance so the field derivation resolves. -/
instance instDifferentialK (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] :
    Differential (CFieldSpec.K α) :=
  CDiffFieldSpec.diffK

/-- The same derivation on `CRingSpec.R α` (= `CFieldSpec.K α`) for ring-generic `toPoly` squares. -/
instance instDifferentialR (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] :
    Differential (CRingSpec.R α) :=
  CDiffFieldSpec.diffK

/-! ### The constant base instance `ℚ` -/

/-- The zero derivation on `ℚ` — `ℚ` is a field of constants under `d/dx`. -/
noncomputable instance instDifferentialQ : Differential ℚ := ⟨0⟩

/-- `CDiffField ℚ`: rationals are constants, so the computable derivation is `0`. -/
instance instCDiffFieldQ : CDiffField ℚ where
  cderiv _ := 0

/-- `CDiffFieldSpec ℚ`: the bridge is the zero derivation on `ℚ` (`CFieldSpec.K ℚ = ℚ`,
`toK = id`). -/
noncomputable instance instCDiffFieldSpecQ : CDiffFieldSpec ℚ where
  diffK := instDifferentialQ
  toK_cderiv a := by
    show (0 : ℚ) = @Differential.deriv _ _ instDifferentialQ a
    show (0 : ℚ) = (0 : Derivation ℤ ℚ ℚ) a
    rw [Derivation.coe_zero]; rfl

/-! ### Representation-independent monomial derivation -/

namespace CPolyEngine

/-- Coefficientwise application of an explicitly selected computable derivation. -/
def mapDerivWith {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] (derivation : CFieldDerivation α) (p : P α) : P α :=
  CPolyEngine.mapCoeffs derivation.cderiv p

/-- The monomial derivation selected by an explicit coefficient derivation and monomial derivative. -/
def monomialDerivWith {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] (derivation : CFieldDerivation α) (Dt p : P α) : P α :=
  CPolyEngine.add (mapDerivWith derivation p) (CPolyEngine.mul (CPolyEngine.deriv p) Dt)

/-- Coefficientwise derivation: apply `CDiffField.cderiv` to every represented coefficient. -/
def mapDeriv {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CDiffField α] (p : P α) : P α :=
  mapDerivWith (CFieldDerivation.ofCDiffField α) p

/-- Monomial derivation `monomialDeriv Dt p = mapDeriv p + (dp/dt)·Dt`: the derivation on `k[t]`
with `Dt` the derivative of the monomial `t`. Needs only `[CDiffField α]`, so it reduces. -/
def monomialDeriv {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CDiffField α] (Dt p : P α) : P α :=
  monomialDerivWith (CFieldDerivation.ofCDiffField α) Dt p

/-- The explicit compatibility dictionary gives the legacy coefficientwise derivation. -/
@[simp] theorem mapDerivWith_ofCDiffField {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CDiffField α] (p : P α) :
    mapDerivWith (CFieldDerivation.ofCDiffField α) p = mapDeriv p := rfl

/-- The explicit compatibility dictionary gives the legacy monomial derivation. -/
@[simp] theorem monomialDerivWith_ofCDiffField {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CDiffField α] (Dt p : P α) :
    monomialDerivWith (CFieldDerivation.ofCDiffField α) Dt p = monomialDeriv Dt p := rfl

end CPolyEngine

namespace CPolyEngine

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]

/-- An explicit coefficientwise derivation denotes `Differential.mapCoeffs`. -/
@[denote] theorem toPoly_mapDerivWith {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    [LawfulCFieldDerivation α derivation diffK] (p : P α) :
    letI : Differential (CRingSpec.R α) :=
    diffK
    CPoly.toPoly (CPolyEngine.mapDerivWith derivation p) =
      Differential.mapCoeffs (CPoly.toPoly p) := by
  letI : Differential (CRingSpec.R α) := diffK
  have hzero : CRingSpec.toR (derivation.cderiv (CCommRing.zero : α)) = 0 := by
    simp only [toR_eq_toK]
    rw [LawfulCFieldDerivation.toK_cderiv (diffK := diffK), CFieldSpec.toK_zero, map_zero]
  apply Polynomial.ext
  intro i
  rw [CPoly.coeff_toPoly, Differential.coeff_mapCoeffs, CPoly.coeff_toPoly]
  change CRingSpec.toR
      (CPoly.coeff (CPolyEngine.mapCoeffs derivation.cderiv p) i) = _
  calc
    CRingSpec.toR (CPoly.coeff (CPolyEngine.mapCoeffs derivation.cderiv p) i) =
        CRingSpec.toR (derivation.cderiv (CPoly.coeff p i)) :=
      LawfulCPolyEngine.toR_coeff_mapCoeffs (P := P) derivation.cderiv hzero p i
    _ = (CRingSpec.toR (CPoly.coeff p i))′ := by
      simpa only [toR_eq_toK] using
        LawfulCFieldDerivation.toK_cderiv (diffK := diffK) (CPoly.coeff p i)

/-- An explicit monomial derivation denotes `Differential.implicitDeriv`. -/
@[denote] theorem toPoly_monomialDerivWith {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    [LawfulCFieldDerivation α derivation diffK] (Dt p : P α) :
    letI : Differential (CRingSpec.R α) :=
    diffK
    CPoly.toPoly (CPolyEngine.monomialDerivWith derivation Dt p) =
      Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly p) := by
  letI : Differential (CRingSpec.R α) := diffK
  change CPoly.toPoly
      (CPolyEngine.add (CPolyEngine.mapDerivWith derivation p)
        (CPolyEngine.mul (CPolyEngine.deriv p) Dt)) = _
  rw [LawfulCPolyEngine.toPoly_add (P := P)
      (CPolyEngine.mapDerivWith derivation p)
      (CPolyEngine.mul (CPolyEngine.deriv p) Dt)]
  rw [toPoly_mapDerivWith derivation diffK]
  rw [LawfulCPolyEngine.toPoly_mul (P := P) (CPolyEngine.deriv p) Dt]
  rw [LawfulCPolyEngine.toPoly_deriv (P := P) p]
  rw [show Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly p) =
      Differential.mapCoeffs (CPoly.toPoly p) +
        CPoly.toPoly Dt * Polynomial.derivative (CPoly.toPoly p) from by
    simp [Differential.implicitDeriv, derivative']]
  ring

/-- Generic coefficientwise derivation denotes `Differential.mapCoeffs`. -/
@[denote] theorem toPoly_mapDeriv {α : Type u} [CField α] [CDiffField α]
    [CFieldSpec.{u,v} α] [CDiffFieldSpec.{u,v} α] (p : P α) :
    CPoly.toPoly (CPolyEngine.mapDeriv p) = Differential.mapCoeffs (CPoly.toPoly p) := by
  have hzero : CRingSpec.toR (CDiffField.cderiv (CCommRing.zero : α)) = 0 := by
    simp only [toR_eq_toK]
    rw [CDiffFieldSpec.toK_cderiv, CFieldSpec.toK_zero, map_zero]
  apply Polynomial.ext
  intro i
  rw [CPoly.coeff_toPoly, Differential.coeff_mapCoeffs, CPoly.coeff_toPoly]
  change CRingSpec.toR
      (CPoly.coeff (CPolyEngine.mapCoeffs CDiffField.cderiv p) i) = _
  calc
    CRingSpec.toR (CPoly.coeff (CPolyEngine.mapCoeffs CDiffField.cderiv p) i) =
        CRingSpec.toR (CDiffField.cderiv (CPoly.coeff p i)) :=
      LawfulCPolyEngine.toR_coeff_mapCoeffs (P := P) CDiffField.cderiv hzero p i
    _ = (CRingSpec.toR (CPoly.coeff p i))′ := by
      simpa only [toR_eq_toK] using CDiffFieldSpec.toK_cderiv (CPoly.coeff p i)

/-- Generic monomial derivation denotes `Differential.implicitDeriv`. -/
@[denote] theorem toPoly_monomialDeriv {α : Type u} [CField α] [CDiffField α]
    [CFieldSpec.{u,v} α] [CDiffFieldSpec.{u,v} α] (Dt p : P α) :
    CPoly.toPoly (CPolyEngine.monomialDeriv Dt p) =
      Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly p) := by
  change CPoly.toPoly
      (CPolyEngine.add (CPolyEngine.mapCoeffs CDiffField.cderiv p)
        (CPolyEngine.mul (CPolyEngine.deriv p) Dt)) = _
  rw [LawfulCPolyEngine.toPoly_add (P := P)
      (CPolyEngine.mapCoeffs CDiffField.cderiv p)
      (CPolyEngine.mul (CPolyEngine.deriv p) Dt)]
  change CPoly.toPoly (CPolyEngine.mapDeriv p) +
      CPoly.toPoly (CPolyEngine.mul (CPolyEngine.deriv p) Dt) = _
  rw [toPoly_mapDeriv]
  rw [LawfulCPolyEngine.toPoly_mul (P := P) (CPolyEngine.deriv p) Dt]
  rw [LawfulCPolyEngine.toPoly_deriv (P := P) p]
  rw [show Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly p) =
      Differential.mapCoeffs (CPoly.toPoly p) +
        CPoly.toPoly Dt * Polynomial.derivative (CPoly.toPoly p) from by
    simp [Differential.implicitDeriv, derivative']]
  ring

end CPolyEngine

namespace DensePoly

/-- Generic coefficientwise derivation specializes to concrete dense list mapping. -/
theorem cmapDeriv_dense_eq {α : Type u} [CField α] [CDiffField α] (p : DensePoly α) :
    CPolyEngine.mapDeriv p = (p : List α).map CDiffField.cderiv := rfl

/-- Generic monomial derivation specializes to the concrete dense engine operations. -/
theorem cmonomialDeriv_dense_eq {α : Type u} [CField α] [CDiffField α]
    (Dt p : DensePoly α) :
    CPolyEngine.monomialDeriv Dt p =
      cadd (CPolyEngine.mapDeriv p) (cmul (cderiv p) Dt) := rfl

/-- `toPoly (CPolyEngine.mapDeriv p) = Differential.mapCoeffs (toPoly p)`: the coefficientwise computable
derivation realizes Mathlib's polynomial coefficient-map derivation. -/
@[denote] theorem toPolyG_cmapDeriv {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]
    (p : DensePoly α) :
    toPoly (CPolyEngine.mapDeriv p) = Differential.mapCoeffs (toPoly p) := by
  induction p with
  | nil => simp [CPolyEngine.mapDeriv, CPolyEngine.mapDerivWith]
  | cons a as ih =>
    show toPoly (CDiffField.cderiv a :: CPolyEngine.mapDeriv as) =
      Differential.mapCoeffs (toPoly (a :: as))
    rw [toPolyG_cons, ih, toPolyG_cons]
    simp only [toR_eq_toK]
    rw [map_add, Differential.mapCoeffs_C, CDiffFieldSpec.toK_cderiv,
      Derivation.leibniz, Differential.mapCoeffs_X, smul_zero, add_zero, smul_eq_mul]

/-- `toPoly (CPolyEngine.monomialDeriv Dt p) = Differential.implicitDeriv (toPoly Dt) (toPoly p)`: the
computable monomial derivation realizes Mathlib's `implicitDeriv`. -/
@[denote] theorem toPolyG_cmonomialDeriv {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]
    (Dt p : DensePoly α) :
    toPoly (CPolyEngine.monomialDeriv Dt p) =
      Differential.implicitDeriv (toPoly Dt) (toPoly p) := by
  rw [cmonomialDeriv_dense_eq]
  simp only [denote]
  rw [show Differential.implicitDeriv (toPoly Dt) (toPoly p)
      = Differential.mapCoeffs (toPoly p) + toPoly Dt * Polynomial.derivative (toPoly p) from by
        simp [Differential.implicitDeriv, derivative']]
  ring

example :
    CPoly.toPoly
        (CPolyEngine.monomialDeriv
          (CPoly.SparsePoly.ofList [(0, (1 : ℚ))])
          (CPoly.SparsePoly.ofList [(0, 1), (2, 3)])) =
      Differential.implicitDeriv
        (CPoly.toPoly (CPoly.SparsePoly.ofList [(0, (1 : ℚ))]))
        (CPoly.toPoly (CPoly.SparsePoly.ofList [(0, (1 : ℚ)), (2, 3)])) :=
  CPolyEngine.toPoly_monomialDeriv _ _


end DensePoly

end DeepWiki.SymbolicIntegration
