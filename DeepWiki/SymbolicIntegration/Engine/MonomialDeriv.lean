import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd
import DeepWiki.ComputableAlgebra.PolyEngine
import DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors

/-! # Computable monomial derivation

`CDiffField`/`CDiffFieldSpec` (the computable coefficient derivation and its bridge) and the monomial
derivation `cmonomialDeriv Dt p = (coefficientwise cderiv of p) + (dp/dt)·Dt` realizing Mathlib's
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

/-! ### The monomial derivation on `DensePoly α` -/

namespace DensePoly

/-- Coefficientwise derivation: apply `CDiffField.cderiv` to every represented coefficient. -/
def cmapDeriv {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CDiffField α] (p : P α) : P α :=
  CPolyEngine.mapCoeffs CDiffField.cderiv p

/-- Monomial derivation `cmonomialDeriv Dt p = cmapDeriv p + (dp/dt)·Dt`: the derivation on `k[t]`
with `Dt` the derivative of the monomial `t`. Needs only `[CDiffField α]`, so it reduces. -/
def cmonomialDeriv {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CDiffField α] (Dt p : P α) : P α :=
  CPolyEngine.add (cmapDeriv p) (CPolyEngine.mul (CPolyEngine.deriv p) Dt)

end DensePoly

namespace CPolyEngine

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]

/-- Generic coefficientwise derivation denotes `Differential.mapCoeffs`. -/
@[denote] theorem toPoly_cmapDeriv {α : Type u} [CField α] [CDiffField α]
    [CFieldSpec.{u,v} α] [CDiffFieldSpec.{u,v} α] (p : P α) :
    CPoly.toPoly (DensePoly.cmapDeriv p) = Differential.mapCoeffs (CPoly.toPoly p) := by
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
@[denote] theorem toPoly_cmonomialDeriv {α : Type u} [CField α] [CDiffField α]
    [CFieldSpec.{u,v} α] [CDiffFieldSpec.{u,v} α] (Dt p : P α) :
    CPoly.toPoly (DensePoly.cmonomialDeriv Dt p) =
      Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly p) := by
  change CPoly.toPoly
      (CPolyEngine.add (CPolyEngine.mapCoeffs CDiffField.cderiv p)
        (CPolyEngine.mul (CPolyEngine.deriv p) Dt)) = _
  rw [LawfulCPolyEngine.toPoly_add (P := P)
      (CPolyEngine.mapCoeffs CDiffField.cderiv p)
      (CPolyEngine.mul (CPolyEngine.deriv p) Dt)]
  change CPoly.toPoly (DensePoly.cmapDeriv p) +
      CPoly.toPoly (CPolyEngine.mul (CPolyEngine.deriv p) Dt) = _
  rw [toPoly_cmapDeriv]
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
    cmapDeriv p = (p : List α).map CDiffField.cderiv := rfl

/-- Generic monomial derivation specializes to the concrete dense engine operations. -/
theorem cmonomialDeriv_dense_eq {α : Type u} [CField α] [CDiffField α]
    (Dt p : DensePoly α) :
    cmonomialDeriv Dt p = cadd (cmapDeriv p) (cmul (cderiv p) Dt) := rfl

/-- `toPoly (cmapDeriv p) = Differential.mapCoeffs (toPoly p)`: the coefficientwise computable
derivation realizes Mathlib's polynomial coefficient-map derivation. -/
@[denote] theorem toPolyG_cmapDeriv {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]
    (p : DensePoly α) :
    toPoly (cmapDeriv p) = Differential.mapCoeffs (toPoly p) := by
  induction p with
  | nil => simp [cmapDeriv]
  | cons a as ih =>
    show toPoly (CDiffField.cderiv a :: cmapDeriv as) = Differential.mapCoeffs (toPoly (a :: as))
    rw [toPolyG_cons, ih, toPolyG_cons]
    simp only [toR_eq_toK]
    rw [map_add, Differential.mapCoeffs_C, CDiffFieldSpec.toK_cderiv,
      Derivation.leibniz, Differential.mapCoeffs_X, smul_zero, add_zero, smul_eq_mul]

/-- `toPoly (cmonomialDeriv Dt p) = Differential.implicitDeriv (toPoly Dt) (toPoly p)`: the
computable monomial derivation realizes Mathlib's `implicitDeriv`. -/
@[denote] theorem toPolyG_cmonomialDeriv {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]
    (Dt p : DensePoly α) :
    toPoly (cmonomialDeriv Dt p) = Differential.implicitDeriv (toPoly Dt) (toPoly p) := by
  rw [cmonomialDeriv_dense_eq]
  simp only [denote]
  rw [show Differential.implicitDeriv (toPoly Dt) (toPoly p)
      = Differential.mapCoeffs (toPoly p) + toPoly Dt * Polynomial.derivative (toPoly p) from by
        simp [Differential.implicitDeriv, derivative']]
  ring

example :
    CPolyEngine.cdeg
      (cmonomialDeriv
        (CPoly.SparsePoly.ofList [(0, (1 : ℚ))])
        (CPoly.SparsePoly.ofList [(0, 1), (2, 3)])) = 1 := by
  ccompute


end DensePoly

end DeepWiki.SymbolicIntegration
