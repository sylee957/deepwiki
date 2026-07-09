import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors

/-! # Computable monomial derivation

`CDiffField`/`CDiffFieldSpec` (the computable coefficient derivation and its bridge) and the monomial
derivation `cmonomialDeriv Dt p = (coefficientwise cderiv of p) + (dp/dt)·Dt` realizing Mathlib's
`Differential.implicitDeriv`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

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

/-- Coefficientwise derivation `cmapDeriv p = p.map cderiv`: apply `CDiffField.cderiv` to every
coefficient (the coefficientwise part of the monomial derivation). -/
def cmapDeriv {α : Type*} [CField α] [CDiffField α] (p : DensePoly α) : DensePoly α :=
  (p : List α).map CDiffField.cderiv

/-- Monomial derivation `cmonomialDeriv Dt p = cmapDeriv p + (dp/dt)·Dt`: the derivation on `k[t]`
with `Dt` the derivative of the monomial `t`. Needs only `[CDiffField α]`, so it reduces. -/
def cmonomialDeriv {α : Type*} [CField α] [CDiffField α] (Dt p : DensePoly α) : DensePoly α :=
  cadd (cmapDeriv p) (cmul (cderiv p) Dt)

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
  rw [cmonomialDeriv]
  simp only [denote]
  rw [show Differential.implicitDeriv (toPoly Dt) (toPoly p)
      = Differential.mapCoeffs (toPoly p) + toPoly Dt * Polynomial.derivative (toPoly p) from by
        simp [Differential.implicitDeriv, derivative']]
  ring


end DensePoly

end DeepWiki.SymbolicIntegration
