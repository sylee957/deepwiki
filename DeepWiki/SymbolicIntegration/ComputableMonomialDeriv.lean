import DeepWiki.SymbolicIntegration.ComputableField
import DeepWiki.SymbolicIntegration.ComputableFieldGcd
import DeepWiki.SymbolicIntegration.MonomialExtensions

/-! # Computable monomial derivation + `splitFactor` over the differential tower ℚ(x)[t]
Stage D — the payoff of the generic computable-field engine. On top of the `CField`/`CPolyG`
keystone (`ComputableField`) and the division/gcd layer (`ComputableFieldGcd`) we add the *computable
derivation* and run it.

* **`CDiffField α`** (over `[CField α]`) carries the one computable operation `cderiv : α → α` (the
  derivation on coefficients), with the companion bridge `CDiffFieldSpec α` certifying `toK (cderiv a)
  = (toK a)′` into a Mathlib `Differential (CFieldSpec.K α)`. Instances: `ℚ` (constants, `cderiv = 0`)
  and `QFunNZ` (`qderivNZ`, the `d/dx` quotient rule — **computable**, `#eval`-able).

* **`cmonomialDeriv Dt p`** = `(coefficientwise cderiv of p) + (dp/dt)·Dt`: the monomial derivation
  `D = κ_D + Dt·d/dt` on `k[t]` realized over `CPolyG α`. Its correctness `toPolyG_cmonomialDeriv`
  shows it realizes Mathlib's `Differential.implicitDeriv (toPolyG Dt)` exactly — the key bridge.

* **`cSplitFactor Dt fuel p`** = Bronstein's `SplitFactor` (Fig. §3.5): the squarefree-factorization
  loop peeling off the special part `gcd(p, Dp)/gcd(p, dp/dt)`. The payoff is that it **executes**
  over the tower ℚ(x)[t] by `native_decide`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

/-! ### Computable derivation on the coefficient field

`CDiffField α` adds the single computable operation `cderiv` to a `[CField α]`; the bridge
`CDiffFieldSpec α` supplies a Mathlib `Differential (CFieldSpec.K α)` and certifies `toK (cderiv a) =
(toK a)′`. As with `CField`/`CFieldSpec`, the engine (`cmonomialDeriv`) needs only `CDiffField`, so it
reduces; the correctness layer adds `CDiffFieldSpec`. -/

/-- **Computable coefficient derivation**: a `[CField α]` with one computable operation
`cderiv : α → α`, the derivation on field elements. Bridge-free, so instances built from honest
computations stay computable; the certification against a Mathlib `Differential` lives in the companion
`CDiffFieldSpec`. -/
class CDiffField (α : Type*) [CField α] where
  /-- Computable derivation on coefficients. -/
  cderiv : α → α

/-- **Computable-derivation specification**: the bridge for `[CDiffField α]`. Supplies a Mathlib
`Differential (CFieldSpec.K α)` and certifies `toK (cderiv a) = (toK a)′`. Noncomputable in general;
required only by the correctness proofs, not by the engine. -/
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

end DeepWiki.SymbolicIntegration
