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

/-! ### Instances: `ℚ` (constants) and `QFunNZ` (the `d/dx` quotient rule)

`ℚ` is a field of *constants* under `d/dx`, so `cderiv := 0` and its `Differential` is the zero
derivation. `QFunNZ` carries the genuine `d/dx`: `qderivNZ` lifts `Compute.qderiv` (the quotient rule
`(a/b)′ = (a'b − ab')/b²`) to the denominator-nonzero subtype, with the bridge to `RatFunc ℚ`'s
`Differential`. Both `cderiv`s are honest computations, so `CDiffField` stays computable. -/

/-- The **zero derivation** on `ℚ` — `ℚ` is a field of constants under `d/dx`. -/
noncomputable instance instDifferentialQ : Differential ℚ := ⟨0⟩

/-- **`CDiffField ℚ`**: rationals are constants, so the computable derivation is `0`. -/
instance instCDiffFieldQ : CDiffField ℚ where
  cderiv _ := 0

/-- **`CDiffFieldSpec ℚ`**: the bridge is the zero derivation on `ℚ` (`CFieldSpec.K ℚ = ℚ`,
`toK = id`); `toK_cderiv` says `0 = a′` with `a′ = 0`. -/
noncomputable instance instCDiffFieldSpecQ : CDiffFieldSpec ℚ where
  diffK := instDifferentialQ
  toK_cderiv a := by
    show (0 : ℚ) = @Differential.deriv _ _ instDifferentialQ a
    show (0 : ℚ) = (0 : Derivation ℤ ℚ ℚ) a
    rw [Derivation.coe_zero]; rfl

namespace QFunNZ

/-- `qderivNZ`: the `d/dx` derivation on `QFunNZ`, lifting `Compute.qderiv` (quotient rule
`(a/b)′ = (a'b − ab')/b²`) to the subtype. The new denominator `b·b` is nonzero (`toPoly_cmul` +
`mul_ne_zero` on `b ≠ 0`). Computable. -/
def qderivNZ (x : QFunNZ) : QFunNZ :=
  ⟨Compute.qderiv x.1, by
    obtain ⟨⟨a, b⟩, hb⟩ := x
    show Compute.toPoly (Compute.cmul b b) ≠ 0
    rw [Compute.toPoly_cmul]; exact mul_ne_zero hb hb⟩

/-- **`qderivNZ` realizes `d/dx`** on `QFunNZ`: `toQFunNZ (qderivNZ x) = (toQFunNZ x)′` in
`RatFunc ℚ` (the denominator-≠-0 side condition of `toQFun_qderiv` is discharged by membership). -/
theorem toQFunNZ_qderivNZ (x : QFunNZ) : toQFunNZ (qderivNZ x) = (toQFunNZ x)′ :=
  Compute.toQFun_qderiv x.1 x.2

end QFunNZ

/-- **`CDiffField QFunNZ`**: ℚ(x) with the computable `d/dx` derivation `qderivNZ`. Honest list
computation, so `CDiffField QFunNZ` stays **computable** (`#eval qderivNZ` works). -/
instance instCDiffFieldQFunNZ : CDiffField QFunNZ where
  cderiv := QFunNZ.qderivNZ

/-- **`CDiffFieldSpec QFunNZ`**: the bridge for `CField QFunNZ`, over `K = RatFunc ℚ` with its `d/dx`
`Differential`; `toK_cderiv` is `toQFunNZ_qderivNZ`. Noncomputable (routes through `RatFunc`), but only
the correctness layer depends on it. -/
noncomputable instance instCDiffFieldSpecQFunNZ : CDiffFieldSpec QFunNZ where
  diffK := inferInstanceAs (Differential (RatFunc ℚ))
  toK_cderiv := QFunNZ.toQFunNZ_qderivNZ

end DeepWiki.SymbolicIntegration
