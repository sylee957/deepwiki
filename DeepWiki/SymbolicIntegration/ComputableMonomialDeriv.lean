import DeepWiki.SymbolicIntegration.ComputableField
import DeepWiki.SymbolicIntegration.ComputableFieldGcd
import DeepWiki.SymbolicIntegration.ComputableFuelFreeGcd
import DeepWiki.SymbolicIntegration.MonomialExtensions

/-! # Computable monomial derivation and `splitFactor`

`CDiffField`/`CDiffFieldSpec` (the computable coefficient derivation and its bridge), the monomial
derivation `cmonomialDeriv Dt p = (coefficientwise cderiv of p) + (dp/dt)·Dt` realizing Mathlib's
`Differential.implicitDeriv`, and the normal/special splitting factorization `cSplitFactor`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

/-! ### Computable derivation on the coefficient field

`CDiffField α` adds the single computable operation `cderiv` to a `[CField α]`; the bridge
`CDiffFieldSpec α` supplies a Mathlib `Differential (CFieldSpec.K α)` and certifies `toK (cderiv a) =
(toK a)′`. As with `CField`/`CFieldSpec`, the engine (`cmonomialDeriv`) needs only `CDiffField`, so it
reduces; the correctness layer adds `CDiffFieldSpec`. -/

/-- Computable coefficient derivation: a `[CField α]` with one computable operation
`cderiv : α → α`. Bridge-free, so instances stay computable; the certification against a Mathlib
`Differential` lives in the companion `CDiffFieldSpec`. -/
class CDiffField (α : Type*) [CField α] where
  /-- Computable derivation on coefficients. -/
  cderiv : α → α

/-- Computable-derivation specification: the bridge for `[CDiffField α]`. Supplies a Mathlib
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

/-! ### The constant base instance `ℚ`

`ℚ` is a field of *constants* under `d/dx`, so `cderiv := 0` and its `Differential` is the zero
derivation. `cderiv` is an honest computation, so `CDiffField` stays computable. The genuine `d/dx` of
ℚ(x) lives one tower level up on the generic `QFunNZG ℚ` (`ComputableTowerDeriv`). -/

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

/-! ### The monomial derivation on `CPolyG α` (`Dt` a polynomial in `t`)

For a monomial `t` over the coefficient field with `Dt ∈ k[t]`, the derivation on `k[t]` sends
`p` to (coefficientwise `cderiv` of `p`) + `(dp/dt)·Dt`; `toPolyG_cmonomialDeriv` proves it equals
Mathlib's `Differential.implicitDeriv (toPolyG Dt)`. -/

namespace CPolyG

/-- Coefficientwise derivation `cmapDeriv p = p.map cderiv`: apply `CDiffField.cderiv` to every
coefficient (the coefficientwise part of the monomial derivation). -/
def cmapDeriv {α : Type*} [CField α] [CDiffField α] (p : CPolyG α) : CPolyG α :=
  (p : List α).map CDiffField.cderiv

/-- Monomial derivation `cmonomialDeriv Dt p = cmapDeriv p + (dp/dt)·Dt`: the derivation on `k[t]`
with `Dt` the derivative of the monomial `t`. Needs only `[CDiffField α]`, so it reduces. -/
def cmonomialDeriv {α : Type*} [CField α] [CDiffField α] (Dt p : CPolyG α) : CPolyG α :=
  caddG (cmapDeriv p) (cmulG (cderivG p) Dt)

/-- `toPolyG (cmapDeriv p) = Differential.mapCoeffs (toPolyG p)`: the coefficientwise computable
derivation realizes Mathlib's polynomial coefficient-map derivation. -/
theorem toPolyG_cmapDeriv {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]
    (p : CPolyG α) :
    toPolyG (cmapDeriv p) = Differential.mapCoeffs (toPolyG p) := by
  induction p with
  | nil => simp [cmapDeriv]
  | cons a as ih =>
    show toPolyG (CDiffField.cderiv a :: cmapDeriv as) = Differential.mapCoeffs (toPolyG (a :: as))
    rw [toPolyG_cons, ih, toPolyG_cons, map_add, Differential.mapCoeffs_C, CDiffFieldSpec.toK_cderiv,
      Derivation.leibniz, Differential.mapCoeffs_X, smul_zero, add_zero, smul_eq_mul]

/-- `toPolyG (cmonomialDeriv Dt p) = Differential.implicitDeriv (toPolyG Dt) (toPolyG p)`: the
computable monomial derivation realizes Mathlib's `implicitDeriv`. -/
theorem toPolyG_cmonomialDeriv {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]
    (Dt p : CPolyG α) :
    toPolyG (cmonomialDeriv Dt p) = Differential.implicitDeriv (toPolyG Dt) (toPolyG p) := by
  rw [cmonomialDeriv, toPolyG_caddG, toPolyG_cmapDeriv, toPolyG_cmulG, toPolyG_cderivG,
    show Differential.implicitDeriv (toPolyG Dt) (toPolyG p)
      = Differential.mapCoeffs (toPolyG p) + toPolyG Dt * Polynomial.derivative (toPolyG p) from by
        simp [Differential.implicitDeriv, derivative']]
  ring

/-! ### Computable `splitFactor`

`cSplitFactor Dt fuel p = (pₙ, pₛ)` peels off the special part `pₛ` and the normal part `pₙ` of `p`
under the monomial derivation `D` (`Dt` the derivative of `t`). The loop: `S = gcd(p, p′) /
gcd(p, dp/dt)` is the squarefree special factor of the current `p`; if it is constant (`cdegG = 0`)
the rest is normal, else recurse on `p/S` and accumulate `S` into the special part. The recursive loop is
fuel-bounded; its Euclidean leaves are fuel-free. -/

/-- **Computable splitting-factorization loop**: `cSplitFactor Dt fuel p = (pₙ, pₛ)`
with `pₛ` the special part and `pₙ` the normal part of `p` w.r.t. the monomial derivation `D`
(`Dt` = `dt/d·`). One step extracts `S = gcd(p, p′)/gcd(p, dp/dt)`; constant `S` ⇒ `p` is normal,
else recurse on `p/S`. The loop is fuel-bounded; the gcd/division leaves are fuel-free and reduce
under `native_decide`. -/
def cSplitFactor {α : Type*} [CField α] [CDiffField α] (Dt : CPolyG α) : ℕ → CPolyG α → CPolyG α × CPolyG α
  | 0, p => (p, [CField.one])
  | fuel + 1, p =>
    let S := cdivWf (cgcdWf p (cmonomialDeriv Dt p)).1
      (cgcdWf p (cderivG p)).1
    if cdegG S = 0 then (p, [CField.one])
    else
      let (qn, qs) := cSplitFactor Dt fuel (cdivWf p S)
      (qn, cmulG S qs)

end CPolyG

end DeepWiki.SymbolicIntegration
