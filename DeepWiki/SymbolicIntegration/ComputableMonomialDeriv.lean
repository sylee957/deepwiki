import DeepWiki.SymbolicIntegration.ComputableField
import DeepWiki.SymbolicIntegration.ComputableFieldGcd
import DeepWiki.SymbolicIntegration.MonomialExtensions

/-! # Computable monomial derivation + `splitFactor` over the differential tower ℚ(x)[t]
Built on the generic computable-field engine (`CField`/`CPolyG`) and its division/gcd layer, this
file adds the *computable derivation* and runs it.

* **`CDiffField α`** (over `[CField α]`) carries the one computable operation `cderiv : α → α` (the
  derivation on coefficients), with the companion bridge `CDiffFieldSpec α` certifying `toK (cderiv a)
  = (toK a)′` into a Mathlib `Differential (CFieldSpec.K α)`. Instances: `ℚ` (constants, `cderiv = 0`)
  and `QFunNZ` (`qderivNZ`, the `d/dx` quotient rule — **computable**, `#eval`-able).

* **`cmonomialDeriv Dt p`** = `(coefficientwise cderiv of p) + (dp/dt)·Dt`: the monomial derivation
  on `k[t]`, realized over `CPolyG α`. Its correctness `toPolyG_cmonomialDeriv`
  shows it realizes Mathlib's `Differential.implicitDeriv (toPolyG Dt)` exactly — the key bridge.

* **`cSplitFactor Dt fuel p`** = the `SplitFactor` algorithm: the squarefree-factorization
  loop peeling off the special part `gcd(p, p′)/gcd(p, dp/dt)`. The payoff is that it **executes**
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

/-! ### The monomial derivation on `CPolyG α` (`Dt` a polynomial in `t`)

For a monomial `t` over the coefficient field with `Dt ∈ k[t]`, the derivation on `k[t]` sends
`p` to (coefficientwise `cderiv` of `p`) + `(dp/dt)·Dt`. `cmonomialDeriv` realizes
this over `CPolyG α` (the engine, needing only `[CDiffField α]`), and `toPolyG_cmonomialDeriv` proves
it equals Mathlib's `Differential.implicitDeriv (toPolyG Dt)` (the correctness, the **key bridge**). -/

namespace CPolyG

/-- **Coefficientwise derivation** `cmapDeriv p = p.map cderiv`: apply `CDiffField.cderiv` to every
coefficient (the coefficientwise part of the monomial derivation). -/
def cmapDeriv {α : Type*} [CField α] [CDiffField α] (p : CPolyG α) : CPolyG α :=
  (p : List α).map CDiffField.cderiv

/-- **Monomial derivation** `cmonomialDeriv Dt p = cmapDeriv p + (dp/dt)·Dt`: coefficientwise `cderiv` plus
the product of the formal `t`-derivative with `Dt`. The derivation on `k[t]` with `Dt` the derivative
of the monomial `t`. Needs only `[CDiffField α]`, so it reduces. -/
def cmonomialDeriv {α : Type*} [CField α] [CDiffField α] (Dt p : CPolyG α) : CPolyG α :=
  caddG (cmapDeriv p) (cmulG (cderivG p) Dt)

/-- **`cmapDeriv` realizes `mapCoeffs`**: `toPolyG (cmapDeriv p) = Differential.mapCoeffs (toPolyG p)`
— the coefficientwise computable derivation realizes Mathlib's polynomial coefficient-map derivation. -/
theorem toPolyG_cmapDeriv {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]
    (p : CPolyG α) :
    toPolyG (cmapDeriv p) = Differential.mapCoeffs (toPolyG p) := by
  induction p with
  | nil => simp [cmapDeriv]
  | cons a as ih =>
    show toPolyG (CDiffField.cderiv a :: cmapDeriv as) = Differential.mapCoeffs (toPolyG (a :: as))
    rw [toPolyG_cons, ih, toPolyG_cons, map_add, Differential.mapCoeffs_C, CDiffFieldSpec.toK_cderiv,
      Derivation.leibniz, Differential.mapCoeffs_X, smul_zero, add_zero, smul_eq_mul]

/-- **`cmonomialDeriv` realizes `implicitDeriv`** — the key bridge: the computable monomial
derivation realizes Mathlib's `Differential.implicitDeriv (toPolyG Dt)` (with `Dt ↦ v = toPolyG Dt`),
i.e. `toPolyG (cmonomialDeriv Dt p) = Differential.implicitDeriv (toPolyG Dt) (toPolyG p)`. -/
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
the rest is normal, else recurse on `p/S` and accumulate `S` into the special part. Fuel-bounded. -/

/-- **Computable splitting-factorization loop**: `cSplitFactor Dt fuel p = (pₙ, pₛ)`
with `pₛ` the special part and `pₙ` the normal part of `p` w.r.t. the monomial derivation `D`
(`Dt` = `dt/d·`). One step extracts `S = gcd(p, p′)/gcd(p, dp/dt)`; constant `S` ⇒ `p` is normal,
else recurse on `p/S`. Fuel-bounded; the engine reduces (`native_decide`). -/
def cSplitFactor {α : Type*} [CField α] [CDiffField α] (Dt : CPolyG α) : ℕ → CPolyG α → CPolyG α × CPolyG α
  | 0, p => (p, [CField.one])
  | fuel + 1, p =>
    let S := cdivG (fuel + 1) (cgcdExtG (fuel + 1) p (cmonomialDeriv Dt p)).1
      (cgcdExtG (fuel + 1) p (cderivG p)).1
    if cdegG S = 0 then (p, [CField.one])
    else
      let (qn, qs) := cSplitFactor Dt fuel (cdivG (fuel + 1) p S)
      (qn, cmulG S qs)

end CPolyG

/-! ### The payoff — the engine **executes** `cSplitFactor` over ℚ(x)[t] (`native_decide`)

These `native_decide` checks are the deliverable: the splitting-factorization loop, routed
through `CField QFunNZ` + `CDiffField QFunNZ`, *reduces* in the native compiler with no dependence on
the noncomputable `CFieldSpec`/`CDiffFieldSpec`. The worked example takes `k = ℚ(x)` with `ℚ`-constant
coefficients and the monomial `t` with `Dt = t − 1`: under the monomial derivation `D`, the root `t = 1` is
*special* (`Dt(1) = 0 = 1′`) and `t = 2` is *normal* (`Dt(2) = 1 ≠ 0 = 2′`). So `cSplitFactor` of
`p = (t−1)(t−2)` returns normal part `~ (t−2)` and special part `~ (t−1)`, which `native_decide`
verifies (degrees, and monic-normalized parts equal to the expected values via `cisZeroG` of the
difference — the engine produces them only up to the gcd's scalar ambiguity).

`native_decide` on the full degree-5 `p` over `ℚ(x)` (with non-constant
coefficients) is the natural next step but is left to a later stage: the `QFunNZ` operations never
reduce to lowest terms (`qaddNZ`/`qmulNZ` just cross-multiply denominators), so the extended-Euclid /
division passes over a degree-5 `t`-polynomial blow the rational-function coefficients up
super-exponentially and the run does not terminate in budget. The fix is a lowest-terms-reducing
`CField QFunNZ` (route `qaddNZ`/`qmulNZ`/the division remainders through `Compute.qnorm`), at which
point the same `cSplitFactor` call computes the expected `pₙ`/`pₛ` directly. -/

namespace QFunNZ

/-- Build a `QFunNZ` from a numerator and a **nonzero** denominator `CPoly` (the denominator-≠-0
membership is discharged by `cisZero`, decided by `decide`). The fiddly subtype constructor for
writing rational-function coefficients of a `CPolyG QFunNZ` by hand. -/
def ofNumDen (num den : Compute.CPoly) (h : Compute.cisZero den = false) : QFunNZ :=
  ⟨(num, den), fun hz => by
    rw [(Compute.cisZero_iff_toPoly_eq_zero den).mpr hz] at h; exact absurd h (by decide)⟩

/-- A `QFunNZ` from a rational constant `n` (numerator `[n]`, denominator `[1]`). -/
def ofConstNZ (n : ℚ) : QFunNZ := ofNumDen [n] [1] (by decide)

end QFunNZ

open QFunNZ in
/-- The quadratic `p = (t−1)(t−2) = t² − 3t + 2` as a `CPolyG QFunNZ` (ℚ-constant coefficients). -/
def cSplitFactorExampleP : CPolyG QFunNZ := [ofConstNZ 2, ofConstNZ (-3), ofConstNZ 1]

open QFunNZ in
/-- The monomial derivative `Dt = t − 1` (so `t = 1` is a special root, `t = 2` a normal root). -/
def cSplitFactorExampleDt : CPolyG QFunNZ := [ofConstNZ (-1), ofConstNZ 1]

/-- **The engine runs**: `cSplitFactor` of `(t−1)(t−2)` over ℚ(x)[t] returns a **degree-1 normal
part** — `cSplitFactor` reduces in native code over the tower. -/
example : CPolyG.cdegG (CPolyG.cSplitFactor cSplitFactorExampleDt 8 cSplitFactorExampleP).1 = 1 := by
  native_decide

/-- **The engine runs**: `cSplitFactor` of `(t−1)(t−2)` returns a **degree-1 special part**. -/
example : CPolyG.cdegG (CPolyG.cSplitFactor cSplitFactorExampleDt 8 cSplitFactorExampleP).2 = 1 := by
  native_decide

open QFunNZ in
/-- **The special part is `~ (t − 1)`**: the monic-normalized special part of the splitting equals
`t − 1` (the special root `t = 1`, where `Dt(1) = 0 = 1′`) — verified by `cisZeroG` of the difference,
reducing over ℚ(x)[t]. -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonicG (CPolyG.cSplitFactor cSplitFactorExampleDt 8 cSplitFactorExampleP).2)
      [ofConstNZ (-1), ofConstNZ 1]) = true := by native_decide

open QFunNZ in
/-- **The normal part is `~ (t − 2)`**: the monic-normalized normal part of the splitting equals
`t − 2` (the normal root `t = 2`, where `Dt(2) = 1 ≠ 0 = 2′`). -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonicG (CPolyG.cSplitFactor cSplitFactorExampleDt 8 cSplitFactorExampleP).1)
      [ofConstNZ (-2), ofConstNZ 1]) = true := by native_decide

open QFunNZ in
/-- **The split recovers `p`**: the product of the monic normal and special parts equals `p` (monic),
so `cSplitFactor` genuinely factors `(t−1)(t−2)` over ℚ(x)[t]. -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmulG
        (CPolyG.cmonicG (CPolyG.cSplitFactor cSplitFactorExampleDt 8 cSplitFactorExampleP).1)
        (CPolyG.cmonicG (CPolyG.cSplitFactor cSplitFactorExampleDt 8 cSplitFactorExampleP).2))
      [ofConstNZ 2, ofConstNZ (-3), ofConstNZ 1]) = true := by native_decide

end DeepWiki.SymbolicIntegration
