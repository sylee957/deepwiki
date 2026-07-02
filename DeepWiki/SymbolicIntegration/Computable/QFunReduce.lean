import DeepWiki.SymbolicIntegration.ComputableTowerField
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd

/-! # `qReduce`: a verified lowest-terms reducer for `QFunNZG α`, with an abstract invariant

`QFunNZG α ≅ Frac(α[t])` is carried as an **unreduced** fraction `num/den`: the engine tests
`K`-equality through `isZero`, never canonicalizing, so `qmulNZG`/`qinvNZG` accumulate spurious common
factors (the value-correct `qinvNZG` of a shared-denominator fraction can be wildly higher degree than
its lowest-terms form). `qReduce a` cancels `g = gcd(num, den)`: it returns `(num/g)/(den/g)` via the
fuel-free generic monic gcd `cgcdMonicWf` and exact division `cdivWf`.

Two layers, matching the project's `native_decide`-validated-then-abstractly-proved discipline:
* **`qReduce`** is computable (data through `cgcdMonicWf`/`cdivWf`, the den-nonzero proof `Prop`-erased), so
  it `native_decide`s — validated value-preserving (`qReduceEq (qReduce a) a`) and degree-dropping on
  swelling fractions below.
* **★ the abstract invariant** `toQFunNZG (qReduce a) = toQFunNZG a` is proved as a GENERAL theorem over
  every `a : QFunNZG α` (via the `[CFieldSpec α]` `toQFunNZG` bridge into `RatFunc (CFieldSpec.K α)`),
  NOT `native_decide`: reduction preserves the field value. The lever is `cgcdMonicWf`'s gcd dividing
  both inputs (`toPolyG_cgcdMonicWf_dvd`) and the shared exact-division spec
  `toPolyG (cdivWf c g) · toPolyG g = toPolyG c` (`CPolyG.toPolyG_cdivWf_exact`).

`qReduce` stays upstream of the integration/Bareiss engines; the invariant `toQFunNZG_qReduce` is
**unconditional** (no hypotheses), so it composes freely upstream and downstream tower demos can reuse the
same proof rather than maintaining a second reducer.

Imports only `ComputableTowerField` (the carrier + bridge) and `ComputableFuelFreeGcd` (the fuel-free
gcd/division layer and semantic exact-division lemmas) — both upstream of the integration/Bareiss engines,
so `qReduce` is reusable everywhere later. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### The reducer `qReduce`

`qReduce ⟨(num, den), _⟩ = ⟨(num/g, den/g), _⟩` with `g = cgcdMonicWf num den`. The denominator-nonzero
proof obligation is discharged abstractly: `den/g` is nonzero because
`(toPolyG (den/g))·(toPolyG g) = toPolyG den ≠ 0`. -/

namespace QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **The gcd of numerator and denominator** `reduceGcd a = cgcdMonicWf num den`, the common factor
`qReduce` cancels. -/
def reduceGcd (a : QFunNZG α) : CPolyG α :=
  cgcdMonicWf a.1.1 a.1.2

/-! #### The denominator-nonzero discharge (`[CFieldSpec α]` reasoning, `Prop`-erased)

The new denominator `den/g` is nonzero. The witness threads through `toPolyG`: from `den ≠ 0` the gcd
`g` divides `den`, so `(toPolyG (den/g))·(toPolyG g) = toPolyG den ≠ 0`, hence
`toPolyG (den/g) ≠ 0`, i.e. `cisZeroG (den/g) = false`. All `[CFieldSpec α]` facts, but they prove a
`Prop` field — erased at runtime, so `qReduce` stays computable. -/

/-- **The reduce-gcd divides numerator and denominator** through the bridge: `toPolyG (reduceGcd a)`
divides both `toPolyG num` and `toPolyG den` in `(CFieldSpec.K α)[X]`. -/
theorem toPolyG_reduceGcd_dvd (a : QFunNZG α) :
    toPolyG (reduceGcd a) ∣ toPolyG a.1.1 ∧ toPolyG (reduceGcd a) ∣ toPolyG a.1.2 :=
  toPolyG_cgcdMonicWf_dvd a.1.1 a.1.2

/-- **The reduce-gcd is nonzero** (for a nonzero denominator): `cnormG (reduceGcd a) ≠ []`. From
`toPolyG (reduceGcd a) ∣ toPolyG den` and `toPolyG den ≠ 0` (a divisor of a nonzero element is nonzero). -/
theorem reduceGcd_ne_nil (a : QFunNZG α) : cnormG (reduceGcd a) ≠ [] := by
  have hden : toPolyG a.1.2 ≠ 0 := toPolyG_ne_zero_of_cisZeroG_false a.2
  intro hnil
  have hg0 : toPolyG (reduceGcd a) = 0 := (cnormG_eq_nil_iff _).mp hnil
  exact hden (eq_zero_of_zero_dvd (hg0 ▸ (toPolyG_reduceGcd_dvd a).2))

/-- **The reduced numerator** `cdivWf num (reduceGcd a)` — the cancelled `num/g`. -/
def reduceNum (a : QFunNZG α) : CPolyG α := cdivWf a.1.1 (reduceGcd a)

/-- **The reduced denominator** `cdivWf den (reduceGcd a)` — the cancelled `den/g`. -/
def reduceDen (a : QFunNZG α) : CPolyG α := cdivWf a.1.2 (reduceGcd a)

/-- **Exact division of the numerator**: `(toPolyG (reduceNum a))·(toPolyG (reduceGcd a)) = toPolyG num`
(the gcd divides the numerator, so its `cdivWf` quotient is exact). -/
theorem toPolyG_reduceNum_mul (a : QFunNZG α) :
    toPolyG (reduceNum a) * toPolyG (reduceGcd a) = toPolyG a.1.1 :=
  CPolyG.toPolyG_cdivWf_exact _ _ (reduceGcd_ne_nil a) (toPolyG_reduceGcd_dvd a).1

/-- **Exact division of the denominator**: `(toPolyG (reduceDen a))·(toPolyG (reduceGcd a)) = toPolyG den`. -/
theorem toPolyG_reduceDen_mul (a : QFunNZG α) :
    toPolyG (reduceDen a) * toPolyG (reduceGcd a) = toPolyG a.1.2 :=
  CPolyG.toPolyG_cdivWf_exact _ _ (reduceGcd_ne_nil a) (toPolyG_reduceGcd_dvd a).2

/-- **The reduced denominator is `cisZeroG`-nonzero**: `cisZeroG (reduceDen a) = false`. Since
`(toPolyG (reduceDen a))·(toPolyG (reduceGcd a)) = toPolyG den ≠ 0`, the left factor `toPolyG (reduceDen
a)` is nonzero. The den-nonzero subtype witness for `qReduce`. -/
theorem cisZeroG_reduceDen (a : QFunNZG α) : cisZeroG (reduceDen a) = false := by
  rw [Bool.eq_false_iff, Ne, cisZeroG_iff]
  intro hz
  have hden : toPolyG a.1.2 ≠ 0 := toPolyG_ne_zero_of_cisZeroG_false a.2
  apply hden
  rw [← toPolyG_reduceDen_mul a, hz, zero_mul]

end QFunNZG

/-- **Reduce a `QFunNZG α` fraction to lowest terms** `qReduce a = (num/g)/(den/g)` with
`g = gcd(num, den)` computed by the fuel-free generic monic gcd `cgcdMonicWf`. Cancels the spurious
common factors that `QFunNZG`'s unreduced `qmulNZG`/`qinvNZG` accumulate (e.g. `xⁿ/xⁿ` for `1`). The
data (`cdivWf`/`cgcdMonicWf`) needs only `[CField α]` and the den-nonzero proof is `Prop`-erased, so
`qReduce` is computable (`native_decide`); `[CFieldSpec α]` is used only to discharge the proof. The
field value is preserved — `toQFunNZG (qReduce a) = toQFunNZG a` (`toQFunNZG_qReduce`). -/
def qReduce {α : Type*} [CField α] [CFieldSpec α] (a : QFunNZG α) : QFunNZG α :=
  ⟨(QFunNZG.reduceNum a, QFunNZG.reduceDen a), QFunNZG.cisZeroG_reduceDen a⟩

/-! ### ★ The abstract invariant: `qReduce` preserves the field value

`toQFunNZG (qReduce a) = toQFunNZG a` over every `a : QFunNZG α`, proved abstractly through the
`RatFunc (CFieldSpec.K α)` bridge — NOT `native_decide`. With `Nq, Dq, G` the `amG ∘ toPolyG` images of
the reduced numerator, reduced denominator, and gcd, the exact-division specs give `Nq·G = N` and
`Dq·G = D` in `RatFunc`; with `G ≠ 0` the fraction `Nq/Dq` equals `(Nq·G)/(Dq·G) = N/D`. -/

namespace QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **`amG (toPolyG (reduceGcd a)) ≠ 0`**: the gcd is nonzero (`reduceGcd_ne_nil`) and `amG` is injective,
so its rational-function image is nonzero — the cancellable factor in the invariant proof. -/
theorem amG_toPolyG_reduceGcd_ne_zero (a : QFunNZG α) :
    amG α (toPolyG (reduceGcd a)) ≠ 0 :=
  amG_toPolyG_ne_zero (fun h => reduceGcd_ne_nil a ((cnormG_eq_nil_iff _).mpr h))

end QFunNZG

/-- **★ The reducer preserves the field value** (the abstract invariant): for every `a : QFunNZG α`,
`toQFunNZG (qReduce a) = toQFunNZG a`. Cancelling `g = gcd(num, den)` does not change `num/den` in
`RatFunc (CFieldSpec.K α)`. Proved abstractly (no `native_decide`): apply `amG` to the exact-division
specs `(toPolyG (num/g))·(toPolyG g) = toPolyG num` and `(toPolyG (den/g))·(toPolyG g) = toPolyG den`,
then cross-multiply the resulting `(Nq/Dq) = (Nq·G)/(Dq·G) = N/D` using `G ≠ 0` and `D ≠ 0`. -/
theorem toQFunNZG_qReduce {α : Type*} [CField α] [CFieldSpec α] (a : QFunNZG α) :
    QFunNZG.toQFunNZG (qReduce a) = QFunNZG.toQFunNZG a := by
  -- abbreviations in RatFunc (CFieldSpec.K α)
  set G : RatFunc (CFieldSpec.K α) := QFunNZG.amG α (toPolyG (QFunNZG.reduceGcd a)) with hG
  set Nq : RatFunc (CFieldSpec.K α) := QFunNZG.amG α (toPolyG (QFunNZG.reduceNum a)) with hNq
  set Dq : RatFunc (CFieldSpec.K α) := QFunNZG.amG α (toPolyG (QFunNZG.reduceDen a)) with hDq
  set N : RatFunc (CFieldSpec.K α) := QFunNZG.amG α (toPolyG a.1.1) with hN
  set D : RatFunc (CFieldSpec.K α) := QFunNZG.amG α (toPolyG a.1.2) with hD
  -- exact-division specs, pushed through the ring hom amG
  have hnum : Nq * G = N := by
    rw [hNq, hG, hN, ← map_mul]; exact congrArg _ (QFunNZG.toPolyG_reduceNum_mul a)
  have hden : Dq * G = D := by
    rw [hDq, hG, hD, ← map_mul]; exact congrArg _ (QFunNZG.toPolyG_reduceDen_mul a)
  -- the cancellable / nonvanishing denominators
  have hGne : G ≠ 0 := QFunNZG.amG_toPolyG_reduceGcd_ne_zero a
  have hDne : D ≠ 0 := QFunNZG.amG_toPolyG_ne_zero (QFunNZG.toPolyG_ne_zero_of_cisZeroG_false a.2)
  have hDqne : Dq ≠ 0 := by
    intro h; rw [h, zero_mul] at hden; exact hDne hden.symm
  -- unfold both sides of the goal to Nq/Dq = N/D and cross-multiply
  show Nq / Dq = N / D
  rw [div_eq_div_iff hDqne hDne, ← hnum, ← hden]
  ring

namespace QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **`qReduce` preserves the zero test** (`isZeroNZG (qReduce x) = isZeroNZG x`), with no fuel or
termination hypotheses. This is the reusable Boolean corollary of `toQFunNZG_qReduce`: reducing a fraction
does not change its field value, so the field-faithful zero test sees the same result before and after
canonicalization. -/
theorem isZeroNZG_qReduce (x : QFunNZG α) :
    isZeroNZG (qReduce x) = isZeroNZG x := by
  have hval : toQFunNZG (qReduce x) = toQFunNZG x := toQFunNZG_qReduce x
  have h1 := isZeroNZG_iff (qReduce x)
  have h2 := isZeroNZG_iff x
  rw [hval] at h1
  by_cases hz : toQFunNZG x = 0
  · rw [h1.mpr hz, h2.mpr hz]
  · rw [Bool.eq_false_iff.mpr (fun h => hz (h1.mp h)),
      Bool.eq_false_iff.mpr (fun h => hz (h2.mp h))]

end QFunNZG

/-! ### Validation: `qReduce` reduces and preserves value at level 1 (`QFunNZG ℚ ≅ ℚ(x)`)

The `native_decide` floor: `qReduce` runs in the native compiler at `α = ℚ` (the data is `[CField ℚ]`,
the proofs `Prop`-erased), it is value-preserving (`qEq (qReduce a) a`, the engine's own field equality),
and on a swelling fraction the reduced num+den degrees drop. -/

/-- **Field equality on `QFunNZG α`** `qReduceEq a b = isZero (a − b)` — the `Bool` test `a = b` via the
engine's `CField` zero test (sidestepping `DecidableEq` on the fraction subtype), used to certify
`qReduce` value-preservation under `native_decide`. -/
def qReduceEq {α : Type*} [CField α] [CFieldDomain α] (a b : QFunNZG α) : Bool :=
  CField.isZero (CField.sub a b)

/-- The swelling test fraction `(x² − 1)/((x − 1)(x + 3)) = (x² − 1)/(x² + 2x − 3)` over `ℚ(x)`, whose
lowest-terms form is `(x + 1)/(x + 3)`. Numerator `[-1, 0, 1] = x² − 1`, denominator
`[-3, 2, 1] = x² + 2x − 3`. -/
def swellFrac : QFunNZG ℚ :=
  ⟨([(-1 : ℚ), 0, 1], [(-3 : ℚ), 2, 1]), by native_decide⟩

/-- **`qReduce` cancels the gcd `x − 1` in `swellFrac`**: the numerator drops from degree 2 (`x² − 1`) to
degree 1. -/
example : cdegG (qReduce swellFrac).1.1 = 1 := by native_decide

/-- **`qReduce` drops `swellFrac`'s denominator to degree 1** (a scalar multiple of `x + 3`), from the
original degree 2 (`x² + 2x − 3`). -/
example : cdegG (qReduce swellFrac).1.2 = 1 := by native_decide

/-- **`qReduce` is value-preserving on `swellFrac`**: `qReduce swellFrac = swellFrac` in `ℚ(x)` (the
engine's field equality `qReduceEq` is `true`), even though the cancelled representative differs by a
constant factor — `(c·(x+1))/(c·(x+3)) = (x²−1)/(x²+2x−3)`. -/
example : qReduceEq (qReduce swellFrac) swellFrac = true := by native_decide

/-- **The total degree drops**: `cdegG num + cdegG den` falls from `2 + 2 = 4` (`swellFrac`) to
`1 + 1 = 2` (`qReduce swellFrac`) — the reducer strictly shrinks the representation. -/
example :
    cdegG (qReduce swellFrac).1.1 + cdegG (qReduce swellFrac).1.2
      < cdegG swellFrac.1.1 + cdegG swellFrac.1.2 := by native_decide

/-- A more dramatic swell `(x⁴ − 1)/((x − 1)(x⁵ + x⁴ + x³ + x² + x + 1))`: numerator `x⁴ − 1` (degree 4),
denominator degree 6, sharing the factor `(x − 1)(x + 1)(x² + 1)`-vs-cyclotomic overlap `x − 1` and more.
Numerator `[-1,0,0,0,1]`, denominator `(x − 1)·(x⁵+x⁴+x³+x²+x+1) = x⁶ − 1 = [-1,0,0,0,0,0,1]`. -/
def swellFrac2 : QFunNZG ℚ :=
  ⟨([(-1 : ℚ), 0, 0, 0, 1], [(-1 : ℚ), 0, 0, 0, 0, 0, 1]), by native_decide⟩

/-- **`qReduce` is value-preserving on the bigger swell** `(x⁴−1)/(x⁶−1)`. -/
example : qReduceEq (qReduce swellFrac2) swellFrac2 = true := by native_decide

/-- **The bigger swell's degree drops** from `4 + 6 = 10` to `3 + 5 = 8`: `gcd(x⁴−1, x⁶−1) = x²−1`
(degree 2) is cancelled, leaving `(x²+1)/(x⁴+x²+1)`. -/
example :
    cdegG (qReduce swellFrac2).1.1 + cdegG (qReduce swellFrac2).1.2
      < cdegG swellFrac2.1.1 + cdegG swellFrac2.1.2 := by native_decide

end DeepWiki.SymbolicIntegration
