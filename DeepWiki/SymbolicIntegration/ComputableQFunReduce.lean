import DeepWiki.SymbolicIntegration.ComputableTowerField
import DeepWiki.SymbolicIntegration.ComputableFuelFreeGcd

/-! # `qReduce`: a verified lowest-terms reducer for `QFunNZG α`, with an abstract invariant

`QFunNZG α ≅ Frac(α[t])` is carried as an **unreduced** fraction `num/den`: the engine tests
`K`-equality through `isZero`, never canonicalizing, so `qmulNZG`/`qinvNZG` accumulate spurious common
factors (the value-correct `qinvNZG` of a shared-denominator fraction can be wildly higher degree than
its lowest-terms form). `qReduce a` cancels `g = gcd(num, den)`: it returns `(num/g)/(den/g)` via the
generic engine's extended-Euclidean gcd `cgcdExtG` and exact division `cdivG`.

Two layers, matching the project's `native_decide`-validated-then-abstractly-proved discipline:
* **`qReduce`** is computable (data through `cgcdExtG`/`cdivG`, the den-nonzero proof `Prop`-erased), so
  it `native_decide`s — validated value-preserving (`qReduceEq (qReduce a) a`) and degree-dropping on
  swelling fractions below.
* **★ the abstract invariant** `toQFunNZG (qReduce a) = toQFunNZG a` is proved as a GENERAL theorem over
  every `a : QFunNZG α` (via the `[CFieldSpec α]` `toQFunNZG` bridge into `RatFunc (CFieldSpec.K α)`),
  NOT `native_decide`: reduction preserves the field value. The lever is `cgcdExtG`'s gcd dividing both
  inputs (`toPolyG_cgcdExtG_dvd`, under the internally-discharged termination `reduceGcd_terminates`) and
  the exact-division spec `toPolyG (cdivG fuel c g) · toPolyG g = toPolyG c` (`toPolyG_cdivG_exact_local`,
  re-derived here from the Euclidean identity so this file stays UPSTREAM of the integration engine).

Unlike the gated `qreduceG`/`toQFunNZG_qreduceG` (`ComputableTowerReduce`, downstream of the integration
engine, with explicit `fuel` + termination/length side-hypotheses), `qReduce` picks its own fuel and the
invariant `toQFunNZG_qReduce` is **unconditional** (no hypotheses), so it composes freely upstream.

Imports only `ComputableTowerField` (the carrier + bridge) and `ComputableFuelFreeGcd` (the termination
lemma) — both upstream of the integration/Bareiss engines, so `qReduce` is reusable everywhere later. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

namespace QFunReduce

/-! ### Exact division, re-derived upstream

`toPolyG_cdivG_exact_local` is the correctness fact the invariant needs beyond the (upstream) gcd-divides
lemma `toPolyG_cgcdExtG_dvd`. It is re-proved here (not imported from `ComputableTowerGcdFFCorrect`, which
sits downstream of the integration engine) from upstream ingredients: the Euclidean identity
`toPolyG_cdivmodG'` and the remainder degree-drop `cmodG_length_lt`. The reducer needs only that the gcd
**divides** both numerator and denominator (`toPolyG_cgcdExtG_dvd`, under termination) — not the full
`Associated`-to-`gcd` characterization — so no `GCDMonoid` machinery is invoked. -/

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **Exact-modulo from divisibility**: if `toPolyG g ∣ toPolyG c` and `fuel` bounds `c`'s length, the
Euclidean remainder vanishes (`toPolyG (cmodG fuel c g) = 0`). The Euclidean identity places the
remainder in the ideal `(toPolyG g)` yet strictly below `deg g`, forcing it to `0`. -/
theorem toPolyG_cmodG_eq_zero_of_dvd (fuel : ℕ) (c g : CPolyG α)
    (hg : cnormG g ≠ []) (hfuel : (cnormG c : List α).length ≤ fuel)
    (hdvd : toPolyG g ∣ toPolyG c) : toPolyG (cmodG fuel c g) = 0 := by
  have hid : toPolyG c = toPolyG (cdivG fuel c g) * toPolyG g + toPolyG (cmodG fuel c g) := by
    have h := toPolyG_cdivmodG' fuel c g hg
    rw [cdivG, cmodG]; exact h
  have hdvdrem : toPolyG g ∣ toPolyG (cmodG fuel c g) := by
    have hsub : toPolyG (cmodG fuel c g) = toPolyG c - toPolyG (cdivG fuel c g) * toPolyG g := by
      rw [hid]; ring
    rw [hsub]
    exact dvd_sub hdvd (Dvd.dvd.mul_left (dvd_refl _) _)
  by_contra hne
  have hcmodnil : cnormG (cmodG fuel c g) ≠ [] := fun h => hne ((cnormG_eq_nil_iff _).mp h)
  have hlen := cmodG_length_lt fuel c g hg hfuel
  have e1 : (toPolyG (cmodG fuel c g)).natDegree ≤ (cnormG (cmodG fuel c g) : List α).length - 1 :=
    natDegree_toPolyG_le _
  have e2 : (toPolyG g).natDegree = (cnormG g : List α).length - 1 := by
    rw [← cdegG_eq_natDegree, cdegG]
  have hcmodpos : 1 ≤ (cnormG (cmodG fuel c g) : List α).length :=
    List.length_pos_iff.mpr hcmodnil
  have hge : (toPolyG g).natDegree ≤ (toPolyG (cmodG fuel c g)).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvdrem hne
  omega

/-- **Exact `cdivG`-division from divisibility**: if `toPolyG g ∣ toPolyG c` (with `g` nonzero and fuel
bounding `c`), the Euclidean quotient is exact — `toPolyG (cdivG fuel c g) · toPolyG g = toPolyG c`. From
the Euclidean identity with the (now zero) remainder. -/
theorem toPolyG_cdivG_exact_local (fuel : ℕ) (c g : CPolyG α)
    (hg : cnormG g ≠ []) (hfuel : (cnormG c : List α).length ≤ fuel)
    (hdvd : toPolyG g ∣ toPolyG c) : toPolyG (cdivG fuel c g) * toPolyG g = toPolyG c := by
  have hid : toPolyG c = toPolyG (cdivG fuel c g) * toPolyG g + toPolyG (cmodG fuel c g) := by
    have h := toPolyG_cdivmodG' fuel c g hg
    rw [cdivG, cmodG]; exact h
  rw [hid, toPolyG_cmodG_eq_zero_of_dvd fuel c g hg hfuel hdvd, add_zero]

end QFunReduce

/-! ### The reducer `qReduce`

`qReduce ⟨(num, den), _⟩ = ⟨(num/g, den/g), _⟩` with `g = (cgcdExtG fuel num den).1` and
`fuel = |num|⁺ + |den|⁺ + 1` (lengths of the normalized lists; enough for both the gcd descent and the
two exact divisions). The denominator-nonzero proof obligation is discharged abstractly: `den/g` is
nonzero because `(toPolyG (den/g))·(toPolyG g) = toPolyG den ≠ 0`. -/

namespace QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **Fuel for the reducer**: `|num|⁺ + |den|⁺ + 1`, the sum of the normalized numerator and denominator
lengths plus one — large enough to bound the `cgcdExtG` remainder descent and both `cdivG` divisions. -/
def reduceFuel (a : QFunNZG α) : ℕ :=
  (cnormG a.1.1 : List α).length + (cnormG a.1.2 : List α).length + 1

/-- **The gcd of numerator and denominator** `reduceGcd a = (cgcdExtG (reduceFuel a) num den).1`, the
common factor `qReduce` cancels. -/
def reduceGcd (a : QFunNZG α) : CPolyG α :=
  (cgcdExtG (reduceFuel a) a.1.1 a.1.2).1

/-! #### The denominator-nonzero discharge (`[CFieldSpec α]` reasoning, `Prop`-erased)

The new denominator `den/g` is nonzero. The witness threads through `toPolyG`: from `den ≠ 0` the gcd
`g` divides `den` (termination by `cgcdTerminatesG_of_fuel`), so `(toPolyG (den/g))·(toPolyG g) =
toPolyG den ≠ 0`, hence `toPolyG (den/g) ≠ 0`, i.e. `cisZeroG (den/g) = false`. All `[CFieldSpec α]`
facts, but they prove a `Prop` field — erased at runtime, so `qReduce` stays computable. -/

/-- **`cgcdExtG` terminates at `reduceFuel`**: the descent reaches a zero remainder within the fuel
(from `cgcdTerminatesG_of_fuel`, since the fuel bounds `|num|` and strictly bounds `|den|`). -/
theorem reduceGcd_terminates (a : QFunNZG α) :
    cgcdTerminatesG (reduceFuel a) a.1.1 a.1.2 :=
  cgcdTerminatesG_of_fuel _ _ _ (by rw [reduceFuel]; omega) (by rw [reduceFuel]; omega)

/-- **The reduce-gcd divides numerator and denominator** through the bridge: `toPolyG (reduceGcd a)`
divides both `toPolyG num` and `toPolyG den` in `(CFieldSpec.K α)[X]`. -/
theorem toPolyG_reduceGcd_dvd (a : QFunNZG α) :
    toPolyG (reduceGcd a) ∣ toPolyG a.1.1 ∧ toPolyG (reduceGcd a) ∣ toPolyG a.1.2 :=
  toPolyG_cgcdExtG_dvd _ _ _ (reduceGcd_terminates a)

/-- **The reduce-gcd is nonzero** (for a nonzero denominator): `cnormG (reduceGcd a) ≠ []`. From
`toPolyG (reduceGcd a) ∣ toPolyG den` and `toPolyG den ≠ 0` (a divisor of a nonzero element is nonzero). -/
theorem reduceGcd_ne_nil (a : QFunNZG α) : cnormG (reduceGcd a) ≠ [] := by
  have hden : toPolyG a.1.2 ≠ 0 := toPolyG_ne_zero_of_cisZeroG_false a.2
  intro hnil
  have hg0 : toPolyG (reduceGcd a) = 0 := (cnormG_eq_nil_iff _).mp hnil
  exact hden (eq_zero_of_zero_dvd (hg0 ▸ (toPolyG_reduceGcd_dvd a).2))

/-- **The reduced numerator** `cdivG (reduceFuel a) num (reduceGcd a)` — the cancelled `num/g`. -/
def reduceNum (a : QFunNZG α) : CPolyG α := cdivG (reduceFuel a) a.1.1 (reduceGcd a)

/-- **The reduced denominator** `cdivG (reduceFuel a) den (reduceGcd a)` — the cancelled `den/g`. -/
def reduceDen (a : QFunNZG α) : CPolyG α := cdivG (reduceFuel a) a.1.2 (reduceGcd a)

/-- **Exact division of the numerator**: `(toPolyG (reduceNum a))·(toPolyG (reduceGcd a)) = toPolyG num`
(the gcd divides the numerator, so its `cdivG` quotient is exact). -/
theorem toPolyG_reduceNum_mul (a : QFunNZG α) :
    toPolyG (reduceNum a) * toPolyG (reduceGcd a) = toPolyG a.1.1 :=
  QFunReduce.toPolyG_cdivG_exact_local _ _ _ (reduceGcd_ne_nil a) (by rw [reduceFuel]; omega)
    (toPolyG_reduceGcd_dvd a).1

/-- **Exact division of the denominator**: `(toPolyG (reduceDen a))·(toPolyG (reduceGcd a)) = toPolyG den`. -/
theorem toPolyG_reduceDen_mul (a : QFunNZG α) :
    toPolyG (reduceDen a) * toPolyG (reduceGcd a) = toPolyG a.1.2 :=
  QFunReduce.toPolyG_cdivG_exact_local _ _ _ (reduceGcd_ne_nil a) (by rw [reduceFuel]; omega)
    (toPolyG_reduceGcd_dvd a).2

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
`g = gcd(num, den)` computed by the generic extended-Euclidean gcd `cgcdExtG`. Cancels the spurious
common factors that `QFunNZG`'s unreduced `qmulNZG`/`qinvNZG` accumulate (e.g. `xⁿ/xⁿ` for `1`). The
data (`cdivG`/`cgcdExtG`) needs only `[CField α]` and the den-nonzero proof is `Prop`-erased, so
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
degree 1 (a scalar multiple of `x + 1` — `cgcdExtG`'s gcd is not normalized monic, so the cancelled
representative carries a constant factor). -/
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
