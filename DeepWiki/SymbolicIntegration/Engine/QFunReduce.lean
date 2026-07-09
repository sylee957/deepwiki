import DeepWiki.SymbolicIntegration.Engine.Tower.Field
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # `qReduce`: a lowest-terms reducer for `QFunNZ α`

`qReduce a` cancels `g = gcd(num, den)` in the unreduced fraction `QFunNZ α ≅ Frac(α[t])`, returning
`(num/g)/(den/g)` via the fuel-free monic gcd `cgcdMonicWf` and exact division `cdivWf`. It is
computable (the den-nonzero proof `Prop`-erased), and the abstract invariant
`toQFunNZ (qReduce a) = toQFunNZ a` proves reduction preserves the field value. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPoly

/-! ### The reducer `qReduce`

`qReduce ⟨(num, den), _⟩ = ⟨(num/g, den/g), _⟩` with `g = cgcdMonicWf num den`; the denominator-nonzero
obligation is discharged from `(toPoly (den/g))·(toPoly g) = toPoly den ≠ 0`. -/

namespace QFunNZ

variable {α : Type*} [CField α] [CFieldSpec α]

/-- The common factor `reduceGcd a = cgcdMonicWf num den` cancelled by `qReduce`. -/
def reduceGcd (a : QFunNZ α) : CPoly α :=
  cgcdMonicWf a.1.1 a.1.2

/-! #### The denominator-nonzero discharge (`Prop`-erased) -/

/-- `toPoly (reduceGcd a)` divides both numerator and denominator through the bridge. -/
theorem toPolyG_reduceGcd_dvd (a : QFunNZ α) :
    toPoly (reduceGcd a) ∣ toPoly a.1.1 ∧ toPoly (reduceGcd a) ∣ toPoly a.1.2 :=
  toPolyG_cgcdMonicWf_dvd a.1.1 a.1.2

/-- `reduceGcd a` is nonzero when the denominator of `a` is nonzero. -/
theorem reduceGcd_ne_nil (a : QFunNZ α) : cnorm (reduceGcd a) ≠ [] := by
  have hden : toPoly a.1.2 ≠ 0 := toPolyG_ne_zero_of_cisZeroG_false a.2
  intro hnil
  have hg0 : toPoly (reduceGcd a) = 0 := (cnormG_eq_nil_iff _).mp hnil
  exact hden (eq_zero_of_zero_dvd (hg0 ▸ (toPolyG_reduceGcd_dvd a).2))

/-- The cancelled numerator `num/g`. -/
def reduceNum (a : QFunNZ α) : CPoly α := cdivWf a.1.1 (reduceGcd a)

/-- The cancelled denominator `den/g`. -/
def reduceDen (a : QFunNZ α) : CPoly α := cdivWf a.1.2 (reduceGcd a)

/-- Exact division of the numerator by `reduceGcd a`. -/
theorem toPolyG_reduceNum_mul (a : QFunNZ α) :
    toPoly (reduceNum a) * toPoly (reduceGcd a) = toPoly a.1.1 :=
  CPoly.toPolyG_cdivWf_exact _ _ (reduceGcd_ne_nil a) (toPolyG_reduceGcd_dvd a).1

/-- Exact division of the denominator by `reduceGcd a`. -/
theorem toPolyG_reduceDen_mul (a : QFunNZ α) :
    toPoly (reduceDen a) * toPoly (reduceGcd a) = toPoly a.1.2 :=
  CPoly.toPolyG_cdivWf_exact _ _ (reduceGcd_ne_nil a) (toPolyG_reduceGcd_dvd a).2

/-- The reduced denominator satisfies `cisZero (reduceDen a) = false`. -/
theorem cisZeroG_reduceDen (a : QFunNZ α) : cisZero (reduceDen a) = false := by
  rw [Bool.eq_false_iff, Ne, cisZeroG_iff]
  intro hz
  have hden : toPoly a.1.2 ≠ 0 := toPolyG_ne_zero_of_cisZeroG_false a.2
  apply hden
  rw [← toPolyG_reduceDen_mul a, hz, zero_mul]

end QFunNZ

/-- Reduce a `QFunNZ α` fraction to `(num/g)/(den/g)` using the fuel-free monic gcd. -/
def qReduce {α : Type*} [CField α] [CFieldSpec α] (a : QFunNZ α) : QFunNZ α :=
  ⟨(QFunNZ.reduceNum a, QFunNZ.reduceDen a), QFunNZ.cisZeroG_reduceDen a⟩

/-! ### The invariant: `qReduce` preserves the field value

`toQFunNZ (qReduce a) = toQFunNZ a` over every `a`, through the `RatFunc (CFieldSpec.K α)` bridge. -/

namespace QFunNZ

variable {α : Type*} [CField α] [CFieldSpec α]

/-- `am (toPoly (reduceGcd a)) ≠ 0`. -/
theorem amG_toPolyG_reduceGcd_ne_zero (a : QFunNZ α) :
    am α (toPoly (reduceGcd a)) ≠ 0 :=
  amG_toPolyG_ne_zero (fun h => reduceGcd_ne_nil a ((cnormG_eq_nil_iff _).mpr h))

end QFunNZ

/-- `qReduce` preserves the field value in `RatFunc (CFieldSpec.K α)`. -/
theorem toQFunNZG_qReduce {α : Type*} [CField α] [CFieldSpec α] (a : QFunNZ α) :
    QFunNZ.toQFunNZ (qReduce a) = QFunNZ.toQFunNZ a := by
  -- abbreviations in RatFunc (CFieldSpec.K α)
  set G : RatFunc (CFieldSpec.K α) := QFunNZ.am α (toPoly (QFunNZ.reduceGcd a)) with hG
  set Nq : RatFunc (CFieldSpec.K α) := QFunNZ.am α (toPoly (QFunNZ.reduceNum a)) with hNq
  set Dq : RatFunc (CFieldSpec.K α) := QFunNZ.am α (toPoly (QFunNZ.reduceDen a)) with hDq
  set N : RatFunc (CFieldSpec.K α) := QFunNZ.am α (toPoly a.1.1) with hN
  set D : RatFunc (CFieldSpec.K α) := QFunNZ.am α (toPoly a.1.2) with hD
  -- exact-division specs, pushed through the ring hom am
  have hnum : Nq * G = N := by
    rw [hNq, hG, hN, ← map_mul]; exact congrArg _ (QFunNZ.toPolyG_reduceNum_mul a)
  have hden : Dq * G = D := by
    rw [hDq, hG, hD, ← map_mul]; exact congrArg _ (QFunNZ.toPolyG_reduceDen_mul a)
  -- the cancellable / nonvanishing denominators
  have hGne : G ≠ 0 := QFunNZ.amG_toPolyG_reduceGcd_ne_zero a
  have hDne : D ≠ 0 := QFunNZ.amG_toPolyG_ne_zero (QFunNZ.toPolyG_ne_zero_of_cisZeroG_false a.2)
  have hDqne : Dq ≠ 0 := by
    intro h; rw [h, zero_mul] at hden; exact hDne hden.symm
  -- unfold both sides of the goal to Nq/Dq = N/D and cross-multiply
  show Nq / Dq = N / D
  rw [div_eq_div_iff hDqne hDne, ← hnum, ← hden]
  ring

namespace QFunNZ

variable {α : Type*} [CField α] [CFieldSpec α]

/-- `qReduce` preserves the Boolean zero test. -/
theorem isZeroNZG_qReduce (x : QFunNZ α) :
    isZeroNZ (qReduce x) = isZeroNZ x := by
  have hval : toQFunNZ (qReduce x) = toQFunNZ x := toQFunNZG_qReduce x
  have h1 := isZeroNZG_iff (qReduce x)
  have h2 := isZeroNZG_iff x
  rw [hval] at h1
  by_cases hz : toQFunNZ x = 0
  · rw [h1.mpr hz, h2.mpr hz]
  · rw [Bool.eq_false_iff.mpr (fun h => hz (h1.mp h)),
      Bool.eq_false_iff.mpr (fun h => hz (h2.mp h))]

end QFunNZ

/-! ### Examples over `QFunNZ ℚ ≅ ℚ(x)` -/

/-- Field equality on `QFunNZ α`, tested as `isZero (a - b)`. -/
def qReduceEq {α : Type*} [CField α] [CFieldDomain α] (a b : QFunNZ α) : Bool :=
  CField.isZero (CField.sub a b)

/-- A reducible fraction over `ℚ(x)` whose lowest-terms form is `(x + 1)/(x + 3)`. -/
def swellFrac : QFunNZ ℚ :=
  ⟨([(-1 : ℚ), 0, 1], [(-3 : ℚ), 2, 1]), by native_decide⟩

-- `qReduce` cancels the gcd `x − 1` in `swellFrac`, dropping the numerator to degree 1.
example : cdeg (qReduce swellFrac).1.1 = 1 := by native_decide

-- `qReduce` drops `swellFrac`'s denominator to degree 1, a scalar multiple of `x + 3`.
example : cdeg (qReduce swellFrac).1.2 = 1 := by native_decide

-- `qReduce` is value-preserving on `swellFrac` in the engine's field equality test.
example : qReduceEq (qReduce swellFrac) swellFrac = true := by native_decide

-- The total degree drops from `2 + 2 = 4` to `1 + 1 = 2`.
example :
    cdeg (qReduce swellFrac).1.1 + cdeg (qReduce swellFrac).1.2
      < cdeg swellFrac.1.1 + cdeg swellFrac.1.2 := by native_decide

/-- A higher-degree reducible fraction over `ℚ(x)` for `qReduce` examples. -/
def swellFrac2 : QFunNZ ℚ :=
  ⟨([(-1 : ℚ), 0, 0, 0, 1], [(-1 : ℚ), 0, 0, 0, 0, 0, 1]), by native_decide⟩

-- `qReduce` is value-preserving on the bigger swell `(x⁴−1)/(x⁶−1)`.
example : qReduceEq (qReduce swellFrac2) swellFrac2 = true := by native_decide

-- The bigger swell's total degree drops from `4 + 6 = 10` to `3 + 5 = 8`.
example :
    cdeg (qReduce swellFrac2).1.1 + cdeg (qReduce swellFrac2).1.2
      < cdeg swellFrac2.1.1 + cdeg swellFrac2.1.2 := by native_decide

end DeepWiki.SymbolicIntegration
