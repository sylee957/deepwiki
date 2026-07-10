import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # `qReduce`: a lowest-terms reducer for `DenseFrac α`

`qReduce a` cancels `g = gcd(num, den)` in the unreduced fraction `DenseFrac α ≅ Frac(α[t])`, returning
`(num/g)/(den/g)` via the fuel-free monic gcd `cgcdMonicWf` and exact division `cdivWf`. It is
computable (the den-nonzero proof `Prop`-erased), and the abstract invariant
`toCFrac (qReduce a) = toCFrac a` proves reduction preserves the field value. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-! ### The reducer `qReduce`

`qReduce ⟨(num, den), _⟩ = ⟨(num/g, den/g), _⟩` with `g = cgcdMonicWf num den`; the denominator-nonzero
obligation is discharged from `(toPoly (den/g))·(toPoly g) = toPoly den ≠ 0`. -/

namespace CFrac

variable {α : Type*} [CField α] [CFieldSpec α]

/-- The common factor `reduceGcd a = cgcdMonicWf num den` cancelled by `qReduce`. -/
def reduceGcd (a : DenseFrac α) : DensePoly α :=
  cgcdMonicWf a.num a.den

/-! #### The denominator-nonzero discharge (`Prop`-erased) -/

/-- `toPoly (reduceGcd a)` divides both numerator and denominator through the bridge. -/
theorem toPolyG_reduceGcd_dvd (a : DenseFrac α) :
    toPoly (reduceGcd a) ∣ toPoly a.num ∧ toPoly (reduceGcd a) ∣ toPoly a.den :=
  toPolyG_cgcdMonicWf_dvd a.num a.den

/-- `reduceGcd a` is nonzero when the denominator of `a` is nonzero. -/
theorem reduceGcd_ne_nil (a : DenseFrac α) : cnorm (reduceGcd a) ≠ [] := by
  have hden : toPoly a.den ≠ 0 := toPolyG_ne_zero_of_cisZeroG_false (cisZeroG_den a)
  intro hnil
  have hg0 : toPoly (reduceGcd a) = 0 := (cnormG_eq_nil_iff _).mp hnil
  exact hden (eq_zero_of_zero_dvd (hg0 ▸ (toPolyG_reduceGcd_dvd a).2))

/-- The cancelled numerator `num/g`. -/
def reduceNum (a : DenseFrac α) : DensePoly α := cdivWf a.num (reduceGcd a)

/-- The cancelled denominator `den/g`. -/
def reduceDen (a : DenseFrac α) : DensePoly α := cdivWf a.den (reduceGcd a)

/-- Exact division of the numerator by `reduceGcd a`. -/
theorem toPolyG_reduceNum_mul (a : DenseFrac α) :
    toPoly (reduceNum a) * toPoly (reduceGcd a) = toPoly a.num :=
  DensePoly.toPolyG_cdivWf_exact _ _ (reduceGcd_ne_nil a) (toPolyG_reduceGcd_dvd a).1

/-- Exact division of the denominator by `reduceGcd a`. -/
theorem toPolyG_reduceDen_mul (a : DenseFrac α) :
    toPoly (reduceDen a) * toPoly (reduceGcd a) = toPoly a.den :=
  DensePoly.toPolyG_cdivWf_exact _ _ (reduceGcd_ne_nil a) (toPolyG_reduceGcd_dvd a).2

/-- The reduced denominator satisfies `cisZero (reduceDen a) = false`. -/
theorem cisZeroG_reduceDen (a : DenseFrac α) : cisZero (reduceDen a) = false := by
  rw [Bool.eq_false_iff, Ne, cisZeroG_iff]
  intro hz
  have hden : toPoly a.den ≠ 0 := toPolyG_ne_zero_of_cisZeroG_false (cisZeroG_den a)
  apply hden
  rw [← toPolyG_reduceDen_mul a, hz, zero_mul]

end CFrac

/-- Reduce a `DenseFrac α` fraction to `(num/g)/(den/g)` using the fuel-free monic gcd. -/
def qReduce {α : Type*} [CField α] [CFieldSpec α] (a : DenseFrac α) : DenseFrac α :=
  CFrac.ofFraction (CFrac.reduceNum a) (CFrac.reduceDen a) (CFrac.cisZeroG_reduceDen a)

/-! ### The invariant: `qReduce` preserves the field value

`toCFrac (qReduce a) = toCFrac a` over every `a`, through the `RatFunc (CFieldSpec.K α)` bridge. -/

namespace CFrac

variable {α : Type*} [CField α] [CFieldSpec α]

/-- `am (toPoly (reduceGcd a)) ≠ 0`. -/
theorem amG_toPolyG_reduceGcd_ne_zero (a : DenseFrac α) :
    am α (toPoly (reduceGcd a)) ≠ 0 :=
  amG_toPolyG_ne_zero (fun h => reduceGcd_ne_nil a ((cnormG_eq_nil_iff _).mpr h))

end CFrac

/-- `qReduce` preserves the field value in `RatFunc (CFieldSpec.K α)`. -/
theorem toCFracG_qReduce {α : Type*} [CField α] [CFieldSpec α] (a : DenseFrac α) :
    CFrac.toCFrac (qReduce a) = CFrac.toCFrac a := by
  -- abbreviations in RatFunc (CFieldSpec.K α)
  set G : RatFunc (CFieldSpec.K α) := CFrac.am α (toPoly (CFrac.reduceGcd a)) with hG
  set Nq : RatFunc (CFieldSpec.K α) := CFrac.am α (toPoly (CFrac.reduceNum a)) with hNq
  set Dq : RatFunc (CFieldSpec.K α) := CFrac.am α (toPoly (CFrac.reduceDen a)) with hDq
  set N : RatFunc (CFieldSpec.K α) := CFrac.am α (toPoly a.num) with hN
  set D : RatFunc (CFieldSpec.K α) := CFrac.am α (toPoly a.den) with hD
  -- exact-division specs, pushed through the ring hom am
  have hnum : Nq * G = N := by
    rw [hNq, hG, hN, ← map_mul]; exact congrArg _ (CFrac.toPolyG_reduceNum_mul a)
  have hden : Dq * G = D := by
    rw [hDq, hG, hD, ← map_mul]; exact congrArg _ (CFrac.toPolyG_reduceDen_mul a)
  -- the cancellable / nonvanishing denominators
  have hGne : G ≠ 0 := CFrac.amG_toPolyG_reduceGcd_ne_zero a
  have hDne : D ≠ 0 := CFrac.amG_toPolyG_ne_zero
    (CFrac.toPolyG_ne_zero_of_cisZeroG_false (CFrac.cisZeroG_den a))
  have hDqne : Dq ≠ 0 := by
    intro h; rw [h, zero_mul] at hden; exact hDne hden.symm
  -- unfold both sides of the goal to Nq/Dq = N/D and cross-multiply
  show Nq / Dq = N / D
  rw [div_eq_div_iff hDqne hDne, ← hnum, ← hden]
  ring

namespace CFrac

variable {α : Type*} [CField α] [CFieldSpec α]

/-- `qReduce` preserves the Boolean zero test. -/
theorem isZeroNZG_qReduce (x : DenseFrac α) :
    isZeroNZ (qReduce x) = isZeroNZ x := by
  have hval : toCFrac (qReduce x) = toCFrac x := toCFracG_qReduce x
  have h1 := isZeroNZG_iff (qReduce x)
  have h2 := isZeroNZG_iff x
  rw [hval] at h1
  by_cases hz : toCFrac x = 0
  · rw [h1.mpr hz, h2.mpr hz]
  · rw [Bool.eq_false_iff.mpr (fun h => hz (h1.mp h)),
      Bool.eq_false_iff.mpr (fun h => hz (h2.mp h))]

end CFrac

/-! ### Examples over `DenseFrac ℚ ≅ ℚ(x)` -/

/-- Field equality on `DenseFrac α`, tested as `isZero (a - b)`. -/
def qReduceEq {α : Type*} [CField α] [CFieldDomain α] (a b : DenseFrac α) : Bool :=
  CCommRing.isZero (CField.sub a b)

/-- A reducible fraction over `ℚ(x)` whose lowest-terms form is `(x + 1)/(x + 3)`. -/
def swellFrac : DenseFrac ℚ :=
  CFrac.ofFraction [(-1 : ℚ), 0, 1] [(-3 : ℚ), 2, 1]

-- `qReduce` cancels the gcd `x − 1` in `swellFrac`, dropping the numerator to degree 1.
example : cdeg (qReduce swellFrac).num = 1 := by native_decide

-- `qReduce` drops `swellFrac`'s denominator to degree 1, a scalar multiple of `x + 3`.
example : cdeg (qReduce swellFrac).den = 1 := by native_decide

-- `qReduce` is value-preserving on `swellFrac` in the engine's field equality test.
example : qReduceEq (qReduce swellFrac) swellFrac = true := by native_decide

-- The total degree drops from `2 + 2 = 4` to `1 + 1 = 2`.
example :
    cdeg (qReduce swellFrac).num + cdeg (qReduce swellFrac).den
      < cdeg swellFrac.num + cdeg swellFrac.den := by native_decide

/-- A higher-degree reducible fraction over `ℚ(x)` for `qReduce` examples. -/
def swellFrac2 : DenseFrac ℚ :=
  CFrac.ofFraction [(-1 : ℚ), 0, 0, 0, 1] [(-1 : ℚ), 0, 0, 0, 0, 0, 1]

-- `qReduce` is value-preserving on the bigger swell `(x⁴−1)/(x⁶−1)`.
example : qReduceEq (qReduce swellFrac2) swellFrac2 = true := by native_decide

-- The bigger swell's total degree drops from `4 + 6 = 10` to `3 + 5 = 8`.
example :
    cdeg (qReduce swellFrac2).num + cdeg (qReduce swellFrac2).den
      < cdeg swellFrac2.num + cdeg swellFrac2.den := by native_decide

end DeepWiki.SymbolicIntegration
