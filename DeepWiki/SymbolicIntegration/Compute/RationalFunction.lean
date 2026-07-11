import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.SymbolicIntegration.Compute.Subresultant
import DeepWiki.SymbolicIntegration.RationalFunctionDerivative

/-! # Computable rational functions `ℚ(x)`

The validated carrier is `DenseFrac ℚ`. Its field operations and formal polynomial-variable
derivative are read through `CFrac.toRatFunc` into `RatFunc ℚ`; unchecked pairs occur only in the explicit
`ratFuncOfPair` boundary used by residual certificates.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-- Exact division selected by a lawful polynomial Euclidean capability becomes division in `RatFunc ℚ`. -/
theorem am_div_of_mod_zero {P : Type → Type} [CPoly P] [CPolyEuclidean P]
    [LawfulCPolyEuclidean.{0,0} P] (p q : P ℚ) (hq : CPoly.toPoly q ≠ 0)
    (hrem : CPoly.toPoly (CPolyEuclidean.mod p q) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly p) /
        algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly q) =
      algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly (CPolyEuclidean.div p q)) := by
  have hqm : algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly q) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr hq
  have hdiv := LawfulCPolyEuclidean.divmod_spec (P := P) (α := ℚ) p q hq
  rw [hrem, add_zero] at hdiv
  rw [hdiv, map_mul, mul_div_assoc, div_self hqm, mul_one]

/-! ### Explicit raw-pair boundary

Some polynomial algorithms return a numerator and denominator before their nonzero certificate has been
discharged. Keep that boundary as a pair-valued denotation, rather than making it a second fraction API.
-/

/-- Read an unchecked represented numerator/denominator pair in `RatFunc ℚ`. -/
noncomputable def ratFuncOfPair {P : Type → Type} [CPoly P] (x : P ℚ × P ℚ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly x.1) /
    algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly x.2)

/-! ### Field-operation readings -/

/-- Read a validated dense fraction in `RatFunc ℚ`. -/
noncomputable def toRatFuncDense (x : DenseFrac ℚ) : RatFunc ℚ := CFrac.toRatFunc x

/-- `DenseFrac` zero reads as `0`. -/
theorem toRatFuncDense_zero : toRatFuncDense (CCommRing.zero : DenseFrac ℚ) = 0 := by
  change CFieldSpec.toK (CCommRing.zero : DenseFrac ℚ) = 0
  exact CFieldSpec.toK_zero

/-- `DenseFrac` one reads as `1`. -/
theorem toRatFuncDense_one : toRatFuncDense (CCommRing.one : DenseFrac ℚ) = 1 := by
  change CFieldSpec.toK (CCommRing.one : DenseFrac ℚ) = 1
  exact CFieldSpec.toK_one

/-- Dense-fraction addition reads as addition in `RatFunc`. -/
theorem toRatFuncDense_add (x y : DenseFrac ℚ) :
    toRatFuncDense (CCommRing.add x y) = toRatFuncDense x + toRatFuncDense y :=
  CFieldSpec.toK_add x y

/-- Dense-fraction multiplication reads as multiplication in `RatFunc`. -/
theorem toRatFuncDense_mul (x y : DenseFrac ℚ) :
    toRatFuncDense (CCommRing.mul x y) = toRatFuncDense x * toRatFuncDense y :=
  CFieldSpec.toK_mul x y

/-- Dense-fraction negation reads as negation in `RatFunc`. -/
theorem toRatFuncDense_neg (x : DenseFrac ℚ) :
    toRatFuncDense (CCommRing.neg x) = -toRatFuncDense x :=
  CFieldSpec.toK_neg x

/-- Dense-fraction inversion reads as inversion in `RatFunc`. -/
theorem toRatFuncDense_inv (x : DenseFrac ℚ) :
    toRatFuncDense (CField.inv x) = (toRatFuncDense x)⁻¹ :=
  CFieldSpec.toK_inv x

/-- Dense-fraction subtraction reads as subtraction in `RatFunc`. -/
theorem toRatFuncDense_sub (x y : DenseFrac ℚ) :
    toRatFuncDense (CField.sub x y) = toRatFuncDense x - toRatFuncDense y :=
  CFieldSpec.toK_sub x y

/-- Dense-fraction division reads as division in `RatFunc`. -/
theorem toRatFuncDense_div (x y : DenseFrac ℚ) :
    toRatFuncDense (CField.div x y) = toRatFuncDense x / toRatFuncDense y :=
  CFieldSpec.toK_div x y

/-! ### Formal derivative -/

open scoped Differential in
/-- The formal derivative of a validated dense fraction reads as the `RatFunc` derivative. -/
theorem toRatFuncDense_deriv (x : DenseFrac ℚ) :
    toRatFuncDense (CFrac.deriv x) = (toRatFuncDense x)′ := by
  obtain ⟨a, b, hb⟩ := x
  have hb0 : DensePoly.toPoly b ≠ 0 := by
    intro h
    have hz := (DensePoly.cisZeroG_iff b).mpr h
    exact (Bool.eq_false_iff.mp hb) hz
  have hb0' : CPoly.toPoly b ≠ 0 := by simpa only [toPoly_list_eq] using hb0
  have hbm : CFrac.am ℚ (CPoly.toPoly b) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr hb0'
  have hda : (CFrac.am ℚ (CPoly.toPoly a))′ =
      CFrac.am ℚ (derivative (CPoly.toPoly a)) :=
    ratFuncDeriv_algebraMap (CPoly.toPoly a)
  have hdb : (CFrac.am ℚ (CPoly.toPoly b))′ =
      CFrac.am ℚ (derivative (CPoly.toPoly b)) :=
    ratFuncDeriv_algebraMap (CPoly.toPoly b)
  have hderiv : (CFrac.am ℚ (CPoly.toPoly a) /
        CFrac.am ℚ (CPoly.toPoly b))′
      = (CFrac.am ℚ (CPoly.toPoly b) *
          CFrac.am ℚ (derivative (CPoly.toPoly a))
          - CFrac.am ℚ (CPoly.toPoly a) *
            CFrac.am ℚ (derivative (CPoly.toPoly b))) /
        (CFrac.am ℚ (CPoly.toPoly b) ^ 2) := by
    rw [deriv_div, hda, hdb]
  rw [toRatFuncDense, CFrac.deriv, CFrac.toRatFunc_ofFraction]
  simp only [CPolyEngine.toPoly_sub, LawfulCPolyEngine.toPoly_mul,
    LawfulCPolyEngine.toPoly_deriv, map_sub, map_mul, CFrac.num, CFrac.den,
    CFrac.toPair, toRatFuncDense, CFrac.toRatFunc_eq_div]
  rw [hderiv, pow_two]
  field_simp [hbm]

/-! ### Folded derivatives -/

open scoped Differential in
/-- The derivative of a sum of validated dense fractions is the sum of the derivatives. -/
theorem deriv_toRatFuncDense_foldl_add (gs : List (DenseFrac ℚ)) :
    (toRatFuncDense (gs.foldl CCommRing.add (CCommRing.zero : DenseFrac ℚ)))′ =
      (gs.map (fun g => (toRatFuncDense g)′)).sum := by
  rw [show toRatFuncDense (gs.foldl CCommRing.add (CCommRing.zero : DenseFrac ℚ)) =
      (gs.map toRatFuncDense).sum by
        have hfold : ∀ (zs : List (DenseFrac ℚ)) (z : DenseFrac ℚ),
            toRatFuncDense (zs.foldl CCommRing.add z) =
              toRatFuncDense z + (zs.map toRatFuncDense).sum := by
          intro zs
          induction zs with
          | nil => intro z; simp
          | cons g zs ih =>
            intro z
            simp only [List.foldl_cons, List.map_cons, List.sum_cons]
            rw [ih, toRatFuncDense_add]
            abel
        have h := hfold gs (CCommRing.zero : DenseFrac ℚ)
        rw [toRatFuncDense_zero, zero_add] at h
        exact h]
  rw [show ((gs.map toRatFuncDense).sum)′ =
      Differential.deriv (R := RatFunc ℚ) (gs.map toRatFuncDense).sum from rfl,
    map_list_sum, List.map_map]
  rfl

open scoped Differential in
/-- A folded derivative with increments `T - resid g` has residual `T - nT + ∑ resid g`. -/
theorem foldl_residual_eq (gs : List (DenseFrac ℚ))
    (T : RatFunc ℚ) (resid : DenseFrac ℚ → RatFunc ℚ)
    (hstep : ∀ g ∈ gs, (toRatFuncDense g)′ = T - resid g) :
    T - (toRatFuncDense (gs.foldl CCommRing.add (CCommRing.zero : DenseFrac ℚ)))′
      = T - gs.length • T + (gs.map resid).sum := by
  rw [deriv_toRatFuncDense_foldl_add gs, List.map_congr_left hstep]
  have hsum : ∀ (zs : List (DenseFrac ℚ)),
      T - (zs.map (fun a => T - resid a)).sum =
        T - zs.length • T + (zs.map resid).sum := by
    intro zs
    induction zs with
    | nil => simp
    | cons g zs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, add_smul, one_smul]
      have ih' : -(zs.map (fun a => T - resid a)).sum =
          -(zs.length • T) + (zs.map resid).sum := by
        linear_combination ih
      linear_combination ih'
  exact hsum gs

end DeepWiki.SymbolicIntegration.Compute
