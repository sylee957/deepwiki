import DeepWiki.SymbolicIntegration.DifferentialAlgebra.RationalFunctionDerivative
import DeepWiki.SymbolicIntegration.Core.Polynomial.RatFuncFractions

/-! # Extending base derivations to fraction fields

Generic quotient-rule derivations on `RatFunc K`, independent of the computable tower engine.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

section Generic
variable (d : Derivation ℤ K[X] K[X])

/-- The quotient-rule numerator/denominator pair `(d p · q − p · d q, q²)` as a rational function,
for an arbitrary base derivation `d` on `K[X]`. -/
private noncomputable def extendDerivAux (p q : K[X]) : RatFunc K :=
  RatFunc.mk (d p * q - p * d q) (q ^ 2)

/-- Well-definedness: `extendDerivAux d (a·p) (a·q) = extendDerivAux d p q`, so it descends to `RatFunc.liftOn'`. -/
private theorem extendDerivAux_wd {p q a : K[X]} (hq : q ≠ 0) (ha : a ≠ 0) :
    extendDerivAux d (a * p) (a * q) = extendDerivAux d p q := by
  unfold extendDerivAux
  rw [RatFunc.mk_eq_mk (pow_ne_zero 2 (mul_ne_zero ha hq)) (pow_ne_zero 2 hq)]
  simp only [Derivation.leibniz, smul_eq_mul]; ring

/-- The `liftOn'` zero-side coherence: `extendDerivAux d p 0 = extendDerivAux d 0 1`. -/
private theorem extendDerivAux_zero (p : K[X]) :
    extendDerivAux d p 0 = extendDerivAux d 0 1 := by
  unfold extendDerivAux
  rw [show (0 : K[X]) ^ 2 = 0 by ring, RatFunc.mk_zero]
  simp [RatFunc.mk_eq_div]

/-- The extended derivative function `(p/q) ↦ (d p · q − p · d q)/q²`, via `RatFunc.liftOn'`. -/
noncomputable def extendDerivFun (x : RatFunc K) : RatFunc K :=
  x.liftOn' (extendDerivAux d) fun {_ _ _} hq ha => extendDerivAux_wd d hq ha

/-- Quotient rule for `extendDerivFun`: `(mk p q) ↦ (d p · q − p · d q)/q²`. -/
theorem extendDerivFun_mk (p q : K[X]) :
    extendDerivFun d (RatFunc.mk p q)
      = RatFunc.mk (d p * q - p * d q) (q ^ 2) :=
  RatFunc.liftOn'_mk p q (extendDerivAux d) (extendDerivAux_zero d)
    (fun {_ _ _} hq ha => extendDerivAux_wd d hq ha)

/-- `extendDerivFun` extends `d`: on `algebraMap K[X] (RatFunc K) p` it is `algebraMap (d p)`. -/
theorem extendDerivFun_algebraMap (p : K[X]) :
    extendDerivFun d (algebraMap K[X] (RatFunc K) p) = algebraMap K[X] (RatFunc K) (d p) := by
  rw [← RatFunc.mk_one p, extendDerivFun_mk]
  simp

/-- Additivity of `extendDerivFun`: `(x + y) ↦ x' + y'`. -/
theorem extendDerivFun_add (x y : RatFunc K) :
    extendDerivFun d (x + y) = extendDerivFun d x + extendDerivFun d y := by
  induction x using RatFunc.induction_on' with | _ p q hq =>
  induction y using RatFunc.induction_on' with | _ r s hs =>
  rw [ratFunc_mk_add_mk p r hq hs, extendDerivFun_mk, extendDerivFun_mk, extendDerivFun_mk,
    ratFunc_mk_add_mk _ _ (pow_ne_zero 2 hq) (pow_ne_zero 2 hs),
    RatFunc.mk_eq_mk (pow_ne_zero 2 (mul_ne_zero hq hs)) (mul_ne_zero (pow_ne_zero 2 hq)
      (pow_ne_zero 2 hs))]
  simp only [Derivation.leibniz, map_add, smul_eq_mul]; ring

/-- Leibniz rule for `extendDerivFun`: `(x·y) ↦ x'·y + x·y'`. -/
theorem extendDerivFun_mul (x y : RatFunc K) :
    extendDerivFun d (x * y) = extendDerivFun d x * y + x * extendDerivFun d y := by
  induction x using RatFunc.induction_on' with | _ p q hq =>
  induction y using RatFunc.induction_on' with | _ r s hs =>
  rw [ratFunc_mk_mul_mk p q r s, extendDerivFun_mk, extendDerivFun_mk, extendDerivFun_mk,
    ratFunc_mk_mul_mk (d p * q - p * d q) (q ^ 2) r s,
    ratFunc_mk_mul_mk p q (d r * s - r * d s) (s ^ 2),
    ratFunc_mk_add_mk _ _ (mul_ne_zero (pow_ne_zero 2 hq) hs) (mul_ne_zero hq (pow_ne_zero 2 hs)),
    RatFunc.mk_eq_mk (pow_ne_zero 2 (mul_ne_zero hq hs))
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hq) hs) (mul_ne_zero hq (pow_ne_zero 2 hs)))]
  simp only [Derivation.leibniz, smul_eq_mul]; ring

/-- `extendDerivFun d` annihilates `0`. -/
theorem extendDerivFun_zero : extendDerivFun d (0 : RatFunc K) = 0 := by
  have h := extendDerivFun_algebraMap d (0 : K[X]); simpa using h

/-- `extendDerivFun d` bundled as an additive homomorphism (additivity + `0 ↦ 0`). -/
noncomputable def extendDerivAddHom : RatFunc K →+ RatFunc K where
  toFun := extendDerivFun d
  map_zero' := extendDerivFun_zero d
  map_add' := extendDerivFun_add d

/-- `extendDerivFun d` commutes with `ℤ`-scalar multiplication: `(n • x) ↦ n • x'` (from additivity
via `map_zsmul`). -/
theorem extendDerivFun_zsmul (n : ℤ) (x : RatFunc K) :
    extendDerivFun d (n • x) = n • extendDerivFun d x :=
  map_zsmul (extendDerivAddHom d) n x

end Generic

/-! ### Bundling as a `Derivation`/`Differential`, via `ℚ`

The `Derivation ℤ (RatFunc K) (RatFunc K)` is built by first making a `Derivation ℚ`
and then restricting scalars to `ℤ`.
-/

section Bundle
variable [Algebra ℚ K] (d : Derivation ℤ K[X] K[X])

/-- `ℚ`-linearity of `extendDerivFun`: `extendDerivFun d (c • x) = c • extendDerivFun d x` for `c : ℚ`. -/
theorem extendDerivFun_smul (c : ℚ) (x : RatFunc K) :
    extendDerivFun d (c • x) = c • extendDerivFun d x :=
  map_rat_smul (extendDerivAddHom d) c x

/-- `extendDerivFun d` bundled as a `ℚ`-derivation `Derivation ℚ (RatFunc K) (RatFunc K)`. -/
noncomputable def extendDerivQ : Derivation ℚ (RatFunc K) (RatFunc K) :=
  Derivation.mk'
    { toFun := extendDerivFun d
      map_add' := extendDerivFun_add d
      map_smul' := fun c x => extendDerivFun_smul d c x }
    fun a b => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
      rw [extendDerivFun_mul]; ring

/-- The extended derivation `extendDeriv d : Derivation ℤ (RatFunc K) (RatFunc K)` realizing
`(p/q) ↦ (d p · q − p · d q)/q²`, from `extendDerivQ` by `restrictScalars ℤ`. -/
noncomputable def extendDeriv : Derivation ℤ (RatFunc K) (RatFunc K) :=
  (extendDerivQ d).restrictScalars ℤ

/-- `extendDeriv d` reads as `extendDerivFun d` pointwise. -/
@[simp] theorem extendDeriv_apply (x : RatFunc K) : extendDeriv d x = extendDerivFun d x := rfl

/-- `extendDeriv d` extends `d`: `extendDeriv d (algebraMap p) = algebraMap (d p)`. -/
theorem extendDeriv_algebraMap (p : K[X]) :
    extendDeriv d (algebraMap K[X] (RatFunc K) p) = algebraMap K[X] (RatFunc K) (d p) := by
  rw [extendDeriv_apply, extendDerivFun_algebraMap]

/-- Quotient rule for `extendDeriv`: `(mk p q) ↦ (d p · q − p · d q)/q²`. -/
theorem extendDeriv_mk (p q : K[X]) :
    extendDeriv d (RatFunc.mk p q) = RatFunc.mk (d p * q - p * d q) (q ^ 2) := by
  rw [extendDeriv_apply, extendDerivFun_mk]

/-- Logarithmic-derivative reading: `extendDeriv d (algMap g) / algMap g = algMap (d g) / algMap g`. -/
theorem extendDeriv_logDeriv (g : K[X]) :
    extendDeriv d (algebraMap K[X] (RatFunc K) g) / algebraMap K[X] (RatFunc K) g
      = algebraMap K[X] (RatFunc K) (d g) / algebraMap K[X] (RatFunc K) g := by
  rw [extendDeriv_algebraMap]

/-- The log-derivative of `algMap g` under `extendDeriv d` equals `RatFunc.mk (d g) g` (= `(d g)/g`). -/
theorem extendDeriv_logDeriv_mk (g : K[X]) :
    extendDeriv d (algebraMap K[X] (RatFunc K) g) / algebraMap K[X] (RatFunc K) g
      = RatFunc.mk (d g) g := by
  rw [extendDeriv_logDeriv, RatFunc.mk_eq_div]

/-- `K(t)` as a `Differential` ring under `extendDeriv d` (pinning the canonical `Algebra ℤ`). -/
@[reducible]
noncomputable def fractionFieldDifferential : Differential (RatFunc K) :=
  letI : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
  ⟨(extendDerivQ d).restrictScalars ℤ⟩

/-- The derivative selected by `fractionFieldDifferential` is `extendDeriv`. -/
@[simp] theorem fractionFieldDifferential_deriv (x : RatFunc K) :
    @Differential.deriv _ _ (fractionFieldDifferential d) x = extendDeriv d x := rfl

end Bundle

/-! ### Axiom audit -/

#print axioms extendDeriv
#print axioms extendDeriv_algebraMap
#print axioms extendDeriv_mk
#print axioms extendDeriv_logDeriv_mk
#print axioms fractionFieldDifferential

end DeepWiki.SymbolicIntegration
