import DeepWiki.SymbolicIntegration.RationalFunctionDerivative
import DeepWiki.SymbolicIntegration.Core.Polynomial.RatFuncFractions
import DeepWiki.SymbolicIntegration.Computable.CanonicalFieldIdentity
import DeepWiki.SymbolicIntegration.Computable.Tower.Field

/-! # Extending a base derivation to the fraction field `K(t)`
A derivation on `RatFunc K` extending a given base derivation `d : Derivation ℤ K[X] K[X]` by the
quotient rule `(p/q)′ = (d p · q − p · d q)/q²`, generic over the base `d`. Headline `extendDeriv d`,
with `extendDeriv_algebraMap` (it extends `d` on polynomial images) and `extendDeriv_logDeriv`. -/

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
The `Derivation ℤ (RatFunc K) (RatFunc K)` is built by first making a `Derivation ℚ` (unambiguous
`Module ℚ` on a characteristic-`0` field, so `Derivation.mk'` succeeds) then `restrictScalars ℤ`.
Generic over any `[Algebra ℚ K]`. -/

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

end Bundle

/-! ### Specialization to the tower fraction field `RatFunc (RatFunc ℚ)`
Specializing `extendDeriv` to the base derivation `implicitDeriv (toPolyG Dt)` on `(RatFunc ℚ)[X]`
yields the tower fraction-field derivation on `RatFunc (RatFunc ℚ)`. -/

open scoped Differential
open CPolyG

/-- The engine carrier `CFieldSpec.K (QFunNZG ℚ)` is `RatFunc ℚ`, a `ℚ`-algebra (needed for the
`ℚ`-route bundle). -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- The engine carrier `CFieldSpec.K (QFunNZG ℚ)` is `RatFunc ℚ`, a `Differential` ring under `d/dx`. -/
noncomputable local instance : Differential (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (Differential (RatFunc ℚ))

/-- The tower fraction-field derivation on `RatFunc (RatFunc ℚ)` for `Dt`:
`extendDeriv (implicitDeriv (toPolyG Dt))`. -/
noncomputable def towerFractionFieldDeriv (Dt : CPolyG (QFunNZG ℚ)) :
    Derivation ℤ (RatFunc (CFieldSpec.K (QFunNZG ℚ))) (RatFunc (CFieldSpec.K (QFunNZG ℚ))) :=
  extendDeriv (Differential.implicitDeriv (toPolyG Dt))

/-- The tower derivation extends the monomial derivation on `algebraMap (RatFunc ℚ)[X]` images. -/
theorem towerFractionFieldDeriv_algebraMap (Dt : CPolyG (QFunNZG ℚ)) (p : (CFieldSpec.K (QFunNZG ℚ))[X]) :
    towerFractionFieldDeriv Dt (algebraMap _ (RatFunc (CFieldSpec.K (QFunNZG ℚ))) p)
      = algebraMap _ (RatFunc (CFieldSpec.K (QFunNZG ℚ))) (Differential.implicitDeriv (toPolyG Dt) p) :=
  extendDeriv_algebraMap _ p

/-- Quotient rule for the tower derivation: `(mk p q) ↦ (Δp·q − p·Δq)/q²`, `Δ = implicitDeriv (toPolyG Dt)`. -/
theorem towerFractionFieldDeriv_mk (Dt : CPolyG (QFunNZG ℚ)) (p q : (CFieldSpec.K (QFunNZG ℚ))[X]) :
    towerFractionFieldDeriv Dt (RatFunc.mk p q)
      = RatFunc.mk (Differential.implicitDeriv (toPolyG Dt) p * q
          - p * Differential.implicitDeriv (toPolyG Dt) q) (q ^ 2) :=
  extendDeriv_mk _ p q

/-- The log-derivative of `g` under the tower derivation is `(Δg)/g`, `Δ = implicitDeriv (toPolyG Dt)`. -/
theorem towerFractionFieldDeriv_logDeriv (Dt : CPolyG (QFunNZG ℚ)) (g : (CFieldSpec.K (QFunNZG ℚ))[X]) :
    towerFractionFieldDeriv Dt (algebraMap _ (RatFunc (CFieldSpec.K (QFunNZG ℚ))) g)
        / algebraMap _ (RatFunc (CFieldSpec.K (QFunNZG ℚ))) g
      = RatFunc.mk (Differential.implicitDeriv (toPolyG Dt) g) g :=
  extendDeriv_logDeriv_mk _ g

/-- `RatFunc (RatFunc ℚ)` as a `Differential` ring under the tower derivation for `Dt`. -/
@[reducible]
noncomputable def towerFractionFieldDifferential (Dt : CPolyG (QFunNZG ℚ)) :
    Differential (RatFunc (CFieldSpec.K (QFunNZG ℚ))) :=
  fractionFieldDifferential (Differential.implicitDeriv (toPolyG Dt))

/-- Headline restatement: `extendDeriv d` extends the base derivation `d` on polynomial images. -/
example [Algebra ℚ K] (d : Derivation ℤ K[X] K[X]) (p : K[X]) :
    extendDeriv d (algebraMap K[X] (RatFunc K) p) = algebraMap K[X] (RatFunc K) (d p) :=
  extendDeriv_algebraMap d p

/-- Headline restatement (Leibniz): `extendDeriv d` is a derivation, so `(x·y)' = x'·y + x·y'`. -/
example [Algebra ℚ K] (d : Derivation ℤ K[X] K[X]) (x y : RatFunc K) :
    extendDeriv d (x * y) = extendDeriv d x * y + x * extendDeriv d y := by
  simp only [extendDeriv_apply]; exact extendDerivFun_mul d x y

/-- Headline restatement: the log-derivative of `g` under `extendDeriv d` is `(d g)/g`. -/
example [Algebra ℚ K] (d : Derivation ℤ K[X] K[X]) (g : K[X]) :
    extendDeriv d (algebraMap K[X] (RatFunc K) g) / algebraMap K[X] (RatFunc K) g
      = RatFunc.mk (d g) g :=
  extendDeriv_logDeriv_mk d g

end DeepWiki.SymbolicIntegration
