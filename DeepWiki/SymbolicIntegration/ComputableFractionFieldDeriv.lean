import DeepWiki.SymbolicIntegration.RationalFunctionDerivative
import DeepWiki.SymbolicIntegration.ComputableCanonicalRepCorrect

/-! # Extending a base derivation to the fraction field `K(t)` (the integral-correctness keystone)
The rational-integration correctness identities — the §6.1 weak normalizer, the §5.6 Rothstein–Trager
`D(∑ aᵢ·log gᵢ) = a/d` log-derivative form, and the §5.3 cleaner `D(g) + h = f` over the fraction
field — all converge on one missing piece: a derivation on `RatFunc K` that extends a *given* base
derivation `d : Derivation ℤ K[X] K[X]` (e.g. the monomial derivation
`implicitDeriv (toPolyG Dt)`) by the quotient rule `(p/q)′ = (d p · q − p · d q)/q²`.

`RationalFunctionDerivative` built this for the *single* base `d = Polynomial.derivative` (the d/dx
case). Here the whole construction is **derivation-generic**: replacing `Polynomial.derivative` by an
arbitrary `d` everywhere, the `a²`-scaling well-definedness cancellation and the quotient-rule
Leibniz algebra are unchanged. The one real obstruction is the **diamond**: the repo's "build a
`K`-derivation first, then `restrictScalars ℤ`" trick (used for d/dx, where `d/dx` is `K`-linear)
*fails* here, because a general base `d` (like `implicitDeriv = mapCoeffs + v·d/dX`, which
differentiates coefficients) is **not** `K`-linear. So we build the `Derivation ℤ (RatFunc K)`
**directly**: bundle additivity into an `AddMonoidHom`, lift it to a `ℤ`-linear map via
`AddMonoidHom.toIntLinearMap` (so `map_smul'` for `zsmul` is automatic), and feed `Derivation.mk'`
the Leibniz rule.

Headlines: `extendDeriv d : Derivation ℤ (RatFunc K) (RatFunc K)`; `extendDeriv_algebraMap` (it
extends `d` on polynomial images); `extendDeriv_logDeriv` (the §5.6 building block
`extendDeriv d (algMap g) / algMap g = algMap (d g) / algMap g`). The tower fraction-field derivation
on `RatFunc (RatFunc ℚ)` is the specialization `extendDeriv (implicitDeriv (toPolyG Dt))`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

section Generic
variable (d : Derivation ℤ K[X] K[X])

/-- The quotient-rule numerator/denominator pair `(d p · q − p · d q, q²)` as a rational function,
for an arbitrary base derivation `d` on `K[X]`. -/
private noncomputable def extendDerivAux (p q : K[X]) : RatFunc K :=
  RatFunc.mk (d p * q - p * d q) (q ^ 2)

/-- **Well-definedness**: scaling `(p, q)` by `a` scales numerator and denominator both by `a²` (the
`d a`-cross-terms cancel by the Leibniz rule), so `extendDerivAux` is constant on the equivalence
class `RatFunc.liftOn'` quotients by. -/
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

/-- **The extended derivative function** `(p/q) ↦ (d p · q − p · d q)/q²`, defined via
`RatFunc.liftOn'` (well-defined by `extendDerivAux_wd`). -/
noncomputable def extendDerivFun (x : RatFunc K) : RatFunc K :=
  x.liftOn' (extendDerivAux d) fun {_ _ _} hq ha => extendDerivAux_wd d hq ha

/-- **Quotient rule** for `extendDerivFun`: `(mk p q) ↦ (d p · q − p · d q)/q²`. -/
theorem extendDerivFun_mk (p q : K[X]) :
    extendDerivFun d (RatFunc.mk p q)
      = RatFunc.mk (d p * q - p * d q) (q ^ 2) :=
  RatFunc.liftOn'_mk p q (extendDerivAux d) (extendDerivAux_zero d)
    (fun {_ _ _} hq ha => extendDerivAux_wd d hq ha)

/-- **`extendDerivFun` extends the base derivation `d`**: on a polynomial (as a rational function),
the extended derivative is `algebraMap (d p)`. -/
theorem extendDerivFun_algebraMap (p : K[X]) :
    extendDerivFun d (algebraMap K[X] (RatFunc K) p) = algebraMap K[X] (RatFunc K) (d p) := by
  rw [← RatFunc.mk_one p, extendDerivFun_mk]
  simp

private theorem algebraMap_ne_zero {q : K[X]} (hq : q ≠ 0) :
    algebraMap K[X] (RatFunc K) q ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hq

/-- Fraction addition for `RatFunc.mk`: `p/q + r/s = (ps + rq)/(qs)`. -/
private theorem mk_add_mk (p r : K[X]) {q s : K[X]} (hq : q ≠ 0) (hs : s ≠ 0) :
    RatFunc.mk p q + RatFunc.mk r s = RatFunc.mk (p * s + r * q) (q * s) := by
  rw [RatFunc.mk_eq_div, RatFunc.mk_eq_div, RatFunc.mk_eq_div,
    div_add_div _ _ (algebraMap_ne_zero hq) (algebraMap_ne_zero hs), map_add, map_mul, map_mul,
    map_mul]
  ring

/-- **Additivity** of `extendDerivFun`: `(x + y) ↦ x' + y'`. -/
theorem extendDerivFun_add (x y : RatFunc K) :
    extendDerivFun d (x + y) = extendDerivFun d x + extendDerivFun d y := by
  induction x using RatFunc.induction_on' with | _ p q hq =>
  induction y using RatFunc.induction_on' with | _ r s hs =>
  rw [mk_add_mk p r hq hs, extendDerivFun_mk, extendDerivFun_mk, extendDerivFun_mk,
    mk_add_mk _ _ (pow_ne_zero 2 hq) (pow_ne_zero 2 hs),
    RatFunc.mk_eq_mk (pow_ne_zero 2 (mul_ne_zero hq hs)) (mul_ne_zero (pow_ne_zero 2 hq)
      (pow_ne_zero 2 hs))]
  simp only [Derivation.leibniz, map_add, smul_eq_mul]; ring

/-- Fraction multiplication for `RatFunc.mk`: `(p/q)·(r/s) = (pr)/(qs)`. -/
private theorem mk_mul_mk (p q r s : K[X]) :
    RatFunc.mk p q * RatFunc.mk r s = RatFunc.mk (p * r) (q * s) := by
  rw [RatFunc.mk_eq_div, RatFunc.mk_eq_div, RatFunc.mk_eq_div, div_mul_div_comm, map_mul, map_mul]

/-- **Leibniz rule** for `extendDerivFun`: `(x·y) ↦ x'·y + x·y'`. -/
theorem extendDerivFun_mul (x y : RatFunc K) :
    extendDerivFun d (x * y) = extendDerivFun d x * y + x * extendDerivFun d y := by
  induction x using RatFunc.induction_on' with | _ p q hq =>
  induction y using RatFunc.induction_on' with | _ r s hs =>
  rw [mk_mul_mk p q r s, extendDerivFun_mk, extendDerivFun_mk, extendDerivFun_mk,
    mk_mul_mk (d p * q - p * d q) (q ^ 2) r s,
    mk_mul_mk p q (d r * s - r * d s) (s ^ 2),
    mk_add_mk _ _ (mul_ne_zero (pow_ne_zero 2 hq) hs) (mul_ne_zero hq (pow_ne_zero 2 hs)),
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

/-! ### Bundling as a `Derivation`/`Differential` — the `Module ℤ` field diamond, dodged via `ℚ`
The `Differential` field wants a `Derivation ℤ (RatFunc K) (RatFunc K)`. Building one **directly**
via `Derivation.mk'` over `ℤ` is blocked by a genuine **`Module ℤ` diamond on a field**:
`Derivation.mk'`'s domain module is the field's `Algebra.toModule` (from `RatFunc K`'s canonical
`Algebra ℤ`), but every `ℤ`-`smul`/`AddMonoidHom`-derived linear map lands on
`AddCommGroup.toIntModule`; the two are defeq but not syntactically equal, and the literal's
`map_smul'` field re-synthesizes the wrong one (the `respectTransparency`/`letI`/explicit-`@` escapes
all fail — see the file's commit log). The d/dx case in `RationalFunctionDerivative` dodged this by
building a `K`-derivation first, but a coefficient-differentiating base `d` (like `implicitDeriv`) is
**not** `K`-linear, so that route is closed here.

The resolution: build a `Derivation ℚ (RatFunc K) (RatFunc K)` instead — over a field of
characteristic `0` the `Module ℚ` is unambiguous (no `AddCommGroup.toIntModule` competitor), so
`Derivation.mk'` succeeds — then `restrictScalars ℤ` lands the `Derivation ℤ` with the correct
`Module ℤ`. The needed `ℚ`-linearity of the base `d` is **free**: any `Derivation ℤ K[X] K[X]` is an
`AddMonoidHom` between the `ℚ`-modules `K[X]` (since `K` is a `ℚ`-algebra), hence `ℚ`-linear by
`map_rat_smul`. So the whole bundle is generic over any `[Algebra ℚ K]` — in particular the engine's
`K = ℚ(x)` tower. -/

section Bundle
variable [Algebra ℚ K] (d : Derivation ℤ K[X] K[X])

/-- **`ℚ`-linearity of `extendDerivFun`** is automatic: the bundled `extendDerivAddHom d` is an
`AddMonoidHom` between the `ℚ`-modules `RatFunc K` (since `K` is a `ℚ`-algebra), so `map_rat_smul`
gives `extendDerivFun d (c • x) = c • extendDerivFun d x` for `c : ℚ` with no manual algebra. -/
theorem extendDerivFun_smul (c : ℚ) (x : RatFunc K) :
    extendDerivFun d (c • x) = c • extendDerivFun d x :=
  map_rat_smul (extendDerivAddHom d) c x

/-- **The extended derivation over `ℚ`**: `extendDerivFun d` bundled as a `ℚ`-derivation (additivity
+ `ℚ`-linearity `extendDerivFun_smul` + Leibniz `extendDerivFun_mul`). The `Derivation.mk'` works
here because the `Module ℚ` on the characteristic-`0` field `RatFunc K` is unambiguous. -/
noncomputable def extendDerivQ : Derivation ℚ (RatFunc K) (RatFunc K) :=
  Derivation.mk'
    { toFun := extendDerivFun d
      map_add' := extendDerivFun_add d
      map_smul' := fun c x => extendDerivFun_smul d c x }
    fun a b => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
      rw [extendDerivFun_mul]; ring

/-- **The extended derivation** `extendDeriv d : Derivation ℤ (RatFunc K) (RatFunc K)` realizing
`(p/q) ↦ (d p · q − p · d q)/q²`, obtained by restricting `extendDerivQ` to `ℤ` (so its `Module ℤ`
is the canonical one, side-stepping the field `Module ℤ` diamond). -/
noncomputable def extendDeriv : Derivation ℤ (RatFunc K) (RatFunc K) :=
  (extendDerivQ d).restrictScalars ℤ

/-- `extendDeriv d` reads as `extendDerivFun d` pointwise. -/
@[simp] theorem extendDeriv_apply (x : RatFunc K) : extendDeriv d x = extendDerivFun d x := rfl

/-- **`extendDeriv d` extends the base derivation `d`**: on `algebraMap K[X] (RatFunc K) p`,
`extendDeriv d (algebraMap p) = algebraMap (d p)`. -/
theorem extendDeriv_algebraMap (p : K[X]) :
    extendDeriv d (algebraMap K[X] (RatFunc K) p) = algebraMap K[X] (RatFunc K) (d p) := by
  rw [extendDeriv_apply, extendDerivFun_algebraMap]

/-- **Quotient rule** for `extendDeriv` (the bundled derivation): `(mk p q) ↦ (d p · q − p · d q)/q²`.
-/
theorem extendDeriv_mk (p q : K[X]) :
    extendDeriv d (RatFunc.mk p q) = RatFunc.mk (d p * q - p * d q) (q ^ 2) := by
  rw [extendDeriv_apply, extendDerivFun_mk]

/-- **The logarithmic-derivative reading** (§5.6 Rothstein–Trager building block): for a nonzero
polynomial `g`, the log-derivative of `algebraMap g` under `extendDeriv d` is `algebraMap (d g)`
over `algebraMap g`, i.e. `extendDeriv d (algMap g) / algMap g = algMap (d g) / algMap g`. -/
theorem extendDeriv_logDeriv (g : K[X]) :
    extendDeriv d (algebraMap K[X] (RatFunc K) g) / algebraMap K[X] (RatFunc K) g
      = algebraMap K[X] (RatFunc K) (d g) / algebraMap K[X] (RatFunc K) g := by
  rw [extendDeriv_algebraMap]

/-- The log-derivative of `algMap g` under `extendDeriv d` equals the rational function
`mk (d g) g` (= `(d g)/g`, the Bronstein §5.6 logarithmic derivative `g′/g`). -/
theorem extendDeriv_logDeriv_mk (g : K[X]) :
    extendDeriv d (algebraMap K[X] (RatFunc K) g) / algebraMap K[X] (RatFunc K) g
      = RatFunc.mk (d g) g := by
  rw [extendDeriv_logDeriv, RatFunc.mk_eq_div]

/-- **`K(t)` is a differential field** for the derivation extending a base `d`: the extended
derivation `extendDeriv d` makes `RatFunc K` a `Differential` ring (pinning the canonical `Algebra ℤ`
so the class field's `Derivation ℤ` instances line up), so the abstract differential-field calculus
applies to the fraction field of a monomial extension. -/
@[reducible]
noncomputable def fractionFieldDifferential : Differential (RatFunc K) :=
  letI : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
  ⟨(extendDerivQ d).restrictScalars ℤ⟩

end Bundle

/-! ### Specialization to the tower fraction field `RatFunc (RatFunc ℚ)`
The computable engine's monomial extension uses the base derivation `implicitDeriv (toPolyG Dt)` on
`(RatFunc ℚ)[X]` (here `K = CFieldSpec.K QFunNZ = RatFunc ℚ`, `t` the monomial variable). Specializing
`extendDeriv` to it yields the genuine tower fraction-field derivation on `RatFunc (RatFunc ℚ)`,
extending the monomial derivation by the quotient rule — the substrate on which the §5/§6
integral-correctness identities (`D(g) + h = f`, `D(∑ aᵢ log gᵢ) = a/d`) are stated. -/

open scoped Differential
open CPolyG

/-- The engine carrier `CFieldSpec.K QFunNZ` is `RatFunc ℚ`, a `ℚ`-algebra (needed for the `ℚ`-route
bundle). -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K QFunNZ) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- **The tower fraction-field derivation** on `RatFunc (RatFunc ℚ)` for the monomial extension with
`Dt`: `extendDeriv (implicitDeriv (toPolyG Dt))`, extending the base monomial derivation
`implicitDeriv (toPolyG Dt)` on `(RatFunc ℚ)[X]` by the quotient rule. -/
noncomputable def towerFractionFieldDeriv (Dt : CPolyG QFunNZ) :
    Derivation ℤ (RatFunc (CFieldSpec.K QFunNZ)) (RatFunc (CFieldSpec.K QFunNZ)) :=
  extendDeriv (Differential.implicitDeriv (toPolyG Dt))

/-- **The tower derivation extends the monomial derivation**: on `algebraMap (RatFunc ℚ)[X]` images,
`towerFractionFieldDeriv Dt` agrees with `implicitDeriv (toPolyG Dt)`. -/
theorem towerFractionFieldDeriv_algebraMap (Dt : CPolyG QFunNZ) (p : (CFieldSpec.K QFunNZ)[X]) :
    towerFractionFieldDeriv Dt (algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) p)
      = algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (Differential.implicitDeriv (toPolyG Dt) p) :=
  extendDeriv_algebraMap _ p

/-- **Quotient rule for the tower derivation**: `(mk p q) ↦ (Δp·q − p·Δq)/q²` with
`Δ = implicitDeriv (toPolyG Dt)`. -/
theorem towerFractionFieldDeriv_mk (Dt : CPolyG QFunNZ) (p q : (CFieldSpec.K QFunNZ)[X]) :
    towerFractionFieldDeriv Dt (RatFunc.mk p q)
      = RatFunc.mk (Differential.implicitDeriv (toPolyG Dt) p * q
          - p * Differential.implicitDeriv (toPolyG Dt) q) (q ^ 2) :=
  extendDeriv_mk _ p q

/-- **The log-derivative reading on the tower** (§5.6 Rothstein–Trager building block): the
log-derivative of `g ∈ (RatFunc ℚ)[X]` under the tower derivation is `(Δg)/g` with
`Δ = implicitDeriv (toPolyG Dt)`. -/
theorem towerFractionFieldDeriv_logDeriv (Dt : CPolyG QFunNZ) (g : (CFieldSpec.K QFunNZ)[X]) :
    towerFractionFieldDeriv Dt (algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) g)
        / algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) g
      = RatFunc.mk (Differential.implicitDeriv (toPolyG Dt) g) g :=
  extendDeriv_logDeriv_mk _ g

/-- **`RatFunc (RatFunc ℚ)` is a differential field** for the monomial extension `Dt`: the tower
derivation `extendDeriv (implicitDeriv (toPolyG Dt))` makes it a `Differential` ring (the substrate
for the §5/§6 integral-correctness identities over the genuine tower fraction field). Built through
`fractionFieldDifferential`, whose `restrictScalars`-under-`letI` resolves the `Module ℤ` field
diamond. -/
@[reducible]
noncomputable def towerFractionFieldDifferential (Dt : CPolyG QFunNZ) :
    Differential (RatFunc (CFieldSpec.K QFunNZ)) :=
  fractionFieldDifferential (Differential.implicitDeriv (toPolyG Dt))

/-- Headline restatement: `extendDeriv d` extends the base derivation `d` on polynomial images. -/
example [Algebra ℚ K] (d : Derivation ℤ K[X] K[X]) (p : K[X]) :
    extendDeriv d (algebraMap K[X] (RatFunc K) p) = algebraMap K[X] (RatFunc K) (d p) :=
  extendDeriv_algebraMap d p

end DeepWiki.SymbolicIntegration
