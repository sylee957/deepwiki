import DeepWiki.CAlgebra.Diff.Frac
import DeepWiki.SymbolicIntegration.Core.Differential.PolynomialFractionDeriv
import Mathlib.RingTheory.Derivation.MapCoeffs

/-! # Extension derivations

The computable extension of a coefficient derivation `d : K → K` along a monomial `t`
with prescribed derivative `Dt`: on `DensePoly K` as coefficient-wise `d` plus `Dt ·`
the formal derivative, on `DenseFrac K` by the quotient rule. `IsDerivation` packages
the derivation laws; the squares read the extensions as Mathlib's
`Differential.implicitDeriv` and its fraction-field extension. -/

namespace DeepWiki.CAlgebra

universe u v

section IsDerivation

variable {K : Type u} [CommRing K]

/-- `d` is a derivation: additive and Leibniz. -/
structure IsDerivation (d : K → K) : Prop where
  map_add : ∀ a b, d (a + b) = d a + d b
  leibniz : ∀ a b, d (a * b) = d a * b + a * d b

namespace IsDerivation

variable {d : K → K}

/-- A derivation kills `0`. -/
theorem map_zero (hd : IsDerivation d) : d 0 = 0 := by
  have h := hd.map_add 0 0
  rw [add_zero] at h
  exact (add_left_cancel (a := d 0) (show d 0 + 0 = d 0 + d 0 by rw [add_zero]; exact h)).symm

/-- A derivation kills `1`. -/
theorem map_one (hd : IsDerivation d) : d 1 = 0 := by
  have h := hd.leibniz 1 1
  rw [mul_one, mul_one, one_mul] at h
  exact (add_left_cancel (a := d 1) (show d 1 + 0 = d 1 + d 1 by rw [add_zero]; exact h)).symm

/-- A derivation commutes with negation. -/
theorem map_neg (hd : IsDerivation d) (a : K) : d (-a) = -d a := by
  have h := hd.map_add a (-a)
  rw [add_neg_cancel, hd.map_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- A derivation commutes with subtraction. -/
theorem map_sub (hd : IsDerivation d) (a b : K) : d (a - b) = d a - d b := by
  rw [sub_eq_add_neg, hd.map_add, hd.map_neg, sub_eq_add_neg]

/-- A derivation commutes with finite sums. -/
theorem map_sum (hd : IsDerivation d) {ι : Type v} (s : Finset ι) (f : ι → K) :
    d (∑ i ∈ s, f i) = ∑ i ∈ s, d (f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using hd.map_zero
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, hd.map_add, ih]

/-- Bundle an `IsDerivation` as Mathlib's `Differential` structure. -/
@[reducible] noncomputable def toDifferential (hd : IsDerivation d) : Differential K :=
  ⟨Derivation.mk'
    (AddMonoidHom.toIntLinearMap
      { toFun := d, map_zero' := hd.map_zero, map_add' := hd.map_add })
    (fun a b => by
      show d (a * b) = a • d b + b • d a
      rw [hd.leibniz, smul_eq_mul, smul_eq_mul]
      ring)⟩

/-- The bundled derivation applies as `d`. -/
theorem toDifferential_deriv (hd : IsDerivation d) :
    ⇑(@Differential.deriv K _ hd.toDifferential) = d := rfl

end IsDerivation

/-- The zero map is a derivation (the constant-field base case). -/
theorem isDerivation_zero : IsDerivation (fun _ => (0 : K)) :=
  ⟨fun _ _ => by simp, fun _ _ => by simp⟩

end IsDerivation

namespace DensePoly

variable {K : Type u} [CommRing K] [DecidableEq K] {d : K → K}

open scoped Differential FormalDiff

/-- Coefficient-wise application of a (zero-preserving) map. -/
def mapCoeffs (f : K → K) (p : DensePoly K) : DensePoly K :=
  ofList (p.coeffs.map f)

/-- Coefficient reading of `mapCoeffs`. -/
theorem coeff_mapCoeffs {f : K → K} (hf : f 0 = 0) (p : DensePoly K) (n : ℕ) :
    (mapCoeffs f p).coeff n = f (p.coeff n) :=
  coeff_ofList_map f hf p n

/-- A pointwise-zero map annihilates every polynomial. -/
theorem mapCoeffs_eq_zero {f : K → K} (hf : ∀ c, f c = 0) (p : DensePoly K) :
    mapCoeffs f p = 0 := by
  ext n
  rw [coeff_mapCoeffs (hf 0) p n, hf, coeff_zero]

/-- The coefficient-wise derivative is additive. -/
theorem mapCoeffs_add (hd : IsDerivation d) (p q : DensePoly K) :
    mapCoeffs d (p + q) = mapCoeffs d p + mapCoeffs d q := by
  ext n
  rw [coeff_mapCoeffs hd.map_zero, coeff_add, hd.map_add, coeff_add,
    coeff_mapCoeffs hd.map_zero, coeff_mapCoeffs hd.map_zero]

/-- Leibniz rule for the coefficient-wise derivative. -/
theorem mapCoeffs_mul (hd : IsDerivation d) (p q : DensePoly K) :
    mapCoeffs d (p * q) = mapCoeffs d p * q + p * mapCoeffs d q := by
  ext n
  rw [coeff_mapCoeffs hd.map_zero, coeff_mul, hd.map_sum, coeff_add, coeff_mul, coeff_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd.leibniz, coeff_mapCoeffs hd.map_zero, coeff_mapCoeffs hd.map_zero]

/-- The coefficient-wise derivative on constants. -/
theorem mapCoeffs_C (hd0 : d 0 = 0) (c : K) : mapCoeffs d (C c) = C (d c) := by
  ext n
  rw [coeff_mapCoeffs hd0, coeff_C, coeff_C, apply_ite d, hd0]

/-- **The extension derivation on `K[t]`**: coefficient-wise `d` plus `Dt ·` the formal
derivative. -/
def extendDeriv (d : K → K) (Dt : DensePoly K) (p : DensePoly K) : DensePoly K :=
  mapCoeffs d p + Dt * p′

/-- Additivity of the polynomial extension. -/
theorem extendDeriv_add (hd : IsDerivation d) (Dt p q : DensePoly K) :
    extendDeriv d Dt (p + q) = extendDeriv d Dt p + extendDeriv d Dt q := by
  rw [extendDeriv, extendDeriv, extendDeriv, mapCoeffs_add hd, deriv_add]
  ring

/-- Leibniz rule for the polynomial extension. -/
theorem extendDeriv_mul (hd : IsDerivation d) (Dt p q : DensePoly K) :
    extendDeriv d Dt (p * q) = extendDeriv d Dt p * q + p * extendDeriv d Dt q := by
  rw [extendDeriv, extendDeriv, extendDeriv, mapCoeffs_mul hd, deriv_mul]
  ring

/-- The polynomial extension is a derivation. -/
theorem isDerivation_extendDeriv (hd : IsDerivation d) (Dt : DensePoly K) :
    IsDerivation (extendDeriv d Dt) :=
  ⟨extendDeriv_add hd Dt, extendDeriv_mul hd Dt⟩

/-- The polynomial extension extends `d` on constants. -/
theorem extendDeriv_C (hd : IsDerivation d) (Dt : DensePoly K) (c : K) :
    extendDeriv d Dt (C c) = C (d c) := by
  rw [extendDeriv, mapCoeffs_C hd.map_zero, deriv_C, mul_zero, add_zero]

/-- The polynomial extension takes the prescribed value on the variable. -/
theorem extendDeriv_X (hd : IsDerivation d) (Dt : DensePoly K) :
    extendDeriv d Dt (ofList [0, 1]) = Dt := by
  have hmc : mapCoeffs d (ofList [0, 1]) = 0 := by
    ext n
    rw [coeff_mapCoeffs hd.map_zero, coeff_zero, coeff_ofList]
    rcases n with _ | _ | n
    · exact hd.map_zero
    · exact hd.map_one
    · exact hd.map_zero
  rw [extendDeriv, deriv_X, mul_one, hmc, zero_add]

/-- At the constant-field base data (`d = 0`, `Dt = 1`), the extension is the formal
derivative. -/
theorem extendDeriv_zero_one (p : DensePoly K) :
    extendDeriv (fun _ => (0 : K)) 1 p = p′ := by
  rw [extendDeriv, mapCoeffs_eq_zero (fun _ => rfl), one_mul, zero_add]

section Square

variable [Differential K]

/-- The coefficient-wise derivative reads as Mathlib's `Differential.mapCoeffs`. -/
theorem toPolynomial_mapCoeffs (hd : ∀ a : K, d a = a′) (p : DensePoly K) :
    toPolynomial (mapCoeffs d p) = Differential.mapCoeffs (toPolynomial p) := by
  have hd0 : d 0 = 0 := by rw [hd 0]; exact Differential.deriv.map_zero
  refine Polynomial.ext fun n => ?_
  rw [coeff_toPolynomial, coeff_mapCoeffs hd0, Differential.coeff_mapCoeffs,
    coeff_toPolynomial, hd]

/-- **The polynomial square**: the computable extension reads as `implicitDeriv`. -/
theorem toPolynomial_extendDeriv (hd : ∀ a : K, d a = a′) (Dt p : DensePoly K) :
    toPolynomial (extendDeriv d Dt p)
      = Differential.implicitDeriv (toPolynomial Dt) (toPolynomial p) := by
  rw [extendDeriv, toPolynomial_add, toPolynomial_mul, toPolynomial_deriv,
    toPolynomial_mapCoeffs hd, Differential.implicitDeriv]
  simp only [Derivation.add_apply, Derivation.smul_apply, Derivation.coe_restrictScalars,
    smul_eq_mul]
  rfl

end Square

end DensePoly

namespace DenseFrac

variable {K : Type u} [Field K] [DecidableEq K] [DensePolyGcd K] {d : K → K}

open scoped Differential FormalDiff

/-- **The extension derivation on `K(t)`** by the quotient rule. -/
def extendDeriv (d : K → K) (Dt : DensePoly K) (f : DenseFrac K) : DenseFrac K :=
  normalize (DensePoly.extendDeriv d Dt f.num * f.den.toPoly
      - f.num * DensePoly.extendDeriv d Dt f.den.toPoly) (f.den.toPoly ^ 2)

/-- At the constant-field base data (`d = 0`, `Dt = 1`), the extension is the formal
quotient rule. -/
theorem extendDeriv_zero_one (f : DenseFrac K) :
    extendDeriv (fun _ => (0 : K)) 1 f = fracDeriv f := by
  rw [extendDeriv, fracDeriv, DensePoly.extendDeriv_zero_one, DensePoly.extendDeriv_zero_one]

section Square

open DeepWiki.SymbolicIntegration.PolynomialFractionDeriv

variable [Differential K]

/-- **The fraction square**: the computable quotient-rule extension reads as the
fraction-field extension of `implicitDeriv`. -/
theorem toRatFunc_extendDeriv (hd : ∀ a : K, d a = a′) (Dt : DensePoly K)
    (f : DenseFrac K) :
    toRatFunc (extendDeriv d Dt f)
      = SymbolicIntegration.PolynomialFractionDeriv.fracDeriv (K := RatFunc K)
          (Differential.implicitDeriv (toPolynomial Dt))
          (toRatFunc f) := by
  have hden : toPolynomial f.den.toPoly ≠ 0 := toPolynomial_ne_zero f.den.ne_zero
  have hmem : toPolynomial f.den.toPoly ∈ nonZeroDivisors (Polynomial K) :=
    mem_nonZeroDivisors_of_ne_zero hden
  rw [extendDeriv, toRatFunc_normalize, toRatFunc,
    show algebraMap (Polynomial K) (RatFunc K) (toPolynomial f.num)
        / algebraMap (Polynomial K) (RatFunc K) (toPolynomial f.den.toPoly)
      = IsLocalization.mk' (RatFunc K) (toPolynomial f.num)
          (⟨toPolynomial f.den.toPoly, hmem⟩ : nonZeroDivisors (Polynomial K)) from
      by rw [IsFractionRing.mk'_eq_div],
    SymbolicIntegration.PolynomialFractionDeriv.fracDeriv_mk',
    SymbolicIntegration.PolynomialFractionDeriv.rawDeriv, IsFractionRing.mk'_eq_div]
  rw [toPolynomial_sub, toPolynomial_mul, toPolynomial_mul,
    DensePoly.toPolynomial_extendDeriv hd, DensePoly.toPolynomial_extendDeriv hd,
    show toPolynomial (f.den.toPoly ^ 2)
        = toPolynomial f.den.toPoly * toPolynomial f.den.toPoly from by
      rw [pow_two, toPolynomial_mul]]
  rw [Submonoid.coe_mul]
  rw [mul_comm (Differential.implicitDeriv (toPolynomial Dt) (toPolynomial f.num))
    (toPolynomial f.den.toPoly)]

end Square

section Laws

open SymbolicIntegration.PolynomialFractionDeriv in
/-- Additivity of the fraction extension. -/
theorem extendDeriv_add (hd : IsDerivation d) (Dt : DensePoly K) (a b : DenseFrac K) :
    extendDeriv d Dt (a + b) = extendDeriv d Dt a + extendDeriv d Dt b := by
  letI := hd.toDifferential
  have hc : ∀ x : K, d x = x′ := fun _ => rfl
  refine toRatFunc_injective ?_
  rw [toRatFunc_extendDeriv hc, toRatFunc_add,
    show SymbolicIntegration.PolynomialFractionDeriv.fracDeriv (K := RatFunc K) (Differential.implicitDeriv (toPolynomial Dt))
        (toRatFunc a + toRatFunc b)
      = SymbolicIntegration.PolynomialFractionDeriv.fracDeriv (K := RatFunc K) (Differential.implicitDeriv (toPolynomial Dt))
          (toRatFunc a)
        + SymbolicIntegration.PolynomialFractionDeriv.fracDeriv (K := RatFunc K) (Differential.implicitDeriv (toPolynomial Dt))
            (toRatFunc b) from
      fracDerivFun_add _ _ _,
    toRatFunc_add, toRatFunc_extendDeriv hc, toRatFunc_extendDeriv hc]

open SymbolicIntegration.PolynomialFractionDeriv in
/-- Leibniz rule for the fraction extension. -/
theorem extendDeriv_mul (hd : IsDerivation d) (Dt : DensePoly K) (a b : DenseFrac K) :
    extendDeriv d Dt (a * b) = extendDeriv d Dt a * b + a * extendDeriv d Dt b := by
  letI := hd.toDifferential
  have hc : ∀ x : K, d x = x′ := fun _ => rfl
  refine toRatFunc_injective ?_
  rw [toRatFunc_extendDeriv hc, toRatFunc_mul,
    show SymbolicIntegration.PolynomialFractionDeriv.fracDeriv (K := RatFunc K) (Differential.implicitDeriv (toPolynomial Dt))
        (toRatFunc a * toRatFunc b)
      = toRatFunc a * SymbolicIntegration.PolynomialFractionDeriv.fracDeriv (K := RatFunc K)
            (Differential.implicitDeriv (toPolynomial Dt)) (toRatFunc b)
        + toRatFunc b * SymbolicIntegration.PolynomialFractionDeriv.fracDeriv (K := RatFunc K)
            (Differential.implicitDeriv (toPolynomial Dt)) (toRatFunc a) from
      fracDerivFun_mul _ _ _,
    toRatFunc_add, toRatFunc_mul, toRatFunc_mul, toRatFunc_extendDeriv hc,
    toRatFunc_extendDeriv hc]
  ring

/-- **The fraction extension is a derivation** — the tower-composability keystone: the
next level's coefficient derivation is again an `IsDerivation`. -/
theorem isDerivation_extendDeriv (hd : IsDerivation d) (Dt : DensePoly K) :
    IsDerivation (extendDeriv d Dt) :=
  ⟨extendDeriv_add hd Dt, extendDeriv_mul hd Dt⟩

open SymbolicIntegration.PolynomialFractionDeriv in
/-- The fraction extension restricts to the polynomial extension on embedded
polynomials. -/
theorem extendDeriv_ofPoly (hd : IsDerivation d) (Dt : DensePoly K) (p : DensePoly K) :
    extendDeriv d Dt (ofPoly p) = ofPoly (DensePoly.extendDeriv d Dt p) := by
  letI := hd.toDifferential
  have hc : ∀ x : K, d x = x′ := fun _ => rfl
  refine toRatFunc_injective ?_
  rw [toRatFunc_extendDeriv hc, toRatFunc_ofPoly, toRatFunc_ofPoly,
    fracDeriv_algebraMap, DensePoly.toPolynomial_extendDeriv hc]

end Laws

end DenseFrac

end DeepWiki.CAlgebra
