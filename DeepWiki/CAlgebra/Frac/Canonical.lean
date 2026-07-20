import DeepWiki.CAlgebra.Frac.Basic
import DeepWiki.CAlgebra.Poly.Euclid

/-! # Canonical form for computable rational functions

`DenseFrac.reduce` canonicalizes a fraction over a field: divide numerator and denominator by
their `gcd`, then scale the denominator monic; zero denominators collapse to the canonical zero
`0 / 1`. The denotation into `RatFunc` is preserved (`toRatFunc_reduce`), the reduced denominator
is monic and in particular nonzero (`reduce_den_leadingCoeff`, `reduce_den_ne_zero`), and the
reduced pair is coprime (`isCoprime_reduce`). -/

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [Field R] [DecidableEq R]

namespace DenseFrac

open DensePoly

/-- Canonicalize a fraction: divide numerator and denominator by their `gcd` and scale the
denominator monic; zero denominators collapse to the canonical zero `0 / 1`. -/
def reduce (f : DenseFrac R) : DenseFrac R :=
  if f.den = 0 then ⟨0, 1⟩
  else
    ⟨C (f.den / DensePoly.gcd f.num f.den).leadingCoeff⁻¹ * (f.num / DensePoly.gcd f.num f.den),
     C (f.den / DensePoly.gcd f.num f.den).leadingCoeff⁻¹ * (f.den / DensePoly.gcd f.num f.den)⟩

/-- Canonicalization preserves the `RatFunc` denotation. -/
theorem toRatFunc_reduce (f : DenseFrac R) : toRatFunc (reduce f) = toRatFunc f := by
  rw [reduce]
  split
  · rename_i hd
    simp [toRatFunc, hd]
  · rename_i hd
    set g := DensePoly.gcd f.num f.den with hgdef
    set n' := f.num / g with hn'def
    set d' := f.den / g with hd'def
    have hg : g ≠ 0 := gcd_ne_zero_of_right hd f.num
    have hnum : g * n' = f.num :=
      EuclideanDomain.mul_div_cancel' hg (DensePoly.gcd_dvd_left f.num f.den)
    have hden : g * d' = f.den :=
      EuclideanDomain.mul_div_cancel' hg (DensePoly.gcd_dvd_right f.num f.den)
    have hd'0 : d' ≠ 0 := fun h0 => hd (by rw [← hden, h0, mul_zero])
    have hc : d'.leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero fun h0 => hd'0 (eq_zero_of_size_zero h0)
    set c := d'.leadingCoeff with hcdef
    simp only [toRatFunc]
    have hB : algebraMap (Polynomial R) (RatFunc R) (toPolynomial (C c⁻¹ * d')) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (by
        rw [toPolynomial_mul, toPolynomial_C]
        exact mul_ne_zero (Polynomial.C_ne_zero.mpr (inv_ne_zero hc)) (toPolynomial_ne_zero hd'0))
    have hD : algebraMap (Polynomial R) (RatFunc R) (toPolynomial f.den) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (toPolynomial_ne_zero hd)
    rw [div_eq_div_iff hB hD, ← map_mul, ← map_mul, ← toPolynomial_mul, ← toPolynomial_mul]
    suffices h : C c⁻¹ * n' * f.den = f.num * (C c⁻¹ * d') by rw [h]
    rw [← hnum, ← hden]
    ring

/-- The canonical denominator is monic. -/
theorem reduce_den_leadingCoeff (f : DenseFrac R) : (reduce f).den.leadingCoeff = 1 := by
  rw [reduce]
  split
  · exact leadingCoeff_one
  · rename_i hd
    set g := DensePoly.gcd f.num f.den with hgdef
    set d' := f.den / g with hd'def
    have hg : g ≠ 0 := gcd_ne_zero_of_right hd f.num
    have hden : g * d' = f.den :=
      EuclideanDomain.mul_div_cancel' hg (DensePoly.gcd_dvd_right f.num f.den)
    have hd'0 : d' ≠ 0 := fun h0 => hd (by rw [← hden, h0, mul_zero])
    have hc : d'.leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero fun h0 => hd'0 (eq_zero_of_size_zero h0)
    show (C d'.leadingCoeff⁻¹ * d').leadingCoeff = 1
    rw [leadingCoeff_C_mul (inv_ne_zero hc), inv_mul_cancel₀ hc]

/-- The canonical denominator is nonzero. -/
theorem reduce_den_ne_zero (f : DenseFrac R) : (reduce f).den ≠ 0 := fun h0 => by
  have h := reduce_den_leadingCoeff f
  rw [h0, leadingCoeff_zero] at h
  exact zero_ne_one h

/-- The canonical numerator and denominator are coprime. -/
theorem isCoprime_reduce (f : DenseFrac R) : IsCoprime (reduce f).num (reduce f).den := by
  rw [reduce]
  split
  · exact isCoprime_zero_left.mpr isUnit_one
  · rename_i hd
    set g := DensePoly.gcd f.num f.den with hgdef
    set n' := f.num / g with hn'def
    set d' := f.den / g with hd'def
    have hg : g ≠ 0 := gcd_ne_zero_of_right hd f.num
    have hnum : g * n' = f.num :=
      EuclideanDomain.mul_div_cancel' hg (DensePoly.gcd_dvd_left f.num f.den)
    have hden : g * d' = f.den :=
      EuclideanDomain.mul_div_cancel' hg (DensePoly.gcd_dvd_right f.num f.den)
    have hd'0 : d' ≠ 0 := fun h0 => hd (by rw [← hden, h0, mul_zero])
    have hc : d'.leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero fun h0 => hd'0 (eq_zero_of_size_zero h0)
    set c := d'.leadingCoeff with hcdef
    show IsCoprime (C c⁻¹ * n') (C c⁻¹ * d')
    -- the gcd-reduced pair has unit gcd: cancel `g` against `gcd n' d' * g ∣ g`
    have hunit : IsUnit (DensePoly.gcd n' d') := by
      apply isUnit_of_dvd_one
      have h2 : g * DensePoly.gcd n' d' ∣ f.num := by
        rw [← hnum]; exact mul_dvd_mul_left _ (DensePoly.gcd_dvd_left _ _)
      have h3 : g * DensePoly.gcd n' d' ∣ f.den := by
        rw [← hden]; exact mul_dvd_mul_left _ (DensePoly.gcd_dvd_right _ _)
      have h1 : g * DensePoly.gcd n' d' ∣ g * 1 := by
        rw [mul_one]; exact DensePoly.dvd_gcd f.num f.den h2 h3
      exact (mul_dvd_mul_iff_left hg).mp h1
    -- Bézout through the Euclidean-domain instance turns the unit gcd into coprimality
    have hcop : IsCoprime n' d' := by
      have hED : IsUnit (EuclideanDomain.gcd n' d') :=
        (euclideanDomain_gcd_associated_gcd n' d').symm.isUnit hunit
      obtain ⟨u, hu⟩ := hED
      refine ⟨↑u⁻¹ * EuclideanDomain.gcdA n' d', ↑u⁻¹ * EuclideanDomain.gcdB n' d', ?_⟩
      have hbez := EuclideanDomain.gcd_eq_gcd_ab n' d'
      calc ↑u⁻¹ * EuclideanDomain.gcdA n' d' * n' + ↑u⁻¹ * EuclideanDomain.gcdB n' d' * d'
          = ↑u⁻¹ * (n' * EuclideanDomain.gcdA n' d' + d' * EuclideanDomain.gcdB n' d') := by ring
        _ = ↑u⁻¹ * ↑u := by rw [← hbez, hu]
        _ = 1 := u.inv_mul
    -- unit scaling preserves coprimality
    obtain ⟨a, b, hab⟩ := hcop
    have hCC : C c * C c⁻¹ = (1 : DensePoly R) := by
      rw [← C_mul, mul_inv_cancel₀ hc, ← one_def]
    refine ⟨a * C c, b * C c, ?_⟩
    calc a * C c * (C c⁻¹ * n') + b * C c * (C c⁻¹ * d')
        = (C c * C c⁻¹) * (a * n' + b * d') := by ring
      _ = 1 * 1 := by rw [hCC, hab]
      _ = 1 := one_mul 1

end DenseFrac

end DeepWiki.CAlgebra
