import DeepWiki.CAlgebra.Gcd
import DeepWiki.CAlgebra.Poly.Monic
import Mathlib.FieldTheory.RatFunc.Basic

/-! # Canonical computable rational functions (`DenseFrac`)

`DenseFrac R` is the canonical computable fraction over a field: a coprime numerator/denominator
pair of dense polynomials with monic denominator, the invariants bundled into the structure
(mirroring `DensePoly`'s normalization invariant). `normalize` is the smart constructor
canonicalizing any pair (zero denominators collapse to the canonical zero `0 / 1`); structural
equality is semantic equality (`toRatFunc_injective`), and the denotation `toRatFunc` into
`RatFunc R` intertwines every operation unconditionally. -/

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

open DensePoly

/-- Canonical computable rational function: a coprime numerator/denominator pair of dense
polynomials with monic denominator. -/
structure DenseFrac (R : Type u) [Field R] [DecidableEq R] where
  /-- The numerator polynomial. -/
  num : DensePoly R
  /-- The monic denominator. -/
  den : DensePolyMonic R
  /-- The numerator and denominator are coprime. -/
  coprime : IsCoprime num den.toPoly

namespace DenseFrac

omit [DensePolyGcd R] in
/-- Canonical fractions are equal when their components are (invariants are proof-irrelevant). -/
@[ext] theorem ext {f g : DenseFrac R} (h1 : f.num = g.num) (h2 : f.den = g.den) : f = g := by
  cases f; cases g; cases h1; cases h2; rfl

/-- Structural equality of canonical fractions is decidable. -/
instance : DecidableEq (DenseFrac R) := fun a b =>
  match decEq a.num b.num, decEq a.den b.den with
  | isTrue h1, isTrue h2 => isTrue (ext h1 h2)
  | isFalse h1, _ => isFalse fun h => h1 (congrArg DenseFrac.num h)
  | _, isFalse h2 => isFalse fun h => h2 (congrArg DenseFrac.den h)

/-! ### The smart constructor `normalize` -/

/-- Numerator of the canonical form of a raw pair. -/
private def normNum (n d : DensePoly R) : DensePoly R :=
  if d = 0 then 0
  else C (d / DensePolyGcd.gcd n d).leadingCoeff⁻¹ * (n / DensePolyGcd.gcd n d)

/-- Denominator of the canonical form of a raw pair. -/
private def normDen (n d : DensePoly R) : DensePoly R :=
  if d = 0 then 1
  else C (d / DensePolyGcd.gcd n d).leadingCoeff⁻¹ * (d / DensePolyGcd.gcd n d)

/-- The canonical denominator of a raw pair is monic. -/
private theorem monic_normDen (n d : DensePoly R) : (normDen n d).leadingCoeff = 1 := by
  rw [normDen]
  split
  · exact leadingCoeff_one
  · rename_i hd
    set g := DensePolyGcd.gcd n d with hgdef
    set d' := d / g with hd'def
    have hg : g ≠ 0 := DensePolyGcd.gcd_ne_zero_of_right hd n
    have hden : g * d' = d :=
      EuclideanDomain.mul_div_cancel' hg (DensePolyGcd.gcd_dvd_right n d)
    have hd'0 : d' ≠ 0 := fun h0 => hd (by rw [← hden, h0, mul_zero])
    have hc : d'.leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero fun h0 => hd'0 (eq_zero_of_size_zero h0)
    rw [leadingCoeff_C_mul (inv_ne_zero hc), inv_mul_cancel₀ hc]

/-- The canonical components of a raw pair are coprime. -/
private theorem isCoprime_norm (n d : DensePoly R) : IsCoprime (normNum n d) (normDen n d) := by
  rw [normNum, normDen]
  split_ifs with hd
  · exact isCoprime_zero_left.mpr isUnit_one
  · set g := DensePolyGcd.gcd n d with hgdef
    set n' := n / g with hn'def
    set d' := d / g with hd'def
    have hg : g ≠ 0 := DensePolyGcd.gcd_ne_zero_of_right hd n
    have hnum : g * n' = n :=
      EuclideanDomain.mul_div_cancel' hg (DensePolyGcd.gcd_dvd_left n d)
    have hden : g * d' = d :=
      EuclideanDomain.mul_div_cancel' hg (DensePolyGcd.gcd_dvd_right n d)
    have hd'0 : d' ≠ 0 := fun h0 => hd (by rw [← hden, h0, mul_zero])
    have hc : d'.leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero fun h0 => hd'0 (eq_zero_of_size_zero h0)
    set c := d'.leadingCoeff with hcdef
    -- the gcd-reduced pair has unit gcd: cancel `g` against `gcd n' d' * g ∣ g`
    have hunit : IsUnit (DensePolyGcd.gcd n' d') := by
      apply isUnit_of_dvd_one
      have h2 : g * DensePolyGcd.gcd n' d' ∣ n := by
        rw [← hnum]; exact mul_dvd_mul_left _ (DensePolyGcd.gcd_dvd_left _ _)
      have h3 : g * DensePolyGcd.gcd n' d' ∣ d := by
        rw [← hden]; exact mul_dvd_mul_left _ (DensePolyGcd.gcd_dvd_right _ _)
      have h1 : g * DensePolyGcd.gcd n' d' ∣ g * 1 := by
        rw [mul_one]; exact DensePolyGcd.dvd_gcd n d h2 h3
      exact (mul_dvd_mul_iff_left hg).mp h1
    -- Bézout through the class-level criterion turns the unit gcd into coprimality
    have hcop : IsCoprime n' d' := DensePolyGcd.isCoprime_iff_isUnit_gcd.mpr hunit
    -- unit scaling preserves coprimality
    obtain ⟨a, b, hab⟩ := hcop
    have hCC : C c * C c⁻¹ = (1 : DensePoly R) := by
      rw [← C_mul, mul_inv_cancel₀ hc, ← one_def]
    refine ⟨a * C c, b * C c, ?_⟩
    calc a * C c * (C c⁻¹ * n') + b * C c * (C c⁻¹ * d')
        = (C c * C c⁻¹) * (a * n' + b * d') := by ring
      _ = 1 * 1 := by rw [hCC, hab]
      _ = 1 := one_mul 1

/-- Canonicalize a numerator/denominator pair (the smart constructor): divide out the gcd and
scale the denominator monic; zero denominators collapse to the canonical zero `0 / 1`. -/
def normalize (n d : DensePoly R) : DenseFrac R :=
  ⟨normNum n d, ⟨normDen n d, monic_normDen n d⟩, isCoprime_norm n d⟩

/-- Embed a polynomial as the fraction with denominator `1` (already canonical). -/
def ofPoly (p : DensePoly R) : DenseFrac R := ⟨p, 1, isCoprime_one_right⟩

/-- Normalizing a zero-denominator pair gives the canonical zero. -/
theorem normalize_den_zero (n : DensePoly R) : normalize n 0 = ⟨0, 1,
    isCoprime_zero_left.mpr isUnit_one⟩ := by
  have h1 : normNum n 0 = 0 := by rw [normNum, if_pos rfl]
  have h2 : normDen n 0 = 1 := by rw [normDen, if_pos rfl]
  exact ext h1 (DensePolyMonic.ext h2)

/-! ### Mathlib bridge -/

omit [DensePolyGcd R] in
/-- Bridge to Mathlib: `num / den` in the rational-function field. -/
noncomputable def toRatFunc (f : DenseFrac R) : RatFunc R :=
  algebraMap (Polynomial R) (RatFunc R) (toPolynomial f.num) /
    algebraMap (Polynomial R) (RatFunc R) (toPolynomial f.den.toPoly)

omit [DensePolyGcd R] in
/-- Denotational equality of quotient expressions is polynomial cross-multiplication. -/
theorem div_eq_div_iff_cross {n d n' d' : DensePoly R} (hd : d ≠ 0) (hd' : d' ≠ 0) :
    algebraMap (Polynomial R) (RatFunc R) (toPolynomial n) /
        algebraMap (Polynomial R) (RatFunc R) (toPolynomial d) =
      algebraMap (Polynomial R) (RatFunc R) (toPolynomial n') /
        algebraMap (Polynomial R) (RatFunc R) (toPolynomial d') ↔ n * d' = n' * d := by
  have hD : algebraMap (Polynomial R) (RatFunc R) (toPolynomial d) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (toPolynomial_ne_zero hd)
  have hD' : algebraMap (Polynomial R) (RatFunc R) (toPolynomial d') ≠ 0 :=
    RatFunc.algebraMap_ne_zero (toPolynomial_ne_zero hd')
  rw [div_eq_div_iff hD hD', ← map_mul, ← map_mul, ← toPolynomial_mul, ← toPolynomial_mul]
  exact ((IsFractionRing.injective (Polynomial R) (RatFunc R)).comp
    toPolynomial_injective).eq_iff

/-- `normalize` computes the quotient of its arguments — unconditionally: a zero denominator
makes both sides `0`. -/
theorem toRatFunc_normalize (n d : DensePoly R) :
    toRatFunc (normalize n d) =
      algebraMap (Polynomial R) (RatFunc R) (toPolynomial n) /
        algebraMap (Polynomial R) (RatFunc R) (toPolynomial d) := by
  rw [toRatFunc]
  show algebraMap (Polynomial R) (RatFunc R) (toPolynomial (normNum n d)) /
      algebraMap (Polynomial R) (RatFunc R) (toPolynomial (normDen n d)) = _
  rw [normNum, normDen]
  split_ifs with hd
  · simp [hd]
  · set g := DensePolyGcd.gcd n d with hgdef
    set n' := n / g with hn'def
    set d' := d / g with hd'def
    have hg : g ≠ 0 := DensePolyGcd.gcd_ne_zero_of_right hd n
    have hnum : g * n' = n :=
      EuclideanDomain.mul_div_cancel' hg (DensePolyGcd.gcd_dvd_left n d)
    have hden : g * d' = d :=
      EuclideanDomain.mul_div_cancel' hg (DensePolyGcd.gcd_dvd_right n d)
    have hd'0 : d' ≠ 0 := fun h0 => hd (by rw [← hden, h0, mul_zero])
    have hc : d'.leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero fun h0 => hd'0 (eq_zero_of_size_zero h0)
    set c := d'.leadingCoeff with hcdef
    rw [div_eq_div_iff_cross (mul_ne_zero (C_ne_zero (inv_ne_zero hc)) hd'0) hd]
    rw [← hnum, ← hden]
    ring

omit [DensePolyGcd R] in
/-- The denotation is injective: canonical representatives are unique — coprimality forces the
denominators to divide each other (Euclid's lemma), monicity pins the unit, cancellation matches
the numerators. -/
theorem toRatFunc_injective : Function.Injective (toRatFunc (R := R)) := by
  intro f g h
  have key : f.num * g.den.toPoly = g.num * f.den.toPoly :=
    (div_eq_div_iff_cross f.den.ne_zero g.den.ne_zero).mp h
  have h12 : f.den.toPoly ∣ g.den.toPoly := by
    apply f.coprime.symm.dvd_of_dvd_mul_left
    rw [key]
    exact dvd_mul_left f.den.toPoly g.num
  have h21 : g.den.toPoly ∣ f.den.toPoly := by
    apply g.coprime.symm.dvd_of_dvd_mul_left
    rw [← key]
    exact dvd_mul_left g.den.toPoly f.num
  have hden : f.den = g.den := DensePolyMonic.eq_of_associated (associated_of_dvd_dvd h12 h21)
  have hnum : f.num = g.num := by
    have hk := key
    rw [hden] at hk
    exact mul_right_cancel₀ g.den.ne_zero hk
  exact ext hnum hden

omit [DensePolyGcd R] in
/-- Structural equality is semantic equality in `RatFunc` — and both are decidable. -/
theorem toRatFunc_eq_iff {f g : DenseFrac R} : toRatFunc f = toRatFunc g ↔ f = g :=
  ⟨fun h => toRatFunc_injective h, fun h => h ▸ rfl⟩

omit [DensePolyGcd R] in
/-- The polynomial embedding denotes as the polynomial itself. -/
@[simp] theorem toRatFunc_ofPoly (p : DensePoly R) :
    toRatFunc (ofPoly p) = algebraMap (Polynomial R) (RatFunc R) (toPolynomial p) := by
  rw [toRatFunc]
  show algebraMap (Polynomial R) (RatFunc R) (toPolynomial p) /
    algebraMap (Polynomial R) (RatFunc R) (toPolynomial (1 : DensePoly R)) = _
  rw [toPolynomial_one, map_one, div_one]

/-! ### Arithmetic (renormalizing through `normalize`) -/

instance : Zero (DenseFrac R) :=
  ⟨⟨0, 1, isCoprime_zero_left.mpr isUnit_one⟩⟩

instance : One (DenseFrac R) := ⟨⟨1, 1, isCoprime_one_right⟩⟩

omit [DensePolyGcd R] in
/-- A canonical fraction with zero numerator is the canonical zero: coprimality forces
the denominator to `1`. -/
theorem eq_zero_of_num_eq_zero {g : DenseFrac R} (h : g.num = 0) : g = 0 := by
  have hco := g.coprime
  rw [h] at hco
  have hu : IsUnit g.den.toPoly := isCoprime_zero_left.mp hco
  have hu' : IsUnit (toPolynomial g.den.toPoly) :=
    hu.map (equiv (R := R) : DensePoly R →+* Polynomial R)
  have hm : (toPolynomial g.den.toPoly).Monic := by
    rw [Polynomial.Monic, leadingCoeff_toPolynomial g.den.ne_zero, g.den.monic]
  have h1 : g.den.toPoly = 1 := by
    apply toPolynomial_injective
    rw [hm.eq_one_of_isUnit hu', toPolynomial_one]
  exact ext h (DensePolyMonic.ext h1)

instance : Add (DenseFrac R) :=
  ⟨fun f g => normalize (f.num * g.den.toPoly + g.num * f.den.toPoly) (f.den.toPoly * g.den.toPoly)⟩

instance : Mul (DenseFrac R) := ⟨fun f g => normalize (f.num * g.num) (f.den.toPoly * g.den.toPoly)⟩

/-- Negation preserves canonicity componentwise — no renormalization needed. -/
instance : Neg (DenseFrac R) := ⟨fun f => ⟨-f.num, f.den, f.coprime.neg_left⟩⟩

instance : Inv (DenseFrac R) := ⟨fun f => normalize f.den.toPoly f.num⟩

omit [DensePolyGcd R] in
@[simp] theorem toRatFunc_zero : toRatFunc (0 : DenseFrac R) = 0 := by
  rw [toRatFunc]
  show algebraMap (Polynomial R) (RatFunc R) (toPolynomial (0 : DensePoly R)) / _ = 0
  rw [toPolynomial_zero, map_zero, zero_div]

omit [DensePolyGcd R] in
@[simp] theorem toRatFunc_one : toRatFunc (1 : DenseFrac R) = 1 := by
  rw [toRatFunc]
  show algebraMap (Polynomial R) (RatFunc R) (toPolynomial (1 : DensePoly R)) /
    algebraMap (Polynomial R) (RatFunc R) (toPolynomial (1 : DensePoly R)) = 1
  rw [toPolynomial_one, map_one, div_one]

/-- `toRatFunc` intertwines addition (unconditionally — the invariants supply nonzeroness). -/
@[simp] theorem toRatFunc_add (f g : DenseFrac R) :
    toRatFunc (f + g) = toRatFunc f + toRatFunc g := by
  show toRatFunc (normalize _ _) = _
  rw [toRatFunc_normalize, toRatFunc, toRatFunc,
    div_add_div _ _ (RatFunc.algebraMap_ne_zero (toPolynomial_ne_zero f.den.ne_zero))
      (RatFunc.algebraMap_ne_zero (toPolynomial_ne_zero g.den.ne_zero))]
  simp only [toPolynomial_add, toPolynomial_mul, map_add, map_mul]
  congr 1
  ring

/-- `toRatFunc` intertwines multiplication. -/
@[simp] theorem toRatFunc_mul (f g : DenseFrac R) :
    toRatFunc (f * g) = toRatFunc f * toRatFunc g := by
  show toRatFunc (normalize _ _) = _
  rw [toRatFunc_normalize, toRatFunc, toRatFunc, toPolynomial_mul, toPolynomial_mul,
    map_mul, map_mul, div_mul_div_comm]

omit [DensePolyGcd R] in
/-- `toRatFunc` intertwines negation. -/
@[simp] theorem toRatFunc_neg (f : DenseFrac R) : toRatFunc (-f) = -toRatFunc f := by
  rw [toRatFunc, toRatFunc]
  show algebraMap (Polynomial R) (RatFunc R) (toPolynomial (-f.num)) /
    algebraMap (Polynomial R) (RatFunc R) (toPolynomial f.den.toPoly) = _
  rw [toPolynomial_neg, map_neg, neg_div]

/-- `toRatFunc` intertwines inversion. -/
@[simp] theorem toRatFunc_inv (f : DenseFrac R) : toRatFunc f⁻¹ = (toRatFunc f)⁻¹ := by
  show toRatFunc (normalize _ _) = _
  rw [toRatFunc_normalize, toRatFunc, inv_div]

/-! ### The canonical denominator's universal property -/

omit [DensePolyGcd R] in
/-- **Universal property of the canonical denominator**: it divides any denominator of any
fraction representation of the same rational function — the bundled coprimality cancels the
numerator from the cross-multiplication identity. -/
theorem den_dvd_of_eq_div {f : DenseFrac R} {n d : DensePoly R} (hd : d ≠ 0)
    (h : toRatFunc f = algebraMap (Polynomial R) (RatFunc R) (toPolynomial n) /
        algebraMap (Polynomial R) (RatFunc R) (toPolynomial d)) :
    f.den.toPoly ∣ d := by
  have hcross : f.num * d = n * f.den.toPoly := by
    rw [toRatFunc] at h
    exact (div_eq_div_iff_cross f.den.ne_zero hd).mp h
  have h1 : f.den.toPoly ∣ f.num * d := ⟨n, hcross.trans (mul_comm _ _)⟩
  exact f.coprime.symm.dvd_of_dvd_mul_left h1

/-- The denominator of `normalize n d` divides `d`. -/
theorem den_normalize_dvd {n d : DensePoly R} (hd : d ≠ 0) :
    (normalize n d).den.toPoly ∣ d :=
  den_dvd_of_eq_div hd (toRatFunc_normalize n d)

/-- The denominator of a sum divides the product of the denominators. -/
theorem den_add_dvd (f g : DenseFrac R) :
    (f + g).den.toPoly ∣ f.den.toPoly * g.den.toPoly := by
  apply den_dvd_of_eq_div (mul_ne_zero f.den.ne_zero g.den.ne_zero)
  rw [toRatFunc_add, toRatFunc, toRatFunc,
    div_add_div _ _ (RatFunc.algebraMap_ne_zero (toPolynomial_ne_zero f.den.ne_zero))
      (RatFunc.algebraMap_ne_zero (toPolynomial_ne_zero g.den.ne_zero)),
    ← map_mul, ← map_mul, ← map_mul, ← toPolynomial_mul, ← toPolynomial_mul,
    ← toPolynomial_mul, ← map_add, ← toPolynomial_add]

/-- `toRatFunc` distributes over list sums. -/
theorem toRatFunc_list_sum (l : List (DenseFrac R)) :
    toRatFunc l.sum = (l.map toRatFunc).sum := by
  induction l with
  | nil => simp
  | cons x t ih => simp [ih]

end DenseFrac

end DeepWiki.CAlgebra
