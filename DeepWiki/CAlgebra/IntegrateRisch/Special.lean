import DeepWiki.CAlgebra.IntegrateRisch.DerivationExtend
import DeepWiki.CAlgebra.Poly.Euclid
import DeepWiki.CAlgebra.Gcd

/-! # Normal and special polynomials

For a derivation `D` on `K[t]`, a polynomial is **normal** when it is coprime with its
derivative and **special** when it divides its derivative. A squarefree polynomial
splits as `normalPart · specialPart` via `gcd(p, Dp)`; the quartet of correctness
theorems (product, coprimality, normality, speciality) is pure divisibility algebra
over the engine carrier. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {K : Type u} [Field K] [DecidableEq K] [DensePolyGcd K]

/-- `p` is normal for the derivation `D`: coprime with its derivative. -/
def IsNormal (D : DensePoly K → DensePoly K) (p : DensePoly K) : Prop :=
  IsCoprime p (D p)

/-- `p` is special for the derivation `D`: divides its derivative. -/
def IsSpecial (D : DensePoly K → DensePoly K) (p : DensePoly K) : Prop :=
  p ∣ D p

/-- Normality descends to divisors. -/
theorem IsNormal.of_dvd {D : DensePoly K → DensePoly K} (hD : IsDerivation D)
    {n q : DensePoly K} (hn : IsNormal D n) (hq : q ∣ n) : IsNormal D q := by
  obtain ⟨m, rfl⟩ := hq
  rw [IsNormal, DensePolyGcd.isCoprime_iff_isUnit_gcd]
  have hw1 : DensePolyGcd.gcd q (D q) ∣ q := DensePolyGcd.gcd_dvd_left _ _
  have hw2 : DensePolyGcd.gcd q (D q) ∣ D q := DensePolyGcd.gcd_dvd_right _ _
  have hwn : DensePolyGcd.gcd q (D q) ∣ q * m := hw1.mul_right m
  have hwDn : DensePolyGcd.gcd q (D q) ∣ D (q * m) := by
    rw [hD.leibniz]
    exact dvd_add (hw2.mul_right m) (hw1.mul_right (D m))
  exact hn.isUnit_of_dvd' hwn hwDn

omit [DensePolyGcd K] in
/-- Normality is closed under coprime products. -/
theorem IsNormal.mul {D : DensePoly K → DensePoly K} (hD : IsDerivation D)
    {a b : DensePoly K} (ha : IsNormal D a) (hb : IsNormal D b) (hab : IsCoprime a b) :
    IsNormal D (a * b) := by
  rw [IsNormal, hD.leibniz]
  refine IsCoprime.mul_left ?_ ?_
  · exact (ha.mul_right hab).add_mul_left_right (D b)
  · rw [add_comm]
    exact (hab.symm.mul_right hb).add_mul_right_right (D a)

omit [DensePolyGcd K] in
/-- Speciality is closed under products. -/
theorem IsSpecial.mul {D : DensePoly K → DensePoly K} (hD : IsDerivation D)
    {a b : DensePoly K} (ha : IsSpecial D a) (hb : IsSpecial D b) :
    IsSpecial D (a * b) := by
  rw [IsSpecial, hD.leibniz]
  exact dvd_add (mul_dvd_mul ha dvd_rfl) (mul_dvd_mul dvd_rfl hb)

omit [DensePolyGcd K] in
/-- Speciality is closed under (positive) powers. -/
theorem IsSpecial.pow {D : DensePoly K → DensePoly K} (hD : IsDerivation D)
    {a : DensePoly K} (ha : IsSpecial D a) (n : ℕ) : IsSpecial D (a ^ (n + 1)) := by
  induction n with
  | zero => simpa using ha
  | succ n ih =>
      rw [pow_succ]
      exact IsSpecial.mul hD ih ha

/-- Cofactors of a squarefree product are coprime. -/
theorem isCoprime_of_squarefree_mul {a b : DensePoly K} (hsf : Squarefree (a * b)) :
    IsCoprime a b := by
  rw [DensePolyGcd.isCoprime_iff_isUnit_gcd]
  exact hsf _ (mul_dvd_mul (DensePolyGcd.gcd_dvd_left a b) (DensePolyGcd.gcd_dvd_right a b))

/-- The special part of a squarefree polynomial: `gcd(p, Dp)`. -/
def specialPart (D : DensePoly K → DensePoly K) (p : DensePoly K) : DensePoly K :=
  DensePolyGcd.gcd p (D p)

/-- The normal part of a squarefree polynomial: `p / gcd(p, Dp)`. -/
def normalPart (D : DensePoly K → DensePoly K) (p : DensePoly K) : DensePoly K :=
  p / specialPart D p

variable {D : DensePoly K → DensePoly K} {p : DensePoly K}

/-- The special part divides the polynomial. -/
theorem specialPart_dvd (D : DensePoly K → DensePoly K) (p : DensePoly K) :
    specialPart D p ∣ p :=
  DensePolyGcd.gcd_dvd_left p (D p)

/-- The special part of a nonzero polynomial is nonzero. -/
theorem specialPart_ne_zero (hp0 : p ≠ 0) : specialPart D p ≠ 0 :=
  fun h0 => hp0 (zero_dvd_iff.mp (h0 ▸ specialPart_dvd D p))

/-- **The split**: normal part times special part reconstructs the polynomial. -/
theorem normalPart_mul_specialPart (hp0 : p ≠ 0) :
    normalPart D p * specialPart D p = p := by
  rw [normalPart, mul_comm]
  exact EuclideanDomain.mul_div_cancel' (specialPart_ne_zero hp0) (specialPart_dvd D p)

/-- The normal part divides the polynomial. -/
theorem normalPart_dvd (hp0 : p ≠ 0) : normalPart D p ∣ p :=
  ⟨specialPart D p, (normalPart_mul_specialPart hp0).symm⟩

/-- The normal part of a nonzero polynomial is nonzero. -/
theorem normalPart_ne_zero (hp0 : p ≠ 0) : normalPart D p ≠ 0 := fun h0 => by
  have := normalPart_mul_specialPart (D := D) hp0
  rw [h0, zero_mul] at this
  exact hp0 this.symm

/-- **Coprimality of the split**: for squarefree `p`, the normal and special parts are
coprime. -/
theorem isCoprime_normalPart_specialPart (hp0 : p ≠ 0) (hsf : Squarefree p) :
    IsCoprime (normalPart D p) (specialPart D p) := by
  rw [DensePolyGcd.isCoprime_iff_isUnit_gcd]
  apply hsf
  calc DensePolyGcd.gcd (normalPart D p) (specialPart D p)
        * DensePolyGcd.gcd (normalPart D p) (specialPart D p)
      ∣ normalPart D p * specialPart D p :=
        mul_dvd_mul (DensePolyGcd.gcd_dvd_left _ _) (DensePolyGcd.gcd_dvd_right _ _)
    _ = p := normalPart_mul_specialPart hp0

/-- **Speciality of the special part**: for squarefree `p` and a derivation `D`,
`gcd(p, Dp)` divides its own derivative. -/
theorem isSpecial_specialPart (hD : IsDerivation D) (hp0 : p ≠ 0) (hsf : Squarefree p) :
    IsSpecial D (specialPart D p) := by
  have hmul := normalPart_mul_specialPart (D := D) hp0
  have hDp : D p = D (normalPart D p) * specialPart D p
      + normalPart D p * D (specialPart D p) := by
    conv_lhs => rw [← hmul, hD.leibniz]
  have hsDp : specialPart D p ∣ D p := DensePolyGcd.gcd_dvd_right p (D p)
  have h1 : specialPart D p ∣ normalPart D p * D (specialPart D p) := by
    rw [hDp] at hsDp
    exact (dvd_add_right (Dvd.intro_left _ rfl)).mp hsDp
  exact ((isCoprime_normalPart_specialPart hp0 hsf).symm).dvd_of_dvd_mul_left h1

/-- **Normality of the normal part**: for squarefree `p` and a derivation `D`,
`p / gcd(p, Dp)` is coprime with its derivative. -/
theorem isNormal_normalPart (hD : IsDerivation D) (hp0 : p ≠ 0) (hsf : Squarefree p) :
    IsNormal D (normalPart D p) := by
  rw [IsNormal, DensePolyGcd.isCoprime_iff_isUnit_gcd]
  have hmul := normalPart_mul_specialPart (D := D) hp0
  have hDp : D p = D (normalPart D p) * specialPart D p
      + normalPart D p * D (specialPart D p) := by
    conv_lhs => rw [← hmul, hD.leibniz]
  have hqn : DensePolyGcd.gcd (normalPart D p) (D (normalPart D p)) ∣ normalPart D p :=
    DensePolyGcd.gcd_dvd_left _ _
  have hqDn : DensePolyGcd.gcd (normalPart D p) (D (normalPart D p)) ∣ D (normalPart D p) :=
    DensePolyGcd.gcd_dvd_right _ _
  have hqp : DensePolyGcd.gcd (normalPart D p) (D (normalPart D p)) ∣ p :=
    hqn.trans (normalPart_dvd hp0)
  have hqDp : DensePolyGcd.gcd (normalPart D p) (D (normalPart D p)) ∣ D p := by
    rw [hDp]
    exact dvd_add (hqDn.mul_right _) (hqn.mul_right _)
  have hqs : DensePolyGcd.gcd (normalPart D p) (D (normalPart D p)) ∣ specialPart D p :=
    DensePolyGcd.dvd_gcd p (D p) hqp hqDp
  exact (isCoprime_normalPart_specialPart hp0 hsf).isUnit_of_dvd' hqn hqs

end DensePoly

end DeepWiki.CAlgebra
