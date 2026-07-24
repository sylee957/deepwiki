import DeepWiki.SymbolicIntegration.RiobooCoprimality
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LazardRiobooTragerCorrectness

/-! # LRT discharges the Rioboo cofactor hypotheses
The Lazard–Rioboo–Trager correctness theorem supplies the gcd-cofactor factorizations that
`rioboo_coprime` takes as hypotheses, giving `rioboo_coprime_lrt`: `IsCoprime A B` for the real and
imaginary parts of the LRT output curve, with hypotheses only on `C, D` real, `D` separable, and `b ≠ 0`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

section SimilarDvd
variable {K : Type*} [Field K]

/-- Over a field, `IsSimilar p q` implies `Associated p q` (`C a, C b` are units, so `p = C(a⁻¹b)·q`
with `C(a⁻¹b)` a unit). -/
theorem IsSimilar.associated {p q : K[X]} (h : IsSimilar p q) : Associated p q := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  -- `p = C(a⁻¹·b) · q`, with `C(a⁻¹·b)` a unit
  have hpq : p = C (a⁻¹ * b) * q := by
    have hca : C (a⁻¹) * (C a * p) = p := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
    rw [← hca, hab, map_mul]; ring
  have hunit : IsUnit (C (a⁻¹ * b) : K[X]) :=
    isUnit_C.mpr (Ne.isUnit (mul_ne_zero (inv_ne_zero ha) hb))
  rw [hpq]; exact associated_unit_mul_left q _ hunit

/-- Over a field, `IsSimilar p q` with `q ∣ r` gives `p ∣ r` (similar ⟹ associated ⟹ same divisors). -/
theorem IsSimilar.dvd_of_dvd {p q r : K[X]} (h : IsSimilar p q) (hqr : q ∣ r) : p ∣ r :=
  h.associated.dvd.trans hqr

end SimilarDvd

section RealImagDecomp
variable {K : Type*} [Field K] [CharZero K]

/-- With an involutive coefficient conjugation `conj` sending `i ↦ −i` (`i² = −1`, char `0`), every
`z ∈ K[x]` decomposes as `z = z₁ + (C i)·z₂` with `z₁, z₂` fixed by `σ = map conj`. -/
theorem exists_realImag_decomp (conj : K →+* K)
    (hconj : ∀ c, conj (conj c) = c) {i : K} (hi : i ^ 2 = -1) (hconji : conj i = -i)
    (z : K[X]) :
    ∃ z₁ z₂ : K[X], z = z₁ + C i * z₂ ∧ z₁.map conj = z₁ ∧ z₂.map conj = z₂ := by
  set σ : K[X] →+* K[X] := Polynomial.mapRingHom conj with hσdef
  have hσσ : ∀ w : K[X], σ (σ w) = w := by
    intro w
    simp only [hσdef, coe_mapRingHom, Polynomial.map_map]
    rw [show (conj.comp conj) = RingHom.id K from by ext c; simp [hconj], Polynomial.map_id]
  have hσCi : σ (C i) = -(C i) := by
    rw [hσdef, coe_mapRingHom, Polynomial.map_C, hconji, C_neg]
  -- the `σ`-fixed scalar `1/2`
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  set c2 : K[X] := C ((2 : K)⁻¹) with hc2def
  have hσc2 : σ c2 = c2 := by
    rw [hσdef, hc2def, coe_mapRingHom, Polynomial.map_C, map_inv₀, map_ofNat]
  have hc2two : c2 * (2 : K[X]) = 1 := by
    rw [hc2def, ← map_ofNat (C : K →+* K[X]) 2, ← C_mul, inv_mul_cancel₀ h2, map_one]
  have hi2 : (C i : K[X]) ^ 2 = -1 := by rw [← C_pow, hi, C_neg, map_one]
  refine ⟨c2 * (z + σ z), c2 * (-(C i) * (z - σ z)), ?_, ?_, ?_⟩
  · -- reconstruct `z`: `z₁ + (C i)·z₂ = c2·(z+σz) + c2·(z−σz) = c2·2·z = z`
    have hcalc : c2 * (z + σ z) + C i * (c2 * (-(C i) * (z - σ z))) = c2 * 2 * z := by
      linear_combination (c2 * σ z - c2 * z) * hi2
    rw [hcalc, hc2two, one_mul]
  · -- `z₁` is `σ`-fixed
    show σ (c2 * (z + σ z)) = c2 * (z + σ z)
    rw [map_mul, hσc2, map_add, hσσ]; ring
  · -- `z₂` is `σ`-fixed
    show σ (c2 * (-(C i) * (z - σ z))) = c2 * (-(C i) * (z - σ z))
    rw [map_mul, hσc2, map_mul, map_neg, hσCi, map_sub, hσσ]; ring

end RealImagDecomp

section LrtCoprime
variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

open scoped Classical in
/-- Over an algebraically closed char-`0` field with conjugation `conj` (`conj i = −i`, `i² = −1`), `C, D`
real, `D` separable, `deg C < deg D`, `b ≠ 0`, and `(a+i·b)` a root of `rtResultant C D`, the real and
imaginary parts of the LRT output curve `S(a+i·b, x) = A + i·B` satisfy `IsCoprime A B`. -/
theorem rioboo_coprime_lrt (Cnum D : K[X]) (hD : D.Separable) (hCD : Cnum.natDegree < D.natDegree)
    (conj : K →+* K) (hconj : ∀ c, conj (conj c) = c) {i : K} (hi : i ^ 2 = -1)
    (hconji : conj i = -i) (hCreal : Cnum.map conj = Cnum) (hDreal : D.map conj = D)
    {a b : K} (hareal : conj a = a) (hbreal : conj b = b) (hb : b ≠ 0)
    (_hroot : (rtResultant Cnum D).IsRoot (a + i * b)) :
    ∃ A B : K[X], IsCoprime A B ∧
      (((if (rtResultant Cnum D).rootMultiplicity (a + i * b) = D.natDegree then
            D.map (C : K →+* K[X])
          else lrtSubresultant Cnum D ((rtResultant Cnum D).rootMultiplicity (a + i * b))).map
        (Polynomial.evalRingHom (a + i * b))) = A + C i * B) := by
  set r : K := a + i * b with hr
  set Sxt : (K[X])[X] :=
    if (rtResultant Cnum D).rootMultiplicity r = D.natDegree then D.map (C : K →+* K[X])
    else lrtSubresultant Cnum D ((rtResultant Cnum D).rootMultiplicity r) with hSxt
  set Sr : K[X] := Sxt.map (Polynomial.evalRingHom r) with hSr
  -- LRT correctness: `S(r, x) ~ gcd(D, C − r·D')`
  have hLRT : IsSimilar Sr (gcd D (Cnum - C r * derivative D)) := by
    rw [hSr, hSxt]
    exact lazardRiobooTrager_output_isSimilar_gcd Cnum D hD hCD r
  -- the gcd divides both, so `S(r, x)` divides both
  have hSrD : Sr ∣ D := hLRT.dvd_of_dvd (gcd_dvd_left _ _)
  have hSrE : Sr ∣ (Cnum - C r * derivative D) := hLRT.dvd_of_dvd (gcd_dvd_right _ _)
  obtain ⟨F, hF⟩ := hSrD
  obtain ⟨E, hE⟩ := hSrE
  -- real/imaginary splits of `S(r, x)`, `E`, `F`
  obtain ⟨A, B, hSrAB, hAreal, hBreal⟩ := exists_realImag_decomp conj hconj hi hconji Sr
  obtain ⟨E₁, E₂, hE12, hE1real, hE2real⟩ := exists_realImag_decomp conj hconj hi hconji E
  obtain ⟨F₁, F₂, hF12, hF1real, hF2real⟩ := exists_realImag_decomp conj hconj hi hconji F
  refine ⟨A, B, ?_, hSrAB⟩
  -- assemble the `rioboo_coprime` hypotheses, with `σ := map conj` and `i := C i`
  set σ : K[X] →+* K[X] := Polynomial.mapRingHom conj with hσdef
  have hσfix : ∀ {w : K[X]}, w.map conj = w → σ w = w := fun {w} h => h
  have hiC : (C i : K[X]) ^ 2 = -1 := by rw [← C_pow, hi, map_neg, map_one]
  have hσCi : σ (C i) = -(C i) := by
    rw [hσdef, coe_mapRingHom, Polynomial.map_C, hconji, C_neg]
  have hσCa : σ (C a) = C a := by rw [hσdef, coe_mapRingHom, Polynomial.map_C, hareal]
  have hσCb : σ (C b) = C b := by rw [hσdef, coe_mapRingHom, Polynomial.map_C, hbreal]
  have hσC : σ Cnum = Cnum := hσfix hCreal
  have hσD : σ D = D := hσfix hDreal
  have hσD' : σ (derivative D) = derivative D := by
    rw [hσdef, coe_mapRingHom, ← derivative_map, hDreal]
  -- `C r = C a + C i · C b`
  have hCr : C r = C a + C i * C b := by rw [hr, map_add, map_mul]
  -- The real and imaginary cofactors factor the shifted numerator.
  have h27 : Cnum - (C a + C i * C b) * derivative D = (E₁ + C i * E₂) * (A + C i * B) := by
    rw [← hCr, hE, hSrAB, ← hE12]; ring
  -- The real and imaginary divisor cofactors factor the denominator.
  have h28 : D = (F₁ + C i * F₂) * (A + C i * B) := by
    rw [hF, hSrAB, ← hF12]; ring
  -- `b` is a unit, `D` separable ⟹ `IsCoprime D D'`
  have hbunit : IsUnit (C b : K[X]) := isUnit_C.mpr (Ne.isUnit hb)
  have hsqfree : IsCoprime D (derivative D) := hD
  exact rioboo_coprime hiC σ hσCi hσCa hσCb hσC hσD hσD'
    (hσfix hE1real) (hσfix hE2real) (hσfix hF1real) (hσfix hF2real)
    (hσfix hAreal) (hσfix hBreal) hbunit hsqfree h27 h28

end LrtCoprime

end DeepWiki.SymbolicIntegration
