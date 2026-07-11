import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.FieldTheory.Separable
import DeepWiki.Algebra.PolynomialNormalization
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory.PartDerivatives

/-! # Polynomial Yun recurrence terms

The polynomial terms driving the squarefree-factorization recurrence.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

section SquarefreeYun
open UniqueFactorizationMonoid
variable {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D] [NormalizedGCDMonoid D]

open Classical in
/-- The polynomial `Yₖ = ∑_{i≥k} (i−k+1)·(dAᵢ/dx)·∏_{l≥k, l≠i} Aₗ` driving the
squarefree-factorization recurrence. -/
noncomputable def Yun (A : D[X]) (i : ℕ) : D[X] :=
  ∑ a ∈ ((normalizedFactors A.primPart).toFinset.image
      (fun P => (normalizedFactors A.primPart).count P)).filter (fun a => i ≤ a),
    C ((a - i + 1 : ℕ) : D) * derivative (sqfreeFactPart A a)
      * ∏ l ∈ (((normalizedFactors A.primPart).toFinset.image
          (fun P => (normalizedFactors A.primPart).count P)).filter (fun a => i ≤ a)).erase a,
        sqfreeFactPart A l

omit [IsDomain D] [UniqueFactorizationMonoid D] [NormalizedGCDMonoid D] in
/-- Exponent-shifting helper: `(∏ₗ gₗ^(l−j))·(∏_{l≠b} gₗ) = gᵦ^(b−j)·∏_{l≠b} gₗ^(l−j+1)`. -/
private theorem prod_pow_sub_mul_prod_erase (g : ℕ → D[X]) (s : Finset ℕ) (j b : ℕ) (hb : b ∈ s) :
    (∏ l ∈ s, g l ^ (l - j)) * (∏ l ∈ s.erase b, g l)
      = g b ^ (b - j) * ∏ l ∈ s.erase b, g l ^ (l - j + 1) := by
  rw [← Finset.mul_prod_erase _ (fun l => g l ^ (l - j)) hb, mul_assoc, ← Finset.prod_mul_distrib]
  exact congrArg _ (Finset.prod_congr rfl fun l _ => (pow_succ (g l) (l - j)).symm)

open Classical in
/-- Derivative recurrence `d(A⁻⁽ⁱ⁻¹⁾)/dx = A⁻ⁱ · Yᵢ` (`1 ≤ i`). -/
theorem derivative_deflation_pred (A : D[X]) (i : ℕ) (hi : 1 ≤ i) :
    derivative (deflation A (i - 1)) = deflation A i * Yun A i := by
  set I := (normalizedFactors A.primPart).toFinset.image
    (fun P => (normalizedFactors A.primPart).count P) with hI
  set f := sqfreeFactPart A with hf
  set I' := I.filter (fun a => i ≤ a) with hI'
  have hdefi : deflation A i = ∏ l ∈ I', f l ^ (l - i) := by
    rw [deflation_eq_prod_sqfreeFactPart A i, ← hI, ← hf]
    refine (Finset.prod_subset (Finset.filter_subset _ _) (fun l hlI hl => ?_)).symm
    rw [Finset.mem_filter, not_and] at hl
    rw [show l - i = 0 from by have := hl hlI; omega, pow_zero]
  rw [derivative_deflation A (i - 1), ← hI, ← hf, hdefi, Yun, ← hI, ← hf, ← hI', Finset.mul_sum,
    ← Finset.sum_subset (Finset.filter_subset (fun a => i ≤ a) I) (fun a haI ha => ?_)]
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_filter] at ha
    have hinner : ∏ b ∈ I.erase a, f b ^ (b - (i - 1)) = ∏ b ∈ I'.erase a, f b ^ (b - i + 1) := by
      refine (Finset.prod_subset (Finset.erase_subset_erase a (Finset.filter_subset _ _))
        (fun b hbI hb => ?_)).symm.trans (Finset.prod_congr rfl fun b hb => ?_)
      · rw [Finset.mem_erase] at hbI
        rw [Finset.mem_erase, Finset.mem_filter, not_and] at hb
        rw [show b - (i - 1) = 0 from by
          have : ¬ i ≤ b := fun h => (hb hbI.1) ⟨hbI.2, h⟩
          omega, pow_zero]
      · rw [Finset.mem_erase, Finset.mem_filter] at hb
        rw [show b - (i - 1) = b - i + 1 from by omega]
    rw [show a - (i - 1) = a - i + 1 from by omega, show a - i + 1 - 1 = a - i from by omega, hinner]
    linear_combination (-(C ((a - i + 1 : ℕ) : D) * derivative (f a)))
      * prod_pow_sub_mul_prod_erase f I' i a (Finset.mem_filter.mpr ha)
  · rw [Finset.mem_filter, not_and] at ha
    rw [show a - (i - 1) = 0 from by have := ha haI; omega]
    simp

open Classical in
/-- `Yᵢ − d(A⁻⁽ⁱ⁻¹⁾)*/dx = Aᵢ·Y_{i+1}` (`1 ≤ i`). -/
theorem Yun_sub_derivative_squarefreePart (A : D[X]) (i : ℕ) (hi : 1 ≤ i) (hA : A.primPart ≠ 0) :
    Yun A i - derivative (squarefreePart (deflation A (i - 1)))
      = sqfreeFactPart A i * Yun A (i + 1) := by
  set I := (normalizedFactors A.primPart).toFinset.image
    (fun P => (normalizedFactors A.primPart).count P) with hI
  set f := sqfreeFactPart A with hf
  have hfi1 : i ∉ I → f i = 1 := by
    intro hiI
    have hempty : (normalizedFactors A.primPart).toFinset.filter
        (fun P => (normalizedFactors A.primPart).count P = i) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun P hP hc => hiI (hc ▸ Finset.mem_image_of_mem _ hP))
    rw [hf, sqfreeFactPart, hempty, Finset.prod_empty]
  have hII : (I.filter (fun a => i ≤ a)).erase i = I.filter (fun a => i + 1 ≤ a) := by
    ext x; simp only [Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨hne, hxI, hle⟩; exact ⟨hxI, by omega⟩
    · rintro ⟨hxI, hle⟩; exact ⟨by omega, hxI, by omega⟩
  have hfilt : I.filter (fun a => i - 1 < a) = I.filter (fun a => i ≤ a) := by
    ext x; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hxI, h⟩; exact ⟨hxI, by omega⟩
    · rintro ⟨hxI, h⟩; exact ⟨hxI, by omega⟩
  have hregroup : ∀ a ∈ I.filter (fun a => i + 1 ≤ a),
      ∏ l ∈ (I.filter (fun a => i ≤ a)).erase a, f l
        = f i * ∏ l ∈ (I.filter (fun a => i + 1 ≤ a)).erase a, f l := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨haI, hai⟩ := ha
    by_cases hiI : i ∈ I
    · have hierase : i ∈ (I.filter (fun a => i ≤ a)).erase a := by
        rw [Finset.mem_erase, Finset.mem_filter]; exact ⟨by omega, hiI, le_refl i⟩
      have hset : ((I.filter (fun a => i ≤ a)).erase a).erase i
          = (I.filter (fun a => i + 1 ≤ a)).erase a := by
        ext x; simp only [Finset.mem_erase, Finset.mem_filter]
        constructor
        · rintro ⟨hxi, hxa, hxI, hle⟩; exact ⟨hxa, hxI, by omega⟩
        · rintro ⟨hxa, hxI, hle⟩; exact ⟨by omega, hxa, hxI, by omega⟩
      rw [← Finset.mul_prod_erase _ f hierase, hset]
    · rw [hfi1 hiI, one_mul]
      refine Finset.prod_congr ?_ (fun _ _ => rfl)
      ext x; simp only [Finset.mem_erase, Finset.mem_filter]
      constructor
      · rintro ⟨hxa, hxI, hle⟩
        exact ⟨hxa, hxI, by have : x ≠ i := fun h => hiI (h ▸ hxI); omega⟩
      · rintro ⟨hxa, hxI, hle⟩; exact ⟨hxa, hxI, by omega⟩
  rw [Yun, ← hI, ← hf, derivative_squarefreePart_deflation A (i - 1) hA, ← hI, ← hf, hfilt,
    Yun, ← hI, ← hf, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun a _ => by
    show C ((a - i + 1 : ℕ) : D) * derivative (f a)
          * ∏ l ∈ (I.filter (fun a => i ≤ a)).erase a, f l
        - (∏ b ∈ (I.filter (fun a => i ≤ a)).erase a, f b) * derivative (f a)
      = C ((a - i : ℕ) : D) * derivative (f a)
          * ∏ l ∈ (I.filter (fun a => i ≤ a)).erase a, f l
    have hc : C ((a - i + 1 : ℕ) : D) - 1 = C ((a - i : ℕ) : D) := by
      rw [show ((a - i + 1 : ℕ) : D) = ((a - i : ℕ) : D) + 1 from by push_cast; ring,
        map_add, map_one]; ring
    linear_combination (derivative (f a)
      * ∏ l ∈ (I.filter (fun a => i ≤ a)).erase a, f l) * hc)]
  rw [← Finset.sum_erase (I.filter (fun a => i ≤ a))
      (show C ((i - i : ℕ) : D) * derivative (f i)
          * ∏ l ∈ (I.filter (fun a => i ≤ a)).erase i, f l = 0 from by
        rw [Nat.sub_self, Nat.cast_zero, map_zero]; ring), hII]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mem_filter] at ha
  rw [(by omega : (a - (i + 1) + 1 : ℕ) = a - i), hregroup a (Finset.mem_filter.mpr ha)]
  ring

end SquarefreeYun

section SquarefreeYunField

open UniqueFactorizationMonoid Classical

variable {K : Type*} [Field K] [CharZero K]

/-- Over a characteristic-`0` field, `(A⁻⁽ⁱ⁻¹⁾)*` and `Yᵢ` are relatively prime:
`IsRelPrime ((A⁻⁽ⁱ⁻¹⁾)*) (Yᵢ)` (`1 ≤ i`). -/
theorem isRelPrime_squarefreePart_Yun (A : K[X]) (i : ℕ) (hi : 1 ≤ i) (hA : A.primPart ≠ 0) :
    IsRelPrime (squarefreePart (deflation A (i - 1))) (Yun A i) := by
  set I := (normalizedFactors A.primPart).toFinset.image
    (fun P => (normalizedFactors A.primPart).count P) with hI
  set f := sqfreeFactPart A with hf
  have hsp := squarefreePart_deflation_eq_prod A (i - 1) hA
  rw [← hI, ← hf] at hsp
  have hne : squarefreePart (deflation A (i - 1)) ≠ 0 := by
    rw [hsp, Finset.prod_ne_zero_iff]; exact fun l _ => sqfreeFactPart_ne_zero A l
  rw [isRelPrime_iff_no_prime_factors hne]
  intro P hPsp hPY hPp
  rw [hsp, hPp.dvd_finsetProd_iff] at hPsp
  obtain ⟨a, haI, hPa⟩ := hPsp
  rw [Finset.mem_filter] at haI
  have haI' : a ∈ I.filter (fun a => i ≤ a) := Finset.mem_filter.mpr ⟨haI.1, by omega⟩
  have hPfa' : ¬ P ∣ derivative (f a) := by
    obtain ⟨m, hm⟩ := hPa
    have hPm : ¬ P ∣ m := by
      rintro ⟨n, hmn⟩
      exact hPp.not_unit ((sqfreeFactPart_squarefree A a) P ⟨n, by rw [← hf, hm, hmn]; ring⟩)
    have hsep : P.Separable := (hPp.irreducible).separable
    have hPP' : ¬ P ∣ derivative P := fun h => hPp.not_unit (hsep.isUnit_of_dvd' (dvd_refl P) h)
    intro hPfad
    rw [hm, derivative_mul] at hPfad
    have hd : P ∣ derivative P * m :=
      (dvd_add_left (dvd_mul_right P (derivative m))).mp hPfad
    rcases hPp.dvd_mul.mp hd with h | h
    · exact hPP' h
    · exact hPm h
  have hPfl : ∀ l, l ≠ a → ¬ P ∣ f l :=
    fun l hla hPl => hPp.not_unit (sqfreeFactPart_isRelPrime A hla hPl hPa)
  set g : ℕ → K[X] := fun b => C ((b - i + 1 : ℕ) : K) * derivative (f b)
    * ∏ l ∈ (I.filter (fun a => i ≤ a)).erase b, f l with hg
  have hga : ¬ P ∣ g a := by
    intro hh
    rcases hPp.dvd_mul.mp hh with h1 | h2
    · rcases hPp.dvd_mul.mp h1 with hc | hd
      · exact hPp.not_unit (isUnit_of_dvd_unit hc
          (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))))
      · exact hPfa' hd
    · rw [hPp.dvd_finsetProd_iff] at h2
      obtain ⟨l, hl, hPl⟩ := h2
      exact hPfl l (Finset.mem_erase.mp hl).1 hPl
  have hPS : P ∣ ∑ b ∈ (I.filter (fun a => i ≤ a)).erase a, g b := by
    refine Finset.dvd_sum (fun b hb => ?_)
    have hab : a ∈ (I.filter (fun a => i ≤ a)).erase b :=
      Finset.mem_erase.mpr ⟨((Finset.mem_erase.mp hb).1).symm, haI'⟩
    exact hg ▸ dvd_mul_of_dvd_right (hPa.trans (Finset.dvd_prod_of_mem f hab)) _
  rw [Yun, ← hI, ← hf, ← Finset.add_sum_erase _ g haI'] at hPY
  exact hga ((dvd_add_left hPS).mp hPY)

/-- The Yun gcd step extracts the `i`-th squarefree-factorization part. -/
theorem gcd_radical_yunStep_assoc (A : K[X]) (i : ℕ) (hi : 1 ≤ i)
    (hA : A.primPart ≠ 0) :
    Associated
      (gcd (squarefreePart (deflation A (i - 1)))
        (Yun A i - derivative (squarefreePart (deflation A (i - 1)))))
      (sqfreeFactPart A i) := by
  have hsplit := squarefreePart_deflation_mul_sqfreeFactPart A i hi hA
  have hd := Yun_sub_derivative_squarefreePart A i hi hA
  set V := sqfreeFactPart A i with hV
  set S' := squarefreePart (deflation A i) with hS'
  set Y := Yun A (i + 1) with hY
  have hS : squarefreePart (deflation A (i - 1)) = V * S' := by
    rw [hV, hS', mul_comm]; exact hsplit.symm
  rw [hd, hS]
  refine (gcd_mul_left' V S' Y).trans ?_
  have hrp : IsRelPrime S' Y := by
    have h := isRelPrime_squarefreePart_Yun A (i + 1) (by omega) hA
    rwa [Nat.add_sub_cancel] at h
  have hunit : IsUnit (gcd S' Y) := gcd_isUnit_iff_isRelPrime.mpr hrp
  have : Associated (V * gcd S' Y) (V * 1) :=
    (associated_one_iff_isUnit.mpr hunit).mul_left V
  rwa [mul_one] at this

end SquarefreeYunField

end DeepWiki.SymbolicIntegration
