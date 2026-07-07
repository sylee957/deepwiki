import DeepWiki.SymbolicIntegration.DifferentialFields
import DeepWiki.SymbolicIntegration.Core.Algebra.GcdBasics
import DeepWiki.SymbolicIntegration.Core.Differential.GcdDeriv
import DeepWiki.SymbolicIntegration.Core.Differential.NormalSpecial
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Algebra.Polynomial.Derivative

/-! # Monomial extensions
Specializes the core `IsNormal`/`IsSpecial` differential-ring API to the monomial
derivation `implicitDeriv v` on `k[X]` (`X′ = v`) and products of linear factors. -/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Polynomial in
/-- Degree bound: `(implicitDeriv v p).natDegree ≤ deg p + max(0, deg v − 1)`. -/
theorem natDegree_implicitDeriv_le {R : Type*} [CommRing R] [Differential R] (v p : R[X]) :
    (Differential.implicitDeriv v p).natDegree ≤ p.natDegree + max 0 (v.natDegree - 1) := by
  have happly : Differential.implicitDeriv v p = Differential.mapCoeffs p + v * derivative p := by
    simp [Differential.implicitDeriv, derivative']
  have h1 : (Differential.mapCoeffs p).natDegree ≤ p.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro N hN
    rw [Differential.coeff_mapCoeffs, coeff_eq_zero_of_natDegree_lt hN]
    simp
  rw [happly]
  rcases eq_or_ne (derivative p) 0 with hdp | hdp
  · rw [hdp, mul_zero, add_zero]
    exact h1.trans (Nat.le_add_right _ _)
  · have hp1 : 1 ≤ p.natDegree := by
      rcases Nat.eq_zero_or_pos p.natDegree with h0 | h0
      · rw [Polynomial.natDegree_eq_zero] at h0
        obtain ⟨c, rfl⟩ := h0
        simp at hdp
      · exact h0
    have h2 : (v * derivative p).natDegree ≤ v.natDegree + (p.natDegree - 1) := by
      calc (v * derivative p).natDegree ≤ v.natDegree + (derivative p).natDegree := natDegree_mul_le
        _ ≤ v.natDegree + (p.natDegree - 1) := by gcongr; exact natDegree_derivative_le p
    calc (Differential.mapCoeffs p + v * derivative p).natDegree
        ≤ max (Differential.mapCoeffs p).natDegree (v * derivative p).natDegree :=
          natDegree_add_le _ _
      _ ≤ max p.natDegree (v.natDegree + (p.natDegree - 1)) := max_le_max h1 h2
      _ ≤ p.natDegree + max 0 (v.natDegree - 1) := by omega

open Polynomial in
/-- Nonlinear degree equality: over char `0`, for `deg v ≥ 2` and `deg p ≥ 1`,
`(implicitDeriv v p).natDegree = deg p + deg v − 1`. -/
theorem natDegree_implicitDeriv_eq {F : Type*} [Field F] [CharZero F] [Differential F]
    (v p : F[X]) (hv : 2 ≤ v.natDegree) (hp : 1 ≤ p.natDegree) :
    (Differential.implicitDeriv v p).natDegree = p.natDegree + (v.natDegree - 1) := by
  have happly : Differential.implicitDeriv v p = Differential.mapCoeffs p + v * derivative p := by
    simp [Differential.implicitDeriv, derivative']
  have h1 : (Differential.mapCoeffs p).natDegree ≤ p.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro N hN
    rw [Differential.coeff_mapCoeffs, coeff_eq_zero_of_natDegree_lt hN]; simp
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have hdp : derivative p ≠ 0 := derivative_ne_zero.mpr (by omega)
  have hmul : (v * derivative p).natDegree = v.natDegree + (p.natDegree - 1) := by
    rw [natDegree_mul hv0 hdp, natDegree_derivative p]
  have hlt : (Differential.mapCoeffs p).natDegree < (v * derivative p).natDegree := by
    rw [hmul]; omega
  rw [happly, natDegree_add_eq_right_of_natDegree_lt hlt, hmul]; omega

section LinearFactor
open Polynomial

/-- Monomial derivation of a linear factor: `implicitDeriv v (X − a) = v − C a′`. -/
theorem implicitDeriv_X_sub_C {A : Type*} [CommRing A] [Differential A] (v : A[X]) (a : A) :
    Differential.implicitDeriv v (X - C a) = v - C a′ := by
  rw [map_sub, Differential.implicitDeriv_X, Differential.implicitDeriv_C]

/-- Over a field, `IsCoprime (X − a) g ↔ g.eval a ≠ 0`. -/
theorem isCoprime_X_sub_C_iff {K : Type*} [Field K] {a : K} {g : K[X]} :
    IsCoprime (X - C a) g ↔ g.eval a ≠ 0 := by
  rw [(prime_X_sub_C a).coprime_iff_not_dvd, dvd_iff_isRoot]; rfl

open Classical in
/-- Squarefree factorization: `∏_{a∈s}(X − a)^{eₐ} = ∏ₖ (∏_{a : eₐ=k}(X − a))ᵏ`. -/
theorem prod_X_sub_C_pow_eq_squarefree_factorization {K : Type*} [CommRing K] (s : Finset K)
    (e : K → ℕ) :
    (∏ a ∈ s, (X - C a) ^ e a)
      = ∏ k ∈ s.image e, (∏ a ∈ s.filter (fun a => e a = k), (X - C a)) ^ k := by
  rw [← Finset.prod_fiberwise_of_maps_to (t := s.image e)
        (fun a ha => Finset.mem_image_of_mem e ha)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun a ha => by rw [(Finset.mem_filter.mp ha).2]

/-- A product of distinct linear factors `∏_{a∈t}(X − a)` is squarefree. -/
theorem squarefree_prod_X_sub_C {K : Type*} [Field K] (t : Finset K) :
    Squarefree (∏ a ∈ t, (X - C a)) :=
  (separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ h => h)).squarefree

/-- Products of linear factors over *disjoint* root sets are coprime. -/
theorem isCoprime_prod_X_sub_C_of_disjoint {K : Type*} [Field K] {s t : Finset K}
    (h : Disjoint s t) :
    IsCoprime (∏ a ∈ s, (X - C a)) (∏ b ∈ t, (X - C b)) := by
  refine IsCoprime.prod_left (fun a ha => IsCoprime.prod_right (fun b hb => ?_))
  refine isCoprime_X_sub_C_iff.mpr ?_
  rw [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr (fun hab => (Finset.disjoint_left.mp h ha) (hab ▸ hb))

open Classical in
/-- The squarefree-factorization parts for distinct multiplicities `k ≠ k'` are coprime. -/
theorem squarefree_factorization_pairwise_coprime {K : Type*} [Field K] (s : Finset K) (e : K → ℕ)
    {k k' : ℕ} (hkk : k ≠ k') :
    IsCoprime (∏ a ∈ s.filter (fun a => e a = k), (X - C a))
      (∏ a ∈ s.filter (fun a => e a = k'), (X - C a)) :=
  isCoprime_prod_X_sub_C_of_disjoint (Finset.disjoint_left.mpr fun _ ha ha' =>
    hkk ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp ha').2))

/-- Single linear factor, normal: `X − a` is normal iff `v(a) ≠ a′`. -/
theorem isCoprime_X_sub_C_implicitDeriv_iff {K : Type*} [Field K] [Differential K] (v : K[X])
    (a : K) :
    IsCoprime (X - C a) (Differential.implicitDeriv v (X - C a)) ↔ v.eval a ≠ a′ := by
  rw [implicitDeriv_X_sub_C, isCoprime_X_sub_C_iff, eval_sub, eval_C, sub_ne_zero]

/-- Single linear factor, special: `X − a` is special iff `v(a) = a′`. -/
theorem dvd_X_sub_C_implicitDeriv_iff {K : Type*} [Field K] [Differential K] (v : K[X]) (a : K) :
    (X - C a) ∣ Differential.implicitDeriv v (X - C a) ↔ v.eval a = a′ := by
  rw [implicitDeriv_X_sub_C, dvd_iff_isRoot, IsRoot.def, eval_sub, eval_C, sub_eq_zero]

/-- Linear-factor power, special: over char `0`, `(X − a)ⁿ` (`n ≥ 1`) is special iff `v(a) = a′`. -/
theorem dvd_X_sub_C_pow_implicitDeriv_iff {K : Type*} [Field K] [CharZero K] [Differential K]
    (v : K[X]) (a : K) {n : ℕ} (hn : 1 ≤ n) :
    (X - C a) ^ n ∣ Differential.implicitDeriv v ((X - C a) ^ n) ↔ v.eval a = a′ := by
  have hnu : IsUnit ((n : K[X])) := by
    rw [← map_natCast (C : K →+* K[X])]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))
  have hD : Differential.implicitDeriv v ((X - C a) ^ n)
      = (X - C a) ^ (n - 1) * ((n : K[X]) * (v - C a′)) := by
    rw [Derivation.leibniz_pow, implicitDeriv_X_sub_C, nsmul_eq_mul, smul_eq_mul]; ring
  rw [hD, show (X - C a) ^ n = (X - C a) ^ (n - 1) * (X - C a) from by
        rw [← pow_succ, Nat.sub_add_cancel hn],
    mul_dvd_mul_iff_left (pow_ne_zero (n - 1) (X_sub_C_ne_zero a)),
    hnu.dvd_mul_left, dvd_iff_isRoot, IsRoot.def, eval_sub, eval_C, sub_eq_zero]

/-- Squarefree polynomial, normal: `∏_{a∈s}(X − a)` is normal iff `∀ a ∈ s, v(a) ≠ a′`. -/
theorem isCoprime_prod_X_sub_C_implicitDeriv_iff {K : Type*} [Field K] [Differential K]
    (v : K[X]) (s : Finset K) :
    IsCoprime (∏ a ∈ s, (X - C a)) (Differential.implicitDeriv v (∏ a ∈ s, (X - C a)))
      ↔ ∀ a ∈ s, v.eval a ≠ a′ := by
  classical
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  constructor
  · intro hnorm a ha
    have hdvd : (X - C a) ∣ ∏ b ∈ s, (X - C b) := Finset.dvd_prod_of_mem _ ha
    exact (isCoprime_X_sub_C_implicitDeriv_iff v a).mp (IsNormal.of_dvd hnorm hdvd)
  · intro h
    refine IsNormal.prod s (fun a => X - C a) (fun a ha => ?_) (fun a _ b _ hab => ?_)
    · exact (isCoprime_X_sub_C_implicitDeriv_iff v a).mpr (h a ha)
    · exact isCoprime_X_sub_C_iff.mpr (by rw [eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr hab)

/-- Squarefree polynomial, special: `∏_{a∈s}(X − a)` is special iff `∀ a ∈ s, v(a) = a′`. -/
theorem dvd_prod_X_sub_C_implicitDeriv_iff {K : Type*} [Field K] [Differential K] (v : K[X])
    (s : Finset K) :
    (∏ a ∈ s, (X - C a)) ∣ Differential.implicitDeriv v (∏ a ∈ s, (X - C a))
      ↔ ∀ a ∈ s, v.eval a = a′ := by
  classical
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  constructor
  · intro hsp a ha
    rw [← Finset.mul_prod_erase s (fun b => X - C b) ha] at hsp
    have hcop : IsCoprime (X - C a) (∏ b ∈ s.erase a, (X - C b)) := by
      rw [isCoprime_X_sub_C_iff, eval_prod]
      refine Finset.prod_ne_zero_iff.mpr (fun b hb => ?_)
      rw [eval_sub, eval_X, eval_C]
      exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hb).symm
    exact (dvd_X_sub_C_implicitDeriv_iff v a).mp (IsSpecial.of_mul_coprime hsp hcop)
  · intro h
    exact IsSpecial.prod s (fun a => X - C a)
      (fun a ha => (dvd_X_sub_C_implicitDeriv_iff v a).mpr (h a ha))

/-- General product, special: over char `0`, `∏_{a∈s}(X − a)^{eₐ}` (each `eₐ ≥ 1`) is special
iff `∀ a ∈ s, v(a) = a′`. -/
theorem dvd_prod_X_sub_C_pow_implicitDeriv_iff {K : Type*} [Field K] [CharZero K] [Differential K]
    (v : K[X]) (s : Finset K) (e : K → ℕ) (he : ∀ a ∈ s, 1 ≤ e a) :
    (∏ a ∈ s, (X - C a) ^ e a) ∣ Differential.implicitDeriv v (∏ a ∈ s, (X - C a) ^ e a)
      ↔ ∀ a ∈ s, v.eval a = a′ := by
  classical
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  constructor
  · intro hsp a ha
    rw [← Finset.mul_prod_erase s (fun b => (X - C b) ^ e b) ha] at hsp
    have hcop : IsCoprime ((X - C a) ^ e a) (∏ b ∈ s.erase a, (X - C b) ^ e b) :=
      IsCoprime.pow_left (IsCoprime.prod_right fun b hb => IsCoprime.pow_right
        (isCoprime_X_sub_C_iff.mpr (by rw [eval_sub, eval_X, eval_C]
                                       exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hb).symm)))
    exact (dvd_X_sub_C_pow_implicitDeriv_iff v a (he a ha)).mp (IsSpecial.of_mul_coprime hsp hcop)
  · intro h
    exact IsSpecial.prod s (fun a => (X - C a) ^ e a)
      (fun a ha => (dvd_X_sub_C_pow_implicitDeriv_iff v a (he a ha)).mpr (h a ha))

open Classical in
/-- Splitting factorization of `∏_{a∈s}(X − a)` into its special part (roots with `v(a) = a′`)
and normal part (roots with `v(a) ≠ a′`). -/
theorem splittingFactorization_prod_X_sub_C {K : Type*} [Field K] [Differential K] (v : K[X])
    (s : Finset K) :
    (∏ a ∈ s, (X - C a))
        = (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a))
          * (∏ a ∈ s.filter (fun a => ¬ v.eval a = a′), (X - C a))
      ∧ (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a))
          ∣ Differential.implicitDeriv v (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a))
      ∧ IsCoprime (∏ a ∈ s.filter (fun a => ¬ v.eval a = a′), (X - C a))
          (Differential.implicitDeriv v
            (∏ a ∈ s.filter (fun a => ¬ v.eval a = a′), (X - C a))) :=
  ⟨(Finset.prod_filter_mul_prod_filter_not s _ _).symm,
   (dvd_prod_X_sub_C_implicitDeriv_iff v _).mpr fun _ ha => (Finset.mem_filter.mp ha).2,
   (isCoprime_prod_X_sub_C_implicitDeriv_iff v _).mpr fun _ ha => (Finset.mem_filter.mp ha).2⟩

open Classical in
/-- Special-part extraction for a general product `∏_{a∈s}(X − a)^{eₐ}`: it factors as its
special part (roots with `v(a)=a′`, with multiplicity) times the rest. -/
theorem isSpecial_special_part {K : Type*} [Field K] [CharZero K] [Differential K] (v : K[X])
    (s : Finset K) (e : K → ℕ) (he : ∀ a ∈ s, 1 ≤ e a) :
    (∏ a ∈ s, (X - C a) ^ e a)
        = (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a) ^ e a)
          * (∏ a ∈ s.filter (fun a => ¬ v.eval a = a′), (X - C a) ^ e a)
      ∧ (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a) ^ e a)
          ∣ Differential.implicitDeriv v
              (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a) ^ e a) :=
  ⟨(Finset.prod_filter_mul_prod_filter_not s _ _).symm,
   (dvd_prod_X_sub_C_pow_implicitDeriv_iff v _ e
       (fun a ha => he a (Finset.mem_of_mem_filter a ha))).mpr
     fun _ ha => (Finset.mem_filter.mp ha).2⟩

open Classical in
/-- Squarefree gcd formula: `gcd(∏_{a∈s}(X − a), (∏)′) ~ ∏_{a : v(a)=a′}(X − a)`. -/
theorem gcd_prod_X_sub_C_implicitDeriv {K : Type*} [Field K] [Differential K] (v : K[X])
    (s : Finset K) :
    Associated (gcd (∏ a ∈ s, (X - C a)) (Differential.implicitDeriv v (∏ a ∈ s, (X - C a))))
      (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a)) := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  refine (associated_gcd_deriv_prod s (fun a => X - C a) (fun a _ b _ hab =>
    gcd_isUnit_iff_isRelPrime.mpr (isCoprime_X_sub_C_iff.mpr
      (by rw [eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr hab)).isRelPrime)).trans ?_
  rw [Finset.prod_filter]
  refine Associated.prod s _ _ (fun a _ => ?_)
  by_cases h : v.eval a = a′
  · rw [if_pos h]
    exact isSpecial_iff_associated_gcd.mp ((dvd_X_sub_C_implicitDeriv_iff v a).mpr h)
  · rw [if_neg h]
    exact associated_one_iff_isUnit.mpr
      (IsNormal.isUnit_gcd ((isCoprime_X_sub_C_implicitDeriv_iff v a).mpr h))

open Classical in
/-- General gcd formula: over char `0`, for `p = ∏_{a∈s}(X − a)^{eₐ}` (each `eₐ ≥ 1`),
`gcd(p, p′) ~ (∏_a (X − a)^{eₐ−1}) · ∏_{a : v(a)=a′}(X − a)`. -/
theorem gcd_prod_X_sub_C_pow_implicitDeriv {K : Type*} [Field K] [CharZero K] [Differential K]
    (v : K[X]) (s : Finset K) (e : K → ℕ) (he : ∀ a ∈ s, 1 ≤ e a) :
    Associated
      (gcd (∏ a ∈ s, (X - C a) ^ e a) (Differential.implicitDeriv v (∏ a ∈ s, (X - C a) ^ e a)))
      ((∏ a ∈ s, (X - C a) ^ (e a - 1)) * ∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a)) := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  have hunit : ∀ a ∈ s, IsUnit ((e a : K[X])) := by
    intro a ha
    rw [← map_natCast (C : K →+* K[X])]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by have := he a ha; omega)))
  refine (associated_gcd_deriv_prod s (fun a => (X - C a) ^ e a) (fun a _ b _ hab =>
    gcd_isUnit_iff_isRelPrime.mpr ((IsCoprime.pow (isCoprime_X_sub_C_iff.mpr
      (by rw [eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr hab))).isRelPrime))).trans ?_
  refine (Associated.prod s _ _ (fun a ha => associated_gcd_deriv_pow (he a ha) (hunit a ha))).trans ?_
  rw [Finset.prod_mul_distrib]
  refine Associated.mul_left _ ?_
  rw [Finset.prod_filter]
  refine Associated.prod s _ _ (fun a _ => ?_)
  by_cases h : v.eval a = a′
  · rw [if_pos h]
    exact isSpecial_iff_associated_gcd.mp ((dvd_X_sub_C_implicitDeriv_iff v a).mpr h)
  · rw [if_neg h]
    exact associated_one_iff_isUnit.mpr
      (IsNormal.isUnit_gcd ((isCoprime_X_sub_C_implicitDeriv_iff v a).mpr h))

open Classical in
/-- The `d/dX` companion: over char `0`, `gcd(∏_{a∈s}(X − a)^{eₐ}, d/dX) ~ ∏_a (X − a)^{eₐ−1}`. -/
theorem gcd_prod_X_sub_C_pow_derivative {K : Type*} [Field K] [CharZero K] (s : Finset K)
    (e : K → ℕ) (he : ∀ a ∈ s, 1 ≤ e a) :
    Associated (gcd (∏ a ∈ s, (X - C a) ^ e a) (derivative (∏ a ∈ s, (X - C a) ^ e a)))
      (∏ a ∈ s, (X - C a) ^ (e a - 1)) := by
  letI : Differential K[X] := ⟨(Polynomial.derivative' (R := K)).restrictScalars ℤ⟩
  have hunit : ∀ a ∈ s, IsUnit ((e a : K[X])) := by
    intro a ha
    rw [← map_natCast (C : K →+* K[X])]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by have := he a ha; omega)))
  refine (associated_gcd_deriv_prod s (fun a => (X - C a) ^ e a) (fun a _ b _ hab =>
    gcd_isUnit_iff_isRelPrime.mpr ((IsCoprime.pow (isCoprime_X_sub_C_iff.mpr
      (by rw [eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr hab))).isRelPrime))).trans ?_
  refine (Associated.prod s _ _ (fun a ha => associated_gcd_deriv_pow (he a ha) (hunit a ha))).trans ?_
  refine Associated.prod s _ _ (fun a _ => ?_)
  have hg1 : IsUnit (gcd (X - C a) ((X - C a)′)) := by
    have hd : (X - C a)′ = 1 := by show derivative (X - C a) = 1; simp
    rw [hd]; exact isUnit_gcd_one_right _
  exact (associated_mul_unit_right _ _ hg1).symm

open Classical in
/-- Squarefree part / radical: over char `0`, `∏_{a∈s}(X − a)^{eₐ} ~ gcd(A, dA/dx) · ∏(X − a)`. -/
theorem prod_X_sub_C_pow_associated_gcd_mul_radical {K : Type*} [Field K] [CharZero K]
    (s : Finset K) (e : K → ℕ) (he : ∀ a ∈ s, 1 ≤ e a) :
    Associated (∏ a ∈ s, (X - C a) ^ e a)
      (gcd (∏ a ∈ s, (X - C a) ^ e a) (derivative (∏ a ∈ s, (X - C a) ^ e a))
        * ∏ a ∈ s, (X - C a)) := by
  have hsplit : (∏ a ∈ s, (X - C a) ^ (e a - 1)) * ∏ a ∈ s, (X - C a)
      = ∏ a ∈ s, (X - C a) ^ e a := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a ha => by rw [← pow_succ, Nat.sub_add_cancel (he a ha)]
  have key := (gcd_prod_X_sub_C_pow_derivative s e he).symm.mul_right (∏ a ∈ s, (X - C a))
  rwa [hsplit] at key

open Classical in
/-- Special-part formula: over char `0`, `gcd(p, p′) ~ gcd(p, dp/dX) · ∏_{a : v(a)=a′}(X − a)`. -/
theorem gcd_implicitDeriv_associated_gcd_derivative_mul_special {K : Type*} [Field K] [CharZero K]
    [Differential K] (v : K[X]) (s : Finset K) (e : K → ℕ) (he : ∀ a ∈ s, 1 ≤ e a) :
    Associated
      (gcd (∏ a ∈ s, (X - C a) ^ e a) (Differential.implicitDeriv v (∏ a ∈ s, (X - C a) ^ e a)))
      (gcd (∏ a ∈ s, (X - C a) ^ e a) (derivative (∏ a ∈ s, (X - C a) ^ e a))
        * ∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a)) :=
  (gcd_prod_X_sub_C_pow_implicitDeriv v s e he).trans
    ((gcd_prod_X_sub_C_pow_derivative s e he).symm.mul_right _)

open Classical in
/-- The special and normal parts of the squarefree splitting are coprime. -/
theorem isCoprime_splitting_parts {K : Type*} [Field K] [Differential K] (v : K[X]) (s : Finset K) :
    IsCoprime (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a))
      (∏ a ∈ s.filter (fun a => ¬ v.eval a = a′), (X - C a)) :=
  isCoprime_prod_X_sub_C_of_disjoint (Finset.disjoint_filter_filter_not s s _)

end LinearFactor

end DeepWiki.SymbolicIntegration
