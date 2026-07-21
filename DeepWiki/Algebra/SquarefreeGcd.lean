import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Perfect

/-! # Squarefreeness via the gcd with the derivative

The algorithmic counterpart of the factorization-based `SquarefreeDeflation`: over a field of
characteristic zero, `p / gcd(p, p′)` is squarefree (`squarefree_div_gcd_derivative`), contains
every irreducible factor of `p` (`irreducible_dvd_div_gcd_derivative`), and hence receives every
squarefree divisor of `p` (`squarefree_dvd_div_gcd_derivative`). The engine behind all three is
the maximal-power derivative drop `pow_not_dvd_derivative`. Mathlib lacks these statements;
upstream candidates. -/

universe u

open Polynomial

/-- In a UFD, a nonzero squarefree element all of whose prime divisors divide `r` divides `r`. -/
theorem UniqueFactorizationMonoid.dvd_of_squarefree_of_forall_prime_dvd
    {α : Type u} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
    [NormalizationMonoid α] {t r : α} (ht : Squarefree t) (ht0 : t ≠ 0) (hr : r ≠ 0)
    (H : ∀ q, Prime q → q ∣ t → q ∣ r) : t ∣ r := by
  classical
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors ht0 hr,
    Multiset.le_iff_count]
  intro P
  by_cases hP : P ∈ UniqueFactorizationMonoid.normalizedFactors t
  · have hnodup :=
      (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors ht0).mp ht
    have hcount1 : (UniqueFactorizationMonoid.normalizedFactors t).count P = 1 := by
      have hle := Multiset.nodup_iff_count_le_one.mp hnodup P
      have hpos := Multiset.count_pos.mpr hP
      omega
    rw [hcount1]
    have hPmem : P ∈ UniqueFactorizationMonoid.normalizedFactors r := by
      rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff' hr]
      exact ⟨(UniqueFactorizationMonoid.prime_of_normalized_factor P hP).irreducible,
        UniqueFactorizationMonoid.normalize_normalized_factor P hP,
        H P (UniqueFactorizationMonoid.prime_of_normalized_factor P hP)
          (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)⟩
    exact Multiset.count_pos.mpr hPmem
  · rw [Multiset.count_eq_zero_of_notMem hP]
    exact Nat.zero_le _

namespace Polynomial

variable {K : Type u} [Field K]

/-- An irreducible polynomial over a field has positive degree. -/
theorem natDegree_pos_of_irreducible' {q : K[X]} (hq : Irreducible q) : 0 < q.natDegree := by
  rcases Nat.eq_zero_or_pos q.natDegree with h | h
  · exfalso
    by_cases hc0 : q.coeff 0 = 0
    · exact hq.ne_zero (by rw [eq_C_of_natDegree_eq_zero h, hc0, map_zero])
    · exact hq.not_isUnit (by
        rw [eq_C_of_natDegree_eq_zero h]
        exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))
  · exact h

/-- Every power of an irreducible dividing a nonzero polynomial is degree-bounded, so a maximal
power exists. -/
theorem exists_max_pow_dvd {p q : K[X]} (hp : p ≠ 0) (hq : Irreducible q) (hqp : q ∣ p) :
    ∃ k, 1 ≤ k ∧ q ^ k ∣ p ∧ ¬ q ^ (k + 1) ∣ p := by
  classical
  have hqdeg : 0 < q.natDegree := natDegree_pos_of_irreducible' hq
  have hbound : ∀ n, q ^ n ∣ p → n ≤ p.natDegree := by
    intro n hdvd
    have h1 := Polynomial.natDegree_le_of_dvd hdvd hp
    rw [Polynomial.natDegree_pow] at h1
    calc n ≤ n * q.natDegree := Nat.le_mul_of_pos_right n hqdeg
      _ ≤ p.natDegree := h1
  refine ⟨Nat.findGreatest (fun n => q ^ n ∣ p) p.natDegree,
    Nat.le_findGreatest (hbound 1 (by simpa using hqp)) (by simpa using hqp),
    Nat.findGreatest_spec (P := fun n => q ^ n ∣ p) (Nat.zero_le _) (by simp),
    fun hdvd => Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hbound _ hdvd) hdvd⟩

variable [CharZero K]

/-- **The derivative drops each multiplicity by exactly one in characteristic zero**: if `q^k`
exactly divides `p` (with `k ≥ 1`), then `q^k` does not divide `p′`. -/
theorem pow_not_dvd_derivative {p q : K[X]} {k : ℕ}
    (hq : Irreducible q) (hk1 : 1 ≤ k) (hdvd : q ^ k ∣ p) (hmax : ¬ q ^ (k + 1) ∣ p) :
    ¬ q ^ k ∣ derivative p := by
  obtain ⟨b, hb⟩ := hdvd
  have hqprime : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
  have hqdeg : 0 < q.natDegree := natDegree_pos_of_irreducible' hq
  have hqb : ¬ q ∣ b := fun hdvd' =>
    hmax (by rw [hb, pow_succ]; exact mul_dvd_mul (dvd_refl _) hdvd')
  intro hdvd'
  have hder : derivative p
      = q ^ (k - 1) * (C (k : K) * derivative q * b) + q ^ k * derivative b := by
    rw [hb, derivative_mul, derivative_pow]; ring
  rw [hder] at hdvd'
  have h2 := (dvd_add_left ⟨derivative b, rfl⟩).mp hdvd'
  rw [show (q : K[X]) ^ k = q ^ (k - 1) * q by
    conv_lhs => rw [← Nat.sub_add_cancel hk1, pow_succ]] at h2
  have h3 : q ∣ C (k : K) * derivative q * b :=
    (mul_dvd_mul_iff_left (pow_ne_zero _ hq.ne_zero)).mp h2
  rcases hqprime.2.2 _ _ h3 with h4 | h4
  · rcases hqprime.2.2 _ _ h4 with h5 | h5
    · have hCk : (C (k : K) : K[X]) ≠ 0 :=
        Polynomial.C_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
      have hle := Polynomial.degree_le_of_dvd h5 hCk
      rw [Polynomial.degree_C (Nat.cast_ne_zero.mpr (by omega))] at hle
      have hdegq : 0 < q.degree := by
        rwa [Polynomial.natDegree_pos_iff_degree_pos] at hqdeg
      exact absurd hdegq (not_lt.mpr hle)
    · have hq'0 : derivative q ≠ 0 := Polynomial.derivative_ne_zero.mpr (by omega)
      have hle := Polynomial.degree_le_of_dvd h5 hq'0
      exact absurd hle (not_le.mpr (Polynomial.degree_derivative_lt hq.ne_zero))
  · exact hqb h4

variable [DecidableEq K]

/-- Over a field of characteristic zero, dividing a nonzero polynomial by the gcd with its
derivative yields a **squarefree** polynomial: for each irreducible `q` with maximal power
`q^k ∣ p`, characteristic zero forces `q^k ∤ p′`, so exactly `q^(k-1)` survives into the gcd and
exactly one `q` into the quotient. -/
theorem squarefree_div_gcd_derivative {p : K[X]} (hp : p ≠ 0) :
    Squarefree (p / EuclideanDomain.gcd p (derivative p)) := by
  classical
  set G := EuclideanDomain.gcd p (derivative p) with hGdef
  have hG0 : G ≠ 0 := fun h => hp (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hGs : G * (p / G) = p :=
    EuclideanDomain.mul_div_cancel' hG0 (EuclideanDomain.gcd_dvd_left _ _)
  set s := p / G with hsdef
  have hs0 : s ≠ 0 := fun h => hp (by rw [← hGs, h, mul_zero])
  rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hs0]
  intro q hq hq2
  have hsp : s ∣ p := ⟨G, by rw [← hGs, mul_comm]⟩
  have hqp : q ∣ p := ((dvd_mul_right q q).trans hq2).trans hsp
  obtain ⟨k, hk1, hk_dvd, hk_max⟩ := exists_max_pow_dvd hp hq hqp
  have hknd : ¬ q ^ k ∣ derivative p := pow_not_dvd_derivative hq hk1 hk_dvd hk_max
  have hG1 : q ^ (k - 1) ∣ G :=
    EuclideanDomain.dvd_gcd ((pow_dvd_pow q (Nat.sub_le k 1)).trans hk_dvd)
      (Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hk_dvd)
  have hfinal : q ^ (k + 1) ∣ p := by
    have hmul : q ^ (k - 1) * (q * q) ∣ G * s := mul_dvd_mul hG1 hq2
    rw [hGs] at hmul
    rwa [show (q : K[X]) ^ (k + 1) = q ^ (k - 1) * (q * q) by
      rw [← sq, ← pow_add]; congr 1; omega]
  exact hk_max hfinal

/-- **Prime coverage of the squarefree part**: every irreducible factor of `p` survives into
`p / gcd(p, p′)` — the multiplicity of `q` in the gcd is exactly one less than in `p`. -/
theorem irreducible_dvd_div_gcd_derivative {p q : K[X]} (hp : p ≠ 0)
    (hq : Irreducible q) (hqp : q ∣ p) :
    q ∣ p / EuclideanDomain.gcd p (derivative p) := by
  classical
  set G := EuclideanDomain.gcd p (derivative p) with hGdef
  have hG0 : G ≠ 0 := fun h => hp (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hGs : G * (p / G) = p :=
    EuclideanDomain.mul_div_cancel' hG0 (EuclideanDomain.gcd_dvd_left _ _)
  set s := p / G with hsdef
  obtain ⟨k, hk1, hk_dvd, hk_max⟩ := exists_max_pow_dvd hp hq hqp
  have hknd : ¬ q ^ k ∣ derivative p := pow_not_dvd_derivative hq hk1 hk_dvd hk_max
  by_contra hqs
  have hqprime : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
  have hkG : q ^ k ∣ G :=
    hqprime.pow_dvd_of_dvd_mul_right k hqs (by rw [hGs]; exact hk_dvd)
  exact hknd (hkG.trans (EuclideanDomain.gcd_dvd_right p (derivative p)))

/-- Every squarefree divisor of `p` divides the squarefree part `p / gcd(p, p′)`. -/
theorem squarefree_dvd_div_gcd_derivative {p t : K[X]} (ht : Squarefree t) (hp : p ≠ 0)
    (htp : t ∣ p) : t ∣ p / EuclideanDomain.gcd p (derivative p) := by
  have ht0 : t ≠ 0 := fun h0 => by rw [h0] at ht; exact not_squarefree_zero ht
  have hG0 : EuclideanDomain.gcd p (derivative p) ≠ 0 :=
    fun h => hp (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hGs : EuclideanDomain.gcd p (derivative p) *
      (p / EuclideanDomain.gcd p (derivative p)) = p :=
    EuclideanDomain.mul_div_cancel' hG0 (EuclideanDomain.gcd_dvd_left _ _)
  have hs0 : p / EuclideanDomain.gcd p (derivative p) ≠ 0 :=
    fun h => hp (by rw [← hGs, h, mul_zero])
  exact UniqueFactorizationMonoid.dvd_of_squarefree_of_forall_prime_dvd ht ht0 hs0
    (fun q hqprime hqt =>
      irreducible_dvd_div_gcd_derivative hp hqprime.irreducible (hqt.trans htp))

end Polynomial
