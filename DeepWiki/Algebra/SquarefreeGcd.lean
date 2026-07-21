import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Perfect

/-! # Squarefreeness via the gcd with the derivative

The algorithmic counterpart of the factorization-based `SquarefreeDeflation`: over a field of
characteristic zero, `p / gcd(p, p′)` is squarefree — the multiplicity keystone behind squarefree
parts and decompositions. Mathlib lacks this statement; upstream candidate. -/

universe u

open Polynomial in
/-- Over a field of characteristic zero, dividing a nonzero polynomial by the gcd with its
derivative yields a **squarefree** polynomial: for each irreducible `q` with maximal power
`q^k ∣ p`, characteristic zero forces `q^k ∤ p'`, so exactly `q^(k-1)` survives into the gcd and
exactly one `q` into the quotient. -/
theorem Polynomial.squarefree_div_gcd_derivative {K : Type u} [Field K]
    [DecidableEq K] [CharZero K]
    {p : K[X]} (hp : p ≠ 0) :
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
  have hqprime : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
  have hqdeg : 0 < q.natDegree := by
    rcases Nat.eq_zero_or_pos q.natDegree with h | h
    · exfalso
      by_cases hc0 : q.coeff 0 = 0
      · exact hq.ne_zero (by rw [eq_C_of_natDegree_eq_zero h, hc0, map_zero])
      · exact hq.not_isUnit (by
          rw [eq_C_of_natDegree_eq_zero h]
          exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))
    · exact h
  have hsp : s ∣ p := ⟨G, by rw [← hGs, mul_comm]⟩
  have hqp : q ∣ p := ((dvd_mul_right q q).trans hq2).trans hsp
  -- the maximal power of `q` in `p`
  have hbound : ∀ n, q ^ n ∣ p → n ≤ p.natDegree := by
    intro n hdvd
    have h1 := Polynomial.natDegree_le_of_dvd hdvd hp
    rw [Polynomial.natDegree_pow] at h1
    calc n ≤ n * q.natDegree := Nat.le_mul_of_pos_right n hqdeg
      _ ≤ p.natDegree := h1
  set k := Nat.findGreatest (fun n => q ^ n ∣ p) p.natDegree with hkdef
  have hk_dvd : q ^ k ∣ p :=
    Nat.findGreatest_spec (P := fun n => q ^ n ∣ p) (Nat.zero_le _) (by simp)
  have hk_max : ¬ q ^ (k + 1) ∣ p := fun hdvd =>
    Nat.findGreatest_is_greatest (Nat.lt_succ_self k) (hbound _ hdvd) hdvd
  have hk1 : 1 ≤ k :=
    Nat.le_findGreatest (hbound 1 (by simpa using hqp)) (by simpa using hqp)
  obtain ⟨b, hb⟩ := hk_dvd
  have hqb : ¬ q ∣ b := fun hdvd =>
    hk_max (by rw [hb, pow_succ]; exact mul_dvd_mul (dvd_refl _) hdvd)
  -- characteristic zero: `q^k` does not divide the derivative
  have hknd : ¬ q ^ k ∣ derivative p := by
    intro hdvd
    have hder : derivative p
        = q ^ (k - 1) * (C (k : K) * derivative q * b) + q ^ k * derivative b := by
      rw [hb, derivative_mul, derivative_pow]; ring
    have h2 : q ^ k ∣ q ^ (k - 1) * (C (k : K) * derivative q * b) := by
      rw [hder] at hdvd
      exact (dvd_add_left ⟨derivative b, rfl⟩).mp hdvd
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
  -- `q^(k-1)` divides the gcd, so `q^(k+1)` would divide `p`: contradiction
  have hG1 : q ^ (k - 1) ∣ G :=
    EuclideanDomain.dvd_gcd ((pow_dvd_pow q (Nat.sub_le k 1)).trans ⟨b, hb⟩)
      (Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd ⟨b, hb⟩)
  have hfinal : q ^ (k + 1) ∣ p := by
    have hmul : q ^ (k - 1) * (q * q) ∣ G * s := mul_dvd_mul hG1 hq2
    rw [hGs] at hmul
    rwa [show (q : K[X]) ^ (k + 1) = q ^ (k - 1) * (q * q) by
      rw [← sq, ← pow_add]; congr 1; omega]
  exact hk_max hfinal
