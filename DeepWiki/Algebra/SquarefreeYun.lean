import DeepWiki.Algebra.SquarefreeGcd

/-! # The Yun step invariant

The sum-free correctness core of Yun's squarefree decomposition. A Yun state `(c, d)` for a
ghost polynomial `g` is characterized by `c` squarefree covering the primes of `g` together
with the identity `d·g = c·g′`. The primewise fact `yun_prime_dvd_iff` — a prime of `c`
divides `d` exactly when it misses `g` — makes any gcd of `(c, d)` the multiplicity-one part
of the state, and `yun_step` shows the updated pair is again a Yun state for `g/(c/P)`.
No multi-factor derivative sums appear; everything reduces to single-prime multiplicity
analysis over the identity. -/

universe u

open Polynomial

/-- Two squarefree elements of a UFD with the same prime divisors are associated. -/
theorem associated_of_squarefree_of_prime_dvd_iff
    {α : Type u} [CommMonoidWithZero α] [UniqueFactorizationMonoid α] [NormalizationMonoid α]
    {s t : α} (hs : Squarefree s) (ht : Squarefree t) (hs0 : s ≠ 0) (ht0 : t ≠ 0)
    (H : ∀ q, Prime q → (q ∣ s ↔ q ∣ t)) : Associated s t :=
  associated_of_dvd_dvd
    (UniqueFactorizationMonoid.dvd_of_squarefree_of_forall_prime_dvd hs hs0 ht0
      fun q hq hqs => (H q hq).mp hqs)
    (UniqueFactorizationMonoid.dvd_of_squarefree_of_forall_prime_dvd ht ht0 hs0
      fun q hq hqt => (H q hq).mpr hqt)

namespace Polynomial

variable {K : Type u} [Field K] [CharZero K]

/-- A prime polynomial does not divide its own derivative (characteristic zero). -/
theorem prime_not_dvd_derivative {q : K[X]} (hq : Prime q) : ¬ q ∣ derivative q := by
  intro h
  have hqdeg : 0 < q.natDegree := natDegree_pos_of_irreducible' hq.irreducible
  have hq'0 : derivative q ≠ 0 := Polynomial.derivative_ne_zero.mpr (by omega)
  exact absurd (Polynomial.degree_le_of_dvd h hq'0)
    (not_le.mpr (Polynomial.degree_derivative_lt hq.ne_zero))

/-- A prime polynomial does not divide a nonzero constant natural cast. -/
theorem prime_not_dvd_C_natCast {q : K[X]} (hq : Prime q) {n : ℕ} (hn : n ≠ 0) :
    ¬ q ∣ C (n : K) := by
  intro h
  have hCn : (C (n : K) : K[X]) ≠ 0 := Polynomial.C_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)
  have hle := Polynomial.degree_le_of_dvd h hCn
  rw [Polynomial.degree_C (Nat.cast_ne_zero.mpr hn)] at hle
  have hdeg : 0 < q.degree := by
    have h1 := natDegree_pos_of_irreducible' hq.irreducible
    rwa [Polynomial.natDegree_pos_iff_degree_pos] at h1
  exact absurd hdeg (not_lt.mpr hle)

/-- **The Yun primewise fact**: for the state identity `d·g = c·g′` with `c` squarefree, a
prime divisor `q` of `c` divides `d` exactly when it does not divide `g` (characteristic
zero). -/
theorem yun_prime_dvd_iff {g c d q : K[X]} (hg : g ≠ 0) (hc : Squarefree c)
    (hq : Prime q) (hqc : q ∣ c) (hid : d * g = c * derivative g) :
    q ∣ d ↔ ¬ q ∣ g := by
  constructor
  · intro hqd hqg
    obtain ⟨k, hk1, hkd, hkmax⟩ := exists_max_pow_dvd hg hq.irreducible hqg
    obtain ⟨h, hgh⟩ := hkd
    have hqh : ¬ q ∣ h := fun hdvd =>
      hkmax (by rw [hgh, pow_succ]; exact mul_dvd_mul (dvd_refl _) hdvd)
    obtain ⟨w, hw⟩ := hqc
    have hqw : ¬ q ∣ w := fun hdvd =>
      hq.not_unit (hc q (by rw [hw]; exact mul_dvd_mul (dvd_refl q) hdvd))
    have hg' : derivative g = C (k : K) * q ^ (k - 1) * derivative q * h
        + q ^ k * derivative h := by
      rw [hgh, derivative_mul, derivative_pow]
    have hqk0 : (q : K[X]) ^ k ≠ 0 := pow_ne_zero _ hq.ne_zero
    have hkey : d * h = C (k : K) * w * derivative q * h + q * (w * derivative h) := by
      apply mul_left_cancel₀ hqk0
      have hpow : q * q ^ (k - 1) = q ^ k := by
        rw [← pow_succ', Nat.sub_add_cancel hk1]
      calc q ^ k * (d * h) = d * (q ^ k * h) := by ring
        _ = q * w * (C (k : K) * q ^ (k - 1) * derivative q * h + q ^ k * derivative h) := by
            rw [← hw, ← hg', ← hgh]; exact hid
        _ = C (k : K) * w * (q * q ^ (k - 1)) * derivative q * h
            + q ^ k * (q * (w * derivative h)) := by ring
        _ = q ^ k * (C (k : K) * w * derivative q * h + q * (w * derivative h)) := by
            rw [hpow]; ring
    have hq_dvd : q ∣ C (k : K) * w * derivative q * h := by
      have h0 : q ∣ d * h := hqd.mul_right h
      rw [hkey] at h0
      exact (dvd_add_left ⟨w * derivative h, rfl⟩).mp h0
    rcases hq.2.2 _ _ hq_dvd with h1 | h1
    · rcases hq.2.2 _ _ h1 with h2 | h2
      · rcases hq.2.2 _ _ h2 with h3 | h3
        · exact prime_not_dvd_C_natCast hq (by omega) h3
        · exact hqw h3
      · exact prime_not_dvd_derivative hq h2
    · exact hqh h1
  · intro hqg
    have h1 : q ∣ d * g := by rw [hid]; exact hqc.mul_right _
    rcases hq.2.2 _ _ h1 with h2 | h3
    · exact h2
    · exact absurd h3 hqg

/-- **The Yun step**: from a Yun state `(c, d)` for ghost `g` — `c` squarefree covering the
primes of `g`, with `d·g = c·g′` — and any gcd `P` of `(c, d)` (given by its universal
property), the quotient `c/P` divides `g` and `(c/P, d/P − (c/P)′)` is a Yun state for the
ghost `g/(c/P)`. -/
theorem yun_step [DecidableEq K] {g c d P : K[X]} (hg : g ≠ 0) (hc0 : c ≠ 0) (hc : Squarefree c)
    (hcov : ∀ q, Prime q → q ∣ g → q ∣ c)
    (hid : d * g = c * derivative g)
    (hPc : P ∣ c) (hPd : P ∣ d) (hPuniv : ∀ e, e ∣ c → e ∣ d → e ∣ P) :
    (c / P) ∣ g ∧
    (∀ q, Prime q → q ∣ g / (c / P) → q ∣ c / P) ∧
    (d / P - derivative (c / P)) * (g / (c / P)) = (c / P) * derivative (g / (c / P)) := by
  have hP0 : P ≠ 0 := fun h => hc0 (zero_dvd_iff.mp (h ▸ hPc))
  have hPc' : P * (c / P) = c := EuclideanDomain.mul_div_cancel' hP0 hPc
  have hPd' : P * (d / P) = d := EuclideanDomain.mul_div_cancel' hP0 hPd
  have hc20 : c / P ≠ 0 := fun h => hc0 (by rw [← hPc', h, mul_zero])
  have hc2c : (c / P) ∣ c := ⟨P, hPc'.symm.trans (mul_comm P (c / P))⟩
  have hc2sf : Squarefree (c / P) := hc.squarefree_of_dvd hc2c
  have hchar : ∀ q, Prime q → (q ∣ c / P ↔ q ∣ c ∧ q ∣ g) := by
    intro q hq
    constructor
    · intro hq2
      have hqc : q ∣ c := hq2.trans hc2c
      refine ⟨hqc, ?_⟩
      by_contra hqg
      have hqd : q ∣ d := (yun_prime_dvd_iff hg hc hq hqc hid).mpr hqg
      have hqP : q ∣ P := hPuniv q hqc hqd
      exact hq.not_unit (hc q (by rw [← hPc']; exact mul_dvd_mul hqP hq2))
    · rintro ⟨hqc, hqg⟩
      have hqd : ¬ q ∣ d := fun hqd =>
        (yun_prime_dvd_iff hg hc hq hqc hid).mp hqd hqg
      have hqP : ¬ q ∣ P := fun h => hqd (h.trans hPd)
      have h1 : q ∣ P * (c / P) := by rw [hPc']; exact hqc
      rcases hq.2.2 _ _ h1 with h | h
      · exact absurd h hqP
      · exact h
  have hdvd_g : (c / P) ∣ g :=
    UniqueFactorizationMonoid.dvd_of_squarefree_of_forall_prime_dvd hc2sf hc20 hg
      fun q hq hq2 => ((hchar q hq).mp hq2).2
  have hg2 : (c / P) * (g / (c / P)) = g := EuclideanDomain.mul_div_cancel' hc20 hdvd_g
  refine ⟨hdvd_g, ?_, ?_⟩
  · intro q hq hqg2
    have hqg : q ∣ g := hqg2.trans ⟨c / P, hg2.symm.trans (mul_comm (c / P) (g / (c / P)))⟩
    exact (hchar q hq).mpr ⟨hcov q hq hqg, hqg⟩
  · have h1 : (d / P) * g = (c / P) * derivative g := by
      apply mul_left_cancel₀ hP0
      calc P * ((d / P) * g) = d * g := by
            conv_rhs => rw [← hPd']
            ring
        _ = c * derivative g := hid
        _ = P * ((c / P) * derivative g) := by
            conv_lhs => rw [← hPc']
            ring
    have h2 : (d / P) * (g / (c / P)) = derivative g := by
      apply mul_left_cancel₀ hc20
      calc (c / P) * ((d / P) * (g / (c / P)))
          = (d / P) * ((c / P) * (g / (c / P))) := by ring
        _ = (d / P) * g := by rw [hg2]
        _ = (c / P) * derivative g := h1
    have h3 : derivative g
        = derivative (c / P) * (g / (c / P)) + (c / P) * derivative (g / (c / P)) := by
      conv_lhs => rw [← hg2]
      rw [derivative_mul]
    rw [sub_mul, h2, h3]
    ring

end Polynomial
