import DeepWiki.SymbolicIntegration.DifferentialFields
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.Derivative

/-! # Monomial extensions — normal and special polynomials (Bronstein §3.4)
A *monomial* `t` over a differential field `k` is a transcendental element with `Dt ∈ k[t]`, so
`k[t]` is closed under `D`. Mathlib's `Differential.implicitDeriv v = mapCoeffs + v • d/dX` is
exactly this derivation on `k[X]` with `Dt = v` (`implicitDeriv_X`/`implicitDeriv_C`). A
polynomial is *normal* if it is coprime to its derivative and *special* if it divides its
derivative; special polynomials cut out differential ideals. We work over a general differential
ring (these are derivation/divisibility facts), the monomial case being `R = k[t]`. -/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R] [Differential R]

/-- **Definition 3.4.2** (§3.4): `p` is *normal* (w.r.t. `D`) if `gcd(p, Dp) = 1`, i.e. `p` and
its derivative `p′` are coprime. -/
def IsNormal (p : R) : Prop := IsCoprime p p′

/-- **Definition 3.4.2** (§3.4): `p` is *special* (w.r.t. `D`) if `p ∣ Dp` (so `gcd(p, Dp) = p`). -/
def IsSpecial (p : R) : Prop := p ∣ p′

/-- The derivative of `a` is `Const`-linear over a special divisor: `(p·b)′ = p·b′ + b·p′`. -/
theorem deriv_mul_eq (p b : R) : (p * b)′ = p * b′ + b * p′ := by
  simp only [Derivation.leibniz, smul_eq_mul]

/-- **Lemma 3.4.3** (§3.4, p.92): a special polynomial generates a *differential ideal* — if
`p ∣ Dp` then `(p)` is closed under `D`. -/
theorem IsSpecial.isDifferentialIdeal {p : R} (hp : IsSpecial p) :
    IsDifferentialIdeal (Ideal.span {p}) := by
  intro a ha
  rw [Ideal.mem_span_singleton] at ha ⊢
  obtain ⟨b, rfl⟩ := ha
  rw [deriv_mul_eq]
  exact dvd_add (dvd_mul_right p b′) (hp.mul_left b)

/-- **Theorem 3.4.1(ii)** (§3.4, p.93): the special polynomials are closed under multiplication
(`S` is a multiplicative monoid). -/
theorem IsSpecial.mul {p q : R} (hp : IsSpecial p) (hq : IsSpecial q) : IsSpecial (p * q) := by
  obtain ⟨s, hs⟩ := hp
  obtain ⟨u, hu⟩ := hq
  refine ⟨u + s, ?_⟩
  rw [deriv_mul_eq, hs, hu]
  ring

/-- `1` is special (the unit of the monoid `S`). -/
theorem isSpecial_one : IsSpecial (1 : R) := by
  simp [IsSpecial]

/-- **Theorem 3.4.1(ii)** (§3.4, p.93), finite form: a finite product of special polynomials is
special. -/
theorem IsSpecial.prod {ι : Type*} (s : Finset ι) (f : ι → R) (hf : ∀ i ∈ s, IsSpecial (f i)) :
    IsSpecial (∏ i ∈ s, f i) :=
  Finset.prod_induction f IsSpecial (fun _ _ ha hb => ha.mul hb) isSpecial_one hf

/-- `1` is normal (`gcd(1, 0) = 1`). -/
theorem isNormal_one : IsNormal (1 : R) := by
  have h : ((1 : R)′) = 0 := (Differential.deriv : Derivation ℤ R R).map_one_eq_zero
  rw [IsNormal, h]
  exact isCoprime_one_left

/-- **Theorem 3.4.1(i)** (§3.4, p.93): the product of two *coprime normal* polynomials is normal
(`gcd(pq, D(pq)) = 1` when `p, q` are normal and coprime). -/
theorem IsNormal.mul {p q : R} (hp : IsNormal p) (hq : IsNormal q) (hpq : IsCoprime p q) :
    IsNormal (p * q) := by
  show IsCoprime (p * q) ((p * q)′)
  rw [deriv_mul_eq]
  refine IsCoprime.mul_left ?_ ?_
  · rw [add_comm]; exact (hpq.mul_right hp).add_mul_left_right q′
  · exact (hpq.symm.mul_right hq).add_mul_left_right p′

/-- **Theorem 3.4.1(i)** (§3.4, p.93), finite form: a finite product of pairwise-coprime normal
polynomials is normal. -/
theorem IsNormal.prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, IsNormal (f i))
    (hco : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (f i) (f j)) :
    IsNormal (∏ i ∈ s, f i) := by
  induction s using Finset.induction with
  | empty => simpa using isNormal_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hfa : IsNormal (f a) := hf a (Finset.mem_insert_self a s)
    have hcoa : IsCoprime (f a) (∏ i ∈ s, f i) :=
      IsCoprime.prod_right fun i hi => hco a (Finset.mem_insert_self a s) i
        (Finset.mem_insert_of_mem hi) (by rintro rfl; exact ha hi)
    refine hfa.mul (ih ?_ ?_) hcoa
    · exact fun i hi => hf i (Finset.mem_insert_of_mem hi)
    · exact fun i hi j hj hij => hco i (Finset.mem_insert_of_mem hi) j
        (Finset.mem_insert_of_mem hj) hij

/-- If `p · q` is normal then `p` is normal (coprimality with the derivative descends). -/
theorem IsNormal.of_mul_left {p q : R} (h : IsNormal (p * q)) : IsNormal p := by
  have h0 : IsCoprime (p * q) ((p * q)′) := h
  have h1 : IsCoprime p ((p * q)′) := h0.of_mul_left_left
  rw [deriv_mul_eq] at h1
  have h2 : IsCoprime p (q * p′) := by
    have := h1.add_mul_left_right (-q′)
    rwa [show (p * q′ + q * p′) + p * -q′ = q * p′ from by ring] at this
  exact h2.of_mul_right_right

/-- **Theorem 3.4.1(i)** (§3.4, p.93), second half: any factor of a normal polynomial is normal. -/
theorem IsNormal.of_dvd {p q : R} (h : IsNormal p) (hq : q ∣ p) : IsNormal q := by
  obtain ⟨r, rfl⟩ := hq
  exact h.of_mul_left

/-- **Theorem 3.4.1(iii)** (§3.4, p.93), coprime case: if `p·q` is special and `p, q` are
coprime, then `p` is special. (Unlike the normal case, the coprimality is needed: `p ∣ q·p′`
gives `p ∣ p′` only when `p ⊥ q`.) -/
theorem IsSpecial.of_mul_coprime {p q : R} (h : IsSpecial (p * q)) (hco : IsCoprime p q) :
    IsSpecial p := by
  have h0 : (p * q) ∣ ((p * q)′) := h
  rw [deriv_mul_eq] at h0
  have hp1 : p ∣ (p * q′ + q * p′) := (dvd_mul_right p q).trans h0
  have hp2 : p ∣ q * p′ := (dvd_add_right (dvd_mul_right p q′)).mp hp1
  exact hco.dvd_of_dvd_mul_left hp2

/-- **Definition 3.5.1** (§3.5): a *splitting factorization* of `p` is `p = pₛ · pₙ` with `pₛ`
special and `pₙ` normal. (By Theorem 3.4.1 — factors of a normal polynomial are normal —
requiring `pₙ` normal is equivalent to the book's "every squarefree factor of `pₙ` is normal".) -/
def IsSplittingFactorization (p ps pn : R) : Prop :=
  p = ps * pn ∧ IsSpecial ps ∧ IsNormal pn

/-- A special polynomial splits as `(p, 1)`. -/
theorem IsSpecial.splittingFactorization {p : R} (hp : IsSpecial p) :
    IsSplittingFactorization p p 1 :=
  ⟨(mul_one p).symm, hp, isNormal_one⟩

/-- A normal polynomial splits as `(1, p)`. -/
theorem IsNormal.splittingFactorization {p : R} (hp : IsNormal p) :
    IsSplittingFactorization p 1 p :=
  ⟨(one_mul p).symm, isSpecial_one, hp⟩

open Polynomial in
/-- **Lemma 3.4.2(i)** (§3.4, p.91): the monomial-derivation degree bound. For the derivation
`D = κ_D + v·d/dX` on `k[X]` with `Dt = v` (so the `D`-degree is `δ(t) = deg v`),
`deg(D p) ≤ deg p + max(0, δ(t) − 1)`. -/
theorem natDegree_implicitDeriv_le (v p : R[X]) :
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

end DeepWiki.SymbolicIntegration
