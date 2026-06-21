import DeepWiki.SymbolicIntegration.DifferentialFields
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Coprime.Lemmas

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

end DeepWiki.SymbolicIntegration
