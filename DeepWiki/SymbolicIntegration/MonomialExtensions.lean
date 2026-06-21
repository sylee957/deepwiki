import DeepWiki.SymbolicIntegration.DifferentialFields
import DeepWiki.SymbolicIntegration.AlgebraicPreliminaries
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

/-- If `p · q` is normal then `q` is normal (the right factor; by commutativity). -/
theorem IsNormal.of_mul_right {p q : R} (h : IsNormal (p * q)) : IsNormal q :=
  IsNormal.of_mul_left (mul_comm p q ▸ h)

/-- **Theorem 3.4.1(i)** (§3.4, p.93), second half: any factor of a normal polynomial is normal. -/
theorem IsNormal.of_dvd {p q : R} (h : IsNormal p) (hq : q ∣ p) : IsNormal q := by
  obtain ⟨r, rfl⟩ := hq
  exact h.of_mul_left

/-- **§3.4 consequence** (p.93): a normal polynomial is squarefree — if `x·x ∣ p` then `x` divides
both `p` and `Dp` (`Dp = x·(…)` by Leibniz), so coprimality of `p, Dp` forces `x` to be a unit.
Holds for *any* derivation (no field or characteristic hypothesis). -/
theorem IsNormal.squarefree {p : R} (hp : IsNormal p) : Squarefree p := by
  intro x hx
  obtain ⟨r, hr⟩ := hx
  have hxp : x ∣ p := ⟨x * r, by rw [hr]; ring⟩
  have hxp' : x ∣ p′ := by
    rw [hr]
    have e : ((x * x) * r)′ = x * (x * r′ + r * x′ + r * x′) := by
      rw [deriv_mul_eq (x * x) r, deriv_mul_eq x x]; ring
    rw [e]; exact dvd_mul_right x _
  exact IsCoprime.isUnit_of_dvd' hp hxp hxp'

variable [GCDMonoid R] in
/-- **Definition 3.4.2** (§3.4, p.92), gcd form: `p` is special iff `gcd(p, Dp) ~ p`
(the `gcd(p, Dp) = p` of the book, up to the unit ambiguity of `gcd`). -/
theorem isSpecial_iff_associated_gcd {p : R} : IsSpecial p ↔ Associated (gcd p p′) p :=
  ⟨fun h => associated_of_dvd_dvd (gcd_dvd_left p p′) (dvd_gcd dvd_rfl h),
   fun h => h.symm.dvd.trans (gcd_dvd_right p p′)⟩

variable [GCDMonoid R] in
/-- **Definition 3.4.2** (§3.4, p.92), gcd form: a normal `p` has `gcd(p, Dp)` a unit
(the book's `gcd(p, Dp) = 1`). -/
theorem IsNormal.isUnit_gcd {p : R} (h : IsNormal p) : IsUnit (gcd p p′) :=
  gcd_isUnit_iff_isRelPrime.mpr h.isRelPrime

variable [NormalizedGCDMonoid R] in
/-- **Lemma 3.4.4** (§3.4, p.94), two-factor base case: for coprime `a, b` (unit `gcd a b`),
`gcd(a·b, D(a·b)) ~ gcd(a, Da)·gcd(b, Db)`. Expand `D(a·b) = a·Db + b·Da`, split the gcd over
the coprime factors (`associated_gcd_mul_of_isUnit_gcd`), drop the absorbed multiples
(`associated_gcd_add_mul`), and cancel the coprime cofactor (`associated_gcd_mul_left_cancel`). -/
theorem associated_gcd_deriv_mul {a b : R} (hab : IsUnit (gcd a b)) :
    Associated (gcd (a * b) ((a * b)′)) (gcd a a′ * gcd b b′) := by
  have hba : IsUnit (gcd b a) := by rwa [gcd_comm]
  rw [deriv_mul_eq]
  refine (associated_gcd_mul_of_isUnit_gcd hab _).trans (Associated.mul_mul ?_ ?_)
  · rw [add_comm (a * b′) (b * a′)]
    exact (associated_gcd_add_mul a (b * a′) b′).trans (associated_gcd_mul_left_cancel hab)
  · exact (associated_gcd_add_mul b (a * b′) a′).trans (associated_gcd_mul_left_cancel hba)

variable [NormalizedGCDMonoid R] in
/-- **Lemma 3.4.4** (§3.4, p.94), the single-power computation: when the exponent `n ≥ 1` is a
unit (characteristic `0`), `gcd(pⁿ, D(pⁿ)) ~ pⁿ⁻¹·gcd(p, Dp)`. Uses `D(pⁿ) = n·pⁿ⁻¹·Dp`
(`leibniz_pow`), factors out `pⁿ⁻¹`, and cancels the unit `n`. -/
theorem associated_gcd_deriv_pow {p : R} {n : ℕ} (hn : 1 ≤ n) (he : IsUnit (n : R)) :
    Associated (gcd (p ^ n) ((p ^ n)′)) (p ^ (n - 1) * gcd p p′) := by
  have hd : (p ^ n)′ = (n : R) * (p ^ (n - 1) * p′) := by
    rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
  have hpe : p ^ n = p ^ (n - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [hd, hpe, show (n : R) * (p ^ (n - 1) * p′) = p ^ (n - 1) * ((n : R) * p′) from by ring]
  refine (gcd_mul_left' (p ^ (n - 1)) p ((n : R) * p′)).trans ?_
  exact Associated.mul_left _
    (associated_gcd_mul_left_cancel (isUnit_of_dvd_unit (gcd_dvd_right p (n : R)) he))

variable [NormalizedGCDMonoid R] in
/-- **Lemma 3.4.4** (§3.4, p.94), pairwise-coprime product form: for a finite family of
pairwise-coprime factors `f i`, `gcd(∏ f i, D ∏ f i) ~ ∏ gcd(f i, D f i)`. Finset induction on the
two-factor base case `associated_gcd_deriv_mul`, using that a factor stays coprime to the rest of
the product (`isUnit_gcd_prod`). -/
theorem associated_gcd_deriv_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → R) :
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsUnit (gcd (f i) (f j))) →
    Associated (gcd (∏ i ∈ s, f i) ((∏ i ∈ s, f i)′)) (∏ i ∈ s, gcd (f i) (f i)′) := by
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.prod_empty]
    exact associated_one_iff_isUnit.mpr (isUnit_of_dvd_one (gcd_dvd_left (1 : R) _))
  | insert a s ha ih =>
    intro hco
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hu : IsUnit (gcd (f a) (∏ i ∈ s, f i)) := by
      apply isUnit_gcd_prod
      intro i hi
      exact hco a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (by rintro rfl; exact ha hi)
    refine (associated_gcd_deriv_mul hu).trans (Associated.mul_left _ (ih ?_))
    intro i hi j hj hij
    exact hco i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij

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

/-- **Theorem 3.4.1** (§3.4, p.93): a polynomial that is both normal and special is a unit
(`(p) = (1)`) — the only normal *and* special polynomials are the units of `k`. -/
theorem isUnit_of_isNormal_of_isSpecial {p : R} (hn : IsNormal p) (hs : IsSpecial p) :
    IsUnit p := by
  obtain ⟨w, hw⟩ := hs
  obtain ⟨u, v, huv⟩ := hn
  rw [hw] at huv
  have h : p * (u + v * w) = 1 := by linear_combination huv
  exact isUnit_of_dvd_one ⟨u + v * w, h.symm⟩

/-- A unit is normal (`gcd(p, p′) = 1` since `p` is coprime to everything). -/
theorem isNormal_of_isUnit {p : R} (hu : IsUnit p) : IsNormal p := by
  obtain ⟨u, rfl⟩ := hu
  exact ⟨↑u⁻¹, 0, by simp⟩

/-- **Theorem 3.4.1** (§3.4, p.93): `p` is both normal and special iff it is a unit. -/
theorem isNormal_and_isSpecial_iff_isUnit {p : R} :
    (IsNormal p ∧ IsSpecial p) ↔ IsUnit p :=
  ⟨fun ⟨hn, hs⟩ => isUnit_of_isNormal_of_isSpecial hn hs,
   fun hu => ⟨isNormal_of_isUnit hu, hu.dvd⟩⟩

/-- Specialness is invariant under multiplication by a unit: `IsSpecial (u·p) ↔ IsSpecial p`
(so it depends only on `p` up to associates — used to normalize by the leading coefficient). -/
theorem IsSpecial.unit_mul_iff {u : R} (hu : IsUnit u) (p : R) :
    IsSpecial (u * p) ↔ IsSpecial p := by
  unfold IsSpecial
  rw [deriv_mul_eq, hu.mul_left_dvd, add_comm, dvd_add_right (dvd_mul_right p u′),
    hu.dvd_mul_left]

/-- Normality is invariant under multiplication by a unit: `IsNormal (u·p) ↔ IsNormal p`
(so it depends only on `p` up to associates — used to normalize by the leading coefficient). -/
theorem IsNormal.unit_mul_iff {u : R} (hu : IsUnit u) (p : R) :
    IsNormal (u * p) ↔ IsNormal p := by
  unfold IsNormal
  rw [deriv_mul_eq, isCoprime_mul_unit_left_left hu, IsCoprime.add_mul_left_right_iff,
    isCoprime_mul_unit_left_right hu]

/-- Specialness is an associate invariant: `Associated p q → IsSpecial p → IsSpecial q`. -/
theorem IsSpecial.of_associated {p q : R} (h : Associated p q) (hp : IsSpecial p) :
    IsSpecial q := by
  obtain ⟨u, rfl⟩ := h
  rw [mul_comm]
  exact (IsSpecial.unit_mul_iff u.isUnit p).mpr hp

/-- Normality is an associate invariant: `Associated p q → IsNormal p → IsNormal q`. -/
theorem IsNormal.of_associated {p q : R} (h : Associated p q) (hp : IsNormal p) :
    IsNormal q := by
  obtain ⟨u, rfl⟩ := h
  rw [mul_comm]
  exact (IsNormal.unit_mul_iff u.isUnit p).mpr hp

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

open Polynomial in
/-- **Lemma 3.4.2(i)** (§3.4, p.91), the *nonlinear* equality case: over a characteristic-`0`
field, when the `D`-degree `δ(t) = deg v ≥ 2` and `deg p ≥ 1`, the bound is sharp —
`deg(D p) = deg p + δ(t) − 1`. (The `v·p′` term has degree `deg v + deg p − 1 > deg p`, so it
strictly dominates `κ_D(p)` and sets the degree.) -/
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

end DeepWiki.SymbolicIntegration
