import DeepWiki.SymbolicIntegration.DifferentialFields
import DeepWiki.SymbolicIntegration.AlgebraicPreliminaries
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
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

variable [IsDomain R] [NormalizedGCDMonoid R] [WfDvdMonoid R] in
/-- **Theorem 3.4.1(iii)** (§3.4, p.93), key step: a prime factor `π` of a special polynomial `p`
is itself special. Write `p = πᵉ·h` with `π ∤ h` (`FiniteMultiplicity`); Lemma 3.4.4 gives
`gcd(p,Dp) ~ πᵉ⁻¹·gcd(π,Dπ)·gcd(h,Dh)`, and `p` special (`gcd(p,Dp) ~ p`) forces, after cancelling
`πᵉ⁻¹`, `π·h ~ gcd(π,Dπ)·gcd(h,Dh)`; as `π` is prime, `gcd(π,Dπ)` is a unit (impossible: it would
make `π` a unit) or `~ π`, i.e. `π ∣ Dπ`. Needs the exponent a unit (`IsUnit (eᵉ:R)`, char `0`). -/
theorem isSpecial_of_prime_dvd {p π : R} (hπ : Prime π) (hdvd : π ∣ p) (hp0 : p ≠ 0)
    (hp : IsSpecial p) (he : IsUnit ((multiplicity π p : R))) : IsSpecial π := by
  have hfin : FiniteMultiplicity π p := FiniteMultiplicity.of_prime_left hπ hp0
  obtain ⟨h, hph, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have he1 : 1 ≤ multiplicity π p := multiplicity_pos_of_dvd hdvd
  set e := multiplicity π p with hedef
  have hh0 : h ≠ 0 := by rintro rfl; rw [mul_zero] at hph; exact hp0 hph
  have hrp : IsRelPrime π h := by
    intro d hdπ hdh
    obtain ⟨k, hk⟩ := hdπ
    rcases hπ.irreducible.isUnit_or_isUnit hk with hu | hu
    · exact hu
    · exact absurd ((show π ∣ d by rw [hk]; exact (associated_mul_unit_right d k hu).symm.dvd).trans
        hdh) hnd
  have hcop : IsUnit (gcd (π ^ e) h) :=
    gcd_isUnit_iff_isRelPrime.mpr ((IsRelPrime.pow_left_iff he1).mpr hrp)
  have hps : Associated (gcd p p′) p := isSpecial_iff_associated_gcd.mp hp
  rw [hph] at hps
  have hchain : Associated (π ^ e * h) (π ^ (e - 1) * gcd π π′ * gcd h h′) :=
    (hps.symm.trans (associated_gcd_deriv_mul hcop)).trans
      ((associated_gcd_deriv_pow he1 he).mul_right (gcd h h′))
  have hpe : π ^ e = π ^ (e - 1) * π := by rw [← pow_succ, Nat.sub_add_cancel he1]
  rw [hpe, mul_assoc, mul_assoc] at hchain
  have hcancel : Associated (π * h) (gcd π π′ * gcd h h′) :=
    Associated.of_mul_left hchain (Associated.refl _) (pow_ne_zero _ hπ.ne_zero)
  obtain ⟨k, hk⟩ := gcd_dvd_left π π′
  rcases hπ.irreducible.isUnit_or_isUnit hk with hgu | hku
  · exfalso
    have h1 : Associated (π * h) (gcd h h′) :=
      hcancel.trans (associated_unit_mul_left (gcd h h′) (gcd π π′) hgu)
    obtain ⟨m, hm⟩ := h1.dvd.trans (gcd_dvd_left h h′)
    have e2 : h * 1 = h * (π * m) := by linear_combination hm
    exact hπ.not_unit (isUnit_of_dvd_one ⟨m, mul_left_cancel₀ hh0 e2⟩)
  · have hgπ : Associated (gcd π π′) π := by
      have hau := associated_mul_unit_right (gcd π π′) k hku
      rwa [← hk] at hau
    exact hgπ.symm.dvd.trans (gcd_dvd_right π π′)

variable [IsDomain R] [NormalizedGCDMonoid R] [UniqueFactorizationMonoid R] in
/-- **Theorem 3.4.1(iii)** (§3.4, p.93): any factor of a special polynomial is special. Factor
`q ∣ p` into primes (`induction_on_prime`); each prime factor divides `p` so is special
(`isSpecial_of_prime_dvd`), and specialness is closed under products (`IsSpecial.mul`) and units.
Needs every prime factor's multiplicity to be a unit (`IsUnit ((multiplicity:R))`, char `0`). -/
theorem isSpecial_of_dvd {p q : R} (hp0 : p ≠ 0) (hp : IsSpecial p)
    (hmult : ∀ π, Prime π → π ∣ p → IsUnit ((multiplicity π p : R))) (hdvd : q ∣ p) :
    IsSpecial q := by
  revert hdvd
  refine UniqueFactorizationMonoid.induction_on_prime q ?_ ?_ ?_
  · intro h; rw [zero_dvd_iff] at h; exact absurd h hp0
  · intro u hu _; exact (isUnit_iff_dvd_one.mp hu).trans (one_dvd _)
  · intro c π hc hπ ih hπc
    have hπp : π ∣ p := (dvd_mul_right π c).trans hπc
    have hcp : c ∣ p := (dvd_mul_left c π).trans hπc
    exact (isSpecial_of_prime_dvd hπ hπp hp0 hp (hmult π hπ hπp)).mul (ih hcp)

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

section LinearFactor
open Polynomial

/-- The monomial derivation of a linear factor: `D(X − a) = v − C(a′)` (with `Dt = v`). This is
how `D` reaches the root value, the crux of the root characterizations 3.4.2/3.4.3. -/
theorem implicitDeriv_X_sub_C {A : Type*} [CommRing A] [Differential A] (v : A[X]) (a : A) :
    Differential.implicitDeriv v (X - C a) = v - C a′ := by
  rw [map_sub, Differential.implicitDeriv_X, Differential.implicitDeriv_C]

/-- A linear factor is coprime to `g` iff its root is not a root of `g`: `(X − a) ⊥ g ↔ g(a) ≠ 0`
(over a field; `X − a` is prime, so coprime ↔ not-dvd ↔ not-a-root). -/
theorem isCoprime_X_sub_C_iff {K : Type*} [Field K] {a : K} {g : K[X]} :
    IsCoprime (X - C a) g ↔ g.eval a ≠ 0 := by
  rw [(prime_X_sub_C a).coprime_iff_not_dvd, dvd_iff_isRoot]; rfl

/-- **Theorem 3.4.2** (§3.4, p.93), single linear factor: `X − a` is normal w.r.t. the monomial
derivation `D` (`Dt = v`) iff `Dα ≠ Hₜ(α)` at its root, i.e. `v(a) ≠ a′`. -/
theorem isCoprime_X_sub_C_implicitDeriv_iff {K : Type*} [Field K] [Differential K] (v : K[X])
    (a : K) :
    IsCoprime (X - C a) (Differential.implicitDeriv v (X - C a)) ↔ v.eval a ≠ a′ := by
  rw [implicitDeriv_X_sub_C, isCoprime_X_sub_C_iff, eval_sub, eval_C, sub_ne_zero]

/-- **Theorem 3.4.3** (§3.4, p.93), single linear factor: `X − a` is special w.r.t. the monomial
derivation `D` (`Dt = v`) iff `Dα = Hₜ(α)` at its root, i.e. `v(a) = a′` — equivalently
`(X − a) ∣ D(X − a)`. -/
theorem dvd_X_sub_C_implicitDeriv_iff {K : Type*} [Field K] [Differential K] (v : K[X]) (a : K) :
    (X - C a) ∣ Differential.implicitDeriv v (X - C a) ↔ v.eval a = a′ := by
  rw [implicitDeriv_X_sub_C, dvd_iff_isRoot, IsRoot.def, eval_sub, eval_C, sub_eq_zero]

/-- **Theorem 3.4.2** (§3.4, p.93), full squarefree form: a squarefree polynomial — written as the
product `∏_{a∈s} (X − a)` of its distinct linear factors — is normal w.r.t. the monomial
derivation `D` (`Dt = v`) iff `Dα ≠ Hₜ(α)` at *every* root, i.e. `∀ a ∈ s, v(a) ≠ a′`. Forward:
each `X − a` divides the product so is normal (`IsNormal.of_dvd`); backward: the pairwise-coprime
normal factors multiply to a normal product (`IsNormal.prod`). -/
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

/-- **Theorem 3.4.3** (§3.4, p.93), full squarefree form: a squarefree polynomial `∏_{a∈s}(X − a)`
is special w.r.t. the monomial derivation `D` (`Dt = v`) iff `Dα = Hₜ(α)` at *every* root, i.e.
`∀ a ∈ s, v(a) = a′`. Backward: special is closed under products (`IsSpecial.prod`); forward: each
`X − a` is a coprime factor of the product, hence special (`IsSpecial.of_mul_coprime`). -/
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

open Classical in
/-- **§3.5** splitting factorization of a squarefree polynomial: `∏_{a∈s}(X − a)` factors as its
special part (roots with `v(a) = a′`) times its normal part (roots with `v(a) ≠ a′`), the first
special and the second normal w.r.t. the monomial derivation `D`. Immediate from Thms 3.4.2/3.4.3
applied to the two halves of the root partition. -/
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

end LinearFactor

end DeepWiki.SymbolicIntegration
