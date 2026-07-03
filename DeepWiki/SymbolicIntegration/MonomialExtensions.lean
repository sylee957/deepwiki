import DeepWiki.SymbolicIntegration.DifferentialFields
import DeepWiki.SymbolicIntegration.AlgebraicPreliminaries
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Algebra.Polynomial.Derivative

/-! # Monomial extensions — normal and special polynomials
`IsNormal p` means `p` is coprime to its derivative, `IsSpecial p` means `p` divides it.
Developed over a general differential ring, with the monomial derivation `implicitDeriv v` on
`k[X]` (`X′ = v`) as the leading case. -/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

/-- `p` is *normal*: coprime to its derivative `p′` (`gcd(p, p′) = 1`). -/
def IsNormal {R : Type*} [CommRing R] [Differential R] (p : R) : Prop := IsCoprime p p′

/-- `p` is *special* (w.r.t. `D`) if `p ∣ p′` (so `gcd(p, p′) = p`). -/
def IsSpecial {R : Type*} [CommRing R] [Differential R] (p : R) : Prop := p ∣ p′

/-- Leibniz product rule: `(p·b)′ = p·b′ + b·p′`. -/
theorem deriv_mul_eq {R : Type*} [CommRing R] [Differential R] (p b : R) :
    (p * b)′ = p * b′ + b * p′ := by
  simp only [Derivation.leibniz, smul_eq_mul]

/-- A special polynomial spans a differential ideal: `p ∣ p′ → IsDifferentialIdeal (span {p})`. -/
theorem IsSpecial.isDifferentialIdeal {R : Type*} [CommRing R] [Differential R] {p : R}
    (hp : IsSpecial p) : IsDifferentialIdeal (Ideal.span {p}) := by
  intro a ha
  rw [Ideal.mem_span_singleton] at ha ⊢
  obtain ⟨b, rfl⟩ := ha
  rw [deriv_mul_eq]
  exact dvd_add (dvd_mul_right p b′) (hp.mul_left b)

/-- Special polynomials are closed under multiplication. -/
theorem IsSpecial.mul {R : Type*} [CommRing R] [Differential R] {p q : R}
    (hp : IsSpecial p) (hq : IsSpecial q) : IsSpecial (p * q) := by
  obtain ⟨s, hs⟩ := hp
  obtain ⟨u, hu⟩ := hq
  refine ⟨u + s, ?_⟩
  rw [deriv_mul_eq, hs, hu]
  ring

/-- `1` is special. -/
theorem isSpecial_one {R : Type*} [CommRing R] [Differential R] : IsSpecial (1 : R) := by
  simp [IsSpecial]

/-- A finite product of special polynomials is special. -/
theorem IsSpecial.prod {R : Type*} [CommRing R] [Differential R] {ι : Type*} (s : Finset ι)
    (f : ι → R) (hf : ∀ i ∈ s, IsSpecial (f i)) : IsSpecial (∏ i ∈ s, f i) :=
  Finset.prod_induction f IsSpecial (fun _ _ ha hb => ha.mul hb) isSpecial_one hf

/-- `1` is normal. -/
theorem isNormal_one {R : Type*} [CommRing R] [Differential R] : IsNormal (1 : R) := by
  have h : ((1 : R)′) = 0 := (Differential.deriv : Derivation ℤ R R).map_one_eq_zero
  rw [IsNormal, h]
  exact isCoprime_one_left

/-- The product of two coprime normal polynomials is normal. -/
theorem IsNormal.mul {R : Type*} [CommRing R] [Differential R] {p q : R}
    (hp : IsNormal p) (hq : IsNormal q) (hpq : IsCoprime p q) : IsNormal (p * q) := by
  show IsCoprime (p * q) ((p * q)′)
  rw [deriv_mul_eq]
  refine IsCoprime.mul_left ?_ ?_
  · rw [add_comm]; exact (hpq.mul_right hp).add_mul_left_right q′
  · exact (hpq.symm.mul_right hq).add_mul_left_right p′

/-- A finite product of pairwise-coprime normal polynomials is normal. -/
theorem IsNormal.prod {R : Type*} [CommRing R] [Differential R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → R)
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

/-- If `p · q` is normal then `p` is normal. -/
theorem IsNormal.of_mul_left {R : Type*} [CommRing R] [Differential R] {p q : R}
    (h : IsNormal (p * q)) : IsNormal p := by
  have h0 : IsCoprime (p * q) ((p * q)′) := h
  have h1 : IsCoprime p ((p * q)′) := h0.of_mul_left_left
  rw [deriv_mul_eq] at h1
  have h2 : IsCoprime p (q * p′) := by
    have := h1.add_mul_left_right (-q′)
    rwa [show (p * q′ + q * p′) + p * -q′ = q * p′ from by ring] at this
  exact h2.of_mul_right_right

/-- If `p · q` is normal then `q` is normal. -/
theorem IsNormal.of_mul_right {R : Type*} [CommRing R] [Differential R] {p q : R}
    (h : IsNormal (p * q)) : IsNormal q :=
  IsNormal.of_mul_left (mul_comm p q ▸ h)

/-- Any factor of a normal polynomial is normal. -/
theorem IsNormal.of_dvd {R : Type*} [CommRing R] [Differential R] {p q : R}
    (h : IsNormal p) (hq : q ∣ p) : IsNormal q := by
  obtain ⟨r, rfl⟩ := hq
  exact h.of_mul_left

/-- A normal polynomial is squarefree (for any derivation). -/
theorem IsNormal.squarefree {R : Type*} [CommRing R] [Differential R] {p : R}
    (hp : IsNormal p) : Squarefree p := by
  intro x hx
  obtain ⟨r, hr⟩ := hx
  have hxp : x ∣ p := ⟨x * r, by rw [hr]; ring⟩
  have hxp' : x ∣ p′ := by
    rw [hr]
    have e : ((x * x) * r)′ = x * (x * r′ + r * x′ + r * x′) := by
      rw [deriv_mul_eq (x * x) r, deriv_mul_eq x x]; ring
    rw [e]; exact dvd_mul_right x _
  exact IsCoprime.isUnit_of_dvd' hp hxp hxp'

/-- gcd form of special: `IsSpecial p ↔ Associated (gcd p p′) p`. -/
theorem isSpecial_iff_associated_gcd {R : Type*} [CommRing R] [Differential R] [GCDMonoid R]
    {p : R} : IsSpecial p ↔ Associated (gcd p p′) p :=
  ⟨fun h => associated_of_dvd_dvd (gcd_dvd_left p p′) (dvd_gcd dvd_rfl h),
   fun h => h.symm.dvd.trans (gcd_dvd_right p p′)⟩

/-- gcd form of normal: a normal `p` has `gcd(p, p′)` a unit. -/
theorem IsNormal.isUnit_gcd {R : Type*} [CommRing R] [Differential R] [GCDMonoid R] {p : R}
    (h : IsNormal p) : IsUnit (gcd p p′) :=
  gcd_isUnit_iff_isRelPrime.mpr h.isRelPrime

/-- gcd of a derivative, two-factor case: for coprime `a, b`,
`gcd(a·b, (a·b)′) ~ gcd(a, a′)·gcd(b, b′)`. -/
theorem associated_gcd_deriv_mul {R : Type*} [CommRing R] [Differential R] [NormalizedGCDMonoid R]
    {a b : R} (hab : IsUnit (gcd a b)) :
    Associated (gcd (a * b) ((a * b)′)) (gcd a a′ * gcd b b′) := by
  have hba : IsUnit (gcd b a) := by rwa [gcd_comm]
  rw [deriv_mul_eq]
  refine (associated_gcd_mul_of_isUnit_gcd hab _).trans (Associated.mul_mul ?_ ?_)
  · rw [add_comm (a * b′) (b * a′)]
    exact (associated_gcd_add_mul a (b * a′) b′).trans (associated_gcd_mul_left_cancel hab)
  · exact (associated_gcd_add_mul b (a * b′) a′).trans (associated_gcd_mul_left_cancel hba)

/-- gcd of a derivative, prime-power case: for `n ≥ 1` a unit,
`gcd(pⁿ, (pⁿ)′) ~ pⁿ⁻¹·gcd(p, p′)`. -/
theorem associated_gcd_deriv_pow {R : Type*} [CommRing R] [Differential R] [NormalizedGCDMonoid R]
    {p : R} {n : ℕ} (hn : 1 ≤ n) (he : IsUnit (n : R)) :
    Associated (gcd (p ^ n) ((p ^ n)′)) (p ^ (n - 1) * gcd p p′) := by
  have hd : (p ^ n)′ = (n : R) * (p ^ (n - 1) * p′) := by
    rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
  have hpe : p ^ n = p ^ (n - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [hd, hpe, show (n : R) * (p ^ (n - 1) * p′) = p ^ (n - 1) * ((n : R) * p′) from by ring]
  refine (gcd_mul_left' (p ^ (n - 1)) p ((n : R) * p′)).trans ?_
  exact Associated.mul_left _
    (associated_gcd_mul_left_cancel (isUnit_of_dvd_unit (gcd_dvd_right p (n : R)) he))

/-- gcd of a derivative, pairwise-coprime product: `gcd(∏ f i, (∏ f i)′) ~ ∏ gcd(f i, (f i)′)`. -/
theorem associated_gcd_deriv_prod {R : Type*} [CommRing R] [Differential R] [NormalizedGCDMonoid R]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → R) :
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

/-- A prime factor `π` of a special polynomial `p` is itself special (multiplicity a unit). -/
theorem isSpecial_of_prime_dvd {R : Type*} [CommRing R] [Differential R] [IsDomain R]
    [NormalizedGCDMonoid R] [WfDvdMonoid R] {p π : R} (hπ : Prime π) (hdvd : π ∣ p) (hp0 : p ≠ 0)
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

/-- Any factor of a special polynomial is special (every prime factor's multiplicity a unit). -/
theorem isSpecial_of_dvd {R : Type*} [CommRing R] [Differential R] [IsDomain R]
    [NormalizedGCDMonoid R] [UniqueFactorizationMonoid R] {p q : R} (hp0 : p ≠ 0) (hp : IsSpecial p)
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

/-- If `p·q` is special and `p, q` are coprime, then `p` is special. -/
theorem IsSpecial.of_mul_coprime {R : Type*} [CommRing R] [Differential R] {p q : R}
    (h : IsSpecial (p * q)) (hco : IsCoprime p q) : IsSpecial p := by
  have h0 : (p * q) ∣ ((p * q)′) := h
  rw [deriv_mul_eq] at h0
  have hp1 : p ∣ (p * q′ + q * p′) := (dvd_mul_right p q).trans h0
  have hp2 : p ∣ q * p′ := (dvd_add_right (dvd_mul_right p q′)).mp hp1
  exact hco.dvd_of_dvd_mul_left hp2

/-- A polynomial that is both normal and special is a unit. -/
theorem isUnit_of_isNormal_of_isSpecial {R : Type*} [CommRing R] [Differential R] {p : R}
    (hn : IsNormal p) (hs : IsSpecial p) : IsUnit p := by
  obtain ⟨w, hw⟩ := hs
  obtain ⟨u, v, huv⟩ := hn
  rw [hw] at huv
  have h : p * (u + v * w) = 1 := by linear_combination huv
  exact isUnit_of_dvd_one ⟨u + v * w, h.symm⟩

/-- A unit is normal. -/
theorem isNormal_of_isUnit {R : Type*} [CommRing R] [Differential R] {p : R} (hu : IsUnit p) :
    IsNormal p := by
  obtain ⟨u, rfl⟩ := hu
  exact ⟨↑u⁻¹, 0, by simp⟩

/-- `p` is both normal and special iff it is a unit. -/
theorem isNormal_and_isSpecial_iff_isUnit {R : Type*} [CommRing R] [Differential R] {p : R} :
    (IsNormal p ∧ IsSpecial p) ↔ IsUnit p :=
  ⟨fun ⟨hn, hs⟩ => isUnit_of_isNormal_of_isSpecial hn hs,
   fun hu => ⟨isNormal_of_isUnit hu, hu.dvd⟩⟩

/-- Specialness is unit-invariant: `IsSpecial (u·p) ↔ IsSpecial p`. -/
theorem IsSpecial.unit_mul_iff {R : Type*} [CommRing R] [Differential R] {u : R} (hu : IsUnit u)
    (p : R) : IsSpecial (u * p) ↔ IsSpecial p := by
  unfold IsSpecial
  rw [deriv_mul_eq, hu.mul_left_dvd, add_comm, dvd_add_right (dvd_mul_right p u′),
    hu.dvd_mul_left]

/-- Normality is unit-invariant: `IsNormal (u·p) ↔ IsNormal p`. -/
theorem IsNormal.unit_mul_iff {R : Type*} [CommRing R] [Differential R] {u : R} (hu : IsUnit u)
    (p : R) : IsNormal (u * p) ↔ IsNormal p := by
  unfold IsNormal
  rw [deriv_mul_eq, isCoprime_mul_unit_left_left hu, IsCoprime.add_mul_left_right_iff,
    isCoprime_mul_unit_left_right hu]

/-- Specialness is an associate invariant: `Associated p q → IsSpecial p → IsSpecial q`. -/
theorem IsSpecial.of_associated {R : Type*} [CommRing R] [Differential R] {p q : R}
    (h : Associated p q) (hp : IsSpecial p) : IsSpecial q := by
  obtain ⟨u, rfl⟩ := h
  rw [mul_comm]
  exact (IsSpecial.unit_mul_iff u.isUnit p).mpr hp

/-- Normality is an associate invariant: `Associated p q → IsNormal p → IsNormal q`. -/
theorem IsNormal.of_associated {R : Type*} [CommRing R] [Differential R] {p q : R}
    (h : Associated p q) (hp : IsNormal p) : IsNormal q := by
  obtain ⟨u, rfl⟩ := h
  rw [mul_comm]
  exact (IsNormal.unit_mul_iff u.isUnit p).mpr hp

/-- A *splitting factorization* of `p` is `p = pₛ · pₙ` with `pₛ` special and `pₙ` normal. -/
def IsSplittingFactorization {R : Type*} [CommRing R] [Differential R] (p ps pn : R) : Prop :=
  p = ps * pn ∧ IsSpecial ps ∧ IsNormal pn

/-- A special polynomial splits as `(p, 1)`. -/
theorem IsSpecial.splittingFactorization {R : Type*} [CommRing R] [Differential R] {p : R}
    (hp : IsSpecial p) : IsSplittingFactorization p p 1 :=
  ⟨(mul_one p).symm, hp, isNormal_one⟩

/-- A normal polynomial splits as `(1, p)`. -/
theorem IsNormal.splittingFactorization {R : Type*} [CommRing R] [Differential R] {p : R}
    (hp : IsNormal p) : IsSplittingFactorization p 1 p :=
  ⟨(one_mul p).symm, isSpecial_one, hp⟩

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
