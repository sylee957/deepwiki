import DeepWiki.SymbolicIntegration.Core.Differential.GcdDeriv
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-! # Core normal and special elements in differential rings
Defines normal and special elements with respect to a derivation and proves their
generic gcd and product API. -/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

/-- `p` is *normal*: coprime to its derivative `p'` (`gcd(p, p') = 1`). -/
def IsNormal {R : Type*} [CommRing R] [Differential R] (p : R) : Prop := IsCoprime p p′

/-- `p` is *special* (w.r.t. `D`) if `p ∣ p'` (so `gcd(p, p') = p`). -/
def IsSpecial {R : Type*} [CommRing R] [Differential R] (p : R) : Prop := p ∣ p′

/-- A special polynomial spans a differential ideal: `p ∣ p' → IsDifferentialIdeal (span {p})`. -/
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

/-- If `p * q` is normal then `p` is normal. -/
theorem IsNormal.of_mul_left {R : Type*} [CommRing R] [Differential R] {p q : R}
    (h : IsNormal (p * q)) : IsNormal p := by
  have h0 : IsCoprime (p * q) ((p * q)′) := h
  have h1 : IsCoprime p ((p * q)′) := h0.of_mul_left_left
  rw [deriv_mul_eq] at h1
  have h2 : IsCoprime p (q * p′) := by
    have := h1.add_mul_left_right (-q′)
    rwa [show (p * q′ + q * p′) + p * -q′ = q * p′ from by ring] at this
  exact h2.of_mul_right_right

/-- If `p * q` is normal then `q` is normal. -/
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

/-- gcd form of special: `IsSpecial p ↔ Associated (gcd p p') p`. -/
theorem isSpecial_iff_associated_gcd {R : Type*} [CommRing R] [Differential R] [GCDMonoid R]
    {p : R} : IsSpecial p ↔ Associated (gcd p p′) p :=
  ⟨fun h => associated_of_dvd_dvd (gcd_dvd_left p p′) (dvd_gcd dvd_rfl h),
   fun h => h.symm.dvd.trans (gcd_dvd_right p p′)⟩

/-- gcd form of normal: a normal `p` has `gcd(p, p')` a unit. -/
theorem IsNormal.isUnit_gcd {R : Type*} [CommRing R] [Differential R] [GCDMonoid R] {p : R}
    (h : IsNormal p) : IsUnit (gcd p p′) :=
  gcd_isUnit_iff_isRelPrime.mpr h.isRelPrime

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

/-- If `p * q` is special and `p, q` are coprime, then `p` is special. -/
theorem IsSpecial.of_mul_coprime {R : Type*} [CommRing R] [Differential R] {p q : R}
    (h : IsSpecial (p * q)) (hco : IsCoprime p q) : IsSpecial p := by
  have h0 : (p * q) ∣ ((p * q)′) := h
  rw [deriv_mul_eq] at h0
  have hp1 : p ∣ (p * q′ + q * p′) := (dvd_mul_right p q).trans h0
  have hp2 : p ∣ q * p′ := (dvd_add_right (dvd_mul_right p q′)).mp hp1
  exact hco.dvd_of_dvd_mul_left hp2

end DeepWiki.SymbolicIntegration
