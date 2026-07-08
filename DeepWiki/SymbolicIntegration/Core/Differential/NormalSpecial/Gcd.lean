import DeepWiki.SymbolicIntegration.Core.Differential.GcdDeriv
import DeepWiki.SymbolicIntegration.Core.Differential.NormalSpecial.Core
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-! # GCD API for normal and special elements

GCD and multiplicity forms of normality and specialness in differential rings.
-/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

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

end DeepWiki.SymbolicIntegration
