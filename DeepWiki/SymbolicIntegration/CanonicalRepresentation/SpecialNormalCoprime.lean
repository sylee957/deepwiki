import DeepWiki.SymbolicIntegration.CanonicalRepresentation.NormalSqfree

/-! # Special ⊥ normal-squarefree coprimality

The special part `pₛ` and the normal(-squarefree) part `pₙ` of a differential splitting factorization are
coprime, in characteristic zero. This is the fact that `IsSplittingFactorizationGen` (`pₛ` special, `pₙ`
normal-squarefree) does *not* bundle but which the canonical Bézout split needs — it was a hypothesis
throughout. Proof: a shared prime `π` would be both special (prime factor of a special polynomial is
special, via multiplicity extraction + the differential power rule `deriv_pow`) and normal (`IsNormal π`
from `IsNormalSqfree pₙ`), forcing `π ∣ π′` and `IsCoprime π π′`, i.e. `π` a unit — impossible. -/

open Polynomial
open scoped Differential

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K] [CharZero K] [Differential (K[X])]

/-- A prime factor of a special polynomial is itself special (`π ∣ π′`), in characteristic zero. -/
theorem isSpecial_of_prime_dvd_isSpecial {ps π : K[X]} (hps0 : ps ≠ 0) (hπ : Prime π)
    (hπps : π ∣ ps) (hps : IsSpecial ps) : IsSpecial π := by
  -- factor `ps = π^k · c` with `π ∤ c`, `k = multiplicity π ps ≥ 1`
  obtain ⟨c, hpsc, hπc⟩ := (FiniteMultiplicity.of_prime_left hπ hps0).exists_eq_pow_mul_and_not_dvd
  set k := multiplicity π ps with hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by rw [hk]; exact multiplicity_ne_zero.mpr hπps)
  -- `IsSpecial (π^k)` from `IsSpecial ps` and `IsCoprime (π^k) c`
  have hcop : IsCoprime (π ^ k) c := ((hπ.coprime_iff_not_dvd.mpr hπc).pow_left)
  have hspk : IsSpecial (π ^ k) := by
    rw [hpsc] at hps; exact hps.of_mul_coprime hcop
  -- `π^k ∣ (π^k)′ = k·π^(k-1)·π′`
  have hdvd : π ^ k ∣ (k : K[X]) * π ^ (k - 1) * π′ := by rw [← deriv_pow]; exact hspk
  -- rearrange RHS and cancel `π^(k-1)`, using `π^k = π^(k-1)·π`
  have hkpow : π ^ k = π ^ (k - 1) * π := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
  have hne : π ^ (k - 1) ≠ 0 := pow_ne_zero _ hπ.ne_zero
  have heq : (k : K[X]) * π ^ (k - 1) * π′ = π ^ (k - 1) * ((k : K[X]) * π′) := by ring
  have hdvd' : π ^ (k - 1) * π ∣ π ^ (k - 1) * ((k : K[X]) * π′) := by
    rw [← hkpow, ← heq]; exact hdvd
  have hπu : π ∣ (k : K[X]) * π′ := (mul_dvd_mul_iff_left hne).mp hdvd'
  -- `(k : K[X])` is a unit (char zero, `k ≥ 1`), so `π ∣ π′`
  have hku : IsUnit ((k : K[X])) := by
    have hkne : ((k : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hk1
    rw [show ((k : K[X])) = C ((k : K)) from (map_natCast (C : K →+* K[X]) k).symm]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr hkne)
  exact (hku.dvd_mul_left).mp hπu

/-- **Special ⊥ normal-squarefree.** A special `pₛ` and a normal-squarefree `pₙ` are coprime (char zero). -/
theorem isCoprime_of_isSpecial_isNormalSqfree {ps pn : K[X]} (hps0 : ps ≠ 0)
    (hps : IsSpecial ps) (hpn : IsNormalSqfree pn) : IsCoprime ps pn := by
  apply IsRelPrime.isCoprime
  intro d hdps hdpn
  by_contra hdu
  have hd0 : d ≠ 0 := fun h => hps0 (zero_dvd_iff.mp (h ▸ hdps))
  obtain ⟨π, hπirr, hπd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd0
  have hπ : Prime π := hπirr.prime
  have hπps : π ∣ ps := hπd.trans hdps
  have hπpn : π ∣ pn := hπd.trans hdpn
  have hπnormal : IsNormal π := hpn π hπirr.squarefree hπpn
  have hπspecial : IsSpecial π := isSpecial_of_prime_dvd_isSpecial hps0 hπ hπps hps
  -- `π ∣ π′` and `IsCoprime π π′` ⇒ `π` a unit, contradicting primality
  obtain ⟨a, b, hab⟩ := hπnormal
  have : π ∣ (1 : K[X]) := hab ▸ dvd_add (Dvd.intro_left a rfl) (hπspecial.mul_left b)
  exact hπ.not_unit (isUnit_of_dvd_one this)

end DeepWiki.SymbolicIntegration
