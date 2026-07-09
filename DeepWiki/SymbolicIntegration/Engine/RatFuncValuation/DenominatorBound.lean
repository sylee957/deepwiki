import DeepWiki.SymbolicIntegration.Engine.RatFuncValuation.Basic

/-! # Denominator bounds from `K(t)` valuations

Global denominator divisibility consequences of per-prime `ratFuncOrd` bounds. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ### The UFM recombination: per-prime no-pole bounds ⟹ `denom(x) ∣ q`

Per-prime valuation bounds `νₚ(y) ≥ −νₚ(q)` combine into the divisibility `denom(y) ∣ q` via
`UniqueFactorizationMonoid.dvd_iff_emultiplicity_le`. -/

/-- `denom(x) ∣ q` from per-prime multiplicity bounds: for `x ∈ K(t)`, `q ∈ K[X]` nonzero, if
`multiplicity p x.denom ≤ multiplicity p q` for every prime `p`, then `x.denom ∣ q`. -/
theorem ratFunc_denom_dvd_of_multiplicity_le {x : RatFunc K} {q : K[X]} (hq : q ≠ 0)
    (h : ∀ p : K[X], Prime p → multiplicity p x.denom ≤ multiplicity p q) :
    x.denom ∣ q := by
  rw [UniqueFactorizationMonoid.dvd_iff_emultiplicity_le (RatFunc.denom_ne_zero x)]
  intro p hp
  rw [(FiniteMultiplicity.of_prime_left hp (RatFunc.denom_ne_zero x)).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_prime_left hp hq).emultiplicity_eq_multiplicity]
  exact_mod_cast h p hp

/-- The valuation bound `−νₚ(x) ≤ νₚ(q)` reads as `multiplicity p x.denom ≤ multiplicity p q`: at a
prime `p`, `−ratFuncOrd p x ≤ multiplicity p q` forces `multiplicity p x.denom ≤ multiplicity p q`, using
coprimality of `num`/`denom`. -/
theorem multiplicity_denom_le_of_ratFuncOrd {x : RatFunc K} {q : K[X]} (p : K[X]) (hp : Prime p)
    (h : -ratFuncOrd p x ≤ (multiplicity p q : ℤ)) :
    multiplicity p x.denom ≤ multiplicity p q := by
  by_cases hpd : p ∣ x.denom
  · -- `p ∣ denom` ⟹ `p ∤ num` (coprime), so `multiplicity p num = 0` and `−νₚ(x) = multiplicity p denom`.
    have hpn : ¬ p ∣ x.num := fun hpnum =>
      hp.not_unit ((RatFunc.isCoprime_num_denom x).isUnit_of_dvd' hpnum hpd)
    have hnum0 : multiplicity p x.num = 0 := multiplicity_eq_zero.mpr hpn
    rw [ratFuncOrd, hnum0] at h
    push_cast at h ⊢
    omega
  · -- `p ∤ denom` ⟹ `multiplicity p denom = 0 ≤ multiplicity p q`.
    rw [multiplicity_eq_zero.mpr hpd]; exact Nat.zero_le _

/-- The global no-pole-bound implies denominator divisibility: for `x ∈ K(t)`, `q ∈ K[X]` nonzero, if
every prime `p` satisfies `νₚ(x) ≥ −νₚ(q)`, then `x.denom ∣ q`. Combines
`multiplicity_denom_le_of_ratFuncOrd` with `ratFunc_denom_dvd_of_multiplicity_le`. -/
theorem ratFunc_denom_dvd_of_ratFuncOrd_bound {x : RatFunc K} {q : K[X]} (hq : q ≠ 0)
    (h : ∀ p : K[X], Prime p → -(multiplicity p q : ℤ) ≤ ratFuncOrd p x) :
    x.denom ∣ q :=
  ratFunc_denom_dvd_of_multiplicity_le hq fun p hp =>
    multiplicity_denom_le_of_ratFuncOrd p hp (by have := h p hp; omega)

end DeepWiki.SymbolicIntegration
