import DeepWiki.SymbolicIntegration.Engine.TranscendentalOverAlgebraic

/-! # Generic helpers for odd-degree radical examples

Odd-degree radicands are not squares in `ℚ(x)`, giving degree-two radical
irreducibility for the generic examples.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem DensePoly

/-! ### The generic irreducibility helper

The odd-`intDegree` parity obstruction shows any odd-`natDegree` polynomial radicand is not a square in
`ℚ(x)`; `X_pow_sub_C_irreducible_of_prime Nat.prime_two` then gives `Irreducible (X² − C(toK f))` for
any non-square radicand `f` — hence the `Fact`, hence `CFieldSpec`/`CFieldDomain` for the tower. -/

/-- `∀ b : RatFunc ℚ, b² ≠ algebraMap ℚ[X] (RatFunc ℚ) p` whenever `p.natDegree` is odd: a square `b²`
has even `intDegree = 2·intDegree b`, but `algebraMap p` has odd `intDegree = p.natDegree`. -/
theorem not_isSquare_algebraMap_of_odd_natDegree {p : ℚ[X]} (hodd : Odd p.natDegree) :
    ∀ b : RatFunc ℚ, b ^ 2 ≠ algebraMap (ℚ[X]) (RatFunc ℚ) p := by
  intro b hb
  obtain ⟨k, hk⟩ := hodd
  have hp_ne : p ≠ 0 := by rintro rfl; rw [natDegree_zero] at hk; omega
  have hrhs_ne : algebraMap (ℚ[X]) (RatFunc ℚ) p ≠ 0 := RatFunc.algebraMap_ne_zero hp_ne
  have hb_ne : b ≠ 0 := by rintro rfl; rw [zero_pow (by norm_num)] at hb; exact hrhs_ne hb.symm
  have hdeg : (b ^ 2).intDegree = (algebraMap (ℚ[X]) (RatFunc ℚ) p).intDegree := by rw [hb]
  rw [sq, RatFunc.intDegree_mul hb_ne hb_ne, RatFunc.intDegree_polynomial, hk] at hdeg
  omega

/-- For `f : DenseFrac ℚ` with `∀ b, b² ≠ toK f`, `Irreducible (X² − C(toK f))` over `ℚ(x)` — the
`X_pow_sub_C_irreducible_of_prime Nat.prime_two` instance abstracted over the radicand. -/
theorem irreducible_radDeg2_of_not_isSquare {f : DenseFrac ℚ}
    (h : ∀ b : RatFunc ℚ, b ^ 2 ≠ CFieldSpec.toK f) :
    Irreducible (X ^ 2 - C (CFieldSpec.toK f)) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two h

end DeepWiki.SymbolicIntegration
