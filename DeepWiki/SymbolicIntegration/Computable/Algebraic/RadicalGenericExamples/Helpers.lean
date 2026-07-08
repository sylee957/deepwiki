import DeepWiki.SymbolicIntegration.Computable.TranscendentalOverAlgebraic

/-! # Generic helpers for odd-degree radical examples

Odd-degree radicands are not squares in `ℚ(x)`, giving degree-two radical
irreducibility for the generic examples.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

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

/-- For `f : QFunNZG ℚ` with `∀ b, b² ≠ toK f`, `Irreducible (X² − C(toK f))` over `ℚ(x)` — the
`X_pow_sub_C_irreducible_of_prime Nat.prime_two` instance abstracted over the radicand. -/
theorem irreducible_radDeg2_of_not_isSquare {f : QFunNZG ℚ}
    (h : ∀ b : RatFunc ℚ, b ^ 2 ≠ CFieldSpec.toK f) :
    Irreducible (X ^ 2 - C (CFieldSpec.toK f)) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two h

/-! ### Reading a `qxOfNum` radicand into `ℚ(x)` and its `natDegree`

`CFieldSpec.toK (qxOfNum num) = algebraMap ℚ[X] (RatFunc ℚ) (toPolyG num)` (generic in `num`), plus a
per-radicand `natDegree` computation. -/

/-- `toK (qxOfNum num) = algebraMap ℚ[X] (RatFunc ℚ) (toPolyG num)`: a denominator-`1` ℚ(x)-value reads
through the tower bridge as the algebra-map image of its numerator (denominator `toPolyG [1] = 1`). -/
theorem toK_qxOfNum (num : CPolyG ℚ) :
    CFieldSpec.toK (qxOfNum num : QFunNZG ℚ) = algebraMap (ℚ[X]) (RatFunc ℚ) (toPolyG num) := by
  show QFunNZG.toQFunNZG (qxOfNum num) = _
  rw [QFunNZG.toQFunNZG]
  show QFunNZG.amG ℚ (toPolyG num) / QFunNZG.amG ℚ (toPolyG ([CField.one] : CPolyG ℚ)) = _
  have h2 : toPolyG ([CField.one] : CPolyG ℚ) = 1 := by
    show C (CFieldSpec.toK (CField.one : ℚ)) + X * 0 = 1; simp [CFieldSpec.toK_one]
  rw [h2, map_one, div_one]
  rfl

end DeepWiki.SymbolicIntegration
