import DeepWiki.SymbolicIntegration.Compute.Hermite.MultifactorResidual
import DeepWiki.SymbolicIntegration.Compute.Hermite.ResidualCorrectness

/-! # Hermite residual numerator bridge
Compares the multifactor residual numerator with the quotient-rule residual numerator and transfers
the interference divisibility across the fold denominator.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### Bridging the two residual numerators: `R·gden² = resNum'`

The whole fold residual `A/D − g′` has two representations: the per-factor form `am R/am D`
(`total_fold_residual_over_D`, `R = C(1−n)·A + Σ residNumIncr`), and the quotient-rule form
`am resNum'/(am D·am gden²)` (`residual_numerator_ratFunc`, `g = gnum/gden`, `resNum' = A·gden² −
D·gprimeNum`). Equating them (both equal `A/D − g′`) pins `R·gden² = resNum'` as polynomials — the
consistency bridge linking the interference numerator `R` to the algorithm's computed residual numerator
`resNum'`, so the interference divisibility `W ∣ R` is equivalent to the algorithm's cleared-identity
divisibility on `resNum'`. -/

open scoped Differential in
/-- The per-factor residual numerator agrees with the quotient-rule one: if the fold `g = (gnum,
gden)` satisfies the per-factor identities (`hstep`), then `R·gden² = resNum'` in `ℚ[X]`, where `R =
C(1−n)·A + Σ residNumIncr` is the interference numerator and `resNum' = A·gden² − D·(gnum'·gden −
gnum·gden')` the quotient-rule residual numerator. Both equal the residual `A/D − g′` over their
denominators; cross-multiplying and `am`-injectivity pin the polynomial identity. -/
theorem residNum_eq_resNumPrime (fuel : ℕ) (A D gnum gden : CPoly ℚ) (factors : List (CPoly ℚ × ℕ))
    (hD : toPoly D ≠ 0) (hgden : toPoly gden ≠ 0)
    (hV : ∀ Vi ∈ factors, toPoly Vi.1 ≠ 0)
    (hg : toQFun ((glocList fuel A D factors).foldl qadd qzero) = toQFun (gnum, gden))
    (hstep : ∀ Vi ∈ factors, 2 ≤ Vi.2 →
      (toQFun (glocIncr fuel A D Vi))′
        = algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
          - algebraMap ℚ[X] (RatFunc ℚ) (residNumIncr fuel A D Vi)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)) :
    (Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ)) * toPoly A
        + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum)
        * (toPoly gden * toPoly gden)
      = toPoly A * (toPoly gden * toPoly gden)
        - toPoly D * (derivative (toPoly gnum) * toPoly gden - toPoly gnum * derivative (toPoly gden)) := by
  have hinj := RatFunc.algebraMap_injective (K := ℚ)
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  set R := Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ)) * toPoly A
    + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum with hRdef
  set resNum' := toPoly A * (toPoly gden * toPoly gden)
    - toPoly D * (derivative (toPoly gnum) * toPoly gden - toPoly gnum * derivative (toPoly gden))
    with hresNum'def
  have hd : am (toPoly D) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
  have hgd : am (toPoly gden) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hgden
  -- per-factor form: `A/D − g′ = am R/am D`.
  have hres1 := total_fold_residual_over_D fuel A D factors hD hV hstep
  rw [← hRdef, hg] at hres1
  -- quotient-rule form: `A/D − (gnum/gden)′ = am resNum'/(am D·(am gden·am gden))`.
  have hres2 := residual_numerator_ratFunc (toPoly A) (toPoly D) (toPoly gnum) (toPoly gden) hD hgden
  rw [← hresNum'def] at hres2
  -- `(toQFun (gnum,gden))′ = (gnum/gden)′`.
  have htoQ : toQFun (gnum, gden) = am (toPoly gnum) / am (toPoly gden) := rfl
  rw [htoQ] at hres1
  -- both equal `A/D − g′`, so `am R/am D = am resNum'/(am D·am gden²)`.
  have heq : am R / am (toPoly D)
      = am resNum' / (am (toPoly D) * (am (toPoly gden) * am (toPoly gden))) := by
    rw [← hres1, ← hres2]
  -- cross-multiply: `am R · (am gden·am gden) = am resNum'`.
  have hRgd : am R * (am (toPoly gden) * am (toPoly gden)) = am resNum' := by
    have hstep1 : am R / am (toPoly D) * (am (toPoly D) * (am (toPoly gden) * am (toPoly gden)))
        = am R * (am (toPoly gden) * am (toPoly gden)) := by
      field_simp
    rw [heq, div_mul_cancel₀ _ (mul_ne_zero hd (mul_ne_zero hgd hgd))] at hstep1
    exact hstep1.symm
  -- the goal `R·gden² = resNum'` is `am`-injective image of `hRgd`.
  apply hinj
  rw [map_mul, map_mul]
  exact hRgd

/-- `W ∣ R ↔ W·gden² ∣ resNum'`: with `R·gden² = resNum'` and `gden ≠ 0`, interference divisibility
is equivalent to the cleared residual-numerator divisibility. -/
theorem dvd_R_iff_dvd_resNumPrime {R resNum' gden W : ℚ[X]} (hgden : gden ≠ 0)
    (hRel : R * (gden * gden) = resNum') :
    W ∣ R ↔ W * (gden * gden) ∣ resNum' := by
  rw [← hRel]
  constructor
  · intro h; exact mul_dvd_mul h dvd_rfl
  · intro h
    have hg2 : gden * gden ≠ 0 := mul_ne_zero hgden hgden
    exact (mul_dvd_mul_iff_right hg2).mp h

end DeepWiki.SymbolicIntegration.Compute
