import DeepWiki.Algebra.ListSums
import DeepWiki.Algebra.ListProducts
import DeepWiki.Algebra.PolynomialDivisibility
import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.Compute.Diophantine
import DeepWiki.SymbolicIntegration.Compute.HermiteInnerCorrectness
import DeepWiki.SymbolicIntegration.Compute.HermiteIncrementDenominator
import DeepWiki.SymbolicIntegration.Compute.HermiteInterferenceDivisibility
import DeepWiki.SymbolicIntegration.Compute.HermiteMultifactorIncrements
import DeepWiki.SymbolicIntegration.Compute.HermiteMultifactorResidual
import DeepWiki.SymbolicIntegration.Compute.HermitePower
import DeepWiki.SymbolicIntegration.Compute.HermiteQRegularity
import DeepWiki.SymbolicIntegration.Compute.HermiteResidualCorrectness
import DeepWiki.SymbolicIntegration.Compute.HermiteResidualBridge
import DeepWiki.SymbolicIntegration.Compute.LrtLogPart
import DeepWiki.SymbolicIntegration.Compute.RationalFunction
import DeepWiki.SymbolicIntegration.Compute.SquarefreeExact
import DeepWiki.SymbolicIntegration.Compute.SquarefreeYun
import DeepWiki.SymbolicIntegration.Core.Polynomial.RatFuncRegular
import DeepWiki.SymbolicIntegration.RationalFunctionDerivative
import DeepWiki.SymbolicIntegration.SquarefreeFactorization

/-! # Correctness of the computable Hermite reduction (`cdiophantine`/`hermiteInner`)
Proves the computable Hermite engine correct in `RatFunc ℚ` through the `toPoly : CPoly → ℚ[X]`
bridge: the Bézout solver `cdiophantine` realizes the abstract `diophantineSolveReduced`, the
`hermiteInner` loop and `hermiteReduce` wrapper reduce `A/D` to a residual over the squarefree
radical, and the multi-factor interference divisibility is discharged. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### Summary: the multi-factor interference invariant, fully closed

The multi-factor `hermiteReduce` `g`-fold correctness is now **fully proven** (no remaining
divisibility hypothesis). The chain:

* `foldl_cond_eq_foldl_glocList` — the conditional `g`-fold is a plain `qadd`-fold over the kept-factor
  increment list `glocList`.
* `glocIncr_residual` / `glocIncr_hstep` — each kept factor's increment reduces the *global* `T = A/D`,
  leaving `residᵢ = am Afinalᵢ/(am Uᵢ·am Vi)` (over the global `D`: `am (Afinalᵢ·Vi^{i−1})/am D`), from
  the per-factor Bézout side conditions and the reconciliation `am D = am Uᵢ·am Vi^{i}`.
* `total_fold_residual` / `total_fold_residual_over_D` — the whole fold residual `A/D − g′` is the
  **single** polynomial fraction `am R/am D` with `R = C(1−n)·A + Σᵢ residNumIncrᵢ` (`n = #kept`): the
  exact `(1−n)·T + Σ residᵢ` overcounting skeleton collapsed onto the common denominator `D`.
* `am_div_D_eq_div_Dstar` — `am R/am D` clears to `am (R/W)/am Dstar` **iff** `W ∣ R`.
* **The interference divisibility `W ∣ R`** (`W = ∏_{kept} Vk^{ik−1} = D/Dstar`) is **proven** by a
  per-factor `Vk`-adic order argument:
  - `IsQRegular Q` — a `RatFunc` with no pole at the prime `Q` (denominator coprime to `Q`); closed
    under `+`, negation, list-sum, and the `RatFunc` derivative (`IsQRegular.add/.neg/.deriv`,
    `isQRegular_list_sum`), with `dvd_num_of_isQRegular` reading `Q^e ∣ r` off `am r/am D` `Q`-regular +
    `Q^e ∣ D`.
  - `glocIncr_den_eq_pow` ⟹ `glocIncr_toQFun_isQRegular`: each `glocᵢ` has denominator a pure power of
    `Vi`, so `glocᵢ′` is pole-free at every *other* factor `Vk`.
  - `deriv_fold_sub_glocIncr_isQRegular`: `g′ − glocₖ′ = Σ_{i≠k} glocᵢ′` is therefore `Vk`-regular, and
    `dvd_residNum_factor` reads `Vk^{ik−1} ∣ R` from `am (R − residNumIncrₖ)/am D = glocₖ′ − g′` being
    `Vk`-regular (with `Vk^{ik} ∣ D`) plus `Vk^{ik−1} ∣ residNumIncrₖ`.
  - `prod_dvd_residNum`: the per-factor bounds `Vk^{ik−1} ∣ R` assemble over the pairwise-coprime kept
    powers (`list_prod_dvd_of_pairwise`) to the product `W = ∏ Vk^{ik−1} ∣ R`.
* `hermiteReduce_residual_correct_multifactor` — the wrapper conditional on `W ∣ R`;
  **`hermiteReduce_residual_correct_uncond'`** — the **fully unconditional** wrapper
  `am A/am D = (toQFun g)′ + am (R/W)/am Dstar`, discharging `W ∣ R` internally via `prod_dvd_residNum`.
* `residNum_eq_resNumPrime` + `dvd_R_iff_dvd_resNumPrime` — `R·gden² = resNum'`, so `W ∣ R ⟺
  W·gden² ∣ resNum'` (the algorithm's own cleared-identity cert), confirming consistency.

The earlier worry that this cancellation is "not implied by the per-factor specifications alone" is
resolved: the order argument needs no per-factor `Afinalᵢ` divisibility — it confines each `Vk`-pole to
factor `k`'s own residual identity (`glocₖ′`) via the `IsQRegular` localization of the *other* factors'
derivatives. The single-repeated-factor case (`n = 1`, `W = 1`) is `hermiteReduce_residual_correct_single`. -/

open scoped Differential in
-- Hermite reduction, multi-factor wrapper (Bronstein §2.2/§2.5): the computable `hermiteReduce`
-- `g`-fold integrates the rational part `g`, leaving a residual over the squarefree radical `Dstar` —
-- conditional ONLY on the single interference divisibility `W ∣ R` (`W = D/Dstar`,
-- `R = C(1−n)·A + Σ Afinalᵢ·Vi^{i−1}`), everything else (the over-`D` residual skeleton, the radical
-- clause `Dstar ∣ D`) proven.
example (fuel : ℕ) (A D Dstar W : CPoly) (factors : List (CPoly × ℕ))
    (hD : toPoly D ≠ 0) (hDstar : toPoly Dstar ≠ 0)
    (hV : ∀ Vi ∈ factors, toPoly Vi.1 ≠ 0)
    (hstep : ∀ Vi ∈ factors, 2 ≤ Vi.2 →
      (toQFun (glocIncr fuel A D Vi))′
        = algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
          - algebraMap ℚ[X] (RatFunc ℚ) (residNumIncr fuel A D Vi)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D))
    (hWdec : toPoly D = toPoly Dstar * toPoly W)
    (hWR : toPoly W ∣ Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ))
        * toPoly A
        + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun ((glocList fuel A D factors).foldl qadd qzero))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            ((Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ))
                * toPoly A
              + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum)
              / toPoly W)
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) :=
  hermiteReduce_residual_correct_multifactor fuel A D Dstar W factors hD hDstar hV hstep hWdec hWR

/-! ### The fully unconditional multi-factor `hermiteReduce` wrapper

With `W ∣ R` now *proven* (`prod_dvd_residNum`), the multi-factor wrapper
(`hermiteReduce_residual_correct_multifactor`) becomes fully unconditional. Taking the radical
decomposition `D = Dstar·W` with `W = ∏_{kept} Vk^{ik−1}` (the cofactor `D/Dstar`) and the per-factor
hypotheses (residual identities, pairwise coprimality, `Vk^{ik} ∣ D`), the `g`-fold residual identity
`am A/am D = (toQFun g)′ + am (R/W)/am Dstar` holds **with no remaining divisibility assumption** — the
integrand lives over the squarefree radical `Dstar`. This closes the multi-factor interference. -/

open scoped Differential in
/-- **Fully unconditional multi-factor `hermiteReduce` wrapper** in `RatFunc ℚ`: with `W =
∏_{kept} Vk^{ik−1}` the radical cofactor (`hWdec : am D = am Dstar · am W`), the per-factor residual
identities (`hstep`), pairwise-coprime kept factors (`hpw`), distinct kept factors (`hnd`), and
`Vk^{ik} ∣ D` for each kept factor (`hpow`), the `g`-fold residual is correct:
`am A/am D = (toQFun g)′ + am (R/W)/am Dstar` — **no `W ∣ R` hypothesis**, the interference divisibility
is discharged internally by `prod_dvd_residNum`. The residual integrand lives over the squarefree radical
`Dstar`. The unconditional multi-factor Hermite reduction (Bronstein §2.2/§2.5). -/
theorem hermiteReduce_residual_correct_uncond' (fuel : ℕ) (A D Dstar : CPoly)
    (factors : List (CPoly × ℕ))
    (W : ℚ[X]) (hWeq : W = ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map
        (fun Vi => toPoly Vi.1 ^ (Vi.2 - 1))).prod)
    (hD : toPoly D ≠ 0) (hDstar : toPoly Dstar ≠ 0)
    (hnd : (factors.filter (fun Vi => decide (2 ≤ Vi.2))).Nodup)
    (hV : ∀ Vi ∈ factors, toPoly Vi.1 ≠ 0)
    (hstep : ∀ Vi ∈ factors, 2 ≤ Vi.2 →
      (toQFun (glocIncr fuel A D Vi))′
        = algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
          - algebraMap ℚ[X] (RatFunc ℚ) (residNumIncr fuel A D Vi)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D))
    (hpw : (factors.filter (fun Vi => decide (2 ≤ Vi.2))).Pairwise
      (fun a b => IsRelPrime (toPoly a.1) (toPoly b.1)))
    (hpow : ∀ Vi ∈ factors.filter (fun Vi => decide (2 ≤ Vi.2)),
      toPoly Vi.1 ^ Vi.2 ∣ toPoly D)
    (hWdec : toPoly D = toPoly Dstar * W) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun ((glocList fuel A D factors).foldl qadd qzero))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            ((Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ))
                * toPoly A
              + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum)
              / W)
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  set R := Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ)) * toPoly A
    + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum with hR
  -- the whole-fold residual `am A/am D − g′ = am R/am D`.
  have hres := total_fold_residual_over_D fuel A D factors hD hV hstep
  rw [← hR] at hres
  -- the interference divisibility `W ∣ R`, now proven.
  have hWR : W ∣ R := by
    rw [hWeq]; exact prod_dvd_residNum fuel A D factors hnd hD hV hstep hpw hpow
  -- clear `am R/am D` to `am (R/W)/am Dstar`.
  have hclear := am_div_D_eq_div_Dstar (R := R) (D := toPoly D) (Dstar := toPoly Dstar)
    (W := W) hD hDstar hWdec hWR
  linear_combination hres + hclear

open scoped Differential in
-- Hermite reduction, multi-factor, UNCONDITIONAL (Bronstein §2.2/§2.5): the computable `hermiteReduce`
-- `g`-fold integrates the rational part `g`, leaving a residual `(R/W)/Dstar` over the **squarefree
-- radical** `Dstar` — with NO interference-divisibility hypothesis (`W ∣ R` discharged internally). The
-- per-factor data alone (residual identities, pairwise-coprime kept factors, `Vk^{ik} ∣ D`, the radical
-- decomposition `D = Dstar·W`, `W = ∏ Vk^{ik−1}`) suffices.
example (fuel : ℕ) (A D Dstar : CPoly) (factors : List (CPoly × ℕ))
    (W : ℚ[X]) (hWeq : W = ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map
        (fun Vi => toPoly Vi.1 ^ (Vi.2 - 1))).prod)
    (hD : toPoly D ≠ 0) (hDstar : toPoly Dstar ≠ 0)
    (hnd : (factors.filter (fun Vi => decide (2 ≤ Vi.2))).Nodup)
    (hV : ∀ Vi ∈ factors, toPoly Vi.1 ≠ 0)
    (hstep : ∀ Vi ∈ factors, 2 ≤ Vi.2 →
      (toQFun (glocIncr fuel A D Vi))′
        = algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
          - algebraMap ℚ[X] (RatFunc ℚ) (residNumIncr fuel A D Vi)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D))
    (hpw : (factors.filter (fun Vi => decide (2 ≤ Vi.2))).Pairwise
      (fun a b => IsRelPrime (toPoly a.1) (toPoly b.1)))
    (hpow : ∀ Vi ∈ factors.filter (fun Vi => decide (2 ≤ Vi.2)),
      toPoly Vi.1 ^ Vi.2 ∣ toPoly D)
    (hWdec : toPoly D = toPoly Dstar * W) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun ((glocList fuel A D factors).foldl qadd qzero))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            ((Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ))
                * toPoly A
              + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum)
              / W)
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) :=
  hermiteReduce_residual_correct_uncond' fuel A D Dstar factors W hWeq hD hDstar hnd hV hstep
    hpw hpow hWdec
