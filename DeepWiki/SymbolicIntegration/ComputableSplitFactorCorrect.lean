import DeepWiki.SymbolicIntegration.ComputableGcdCorrect
import DeepWiki.SymbolicIntegration.CanonicalRepresentation

/-! # Abstract correctness of the fraction-free `splitFactor` over ℚ(x)[t] — Bronstein §3.5
The fraction-free splitting-factorization loop `cSplitFactorFast Dt fuel p` (`ComputableSplitFactorFast`)
runs Bronstein's `SplitFactor` over the tower ℚ(x)[t], with the fraction-free gcd `cgcdFF` for its two
gcds `gcd(p, Dp)` / `gcd(p, dp/dt)` and exact Euclidean division `cdivFF` for the special-factor ratio.
It is validated *pointwise* by `native_decide` (Example 3.5.1 in `ComputableSplitFactorFast`). This file
proves the **abstract** correctness — for inputs satisfying the (transparent) per-node degree
preconditions of `cgcdFF`, axiom-clean (no `native_decide`) — that the loop output `(pₙ, pₛ)`, read
through `toPolyG` over the field ℚ(x) = `RatFunc ℚ`, is a *book-faithful splitting factorization* of
`toPolyG p` w.r.t. the monomial derivation `D` (`Dt = toPolyG Dt`): `IsSplittingFactorizationGen`.

The spine is **route (B)**, a direct loop invariant mirroring `splitFactorAux_isSplittingFactorizationGen`
(`CanonicalRepresentation`), reusing the abstract step facts:

1. **`cdivFF` is the Euclidean quotient** (`toPolyG_cdivFF`): `cdivFF = cdivG`, so its `toPolyG` reading
   is the quotient of `toPolyG_cdivmodG'`. For an **exact** divisor (remainder zero), the identity
   becomes the exact factorization `toPolyG p = toPolyG (cdivFF p q) · toPolyG q`.

2. **The computable step `S` is associated to the abstract `splitFactorStep`** (`associated_toPolyG_cstep`):
   `cgcdFF p (cmonomialDeriv Dt p) ~ gcd(p, Dp)` and `cgcdFF p (cderivG p) ~ gcd(p, dp/dt)`
   (`associated_toPolyG_cgcdFF_of_nodeRegular` + the `cmonomialDeriv`/`cderivG` bridges); exact division
   cancels the (nonzero) denominator gcd, so `toPolyG S ~ splitFactorStep`.

3. **Assembly** (`cSplitFactorFast_isSplittingFactorizationGen`): by induction on fuel, each step's `S`
   divides `toPolyG p` exactly (the abstract step divides, transported through the association), the
   exact division keeps the invariant `toPolyG p = toPolyG S · toPolyG (p/S)`, and the abstract step
   facts (`isSpecial_splitFactorStep`, `splitFactorStep_dvd`,
   `isNormalSqfree_of_splitFactorStep_natDegree_zero`) — pushed across the association — give
   `IsSpecial`/`IsNormalSqfree`. The result is `IsSplittingFactorizationGen` over ℚ(x)[t]. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### Step 0 — the thin `cdivFF` wrapper
`cdivFF fuel p q = cdivG fuel p q` (`ComputableSplitFactorFast`, monomorphic to ℚ(x)[t] = `CPolyG
QFunNZ`), so its correctness is the generic Euclidean-division identity `toPolyG_cdivmodG'`. -/

/-- **`cdivFF` is the generic Euclidean quotient**: `toPolyG (cdivFF fuel p q)` is the quotient part of
`cdivmodG`, so the Euclidean identity `toPolyG p = toPolyG (cdivFF fuel p q) · toPolyG q + toPolyG
(cmodG fuel p q)` holds for a nonzero divisor (`cnormG q ≠ []`). The thin wrapper over
`toPolyG_cdivmodG'` (`cdivFF := cdivG`). -/
theorem toPolyG_cdivFF (fuel : ℕ) (p q : CPolyG QFunNZ) (hq0 : cnormG q ≠ []) :
    toPolyG p
      = toPolyG (CPolyG.cdivFF fuel p q) * toPolyG q + toPolyG (cmodG fuel p q) := by
  rw [CPolyG.cdivFF, cdivG, cmodG]
  exact toPolyG_cdivmodG' fuel p q hq0

/-! ### Exact division over a field — the remainder vanishes when the divisor divides
Over the field ℚ(x), the Euclidean identity plus the strict remainder-degree bound force the remainder to
zero whenever the divisor divides the dividend. Purely abstract over `(RatFunc ℚ)[X]`: `q ∣ p` and
`q ∣ quo·q` give `q ∣ rem`, and `deg rem < deg q` then forces `rem = 0`. -/

/-- **A remainder of degree `< deg q` divisible by `q` vanishes** (over a field): if `q ∣ r` and
`r.degree < q.degree` (`q ≠ 0`), then `r = 0`. The Euclidean-uniqueness core of exact division. -/
theorem eq_zero_of_dvd_of_degree_lt {K : Type*} [Field K] {q r : K[X]}
    (hdvd : q ∣ r) (hdeg : r.degree < q.degree) : r = 0 := by
  by_contra hr
  exact absurd hdeg (not_lt.mpr (Polynomial.degree_le_of_dvd hdvd hr))

/-- **Exact-division factorization through `cdivFF`** over ℚ(x): if the divisor `cgcdFF`-style `q`
divides `toPolyG p` (`hQdvd`) and is nonzero (`cnormG q ≠ []`) with fuel bounding the dividend length
(so `cmodG` is fully reduced), then `toPolyG p = toPolyG (cdivFF fuel p q) · toPolyG q` exactly — the
remainder vanishes. Combines `toPolyG_cdivFF` with `eq_zero_of_dvd_of_degree_lt`. -/
theorem toPolyG_cdivFF_exact (fuel : ℕ) (p q : CPolyG QFunNZ)
    (hq0 : cnormG q ≠ []) (hfuel : (cnormG p : List QFunNZ).length ≤ fuel)
    (hQdvd : toPolyG q ∣ toPolyG p) :
    toPolyG p = toPolyG (CPolyG.cdivFF fuel p q) * toPolyG q := by
  have hid := toPolyG_cdivFF fuel p q hq0
  -- the divisor is nonzero over the field
  have hqne : toPolyG q ≠ 0 := fun h => hq0 ((cnormG_eq_nil_iff q).mpr h)
  -- the remainder divides into `p`: `q ∣ p` and `q ∣ quo·q`, so `q ∣ rem`
  have hrdvd : toPolyG q ∣ toPolyG (cmodG fuel p q) := by
    have : toPolyG (cmodG fuel p q)
        = toPolyG p - toPolyG (CPolyG.cdivFF fuel p q) * toPolyG q := by
      rw [hid]; ring
    rw [this]
    exact dvd_sub hQdvd (Dvd.intro_left _ rfl)
  -- the remainder has degree `< deg q`
  have hrdeg : (toPolyG (cmodG fuel p q)).degree < (toPolyG q).degree := by
    have hlt := cmodG_length_lt fuel p q hq0 hfuel
    by_cases hr0 : cnormG (cmodG fuel p q) = []
    · rw [(cnormG_eq_nil_iff _).mp hr0, Polynomial.degree_zero]
      exact Ne.bot_lt' (fun h => hqne (Polynomial.degree_eq_bot.mp h.symm))
    · rw [Polynomial.degree_eq_natDegree (fun h => hr0 ((cnormG_eq_nil_iff _).mpr h)),
        Polynomial.degree_eq_natDegree hqne]
      have e1 := length_cnormG_of_ne (cmodG fuel p q) hr0
      have e2 := length_cnormG_of_ne q hq0
      exact_mod_cast by omega
  have hrem0 : toPolyG (cmodG fuel p q) = 0 :=
    eq_zero_of_dvd_of_degree_lt hrdvd hrdeg
  rw [hid, hrem0, add_zero]

/-! ### Step 1.5 — `gcd(p, dp/dt) ∣ gcd(p, Dp)` (the denominator gcd divides the numerator gcd)
The `SplitFactor` step `S = gcd(p, Dp)/gcd(p, dp/dt)` is an **exact** quotient: over a char-`0` field, the
`d/dt`-derivative gcd `gcd(p, dp/dt)` divides the monomial-derivation gcd `gcd(p, Dp)`. This is the
divisibility certificate that the cleared step-division is exact (and so its computable analogue's
remainder vanishes). Reconstructed from the char-`0` gcd formula
`associated_gcd_deriv_special_part` (numerator `~ defect·special`, denominator `~ defect`). -/

open UniqueFactorizationMonoid Classical in
/-- **The denominator gcd divides the numerator gcd** (char `0`): `gcd(p, dp/dt) ∣ gcd(p, Dp)` for the
monomial derivation `D = implicitDeriv v`. Both gcds carry the multiplicity defect `∏ π^{m−1}`; the
numerator additionally carries the special product `∏_{special} π`, while the `d/dt`-special filter is
empty in char `0`, so the denominator is exactly the defect — which divides the numerator. The
divisibility that makes the `SplitFactor` step quotient exact. -/
theorem gcd_derivative_dvd_gcd_implicitDeriv {K : Type*} [Field K] [CharZero K] [Differential K]
    (v : K[X]) {p : K[X]} (hp : p ≠ 0) :
    gcd p (derivative p) ∣ gcd p (Differential.implicitDeriv v p) := by
  have hunit := fun π (hπ : π ∈ primeFactors p) => isUnit_natCast_count_primeFactors hπ
  have hnum : Associated (gcd p (Differential.implicitDeriv v p))
      ((∏ π ∈ primeFactors p, π ^ ((normalizedFactors p).count π - 1))
        * ∏ π ∈ (primeFactors p).filter
            (fun π => @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ π), π) :=
    @associated_gcd_deriv_special_part K _ ⟨Differential.implicitDeriv v⟩ p hp hunit
  have hfilt : (primeFactors p).filter
      (fun π => @IsSpecial _ _ ⟨(Polynomial.derivative' (R := K)).restrictScalars ℤ⟩ π) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro π hπ
    exact not_isSpecial_derivative_of_irreducible
      (irreducible_of_normalized_factor π (mem_primeFactors.mp hπ))
  have hden : Associated (gcd p (derivative p))
      (∏ π ∈ primeFactors p, π ^ ((normalizedFactors p).count π - 1)) := by
    have h := @associated_gcd_deriv_special_part K _
      ⟨(Polynomial.derivative' (R := K)).restrictScalars ℤ⟩ p hp hunit
    rwa [hfilt, Finset.prod_empty, mul_one] at h
  refine hden.dvd.trans ?_
  exact (dvd_mul_right _ _).trans hnum.symm.dvd
