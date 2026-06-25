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

/-! ### Step 2 — the computable step `S` is associated to the abstract `splitFactorStep`
The loop's special-factor candidate is `S = cdivFF (cgcdFF p (cmonomialDeriv Dt p)) (cgcdFF p
(cderivG p))`. Each `cgcdFF` is associated to the corresponding abstract gcd
(`associated_toPolyG_cgcdFF_of_nodeRegular`, with the `cmonomialDeriv`/`cderivG` bridges identifying the
second arguments as `Dp = implicitDeriv v p` and `dp/dt = derivative p`). Since the denominator gcd
divides the numerator gcd (`gcd_derivative_dvd_gcd_implicitDeriv`), exact division cancels it, and
`toPolyG S ~ splitFactorStep v (toPolyG p)`. -/

/-- **Per-`cgcdFF`-call node-regularity bundle** `CgcdFFNodeReg fuel p q`: the three transparent
preconditions of `associated_toPolyG_cgcdFF_of_nodeRegular` on the `bdeg`-ordered cleared pair — fuel
exceeds the divisor `t`-degree, divisor `t`-degree ≤ dividend `t`-degree, and the per-node degree bounds
`PrimPRSNodeRegular` (`deg_x < 30`, `deg_t ≤ 60`). Bundled to keep step/loop signatures readable. -/
def CgcdFFNodeReg (fuel : ℕ) (p q : CPolyG QFunNZ) : Prop :=
  (bnorm (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
      then CPolyG.clearDenoms p else CPolyG.clearDenoms q)).length ≤ fuel ∧
  (bnorm (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
      then CPolyG.clearDenoms p else CPolyG.clearDenoms q)).length
    ≤ (bnorm (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
      then CPolyG.clearDenoms q else CPolyG.clearDenoms p)).length ∧
  PrimPRSNodeRegular fuel
    (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
      then CPolyG.clearDenoms q else CPolyG.clearDenoms p)
    (if Compute.bdeg (CPolyG.clearDenoms p) < Compute.bdeg (CPolyG.clearDenoms q)
      then CPolyG.clearDenoms p else CPolyG.clearDenoms q)

/-- `cgcdFF` is associated to the abstract gcd, from a `CgcdFFNodeReg` bundle — the wrapper of
`associated_toPolyG_cgcdFF_of_nodeRegular` with its three hypotheses bundled. -/
theorem associated_toPolyG_cgcdFF_node (fuel : ℕ) (p q : CPolyG QFunNZ)
    (hreg : CgcdFFNodeReg fuel p q) :
    Associated (toPolyG (CPolyG.cgcdFF fuel p q)) (gcd (toPolyG p) (toPolyG q)) :=
  associated_toPolyG_cgcdFF_of_nodeRegular fuel p q hreg.1 hreg.2.1 hreg.2.2

/-- **The computable `SplitFactor` step** `cstep Dt fuel p = cdivFF (cgcdFF p (cmonomialDeriv Dt p))
(cgcdFF p (cderivG p))` — the special-factor candidate `S = gcd(p, Dp)/gcd(p, dp/dt)` computed with the
fraction-free gcd and exact Euclidean division (the inner `S` of `cSplitFactorFast`). -/
def cstep (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ) : CPolyG QFunNZ :=
  CPolyG.cdivFF fuel (CPolyG.cgcdFF fuel p (cmonomialDeriv Dt p))
    (CPolyG.cgcdFF fuel p (cderivG p))

/-- **Per-step regularity bundle** `CStepRegular Dt fuel p`: the transparent preconditions for the
computable step `cstep Dt fuel p` to match the abstract `splitFactorStep` — node-regularity of both
`cgcdFF` calls (numerator `gcd(p, Dp)`, denominator `gcd(p, dp/dt)`) and a fuel bound on the numerator
gcd's length so the exact Euclidean division `cdivFF` is fully reduced. -/
def CStepRegular (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ) : Prop :=
  CgcdFFNodeReg fuel p (cmonomialDeriv Dt p) ∧
  CgcdFFNodeReg fuel p (cderivG p) ∧
  (cnormG (CPolyG.cgcdFF fuel p (cmonomialDeriv Dt p)) : List QFunNZ).length ≤ fuel

/-- **Step 2 — the computable step is associated to the abstract `splitFactorStep`**: for `toPolyG p ≠ 0`
and a regular step (`CStepRegular`), `toPolyG (cstep Dt fuel p)` is `Associated` to
`splitFactorStep (toPolyG Dt) (toPolyG p)` in `(RatFunc ℚ)[X]`. The two `cgcdFF` calls land the
numerator/denominator gcds up to associates; exact division cancels the (nonzero) denominator gcd, which
divides the numerator gcd (`gcd_derivative_dvd_gcd_implicitDeriv`). -/
theorem associated_toPolyG_cstep (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ)
    (hp : toPolyG p ≠ 0) (hreg : CStepRegular Dt fuel p) :
    Associated (toPolyG (cstep Dt fuel p))
      (splitFactorStep (toPolyG Dt) (toPolyG p)) := by
  haveI : CharZero (CFieldSpec.K QFunNZ) := inferInstanceAs (CharZero (RatFunc ℚ))
  obtain ⟨hregN, hregD, hfuelN⟩ := hreg
  set v := toPolyG Dt with hv
  set P := toPolyG p with hP
  set N := CPolyG.cgcdFF fuel p (cmonomialDeriv Dt p) with hN
  set Dn := CPolyG.cgcdFF fuel p (cderivG p) with hDn
  -- the two gcd associations, with the second arguments identified by the bridges
  have aN : Associated (toPolyG N) (gcd P (Differential.implicitDeriv v P)) := by
    have h := associated_toPolyG_cgcdFF_node fuel p (cmonomialDeriv Dt p) hregN
    rwa [toPolyG_cmonomialDeriv, ← hP, ← hv] at h
  have aD : Associated (toPolyG Dn) (gcd P (derivative P)) := by
    have h := associated_toPolyG_cgcdFF_node fuel p (cderivG p) hregD
    rwa [toPolyG_cderivG, ← hP] at h
  -- the abstract gcds, the divisibility, and the exact factorization of the numerator gcd
  set gN := gcd P (Differential.implicitDeriv v P) with hgN
  set gD := gcd P (derivative P) with hgD
  have hgDdvd : gD ∣ gN := gcd_derivative_dvd_gcd_implicitDeriv v hp
  have hgDne : gD ≠ 0 := fun h => hp (eq_zero_of_zero_dvd (h ▸ gcd_dvd_left _ _))
  have hstepmul : splitFactorStep v P * gD = gN := by
    rw [splitFactorStep, ← hgN, ← hgD, mul_comm, EuclideanDomain.mul_div_cancel' hgDne hgDdvd]
  -- the denominator gcd divides the numerator gcd in the computable readings
  have hDn0 : toPolyG Dn ≠ 0 := fun h => hgDne (aD.eq_zero_iff.mp h)
  have hDncn : cnormG Dn ≠ [] := fun h => hDn0 ((cnormG_eq_nil_iff Dn).mp h)
  have hDnNdvd : toPolyG Dn ∣ toPolyG N :=
    (aD.dvd.trans hgDdvd).trans aN.symm.dvd
  -- exact division: toPolyG N = toPolyG (cstep …) · toPolyG Dn
  have hexact : toPolyG N = toPolyG (cstep Dt fuel p) * toPolyG Dn := by
    have := toPolyG_cdivFF_exact fuel N Dn hDncn hfuelN hDnNdvd
    rwa [show cstep Dt fuel p = CPolyG.cdivFF fuel N Dn from rfl]
  -- cancel the denominator gcd: toPolyG (cstep) · toPolyG Dn ~ splitFactorStep · gD, toPolyG Dn ~ gD
  have hmul : Associated (toPolyG (cstep Dt fuel p) * toPolyG Dn) (splitFactorStep v P * gD) := by
    rw [← hexact, hstepmul]; exact aN
  exact Associated.of_mul_right hmul aD hDn0
