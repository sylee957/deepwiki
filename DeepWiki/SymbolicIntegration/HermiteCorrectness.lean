import DeepWiki.Algebra.ListSums
import DeepWiki.Algebra.ListProducts
import DeepWiki.Algebra.PolynomialDivisibility
import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.Compute.Diophantine
import DeepWiki.SymbolicIntegration.Compute.HermiteInnerCorrectness
import DeepWiki.SymbolicIntegration.Compute.HermiteMultifactorIncrements
import DeepWiki.SymbolicIntegration.Compute.HermiteMultifactorResidual
import DeepWiki.SymbolicIntegration.Compute.HermitePower
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

/-! ### Toward an abstract `W ∣ R`: the increment `glocᵢ` has denominator a power of `Vi` only

The crux making the multi-factor interference *per-factor* tractable: each `glocᵢ = hermiteInner fuel Vi
Uᵢ … A qzero` accumulates **only** summands `B/Vi^{j+1}` (the inner loop `qadd`s `(B, Vi^{j+1})`), so its
denominator is a *power of `Vi` alone*. Hence `glocᵢ′` has poles **only** at `Vi`, and at any other
irreducible `Vk` (`k ≠ i`, coprime to `Vi`) `glocᵢ′` is regular. This localizes the pole-order of
`A/D − g′` at each `Vk` to the single factor `k`'s `hermiteInner_spec_of` — the structural fact behind a
future order/valuation proof of `W ∣ R`. The lemma below is the first step: `hermiteInner`'s denominator
is `(seed denominator)·Vi^m`. -/

/-- **`hermiteInner`'s denominator is the seed denominator times a power of `V`**: there is `m` with
`toPoly (hermiteInner fuel V U j A g).1.2 = toPoly g.2 · (toPoly V)^m`. Each loop step `qadd`s
`(B, V^{j+1})`, multiplying the denominator by `V^{j+1}`; so the accumulated denominator is the seed
times a power of `V`. The structural fact that `glocᵢ` has poles only at `Vi`. -/
theorem hermiteInner_den_eq_pow (fuel : ℕ) (V U : CPoly) :
    ∀ (j : ℕ) (A : CPoly) (g : QFun),
      ∃ m : ℕ, toPoly (hermiteInner fuel V U j A g).1.2 = toPoly g.2 * toPoly V ^ m := by
  intro j
  induction j with
  | zero => intro A g; exact ⟨0, by simp [hermiteInner]⟩
  | succ j ih =>
    intro A g
    rw [hermiteInner]
    rcases hBC : cdiophantine fuel (cmul U (cderiv V)) V (cscale (-((j : ℚ) + 1)⁻¹) A) with ⟨B, C⟩
    simp only []
    set Vpow := (List.range (j + 1)).foldl (fun acc _ => cmul acc V) [1] with hVpowdef
    obtain ⟨m, hm⟩ := ih (csub (cscale (-((j : ℚ) + 1)) C) (cmul U (cderiv B))) (qadd g (B, Vpow))
    refine ⟨m + (j + 1), ?_⟩
    rw [hm]
    show toPoly (qadd g (B, Vpow)).2 * toPoly V ^ m = toPoly g.2 * toPoly V ^ (m + (j + 1))
    show toPoly (cmul g.2 Vpow) * toPoly V ^ m = toPoly g.2 * toPoly V ^ (m + (j + 1))
    rw [toPoly_cmul, toPoly_hermiteInner_Vpow, pow_add]
    ring

/-- **`glocIncr`'s denominator is a pure power of `Vi`**: there is `m` with
`toPoly (glocIncr fuel A D Vi).2 = (toPoly Vi.1)^m`. From `hermiteInner_den_eq_pow` at the `qzero`
seed (denominator `1`). So `glocIncr Vi` (and its derivative) has poles only at `Vi` — regular at every
other irreducible factor. -/
theorem glocIncr_den_eq_pow (fuel : ℕ) (A D : CPoly) (Vi : CPoly × ℕ) :
    ∃ m : ℕ, toPoly (glocIncr fuel A D Vi).2 = toPoly Vi.1 ^ m := by
  obtain ⟨m, hm⟩ := hermiteInner_den_eq_pow fuel Vi.1
    (cdiv fuel D ((List.range Vi.2).foldl (fun acc _ => cmul acc Vi.1) [1]))
    (Vi.2 - 1) A qzero
  refine ⟨m, ?_⟩
  rw [show (glocIncr fuel A D Vi).2
      = (hermiteInner fuel Vi.1 (cdiv fuel D
          ((List.range Vi.2).foldl (fun acc _ => cmul acc Vi.1) [1])) (Vi.2 - 1) A qzero).1.2 from rfl,
    hm]
  simp [qzero, toPoly_cons]

/-- **`glocIncr` is `Vk`-regular for `k ≠ i`**: if `P` is coprime to `Vi`, then `P` does not divide the
denominator of `glocIncr fuel A D Vi` to any positive power beyond what `P ∣ Vi^m` allows — concretely,
`IsRelPrime P (toPoly (glocIncr fuel A D Vi).2)` whenever `IsRelPrime P (toPoly Vi.1)`. The denominator
is `Vi^m` (`glocIncr_den_eq_pow`), coprime to `P`. This is the regularity that localizes `g′`'s pole at
each `Vk` to the single factor `k`. -/
theorem glocIncr_den_isRelPrime (fuel : ℕ) (A D : CPoly) (Vi : CPoly × ℕ) (P : ℚ[X])
    (hP : IsRelPrime P (toPoly Vi.1)) :
    IsRelPrime P (toPoly (glocIncr fuel A D Vi).2) := by
  obtain ⟨m, hm⟩ := glocIncr_den_eq_pow fuel A D Vi
  rw [hm]
  exact hP.pow_right

/-! ### `Q`-regularity: a denominator-coprimality abstraction for the order argument

To prove the interference divisibility `W ∣ R` by a per-factor `Vk`-adic order argument, we track when a
`RatFunc ℚ` has **no pole at a prime `Q`** — i.e. is representable `am p/am q` with `q` coprime to `Q`.
This `IsQRegular Q` predicate is closed under `+` (common denominator stays coprime) and under the
`RatFunc` derivative (the quotient rule squares the denominator, keeping it coprime to `Q`), and the key
**extraction** lemma reads a divisibility off it: if `am r/am D` is `Q`-regular and `Q^e ∣ D`, then
`Q^e ∣ r` — the numerator carries the pole order the regular function refuses. -/

/-- **`Q`-regular**: a `RatFunc ℚ` representable `am p/am q` with `q ≠ 0` coprime to `Q` — no pole at
`Q`. The denominator-coprimality witness driving the per-factor order argument for `W ∣ R`. -/
abbrev IsQRegular (Q : ℚ[X]) (f : RatFunc ℚ) : Prop :=
  IsRatFuncRegular Q f

/-- `0` is `Q`-regular (denominator `1`). -/
theorem isQRegular_zero (Q : ℚ[X]) : IsQRegular Q 0 :=
  isRatFuncRegular_zero Q

/-- **`Q`-regular is closed under `+`**: over the common denominator `q₁·q₂` (coprime to `Q` since each
`qᵢ` is, by `IsRelPrime.mul_right`). The sum of two pole-free-at-`Q` functions is pole-free at `Q`. -/
theorem IsQRegular.add {Q : ℚ[X]} {f g : RatFunc ℚ} (hf : IsQRegular Q f) (hg : IsQRegular Q g) :
    IsQRegular Q (f + g) :=
  IsRatFuncRegular.add hf hg

/-- **Order extraction from `Q`-regularity**: if the fraction `am r/am D` is `Q`-regular, `D ≠ 0`, and
`Q^e ∣ D`, then `Q^e ∣ r`. Cross-multiplying `r·q = p·D` (the regular representation), `Q^e ∣ D ∣ p·D =
r·q`; coprimality `IsRelPrime (Q^e) q` then transfers the power onto `r`. The numerator absorbs the pole
order the `Q`-regular function declines to carry. -/
theorem dvd_num_of_isQRegular {Q r D : ℚ[X]} {e : ℕ} (hD : D ≠ 0) (hQe : Q ^ e ∣ D)
    (hf : IsQRegular Q (algebraMap ℚ[X] (RatFunc ℚ) r / algebraMap ℚ[X] (RatFunc ℚ) D)) :
    Q ^ e ∣ r :=
  dvd_num_of_isRatFuncRegular hD hQe hf

open scoped Differential in
/-- **`Q`-regular is closed under the `RatFunc` derivative**: if `f = am p/am q` has denominator `q`
coprime to `Q`, then `f′` has denominator `q²` (quotient rule `ratFuncDeriv_mk`), still coprime to `Q`
(`IsRelPrime.pow_right`). A pole-free-at-`Q` function differentiates to a pole-free-at-`Q` function. -/
theorem IsQRegular.deriv {Q : ℚ[X]} {f : RatFunc ℚ} (hf : IsQRegular Q f) :
    IsQRegular Q (f′) := by
  obtain ⟨p, q, hq, hQ, hfeq⟩ := hf
  refine ⟨derivative p * q - p * derivative q, q ^ 2, pow_ne_zero 2 hq, hQ.pow_right, ?_⟩
  rw [hfeq, ← RatFunc.mk_eq_div]
  show ratFuncDeriv (RatFunc.mk p q) = _
  rw [ratFuncDeriv_mk, RatFunc.mk_eq_div]

/-- **`glocᵢ` is `Q`-regular for `Q` coprime to `Vi`**: `toQFun (glocIncr fuel A D Vi)` has denominator
`(toPoly Vi.1)^m` (`glocIncr_den_eq_pow`), coprime to `Q` whenever `IsRelPrime Q (toPoly Vi.1)`. So the
increment's rational read has no pole at any other irreducible factor — the localization that confines
factor `i`'s pole to `Vi`. -/
theorem glocIncr_toQFun_isQRegular (fuel : ℕ) (A D : CPoly) (Vi : CPoly × ℕ) {Q : ℚ[X]}
    (hV : toPoly Vi.1 ≠ 0) (hQ : IsRelPrime Q (toPoly Vi.1)) :
    IsQRegular Q (toQFun (glocIncr fuel A D Vi)) := by
  obtain ⟨m, hm⟩ := glocIncr_den_eq_pow fuel A D Vi
  refine ⟨toPoly (glocIncr fuel A D Vi).1, toPoly Vi.1 ^ m, pow_ne_zero m hV, hQ.pow_right, ?_⟩
  rw [toQFun, hm]

/-- **`Q`-regular is closed under negation**: `−f = am(−p)/am q`, same `Q`-coprime denominator. -/
theorem IsQRegular.neg {Q : ℚ[X]} {f : RatFunc ℚ} (hf : IsQRegular Q f) : IsQRegular Q (-f) := by
  exact IsRatFuncRegular.neg hf

/-- **A `List`-sum of `Q`-regular summands is `Q`-regular**: by induction, folding `IsQRegular.add`
from `isQRegular_zero`. The interference sum over the *other* factors (each `glocᵢ′`, `i≠k`, pole-free at
`Vk`) is itself pole-free at `Vk`. -/
theorem isQRegular_list_sum {α : Type*} {Q : ℚ[X]} (L : List α)
    (f : α → RatFunc ℚ) (hreg : ∀ a ∈ L, IsQRegular Q (f a)) :
    IsQRegular Q (L.map f).sum :=
  isRatFuncRegular_list_sum L f hreg

open scoped Differential in
/-- **The interference derivative `g′ − glocₖ′` is `Vk`-regular**: the fold derivative `g′ = Σ_{i∈kept}
glocᵢ′` minus the `k`-term `glocₖ′` is the sum `Σ_{i∈kept.erase k} glocᵢ′` (`perm_cons_erase`), whose
every summand is `glocᵢ′` for `i ≠ k` — pole-free at `Vk` by `glocIncr_toQFun_isQRegular` +
`IsQRegular.deriv`. Hence the whole interference difference has no pole at `Vk`. The structural heart of
the per-factor order argument: removing factor `k`'s own contribution leaves a `Vk`-regular remainder. -/
theorem deriv_fold_sub_glocIncr_isQRegular (fuel : ℕ) (A D : CPoly)
    (factors : List (CPoly × ℕ)) (kelem : CPoly × ℕ)
    (hkmem : kelem ∈ factors.filter (fun Vi => decide (2 ≤ Vi.2)))
    (hnd : (factors.filter (fun Vi => decide (2 ≤ Vi.2))).Nodup)
    (hV : ∀ Vi ∈ factors, toPoly Vi.1 ≠ 0)
    (hcop : ∀ Vi ∈ factors.filter (fun Vi => decide (2 ≤ Vi.2)), Vi ≠ kelem →
      IsRelPrime (toPoly kelem.1) (toPoly Vi.1)) :
    IsQRegular (toPoly kelem.1)
      ((toQFun ((glocList fuel A D factors).foldl qadd qzero))′
        - (toQFun (glocIncr fuel A D kelem))′) := by
  classical
  set kept := factors.filter (fun Vi => decide (2 ≤ Vi.2)) with hkept
  -- denominators of the increments are nonzero (needed for `deriv_toQFun_foldl_qadd`).
  have hden : ∀ g ∈ glocList fuel A D factors, toPoly g.2 ≠ 0 := by
    intro g hg
    rw [glocList, ← hkept, List.mem_map] at hg
    obtain ⟨Vi, hViMem, rfl⟩ := hg
    exact glocIncr_den_ne_zero fuel A D Vi (hV Vi (List.mem_of_mem_filter hViMem))
  -- `g′ = Σ_{i∈kept} glocᵢ′`.
  rw [deriv_toQFun_foldl_qadd (glocList fuel A D factors) hden, glocList, ← hkept, List.map_map]
  set h := (fun g => (toQFun g)′) ∘ glocIncr fuel A D with hh
  -- `kept` permutes to `kelem :: kept.erase kelem`, so the mapped sum splits off the `k`-term.
  have hsum : (kept.map h).sum = h kelem + ((kept.erase kelem).map h).sum := by
    have hp : (kept.map h).Perm ((kelem :: kept.erase kelem).map h) :=
      (List.perm_cons_erase hkmem).map h
    rw [hp.sum_eq, List.map_cons, List.sum_cons]
  rw [hsum, hh]
  simp only [Function.comp_apply]
  -- `(glocₖ′ + Σ_{i≠k} glocᵢ′) − glocₖ′ = Σ_{i≠k} glocᵢ′`, which is `Vk`-regular.
  rw [add_sub_cancel_left]
  refine isQRegular_list_sum (kept.erase kelem) (fun g => (toQFun (glocIncr fuel A D g))′) ?_
  intro Vi hVi
  rw [(hkept ▸ hnd : kept.Nodup).mem_erase_iff] at hVi
  obtain ⟨hVine, hVimem⟩ := hVi
  have hVi0 : toPoly Vi.1 ≠ 0 := hV Vi (List.mem_of_mem_filter (hkept ▸ hVimem))
  exact (glocIncr_toQFun_isQRegular fuel A D Vi hVi0
    (hcop Vi (hkept ▸ hVimem) hVine)).deriv

/-! ### The per-factor interference divisibility `Vk^{ik−1} ∣ R`

The single-factor order bound. With `R = C(1−n)·A + Σ_{kept} residNumIncr` the whole-fold residual
numerator, fix a kept factor `(Vk, ik)`. Subtracting the factor-`k` residual identity (`hstep` at `k`,
`glocₖ′ = A/D − residNumIncrₖ/D`) from the total residual (`total_fold_residual_over_D`,
`A/D − g′ = R/D`) gives `am (R − residNumIncrₖ)/am D = glocₖ′ − g′`, which is `Vk`-regular
(`deriv_fold_sub_glocIncr_isQRegular`). With `Vk^{ik} ∣ D`, the order-extraction lemma
`dvd_num_of_isQRegular` yields `Vk^{ik} ∣ (R − residNumIncrₖ)`; and `residNumIncrₖ = Afinalₖ·Vk^{ik−1}`
already carries `Vk^{ik−1}`, so `Vk^{ik−1} ∣ R`. -/

open scoped Differential in
/-- **Per-factor interference divisibility `Vk^{ik−1} ∣ R`**: for a kept factor `kelem = (Vk, ik)`
(distinct kept factors, `hnd`), with the per-factor residual identities (`hstep`, the
`total_fold_residual_over_D` input), the localization coprimality `IsRelPrime Vk Vi` for every *other*
kept factor, and `Vk^{ik} ∣ D`, the whole-fold residual numerator
`R = C(1−n)·A + Σ residNumIncr` is divisible by `Vk^{ik−1}`. The order argument: `R − residNumIncrₖ`
over `D` is `Vk`-regular, so `Vk^{ik} ∣ (R − residNumIncrₖ)`, and `Vk^{ik−1} ∣ residNumIncrₖ`. -/
theorem dvd_residNum_factor (fuel : ℕ) (A D : CPoly) (factors : List (CPoly × ℕ))
    (kelem : CPoly × ℕ) (hkmem : kelem ∈ factors.filter (fun Vi => decide (2 ≤ Vi.2)))
    (hnd : (factors.filter (fun Vi => decide (2 ≤ Vi.2))).Nodup)
    (hD : toPoly D ≠ 0) (hV : ∀ Vi ∈ factors, toPoly Vi.1 ≠ 0)
    (hstep : ∀ Vi ∈ factors, 2 ≤ Vi.2 →
      (toQFun (glocIncr fuel A D Vi))′
        = algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
          - algebraMap ℚ[X] (RatFunc ℚ) (residNumIncr fuel A D Vi)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D))
    (hcop : ∀ Vi ∈ factors.filter (fun Vi => decide (2 ≤ Vi.2)), Vi ≠ kelem →
      IsRelPrime (toPoly kelem.1) (toPoly Vi.1))
    (hpow : toPoly kelem.1 ^ kelem.2 ∣ toPoly D) :
    toPoly kelem.1 ^ (kelem.2 - 1)
      ∣ Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ)) * toPoly A
        + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum := by
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  set R := Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ)) * toPoly A
    + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum with hR
  -- the kept membership gives `2 ≤ kelem.2` and `kelem ∈ factors`.
  have hk2 : 2 ≤ kelem.2 := by simpa using (List.mem_filter.mp hkmem).2
  have hkF : kelem ∈ factors := List.mem_of_mem_filter hkmem
  -- total residual: `am A/am D − g′ = am R/am D`.
  have hres := total_fold_residual_over_D fuel A D factors hD hV hstep
  rw [← hR] at hres
  -- factor-`k` step.
  have hk := hstep kelem hkF hk2
  -- `glocₖ′ − g′ = am (R − residNumIncrₖ)/am D`.
  have hinj := RatFunc.algebraMap_injective (K := ℚ)
  have had : am (toPoly D) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
  have hdiff : (toQFun (glocIncr fuel A D kelem))′
      - (toQFun ((glocList fuel A D factors).foldl qadd qzero))′
      = am (R - residNumIncr fuel A D kelem) / am (toPoly D) := by
    rw [map_sub, sub_div]
    linear_combination hk + hres
  -- `Vk`-regularity of the difference, transported across `hdiff`.
  have hreg : IsQRegular (toPoly kelem.1)
      (am (R - residNumIncr fuel A D kelem) / am (toPoly D)) := by
    rw [← hdiff, ← neg_sub]
    exact (deriv_fold_sub_glocIncr_isQRegular fuel A D factors kelem hkmem hnd hV hcop).neg
  -- `Vk^{ik} ∣ (R − residNumIncrₖ)`.
  have hdvdSub : toPoly kelem.1 ^ kelem.2 ∣ R - residNumIncr fuel A D kelem :=
    dvd_num_of_isQRegular hD hpow hreg
  -- `Vk^{ik−1} ∣ residNumIncrₖ` (it is `Afinalₖ·Vk^{ik−1}`).
  have hdvdInc : toPoly kelem.1 ^ (kelem.2 - 1) ∣ residNumIncr fuel A D kelem := by
    rw [residNumIncr]; exact Dvd.intro_left _ rfl
  -- `Vk^{ik−1} ∣ Vk^{ik} ∣ (R − residNumIncrₖ)`, plus `Vk^{ik−1} ∣ residNumIncrₖ`, gives `Vk^{ik−1} ∣ R`.
  have hdvdSub' : toPoly kelem.1 ^ (kelem.2 - 1) ∣ R - residNumIncr fuel A D kelem :=
    (pow_dvd_pow _ (Nat.sub_le _ _)).trans hdvdSub
  have : toPoly kelem.1 ^ (kelem.2 - 1) ∣ (R - residNumIncr fuel A D kelem)
      + residNumIncr fuel A D kelem := dvd_add hdvdSub' hdvdInc
  simpa using this

/-! ### The product divisibility `W ∣ R` over the pairwise-coprime kept factors

The interference numerator `R` is divisible by each `Vk^{ik−1}` (`dvd_residNum_factor`). Since the kept
factors `Vk` are pairwise coprime (Yun's `csqfreeFactor_pairwise_isRelPrime`), so are the powers
`Vk^{ik−1}`, hence their product `W = ∏_{kept} Vk^{ik−1} = D/Dstar` divides `R` — the single remaining
interference divisibility, now proven by the per-factor order argument. -/

open scoped Differential in
/-- **The product interference divisibility `W ∣ R`**: with `W = ∏_{kept} Vk^{ik−1}` and `R =
C(1−n)·A + Σ residNumIncr`, given the per-factor residual identities (`hstep`), pairwise coprimality of
the kept factors `Vk` (`hpw`), each `Vk^{ik} ∣ D`, the product `∏_{kept} Vk^{ik−1}` divides `R`. The
per-factor order bounds `Vk^{ik−1} ∣ R` (`dvd_residNum_factor`) assemble over the coprime powers
(`list_prod_dvd_of_pairwise`): the entire multi-factor interference clears, the last remaining piece. -/
theorem prod_dvd_residNum (fuel : ℕ) (A D : CPoly) (factors : List (CPoly × ℕ))
    (hnd : (factors.filter (fun Vi => decide (2 ≤ Vi.2))).Nodup)
    (hD : toPoly D ≠ 0) (hV : ∀ Vi ∈ factors, toPoly Vi.1 ≠ 0)
    (hstep : ∀ Vi ∈ factors, 2 ≤ Vi.2 →
      (toQFun (glocIncr fuel A D Vi))′
        = algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
          - algebraMap ℚ[X] (RatFunc ℚ) (residNumIncr fuel A D Vi)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D))
    (hpw : (factors.filter (fun Vi => decide (2 ≤ Vi.2))).Pairwise
      (fun a b => IsRelPrime (toPoly a.1) (toPoly b.1)))
    (hpow : ∀ Vi ∈ factors.filter (fun Vi => decide (2 ≤ Vi.2)),
      toPoly Vi.1 ^ Vi.2 ∣ toPoly D) :
    ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map
        (fun Vi => toPoly Vi.1 ^ (Vi.2 - 1))).prod
      ∣ Polynomial.C (1 - ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).length : ℚ)) * toPoly A
        + ((factors.filter (fun Vi => decide (2 ≤ Vi.2))).map (residNumIncr fuel A D)).sum := by
  set kept := factors.filter (fun Vi => decide (2 ≤ Vi.2)) with hkept
  -- the mapped powers are pairwise `IsRelPrime` (from pairwise coprimality of the `Vk`).
  have hpwpow : (kept.map (fun Vi => toPoly Vi.1 ^ (Vi.2 - 1))).Pairwise IsRelPrime := by
    rw [List.pairwise_map]
    exact hpw.imp (fun {a b} hab => (hab.pow_left).pow_right)
  refine list_prod_dvd_of_pairwise _ _ hpwpow ?_
  -- each mapped power `Vk^{ik−1}` divides `R` by the per-factor order bound.
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨kelem, hkelem, rfl⟩ := ha
  -- the localization coprimality for the OTHER kept factors at `kelem`.
  haveI hsymInst : Std.Symm (fun a b : CPoly × ℕ => IsRelPrime (toPoly a.1) (toPoly b.1)) :=
    ⟨fun {_ _} (h : IsRelPrime _ _) => h.symm⟩
  have hcop : ∀ Vi ∈ kept, Vi ≠ kelem → IsRelPrime (toPoly kelem.1) (toPoly Vi.1) := by
    intro Vi hVi hne
    -- from pairwise coprimality (symmetric): `kelem` and `Vi` distinct kept factors are coprime.
    exact (hkept ▸ hpw : kept.Pairwise _).forall hkelem hVi (Ne.symm hne)
  exact dvd_residNum_factor fuel A D factors kelem hkelem hnd hD hV hstep hcop
    (hpow kelem hkelem)

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
