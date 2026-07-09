import DeepWiki.SymbolicIntegration.Compute.Hermite.IncrementDenominator
import DeepWiki.SymbolicIntegration.Compute.Hermite.MultifactorResidual
import DeepWiki.SymbolicIntegration.Core.Polynomial.RatFuncRegular

/-! # Hermite `Q`-regularity for multifactor interference
Packages the pole-free-at-`Q` API used to localize Hermite multifactor interference.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

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
theorem glocIncr_toQFun_isQRegular (fuel : ℕ) (A D : CPoly ℚ) (Vi : CPoly ℚ × ℕ) {Q : ℚ[X]}
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
theorem deriv_fold_sub_glocIncr_isQRegular (fuel : ℕ) (A D : CPoly ℚ)
    (factors : List (CPoly ℚ × ℕ)) (kelem : CPoly ℚ × ℕ)
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

end DeepWiki.SymbolicIntegration.Compute
