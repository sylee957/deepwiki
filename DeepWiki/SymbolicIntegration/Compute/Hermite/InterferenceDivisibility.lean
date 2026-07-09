import DeepWiki.Algebra.ListProducts
import DeepWiki.SymbolicIntegration.Compute.Hermite.QRegularity
import DeepWiki.SymbolicIntegration.Compute.Hermite.MultifactorResidual

/-! # Hermite multifactor interference divisibility
Proves the per-factor and product divisibility that clears the multifactor Hermite residual.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

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
theorem dvd_residNum_factor (fuel : ℕ) (A D : DensePoly ℚ) (factors : List (DensePoly ℚ × ℕ))
    (kelem : DensePoly ℚ × ℕ) (hkmem : kelem ∈ factors.filter (fun Vi => decide (2 ≤ Vi.2)))
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
interference divisibility follows from the per-factor order argument. -/

open scoped Differential in
/-- **The product interference divisibility `W ∣ R`**: with `W = ∏_{kept} Vk^{ik−1}` and `R =
C(1−n)·A + Σ residNumIncr`, given the per-factor residual identities (`hstep`), pairwise coprimality of
the kept factors `Vk` (`hpw`), each `Vk^{ik} ∣ D`, the product `∏_{kept} Vk^{ik−1}` divides `R`. The
per-factor order bounds `Vk^{ik−1} ∣ R` (`dvd_residNum_factor`) assemble over the coprime powers
(`list_prod_dvd_of_pairwise`): the multi-factor interference numerator clears. -/
theorem prod_dvd_residNum (fuel : ℕ) (A D : DensePoly ℚ) (factors : List (DensePoly ℚ × ℕ))
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
  haveI hsymInst : Std.Symm (fun a b : DensePoly ℚ × ℕ => IsRelPrime (toPoly a.1) (toPoly b.1)) :=
    ⟨fun {_ _} (h : IsRelPrime _ _) => h.symm⟩
  have hcop : ∀ Vi ∈ kept, Vi ≠ kelem → IsRelPrime (toPoly kelem.1) (toPoly Vi.1) := by
    intro Vi hVi hne
    -- from pairwise coprimality (symmetric): `kelem` and `Vi` distinct kept factors are coprime.
    exact (hkept ▸ hpw : kept.Pairwise _).forall hkelem hVi (Ne.symm hne)
  exact dvd_residNum_factor fuel A D factors kelem hkelem hnd hD hV hstep hcop
    (hpow kelem hkelem)

end DeepWiki.SymbolicIntegration.Compute
