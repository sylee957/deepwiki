import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms
import DeepWiki.SymbolicIntegration.PseudoRemainderSequence
import DeepWiki.SymbolicIntegration.ResidueMultiplicity

/-! # Lazard–Rioboo–Trager correctness (Bronstein Theorem 2.5.1, part (ii))
The LRT log-part algorithm replaces the Rothstein–Trager per-residue gcds `gcd(D, A − a·D')` by the
specializations `Sᵢ(a, x)` of one subresultant PRS. Theorem 2.5.1(ii) is the correctness statement
`ppₓ(Sₘ)(a, x) ~ gcd(D, A − a·D')`. This file connects the *concrete* subresultant ↔ gcd engine
(`subresultant_euclideanPRS_isSimilar_gcd`) to the algorithm's primitive `lrtSubresultant` via the
specialization `lrtSubresultant_eval` (`t ↦ a`). `lrtSubresultant_eval` lands on the formal-degree-`deg D − 1`
subresultant; `isSimilar_subresultant_padding` matches that to the *actual* degree of `A − a·D'` driving the
Euclidean p.r.s. up to a nonzero `lc(D)` power, so the correctness holds for **every** residue — including
the degenerate `deg(A − a·D') < deg D − 1`. (Over a field `ppₓ(Sₘ) ~ Sₘ`, so the similarity below is the
part-(ii) conclusion with the primitive part absorbed by `~`.) -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-- **Residue non-degeneracy** (the characterization of when `A − a·D'` keeps the full degree `deg D − 1`):
the degree drops below `deg D − 1` exactly at the single residue value `a = A_{n−1}/(n·lc D)` (`n = deg D`),
where the `xⁿ⁻¹`-coefficient `A_{n−1} − a·n·lc(D)` cancels (the leading coefficient of `D'` is `n·lc(D)`).
Under the non-cancellation `A_{n−1} ≠ a·n·lc(D)` the full degree is kept. (`deg(A − a·D') ≤ deg D − 1`
always, since `deg A < deg D`; `isSimilar_lrtSubresultant_eval_gcd` no longer needs this, handling the
degenerate value uniformly via padding — this records the dividing line.) -/
theorem natDegree_sub_C_mul_derivative {K : Type*} [Field K] (A D : K[X]) (a : K)
    (hA : A.natDegree < D.natDegree)
    (hne : A.coeff (D.natDegree - 1) ≠ a * ((D.natDegree : K) * D.leadingCoeff)) :
    (A - C a * derivative D).natDegree = D.natDegree - 1 := by
  have hle : (A - C a * derivative D).natDegree ≤ D.natDegree - 1 :=
    (natDegree_sub_le _ _).trans
      (max_le (by omega) ((natDegree_C_mul_le _ _).trans (natDegree_derivative_le D)))
  refine le_antisymm hle (le_natDegree_of_ne_zero ?_)
  have hcast : ((D.natDegree - 1 : ℕ) : K) + 1 = (D.natDegree : K) := by
    rw [Nat.cast_sub (by omega : 1 ≤ D.natDegree), Nat.cast_one]; ring
  rw [coeff_sub, coeff_C_mul, coeff_derivative, Nat.sub_add_cancel (by omega : 1 ≤ D.natDegree),
    hcast, ← leadingCoeff]
  intro h
  exact hne (by linear_combination h)

/-- **Theorem 2.5.1, part (ii)** (the LRT subresultant correctness — *all* residues): for `D ≠ 0` and
`deg A < deg D`, the LRT subresultant `lrtSubresultant A D` at the index `i = deg R_k` (`R_k` the last
nonzero element of the Euclidean p.r.s. of `D, A − a·D'`), specialized by `t ↦ a`, is *similar* to
`gcd(D, A − a·D')` — the book's `ppₓ(R_m)(a,x) ~ gcd(D, A−aD')` (over a field `ppₓ(R_m) ~ R_m`). Holds for
every residue, including the *degenerate* one where `deg(A − a·D') < deg D − 1`: `lrtSubresultant_eval`
lands on the formal-degree-`(deg D − 1)` subresultant, which `isSimilar_subresultant_padding` matches to the
actual-degree p.r.s. computation `subresultant_euclideanPRS_isSimilar_gcd` up to a nonzero `lc(D)` power
(absorbed by `~`). The index bound `i = deg R_k < deg(A − a·D')` follows from `k ≥ 2` via the strict degree
decrease `euclideanPRS_natDegree_strictAnti`. -/
theorem isSimilar_lrtSubresultant_eval_gcd {K : Type*} [Field K] [GCDMonoid K[X]]
    (A D : K[X]) (a : K) (hD : D ≠ 0) (hA : A.natDegree < D.natDegree)
    {k : ℕ} (hk2 : 2 ≤ k) (hk0 : euclideanPRS D (A - C a * derivative D) (k + 1) = 0)
    (hknz : ∀ j, 1 ≤ j → j ≤ k → euclideanPRS D (A - C a * derivative D) j ≠ 0) :
    IsSimilar
      ((lrtSubresultant A D (euclideanPRS D (A - C a * derivative D) k).natDegree).map
        (Polynomial.evalRingHom a))
      (gcd D (A - C a * derivative D)) := by
  rw [lrtSubresultant_eval]
  set E := A - C a * derivative D with hE
  have hElt : E.natDegree ≤ D.natDegree - 1 :=
    (natDegree_sub_le _ _).trans
      (max_le (by omega) ((natDegree_C_mul_le _ _).trans (natDegree_derivative_le D)))
  have hjE : (euclideanPRS D E k).natDegree < E.natDegree := by
    have h := euclideanPRS_natDegree_strictAnti D E hknz 1 k (le_refl 1) (by omega) (le_refl k)
    rwa [euclideanPRS_one] at h
  have hengine := subresultant_euclideanPRS_isSimilar_gcd D E hD
    (le_trans hElt (Nat.sub_le _ _)) hk2 hk0 hknz
  exact (isSimilar_subresultant_padding D E D.natDegree E.natDegree
    (euclideanPRS D E k).natDegree hjE
    (le_trans (le_of_lt hjE) (le_trans hElt (Nat.sub_le _ _))) le_rfl le_rfl
    (leadingCoeff_ne_zero.mpr hD) hElt).trans hengine

/-- **Theorem 2.5.1, part (ii) — the top-index `k = 1` case** (`E := A − a·D'` *divides* `D`): the
Euclidean p.r.s. of `D, E` terminates in one step (`R₂ = prem(D, E) = 0`), so the last nonzero element
is `R₁ = E` and `i = deg R₁ = deg E` is the *top* p.r.s. index. The LRT subresultant at index `deg E`,
specialized `t ↦ a`, is `subresultant D E (deg D) (deg D − 1) (deg E)`, which the *normal*-orientation
degenerate formula `subresultant_deg_ge_normal` (first poly `D`, the larger formal degree, `deg E < deg D`)
collapses to `C(...)·E`, i.e. `~ E`; chaining `gcd D E ~ E` gives `~ gcd(D, A − a·D')`. This is the
`k = 1` boundary that padding cannot reach (`j = deg E` may equal `deg D − 1`). -/
theorem isSimilar_lrtSubresultant_eval_gcd_top {K : Type*} [Field K] [GCDMonoid K[X]]
    (A D : K[X]) (a : K) (hD : D ≠ 0) (hA : A.natDegree < D.natDegree)
    (hE : A - C a * derivative D ≠ 0)
    (h0 : euclideanPRS D (A - C a * derivative D) 2 = 0) :
    IsSimilar
      ((lrtSubresultant A D (A - C a * derivative D).natDegree).map (Polynomial.evalRingHom a))
      (gcd D (A - C a * derivative D)) := by
  rw [lrtSubresultant_eval]
  set E := A - C a * derivative D with hEdef
  have hElt : E.natDegree ≤ D.natDegree - 1 :=
    (natDegree_sub_le _ _).trans
      (max_le (by omega) ((natDegree_C_mul_le _ _).trans (natDegree_derivative_le D)))
  have hsim : IsSimilar (subresultant D E D.natDegree (D.natDegree - 1) E.natDegree) E := by
    rw [subresultant_deg_ge_normal D E D.natDegree (D.natDegree - 1) E.natDegree le_rfl
      (by omega) (Nat.sub_le _ _) hElt]
    exact ⟨1, (D.coeff D.natDegree) ^ (D.natDegree - 1 - E.natDegree)
        * E.coeff E.natDegree ^ (D.natDegree - E.natDegree - 1), one_ne_zero,
      mul_ne_zero (pow_ne_zero _ (by rw [← leadingCoeff]; exact leadingCoeff_ne_zero.mpr hD))
        (pow_ne_zero _ (by rw [← leadingCoeff]; exact leadingCoeff_ne_zero.mpr hE)),
      by rw [map_one, one_mul]⟩
  exact hsim.trans (isSimilar_gcd_right_of_euclideanPRS_two_eq_zero D E hE h0).symm

open scoped Classical in
/-- **Theorem 2.5.1 — algorithm-level capstone (full part-(ii) regime)**: state part-(ii) correctness
directly at the LRT algorithm's own index `i = rootMultiplicity a R` (`R = rtResultant A D`), with the
p.r.s.-termination hypotheses discharged internally. Over an algebraically closed field with `D`
separable and `deg A < deg D`, for a residue `a` whose multiplicity `i` in `R` is *strictly* below
`deg D` (i.e. `gcd(D, A − a·D')` is a *proper* factor of `D` — the genuine part-(ii) regime, excluding
only the part-(i) `i = deg D` case where `A − a·D' = 0` and `gcd ~ D`), the LRT subresultant at index
`i`, specialized `t ↦ a`, is similar to the Rothstein–Trager gcd `gcd(D, A − a·D')`. The index is
rewritten from `i` to the last-p.r.s. degree via `rootMultiplicity_rtResultant_eq_natDegree_gcd`
(`i = deg gcd`) and `IsSimilar.natDegree_eq` on `(isPRS_euclideanPRS …).isSimilar_gcd`
(`deg gcd = deg R_k`); the termination data `hk0`/`hknz` come from `exists_last_euclideanPRS_nonzero`.
Both `k ≥ 2` (multi-step, via `isSimilar_lrtSubresultant_eval_gcd` + padding) and `k = 1` (one-step,
`E ∣ D`, the top p.r.s. index `i = deg E`, via `isSimilar_lrtSubresultant_eval_gcd_top`) are covered;
only `A − a·D' = 0` (the part-(i) `i = deg D` regime) is excluded by `hi`. -/
theorem lazardRiobooTrager_isSimilar_gcd {K : Type*} [Field K] [IsAlgClosed K]
    (A D : K[X]) (hD : D.Separable) (hA : A.natDegree < D.natDegree) (a : K)
    (hi : (rtResultant A D).rootMultiplicity a < D.natDegree) :
    IsSimilar
      ((lrtSubresultant A D ((rtResultant A D).rootMultiplicity a)).map
        (Polynomial.evalRingHom a))
      (gcd D (A - C a * derivative D)) := by
  set E := A - C a * derivative D with hE
  have hDne : D ≠ 0 := fun h => by simp [h] at hA
  -- the multiplicity bridge: `i = deg gcd(D, E)`
  have hmul : (rtResultant A D).rootMultiplicity a = (gcd D E).natDegree :=
    rootMultiplicity_rtResultant_eq_natDegree_gcd A D hD hA a
  -- `E ≠ 0`: were `E = 0`, `gcd D 0 ~ D` would give `deg gcd = deg D`, contradicting `i < deg D`
  have hEne : E ≠ 0 := by
    intro h
    rw [h, (IsSimilar.of_associated
      (gcd_zero_right D ▸ normalize_associated D)).natDegree_eq] at hmul
    rw [hmul] at hi; exact absurd hi (lt_irrefl _)
  -- termination data for the Euclidean p.r.s. of `D, E`
  obtain ⟨k, hk1, hk0, hknz⟩ := exists_last_euclideanPRS_nonzero D E hEne
  -- the last nonzero p.r.s. element is similar to the gcd, so they share the degree
  have hsim : IsSimilar (euclideanPRS D E k) (gcd D E) :=
    (isPRS_euclideanPRS D E).isSimilar_gcd hk0 (fun j hj1 hjk => hknz j hj1 hjk)
  have hdeg : (euclideanPRS D E k).natDegree = (gcd D E).natDegree := hsim.natDegree_eq
  -- split on the number of p.r.s. steps
  rcases Nat.lt_or_ge k 2 with hk | hk2
  · -- `k = 1`: one-step termination, `E ∣ D`, the top p.r.s. index `i = deg E`
    have hk1' : k = 1 := by omega
    subst hk1'
    rw [euclideanPRS_one] at hdeg
    have h0 : euclideanPRS D E 2 = 0 := hk0
    rw [hmul, ← hdeg]
    exact isSimilar_lrtSubresultant_eval_gcd_top A D a hDne hA hEne h0
  · -- `k ≥ 2`: multi-step termination, the part-(ii) padding path
    rw [hmul, ← hdeg]
    exact isSimilar_lrtSubresultant_eval_gcd A D a hDne hA hk2 hk0 hknz

open scoped Classical in
example {K : Type*} [Field K] [IsAlgClosed K]
    (A D : K[X]) (hD : D.Separable) (hA : A.natDegree < D.natDegree) (a : K)
    (hi : (rtResultant A D).rootMultiplicity a < D.natDegree) :
    IsSimilar
      ((lrtSubresultant A D ((rtResultant A D).rootMultiplicity a)).map
        (Polynomial.evalRingHom a))
      (gcd D (A - C a * derivative D)) :=
  lazardRiobooTrager_isSimilar_gcd A D hD hA a hi

open scoped Classical in
/-- **Theorem 2.5.1, unified algorithm output** (no excluded case): for any `a`, the LRT algorithm's
output curve `Sᵢ` at multiplicity `i = rootMultiplicity a R` — namely `D` if `i = deg D` (part (i), the
`A − a·D' = 0` regime, where `gcd ~ D`) else `lrtSubresultant A D i` (part (ii)) — specialized `t ↦ a`,
is similar to `gcd(D, A − a·D')`. The `if i = deg D` branch is exactly `lazardRiobooTrager`'s own, so this
stitches parts (i) and (ii) into one statement covering EVERY residue with no boundary: `i ≤ deg D` always
(`gcd ∣ D`), and the `i = deg D` case routes to `isSimilar_gcd_left_of_natDegree_eq`, `i < deg D` to the
capstone `lazardRiobooTrager_isSimilar_gcd`. -/
theorem lazardRiobooTrager_output_isSimilar_gcd {K : Type*} [Field K] [IsAlgClosed K]
    (A D : K[X]) (hD : D.Separable) (hA : A.natDegree < D.natDegree) (a : K) :
    IsSimilar
      ((if (rtResultant A D).rootMultiplicity a = D.natDegree then D.map (C : K →+* K[X])
        else lrtSubresultant A D ((rtResultant A D).rootMultiplicity a)).map
        (Polynomial.evalRingHom a))
      (gcd D (A - C a * derivative D)) := by
  have hDne : D ≠ 0 := fun h => by simp [h] at hA
  set E := A - C a * derivative D with hE
  have hmul : (rtResultant A D).rootMultiplicity a = (gcd D E).natDegree :=
    rootMultiplicity_rtResultant_eq_natDegree_gcd A D hD hA a
  have hile : (rtResultant A D).rootMultiplicity a ≤ D.natDegree :=
    hmul.le.trans (natDegree_le_of_dvd (gcd_dvd_left D E) hDne)
  by_cases hcase : (rtResultant A D).rootMultiplicity a = D.natDegree
  · rw [if_pos hcase]
    have hmapid : (D.map (C : K →+* K[X])).map (Polynomial.evalRingHom a) = D := by
      rw [Polynomial.map_map,
        show (Polynomial.evalRingHom a).comp (C : K →+* K[X]) = RingHom.id K from by ext k; simp,
        Polynomial.map_id]
    rw [hmapid]
    exact (isSimilar_gcd_left_of_natDegree_eq hDne (hmul.symm.trans hcase)).symm
  · rw [if_neg hcase]
    exact lazardRiobooTrager_isSimilar_gcd A D hD hA a (lt_of_le_of_ne hile hcase)

end DeepWiki.SymbolicIntegration
