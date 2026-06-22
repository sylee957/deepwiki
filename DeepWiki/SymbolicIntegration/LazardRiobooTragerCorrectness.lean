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

open scoped Classical in
/-- **Theorem 2.5.1 — algorithm-level capstone**: state part-(ii) correctness directly at the LRT
algorithm's own index `i = rootMultiplicity a R` (`R = rtResultant A D`), with the p.r.s.-termination
hypotheses discharged internally. Over an algebraically closed field with `D` separable and
`deg A < deg D`, for a residue `a` whose multiplicity `i` in `R` is *strictly* below `deg(A − a·D')`
(the genuine part-(ii) regime: the gcd is a proper factor of `A − a·D'`, forcing the Euclidean p.r.s.
to take `≥ 2` steps), the LRT subresultant at index `i`, specialized `t ↦ a`, is similar to the
Rothstein–Trager gcd `gcd(D, A − a·D')`. The index is rewritten from `i` to the last-p.r.s. degree via
`rootMultiplicity_rtResultant_eq_natDegree_gcd` (`i = deg gcd`) and `IsSimilar.natDegree_eq` on
`(isPRS_euclideanPRS …).isSimilar_gcd` (`deg gcd = deg R_k`), and the termination data
`hk0`/`hknz` come from `exists_last_euclideanPRS_nonzero`; the strict bound `hi` forces `2 ≤ k`. The
boundary `i = deg(A − a·D')` (`k = 1`, `A − a·D' ∣ D`) and `A − a·D' = 0` (the part-(i) `i = deg D`
regime) are excluded by `hi`. -/
theorem lazardRiobooTrager_isSimilar_gcd {K : Type*} [Field K] [IsAlgClosed K]
    (A D : K[X]) (hD : D.Separable) (hA : A.natDegree < D.natDegree) (a : K)
    (hi : (rtResultant A D).rootMultiplicity a < (A - C a * derivative D).natDegree) :
    IsSimilar
      ((lrtSubresultant A D ((rtResultant A D).rootMultiplicity a)).map
        (Polynomial.evalRingHom a))
      (gcd D (A - C a * derivative D)) := by
  set E := A - C a * derivative D with hE
  have hDne : D ≠ 0 := fun h => by simp [h] at hA
  -- `A − a·D'` has positive degree, hence is nonzero (from `hi`)
  have hEne : E ≠ 0 := fun h => by rw [h, natDegree_zero] at hi; exact Nat.not_lt_zero _ hi
  -- the multiplicity bridge: `i = deg gcd(D, E)`
  have hmul : (rtResultant A D).rootMultiplicity a = (gcd D E).natDegree :=
    rootMultiplicity_rtResultant_eq_natDegree_gcd A D hD hA a
  -- termination data for the Euclidean p.r.s. of `D, E`
  obtain ⟨k, hk1, hk0, hknz⟩ := exists_last_euclideanPRS_nonzero D E hEne
  -- the last nonzero p.r.s. element is similar to the gcd, so they share the degree
  have hsim : IsSimilar (euclideanPRS D E k) (gcd D E) :=
    (isPRS_euclideanPRS D E).isSimilar_gcd hk0 (fun j hj1 hjk => hknz j hj1 hjk)
  have hdeg : (euclideanPRS D E k).natDegree = (gcd D E).natDegree := hsim.natDegree_eq
  -- the strict bound forces `2 ≤ k`: at `k = 1` the last element is `E`, giving `deg E < deg E`
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · have hk1' : k = 1 := by omega
      subst hk1'
      rw [euclideanPRS_one] at hdeg
      rw [hmul, ← hdeg] at hi
      exact absurd hi (lt_irrefl _)
    · exact hk
  -- rewrite the algorithm index to the last-p.r.s. degree and apply part (ii)
  rw [hmul, ← hdeg]
  exact isSimilar_lrtSubresultant_eval_gcd A D a hDne hA hk2 hk0 hknz

open scoped Classical in
example {K : Type*} [Field K] [IsAlgClosed K]
    (A D : K[X]) (hD : D.Separable) (hA : A.natDegree < D.natDegree) (a : K)
    (hi : (rtResultant A D).rootMultiplicity a < (A - C a * derivative D).natDegree) :
    IsSimilar
      ((lrtSubresultant A D ((rtResultant A D).rootMultiplicity a)).map
        (Polynomial.evalRingHom a))
      (gcd D (A - C a * derivative D)) :=
  lazardRiobooTrager_isSimilar_gcd A D hD hA a hi

end DeepWiki.SymbolicIntegration
