import DeepWiki.SymbolicIntegration.SubresultantCorrectness.DividedStep
import DeepWiki.Algebra.SubresultantPRS

/-! # Subresultant PRS chain endpoint

Packages the abstract subresultant-PRS telescope and its endpoint specialization for
the computable divided PRS chain. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### The abstract-PRS telescope over the computable chain -/

/-- Full chain telescope: for a computable PRS chain `G` satisfying the divided one-step hypotheses,
`IsSimilar (Sⱼ(DensePoly.toPoly (G 0), DensePoly.toPoly (G 1))) (Sⱼ(DensePoly.toPoly (G m), DensePoly.toPoly (G (m+1))))` at the elements'
own degrees. -/
theorem isSimilar_subresPRS_telescope (fuel : ℕ) (G : ℕ → GBPolyCore ℚ)
    (bt : ℕ → DensePoly ℚ) (s : ℕ → GBPolyCore ℚ) (c : ℕ → DensePoly ℚ) (j m : ℕ)
    (hsc : ∀ l < m, Polynomial.C (toPoly (c l)) * DensePoly.toPoly (G l)
        = DensePoly.toPoly (s l) * DensePoly.toPoly (G (l + 1)) + DensePoly.toPoly (GBPolyCore.gbpsremainderCore fuel (G l) (G (l + 1))))
    (hβcn : ∀ l < m, cnorm (bt l) ≠ [])
    (hdiv : ∀ l < m, ∀ a ∈ GBPolyCore.gbpsremainderCore fuel (G l) (G (l + 1)), toPoly (CPolyEuclidean.mod a (bt l)) = 0)
    (hG2 : ∀ l < m, G (l + 2) = bdivC (GBPolyCore.gbpsremainderCore fuel (G l) (G (l + 1))) (bt l))
    (hc0 : ∀ l < m, toPoly (c l) ≠ 0) (hβ0 : ∀ l < m, toPoly (bt l) ≠ 0)
    (hlc : ∀ l < m, (DensePoly.toPoly (G (l + 1))).coeff (DensePoly.toPoly (G (l + 1))).natDegree ≠ 0)
    (hcb : ∀ l < m, (DensePoly.toPoly (G (l + 2))).natDegree < (DensePoly.toPoly (G (l + 1))).natDegree)
    (hj : ∀ l < m, j < (DensePoly.toPoly (G (l + 2))).natDegree)
    (hQ : ∀ l < m, (DensePoly.toPoly (s l)).natDegree + (DensePoly.toPoly (G (l + 1))).natDegree
      ≤ (DensePoly.toPoly (G l)).natDegree) :
    IsSimilar
      (subresultant (DensePoly.toPoly (G 0)) (DensePoly.toPoly (G 1))
        (DensePoly.toPoly (G 0)).natDegree (DensePoly.toPoly (G 1)).natDegree j)
      (subresultant (DensePoly.toPoly (G m)) (DensePoly.toPoly (G (m + 1)))
        (DensePoly.toPoly (G m)).natDegree (DensePoly.toPoly (G (m + 1))).natDegree j) :=
  subresultant_prs_telescope (fun i => DensePoly.toPoly (G i)) (fun l => toPoly (c l))
    (fun l => toPoly (bt l)) (fun l => DensePoly.toPoly (s l)) j m
    hc0 hβ0 hlc hcb hj hQ
    (fun l hl => by
      have hrel := toBPoly_prs_rel fuel (G l) (G (l + 1)) (bt l) (s l) (c l)
        ⟨hsc l hl, hβcn l hl, hdiv l hl⟩
      rw [hG2 l hl]; exact hrel)

/-! ### The chain endpoint: `Sⱼ` is similar to the degree-`j` `subresPRS` element -/

/-- A divided subresultant PRS chain through index `m` with a regular endpoint. -/
structure IsSubresPRSChainInput (fuel : ℕ) (G : ℕ → GBPolyCore ℚ) (bt : ℕ → DensePoly ℚ)
    (s : ℕ → GBPolyCore ℚ) (c : ℕ → DensePoly ℚ) (m : ℕ) : Prop where
  /-- Each pseudo-remainder step is exact after β-division. -/
  exact_step : ∀ l ≤ m, IsBdivCExactStep fuel (G l) (G (l + 1)) (bt l) (s l) (c l)
  /-- Each next chain element is the β-divided pseudo-remainder. -/
  next_eq : ∀ l ≤ m, G (l + 2) = bdivC (GBPolyCore.gbpsremainderCore fuel (G l) (G (l + 1))) (bt l)
  /-- Each pseudo-division scalar reads to a nonzero polynomial. -/
  scale_toPoly_ne : ∀ l ≤ m, toPoly (c l) ≠ 0
  /-- Each β divisor reads to a nonzero polynomial. -/
  beta_toPoly_ne : ∀ l ≤ m, toPoly (bt l) ≠ 0
  /-- Each middle chain element has nonzero leading coefficient. -/
  leading_coeff_ne : ∀ l ≤ m, (DensePoly.toPoly (G (l + 1))).coeff (DensePoly.toPoly (G (l + 1))).natDegree ≠ 0
  /-- Degrees strictly drop along the divided PRS chain. -/
  degree_drop : ∀ l ≤ m, (DensePoly.toPoly (G (l + 2))).natDegree < (DensePoly.toPoly (G (l + 1))).natDegree
  /-- The endpoint degree lies below all earlier second-successor degrees. -/
  endpoint_degree_lt : ∀ l < m, (DensePoly.toPoly (G (m + 2))).natDegree < (DensePoly.toPoly (G (l + 2))).natDegree
  /-- Each pseudo-quotient satisfies the degree bound used by subresultant reduction. -/
  quotient_degree_le : ∀ l ≤ m, (DensePoly.toPoly (s l)).natDegree + (DensePoly.toPoly (G (l + 1))).natDegree
    ≤ (DensePoly.toPoly (G l)).natDegree
  /-- The endpoint chain element is nonzero after `DensePoly.toPoly`. -/
  endpoint_ne_zero : DensePoly.toPoly (G (m + 2)) ≠ 0

/-- At the regular index `j = deg (DensePoly.toPoly (G (m+2)))`,
`IsSimilar (Sⱼ(DensePoly.toPoly (G 0), DensePoly.toPoly (G 1))) (DensePoly.toPoly (G (m+2)))`. -/
theorem isSimilar_subresPRS_elt (fuel : ℕ) (G : ℕ → GBPolyCore ℚ)
    (bt : ℕ → DensePoly ℚ) (s : ℕ → GBPolyCore ℚ) (c : ℕ → DensePoly ℚ) (m : ℕ)
    (hchain : IsSubresPRSChainInput fuel G bt s c m) :
    IsSimilar
      (subresultant (DensePoly.toPoly (G 0)) (DensePoly.toPoly (G 1))
        (DensePoly.toPoly (G 0)).natDegree (DensePoly.toPoly (G 1)).natDegree (DensePoly.toPoly (G (m + 2))).natDegree)
      (DensePoly.toPoly (G (m + 2))) :=
  subresultant_prs_similar_elt (fun i => DensePoly.toPoly (G i)) (fun l => toPoly (c l))
    (fun l => toPoly (bt l)) (fun l => DensePoly.toPoly (s l)) m
    hchain.scale_toPoly_ne hchain.beta_toPoly_ne hchain.leading_coeff_ne hchain.degree_drop
    hchain.endpoint_degree_lt hchain.quotient_degree_le
    (fun l hl => by
      have hrel := toBPoly_prs_rel fuel (G l) (G (l + 1)) (bt l) (s l) (c l)
        (hchain.exact_step l hl)
      rw [hchain.next_eq l hl]; exact hrel)
    hchain.endpoint_ne_zero

/-! ### LRT endpoint: `lrtSubresultant` similar to the degree-`j` `subresPRS` element -/

/-- For the LRT chain (`G 0 = liftCtoBPoly D`, `G 1 = bArgAmtD' A D`) with the regular formal degrees,
`IsSimilar (lrtSubresultant A D (deg (G (m+2)))) (DensePoly.toPoly (G (m+2)))`. -/
theorem isSimilar_lrtSubresultant_subresPRS_elt (fuel : ℕ) (A D : DensePoly ℚ) (G : ℕ → GBPolyCore ℚ)
    (bt : ℕ → DensePoly ℚ) (s : ℕ → GBPolyCore ℚ) (c : ℕ → DensePoly ℚ) (m : ℕ)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (DensePoly.toPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (DensePoly.toPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hchain : IsSubresPRSChainInput fuel G bt s c m) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) (DensePoly.toPoly (G (m + 2))).natDegree)
      (DensePoly.toPoly (G (m + 2))) := by
  have hend := isSimilar_subresPRS_elt fuel G bt s c m hchain
  rw [hd0, hd1] at hend
  rw [lrtSubresultant_eq_subresultant_toBPoly, ← hG0, ← hG1]
  exact hend

end DeepWiki.SymbolicIntegration.Compute
