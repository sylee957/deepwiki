import DeepWiki.SymbolicIntegration.SubresultantCorrectness.ChainEndpoint
import DeepWiki.SymbolicIntegration.SubresultantCorrectness.DividedStep

/-! # Subresultant filter and primitive-part bridge

Connects singleton-filter hypotheses for `bsubresultantGcd` to the abstract LRT
subresultant endpoint, then strips bivariate content by `GBPolyCore.gbprimitivePartCore DensePoly.cgcdWfGcd`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### `bsubresultantGcd ∼ lrtSubresultant` (modulo the degree-`j` filter identity) -/

/-! #### The degree-`j` filter identity, structurally -/

/-- If `L.filter pred = [w]`, then `(L.filter pred).getLast?.getD d = w`. -/
theorem getLast?_getD_filter_eq_of_singleton {α : Type*} (L : List α) (pred : α → Bool) (w d : α)
    (hfil : L.filter pred = [w]) :
    (L.filter pred).getLast?.getD d = w := by
  rw [hfil, List.getLast?_singleton, Option.getD_some]

/-- If the degree-`j` nonzero filter of `subresPRS fuel P Q` is `[w]`, then `bsubresultantGcd fuel j P Q = w`. -/
theorem bsubresultantGcd_eq_of_filter_singleton (fuel j : ℕ) (P Q : GBPolyCore ℚ) (w : GBPolyCore ℚ)
    (hfil : (subresPRS fuel P Q).filter (fun R => decide (GBPolyCore.gbdegCore R = j ∧ ¬ GBPolyCore.gbisZeroCore R)) = [w]) :
    bsubresultantGcd fuel j P Q = w := by
  rw [bsubresultantGcd]
  exact getLast?_getD_filter_eq_of_singleton _ _ w [] hfil

/-- If the degree-`j` nonzero filter of `subresPRS fuel P Q` is `[G (m+2)]`, then
`GBPolyCore.toGBCoeffPoly (bsubresultantGcd fuel j P Q) = GBPolyCore.toGBCoeffPoly (G (m+2))`. -/
theorem toBPoly_bsubresultantGcd_eq_of_filter_singleton (fuel : ℕ) (P Q : GBPolyCore ℚ) (G : ℕ → GBPolyCore ℚ) (m : ℕ)
    (hfil : (subresPRS fuel P Q).filter
        (fun R => decide (GBPolyCore.gbdegCore R = (GBPolyCore.toGBCoeffPoly (G (m + 2))).natDegree ∧ ¬ GBPolyCore.gbisZeroCore R)) = [G (m + 2)]) :
    GBPolyCore.toGBCoeffPoly (bsubresultantGcd fuel (GBPolyCore.toGBCoeffPoly (G (m + 2))).natDegree P Q) = GBPolyCore.toGBCoeffPoly (G (m + 2)) := by
  rw [bsubresultantGcd_eq_of_filter_singleton fuel (GBPolyCore.toGBCoeffPoly (G (m + 2))).natDegree P Q (G (m + 2)) hfil]

/-- Given the filter identity `hfilt`, `IsSimilar (lrtSubresultant A D j) (GBPolyCore.toGBCoeffPoly (bsubresultantGcd
fuel j (G 0) (G 1)))` at `j = deg (GBPolyCore.toGBCoeffPoly (G (m+2)))`. -/
theorem isSimilar_lrtSubresultant_bsubresultantGcd (fuel : ℕ) (A D : DensePoly ℚ) (G : ℕ → GBPolyCore ℚ)
    (bt : ℕ → DensePoly ℚ) (s : ℕ → GBPolyCore ℚ) (c : ℕ → DensePoly ℚ) (m : ℕ)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (GBPolyCore.toGBCoeffPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (GBPolyCore.toGBCoeffPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hchain : IsSubresPRSChainInput fuel G bt s c m)
    (hfilt : GBPolyCore.toGBCoeffPoly (bsubresultantGcd fuel (GBPolyCore.toGBCoeffPoly (G (m + 2))).natDegree (G 0) (G 1))
      = GBPolyCore.toGBCoeffPoly (G (m + 2))) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) (GBPolyCore.toGBCoeffPoly (G (m + 2))).natDegree)
      (GBPolyCore.toGBCoeffPoly (bsubresultantGcd fuel (GBPolyCore.toGBCoeffPoly (G (m + 2))).natDegree (G 0) (G 1))) := by
  rw [hfilt]
  exact isSimilar_lrtSubresultant_subresPRS_elt fuel A D G bt s c m hG0 hG1 hd0 hd1
    hchain

/-- As `isSimilar_lrtSubresultant_bsubresultantGcd`, but with the filter identity derived from the
singleton-filter hypothesis `hfil` instead of taken directly. -/
theorem isSimilar_lrtSubresultant_bsubresultantGcd_real (fuel : ℕ) (A D : DensePoly ℚ) (G : ℕ → GBPolyCore ℚ)
    (bt : ℕ → DensePoly ℚ) (s : ℕ → GBPolyCore ℚ) (c : ℕ → DensePoly ℚ) (m : ℕ)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (GBPolyCore.toGBCoeffPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (GBPolyCore.toGBCoeffPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hchain : IsSubresPRSChainInput fuel G bt s c m)
    (hfil : (subresPRS fuel (G 0) (G 1)).filter
        (fun R => decide (GBPolyCore.gbdegCore R = (GBPolyCore.toGBCoeffPoly (G (m + 2))).natDegree ∧ ¬ GBPolyCore.gbisZeroCore R)) = [G (m + 2)]) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) (GBPolyCore.toGBCoeffPoly (G (m + 2))).natDegree)
      (GBPolyCore.toGBCoeffPoly (bsubresultantGcd fuel (GBPolyCore.toGBCoeffPoly (G (m + 2))).natDegree (G 0) (G 1))) :=
  isSimilar_lrtSubresultant_bsubresultantGcd fuel A D G bt s c m hG0 hG1 hd0 hd1
    hchain
    (toBPoly_bsubresultantGcd_eq_of_filter_singleton fuel (G 0) (G 1) G m hfil)

/-! ### `GBPolyCore.gbprimitivePartCore DensePoly.cgcdWfGcd` preserves similarity, and `lrtSubresultant ∼ lrtSubresultantCompute` -/

/-- The content stripped by `GBPolyCore.gbprimitivePartCore DensePoly.cgcdWfGcd p` is nonzero and divides every coefficient exactly. -/
structure IsPrimitivePartXInput (p : GBPolyCore ℚ) : Prop where
  /-- The computed content is not boolean-zero. -/
  content_not_zero : ¬ cisZero (GBPolyCore.gbcontentCore DensePoly.cgcdWfGcd p) = true
  /-- The normalized content list is nonempty. -/
  content_cnorm_ne : cnorm (GBPolyCore.gbcontentCore DensePoly.cgcdWfGcd p) ≠ []
  /-- The computed content reads to a nonzero polynomial. -/
  content_toPoly_ne : toPoly (GBPolyCore.gbcontentCore DensePoly.cgcdWfGcd p) ≠ 0
  /-- The content divides every normalized `x`-coefficient exactly. -/
  exact_division : ∀ a ∈ GBPolyCore.gbnormCore p, toPoly (DensePoly.cmodWf a (GBPolyCore.gbcontentCore DensePoly.cgcdWfGcd p)) = 0

/-- The `cgcdWfGcd` primitive part is similar to its input under exact content division. -/
theorem isSimilar_toGBCoeffPoly_gbprimitivePartCore_cgcdWfGcd (p : GBPolyCore ℚ)
    (hprim : IsPrimitivePartXInput p) :
    IsSimilar (GBPolyCore.toGBCoeffPoly p) (GBPolyCore.toGBCoeffPoly (GBPolyCore.gbprimitivePartCore DensePoly.cgcdWfGcd p)) :=
  ⟨1, toPoly (GBPolyCore.gbcontentCore DensePoly.cgcdWfGcd p), one_ne_zero, hprim.content_toPoly_ne, by
    rw [map_one, one_mul, toGBCoeffPoly_gbprimitivePartCore_cgcdWfGcd_exact p hprim.content_not_zero
      hprim.content_cnorm_ne hprim.exact_division]⟩

/-- Given the endpoint hypotheses, the filter identity `hfilt`, and content-exactness of `GBPolyCore.gbprimitivePartCore DensePoly.cgcdWfGcd`,
`IsSimilar (lrtSubresultant A D j) (GBPolyCore.toGBCoeffPoly (lrtSubresultantCompute fuel j A D))`. -/
theorem isSimilar_lrtSubresultant_lrtSubresultantCompute (fuel : ℕ) (A D : DensePoly ℚ) (G : ℕ → GBPolyCore ℚ)
    (bt : ℕ → DensePoly ℚ) (s : ℕ → GBPolyCore ℚ) (c : ℕ → DensePoly ℚ) (m : ℕ)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (GBPolyCore.toGBCoeffPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (GBPolyCore.toGBCoeffPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hchain : IsSubresPRSChainInput fuel G bt s c m)
    (hfilt : GBPolyCore.toGBCoeffPoly (bsubresultantGcd fuel (GBPolyCore.toGBCoeffPoly (G (m + 2))).natDegree (G 0) (G 1))
      = GBPolyCore.toGBCoeffPoly (G (m + 2)))
    (hprim : IsPrimitivePartXInput
      (bsubresultantGcd fuel (GBPolyCore.toGBCoeffPoly (G (m + 2))).natDegree (G 0) (G 1))) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) (GBPolyCore.toGBCoeffPoly (G (m + 2))).natDegree)
      (GBPolyCore.toGBCoeffPoly (lrtSubresultantCompute fuel (GBPolyCore.toGBCoeffPoly (G (m + 2))).natDegree A D)) := by
  have hraw := isSimilar_lrtSubresultant_bsubresultantGcd fuel A D G bt s c m hG0 hG1 hd0 hd1
    hchain hfilt
  have hprimSim := isSimilar_toGBCoeffPoly_gbprimitivePartCore_cgcdWfGcd
    (bsubresultantGcd fuel (GBPolyCore.toGBCoeffPoly (G (m + 2))).natDegree (G 0) (G 1)) hprim
  rw [lrtSubresultantCompute, ← hG0, ← hG1]
  exact hraw.trans hprimSim

end DeepWiki.SymbolicIntegration.Compute
