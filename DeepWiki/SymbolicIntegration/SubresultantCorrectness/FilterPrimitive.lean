import DeepWiki.SymbolicIntegration.SubresultantCorrectness.ChainEndpoint
import DeepWiki.SymbolicIntegration.SubresultantCorrectness.DividedStep

/-! # Subresultant filter and primitive-part bridge

Connects singleton-filter hypotheses for `bsubresultantGcd` to the abstract LRT
subresultant endpoint, then strips bivariate content by `bprimitivePartX`. -/

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
theorem bsubresultantGcd_eq_of_filter_singleton (fuel j : ℕ) (P Q : BPoly) (w : BPoly)
    (hfil : (subresPRS fuel P Q).filter (fun R => decide (bdeg R = j ∧ ¬ bisZero R)) = [w]) :
    bsubresultantGcd fuel j P Q = w := by
  rw [bsubresultantGcd]
  exact getLast?_getD_filter_eq_of_singleton _ _ w [] hfil

/-- If the degree-`j` nonzero filter of `subresPRS fuel P Q` is `[G (m+2)]`, then
`toBPoly (bsubresultantGcd fuel j P Q) = toBPoly (G (m+2))`. -/
theorem toBPoly_bsubresultantGcd_eq_of_filter_singleton (fuel : ℕ) (P Q : BPoly) (G : ℕ → BPoly) (m : ℕ)
    (hfil : (subresPRS fuel P Q).filter
        (fun R => decide (bdeg R = (toBPoly (G (m + 2))).natDegree ∧ ¬ bisZero R)) = [G (m + 2)]) :
    toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree P Q) = toBPoly (G (m + 2)) := by
  rw [bsubresultantGcd_eq_of_filter_singleton fuel (toBPoly (G (m + 2))).natDegree P Q (G (m + 2)) hfil]

/-- Given the filter identity `hfilt`, `IsSimilar (lrtSubresultant A D j) (toBPoly (bsubresultantGcd
fuel j (G 0) (G 1)))` at `j = deg (toBPoly (G (m+2)))`. -/
theorem isSimilar_lrtSubresultant_bsubresultantGcd (fuel : ℕ) (A D : DensePoly ℚ) (G : ℕ → BPoly)
    (bt : ℕ → DensePoly ℚ) (s : ℕ → BPoly) (c : ℕ → DensePoly ℚ) (m : ℕ)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (toBPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (toBPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hchain : IsSubresPRSChainInput fuel G bt s c m)
    (hfilt : toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))
      = toBPoly (G (m + 2))) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) (toBPoly (G (m + 2))).natDegree)
      (toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))) := by
  rw [hfilt]
  exact isSimilar_lrtSubresultant_subresPRS_elt fuel A D G bt s c m hG0 hG1 hd0 hd1
    hchain

/-- As `isSimilar_lrtSubresultant_bsubresultantGcd`, but with the filter identity derived from the
singleton-filter hypothesis `hfil` instead of taken directly. -/
theorem isSimilar_lrtSubresultant_bsubresultantGcd_real (fuel : ℕ) (A D : DensePoly ℚ) (G : ℕ → BPoly)
    (bt : ℕ → DensePoly ℚ) (s : ℕ → BPoly) (c : ℕ → DensePoly ℚ) (m : ℕ)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (toBPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (toBPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hchain : IsSubresPRSChainInput fuel G bt s c m)
    (hfil : (subresPRS fuel (G 0) (G 1)).filter
        (fun R => decide (bdeg R = (toBPoly (G (m + 2))).natDegree ∧ ¬ bisZero R)) = [G (m + 2)]) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) (toBPoly (G (m + 2))).natDegree)
      (toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))) :=
  isSimilar_lrtSubresultant_bsubresultantGcd fuel A D G bt s c m hG0 hG1 hd0 hd1
    hchain
    (toBPoly_bsubresultantGcd_eq_of_filter_singleton fuel (G 0) (G 1) G m hfil)

/-! ### `bprimitivePartX` preserves similarity, and `lrtSubresultant ∼ lrtSubresultantCompute` -/

/-- The content stripped by `bprimitivePartX fuel p` is nonzero and divides every coefficient exactly. -/
structure IsPrimitivePartXInput (fuel : ℕ) (p : BPoly) : Prop where
  /-- The computed content is not boolean-zero. -/
  content_not_zero : ¬ cisZero (bcontentX fuel p) = true
  /-- The normalized content list is nonempty. -/
  content_cnorm_ne : cnorm (bcontentX fuel p) ≠ []
  /-- The computed content reads to a nonzero polynomial. -/
  content_toPoly_ne : toPoly (bcontentX fuel p) ≠ 0
  /-- The content divides every normalized `x`-coefficient exactly. -/
  exact_division : ∀ a ∈ bnorm p, toPoly (DensePoly.cmodWf a (bcontentX fuel p)) = 0

/-- `IsSimilar (toBPoly p) (toBPoly (bprimitivePartX fuel p))` under the content-exactness hypotheses. -/
theorem isSimilar_toBPoly_bprimitivePartX (fuel : ℕ) (p : BPoly)
    (hprim : IsPrimitivePartXInput fuel p) :
    IsSimilar (toBPoly p) (toBPoly (bprimitivePartX fuel p)) :=
  ⟨1, toPoly (bcontentX fuel p), one_ne_zero, hprim.content_toPoly_ne, by
    rw [map_one, one_mul, toBPoly_bprimitivePartX_exact fuel p hprim.content_not_zero
      hprim.content_cnorm_ne hprim.exact_division]⟩

/-- Given the endpoint hypotheses, the filter identity `hfilt`, and content-exactness of `bprimitivePartX`,
`IsSimilar (lrtSubresultant A D j) (toBPoly (lrtSubresultantCompute fuel j A D))`. -/
theorem isSimilar_lrtSubresultant_lrtSubresultantCompute (fuel : ℕ) (A D : DensePoly ℚ) (G : ℕ → BPoly)
    (bt : ℕ → DensePoly ℚ) (s : ℕ → BPoly) (c : ℕ → DensePoly ℚ) (m : ℕ)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (toBPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (toBPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hchain : IsSubresPRSChainInput fuel G bt s c m)
    (hfilt : toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))
      = toBPoly (G (m + 2)))
    (hprim : IsPrimitivePartXInput fuel
      (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) (toBPoly (G (m + 2))).natDegree)
      (toBPoly (lrtSubresultantCompute fuel (toBPoly (G (m + 2))).natDegree A D)) := by
  have hraw := isSimilar_lrtSubresultant_bsubresultantGcd fuel A D G bt s c m hG0 hG1 hd0 hd1
    hchain hfilt
  have hprimSim := isSimilar_toBPoly_bprimitivePartX fuel
    (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1)) hprim
  rw [lrtSubresultantCompute, ← hG0, ← hG1]
  exact hraw.trans hprimSim

end DeepWiki.SymbolicIntegration.Compute
