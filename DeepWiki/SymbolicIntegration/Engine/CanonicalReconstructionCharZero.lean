import DeepWiki.SymbolicIntegration.Engine.IntegratorAssembly
import DeepWiki.SymbolicIntegration.Engine.SplitFactorWfCorrect
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.SpecialNormalCoprime

/-! # Canonical reconstruction with the split conditions discharged (`CharZero`)

`canonicalReconstruction_of_charZero`: the canonical pieces recombine `⟦fₚ⟧ + ⟦b/dₛ⟧ + ⟦cₙ/dₙ⟧ = ⟦a/d⟧`
needing only `[CharZero]` + `LawfulCPolyGcd` + `d ≠ 0` — the split identity, factor-nonvanishing, and
coprimality (`hsplit`/`hdn`/`hds`/`hgdeg`/`hgne` of `canonicalReconstruction`) are *derived* from
`CPoly.splitFactor_isSplittingFactorizationGen` (the abstract split correctness) and
`isCoprime_of_isSpecial_isNormalSqfree` (special ⊥ normal). No split hypothesis remains. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac Polynomial Classical
open scoped Differential

universe u v

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CPolyGcd DensePoly α] [LawfulCPolyGcd.{u,v} DensePoly α]
  [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

omit [CRischField α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **Canonical reconstruction, split conditions discharged.** From `[CharZero]`, lawful selected gcd
correctness, and `d ≠ 0`, the split is a genuine coprime factorization (via
`CPoly.splitFactor_isSplittingFactorizationGen` + `isCoprime_of_isSpecial_isNormalSqfree`), so the
canonical pieces recombine to `⟦a/d⟧`. -/
theorem canonicalReconstruction_of_charZero (Dt a d : DensePoly α) (hd : toPoly d ≠ 0) :
    fieldFrac (crPoly Dt a d) [CCommRing.one]
        + fieldFrac (crSpecNum Dt a d) (crSpecDen Dt a d)
        + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d)
      = fieldFrac a d := by
  -- the canonical special/normal denominators are the split output
  have hspd : crSpecDen Dt a d = (CPoly.splitFactor Dt d).2 := by
    simp only [crSpecDen, canonicalRepresentationFast]
  have hnd : crNormDen Dt a d = (CPoly.splitFactor Dt d).1 := by
    simp only [crNormDen, canonicalRepresentationFast]
  -- abstract split correctness (special/normal factorization)
  letI : Differential ((CFieldSpec.K α)[X]) := ⟨Differential.implicitDeriv (toPoly Dt)⟩
  obtain ⟨hfac, hspec, hnorm⟩ := CPoly.splitFactor_isSplittingFactorizationGen Dt d hd
  -- factor nonvanishing
  have hds : toPoly (crSpecDen Dt a d) ≠ 0 := by
    rw [hspd]; intro h; exact hd (by rw [hfac, h, zero_mul])
  have hdn : toPoly (crNormDen Dt a d) ≠ 0 := by
    rw [hnd]; intro h; exact hd (by rw [hfac, h, mul_zero])
  have hsplit : toPoly d = toPoly (crSpecDen Dt a d) * toPoly (crNormDen Dt a d) := by
    rw [hspd, hnd]; exact hfac
  -- special ⊥ normal coprimality
  have hcop : IsCoprime (toPoly (crSpecDen Dt a d)) (toPoly (crNormDen Dt a d)) := by
    rw [hspd, hnd]
    exact isCoprime_of_isSpecial_isNormalSqfree (by rw [← hspd]; exact hds) hspec hnorm
  -- coprime split parts make the selected extended gcd a nonzero constant
  have hgu' : IsUnit (toPoly (CPolyEuclidean.gcdExt (crNormDen Dt a d) (crSpecDen Dt a d)).1) := by
    simpa only [toPoly_list_eq] using
      (CPolyEuclidean.gcdExt_isUnit_of_isCoprime (P := DensePoly)
        (crNormDen Dt a d) (crSpecDen Dt a d)
        (by simpa only [toPoly_list_eq] using hcop.symm))
  have hgdeg : (toPoly (CPolyEuclidean.gcdExt (crNormDen Dt a d) (crSpecDen Dt a d)).1).natDegree = 0 :=
    natDegree_eq_zero_of_isUnit hgu'
  have hgne : toPoly (CPolyEuclidean.gcdExt (crNormDen Dt a d) (crSpecDen Dt a d)).1 ≠ 0 := hgu'.ne_zero
  exact canonicalReconstruction Dt a d hd hdn hds hsplit hgdeg hgne

omit [CRischField α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The canonical normal denominator is nonzero when `d ≠ 0`** (`[CharZero]` + lawful selected gcd): `dₙ` is a
factor of the split `d = dₛ·dₙ`, so `d ≠ 0 ⇒ dₙ ≠ 0`. -/
theorem crNormDen_ne_zero_of_charZero (Dt a d : DensePoly α)
    (hd : toPoly d ≠ 0) : toPoly (crNormDen Dt a d) ≠ 0 := by
  have hnd : crNormDen Dt a d = (CPoly.splitFactor Dt d).1 := by
    simp only [crNormDen, canonicalRepresentationFast]
  letI : Differential ((CFieldSpec.K α)[X]) := ⟨Differential.implicitDeriv (toPoly Dt)⟩
  obtain ⟨hfac, _, _⟩ := CPoly.splitFactor_isSplittingFactorizationGen Dt d hd
  rw [hnd]; intro h; exact hd (by rw [hfac, h, mul_zero])

omit [CRischField α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The canonical normal part is proper** (`[CharZero]` + lawful selected gcd, `d ≠ 0`): `deg crNormNum <
deg crNormDen`. `crNormNum` is the second cofactor of `CPoly.extendedEuclideanSplit` over the normal denominator
`crNormDen = dₙ`, so `extendedEuclideanSplit_snd_degree_lt` gives properness — from the split `d = dₛ·dₙ`
(`CPoly.splitFactor_isSplittingFactorizationGen`), the special⊥normal Bézout identity
(`isCoprime_of_isSpecial_isNormalSqfree`, `toPolyG_bezoutOne`), and the remainder bound `deg (a mod d) <
deg d` (selected-remainder shortening). The `degree` form holds unconditionally on `d ≠ 0` (incl. the trivial `crNormNum =
0` case, `⊥ < deg dₙ`); it is the never-done crNorm-properness cleanup target, the foundation of the Hermite
properness `hAD`. -/
theorem crNormNum_degree_lt_crNormDen (Dt a d : DensePoly α)
    (hd : toPoly d ≠ 0) :
    (toPoly (crNormNum Dt a d)).degree < (toPoly (crNormDen Dt a d)).degree := by
  letI : Differential ((CFieldSpec.K α)[X]) := ⟨Differential.implicitDeriv (toPoly Dt)⟩
  obtain ⟨hfac, hspec, hnorm⟩ := CPoly.splitFactor_isSplittingFactorizationGen Dt d hd
  -- factor nonvanishing (from `d = dₛ·dₙ`) and the derived `cnorm ≠ []` guards
  have hds0 : toPoly (CPoly.splitFactor Dt d).2 ≠ 0 := fun h => hd (by rw [hfac, h, zero_mul])
  have hdn0 : toPoly (CPoly.splitFactor Dt d).1 ≠ 0 := fun h => hd (by rw [hfac, h, mul_zero])
  have hds : cnorm (CPoly.splitFactor Dt d).2 ≠ [] := fun h => hds0 ((cnormG_eq_nil_iff _).mp h)
  have hdn : cnorm (CPoly.splitFactor Dt d).1 ≠ [] := fun h => hdn0 ((cnormG_eq_nil_iff _).mp h)
  -- special ⊥ normal ⇒ the split parts are coprime ⇒ the computable gcd is a nonzero constant ⇒ Bézout
  have hcop : IsCoprime (toPoly (CPoly.splitFactor Dt d).2) (toPoly (CPoly.splitFactor Dt d).1) :=
    isCoprime_of_isSpecial_isNormalSqfree hds0 hspec hnorm
  have hgu' : IsUnit (toPoly (CPolyEuclidean.gcdExt (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2).1) := by
    simpa only [toPoly_list_eq] using
      (CPolyEuclidean.gcdExt_isUnit_of_isCoprime (P := DensePoly)
        (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2
        (by simpa only [toPoly_list_eq] using hcop.symm))
  have hgdeg : (toPoly (CPolyEuclidean.gcdExt (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2).1).natDegree = 0 :=
    natDegree_eq_zero_of_isUnit hgu'
  have hgne : toPoly (CPolyEuclidean.gcdExt (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2).1 ≠ 0 := hgu'.ne_zero
  have hbez : toPoly (CPoly.bezoutOne (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2).1
        * toPoly (CPoly.splitFactor Dt d).1
      + toPoly (CPoly.bezoutOne (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2).2
        * toPoly (CPoly.splitFactor Dt d).2 = 1 :=
    toPolyG_bezoutOne (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2 hgdeg hgne
  -- the remainder `a mod d` is proper over `d`
  have hr : (toPoly (CPolyEuclidean.divmod a d).2).degree < (toPoly d).degree := by
    simpa only [CPolyEuclidean.mod, toPoly_list_eq] using
      (LawfulCPolyEuclidean.mod_degree_lt a d (by simpa only [toPoly_list_eq] using hd))
  -- `crNormNum = (CPoly.extendedEuclideanSplit dₙ dₛ (a mod d) u w).2`, `crNormDen = dₙ`
  have hnn : crNormNum Dt a d = (CPoly.extendedEuclideanSplit (CPoly.splitFactor Dt d).1
      (CPoly.splitFactor Dt d).2 (CPolyEuclidean.divmod a d).2
      (CPoly.bezoutOne (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2).1
      (CPoly.bezoutOne (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2).2).2 := by
    simp only [crNormNum, canonicalRepresentationFast]
  have hnd : crNormDen Dt a d = (CPoly.splitFactor Dt d).1 := by
    simp only [crNormDen, canonicalRepresentationFast]
  rw [hnn, hnd]
  exact extendedEuclideanSplit_snd_degree_lt (CPoly.splitFactor Dt d).1
    (CPoly.splitFactor Dt d).2 (CPolyEuclidean.divmod a d).2
    (CPoly.bezoutOne (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2).1
    (CPoly.bezoutOne (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2).2 d hds hdn hfac hbez hr

omit [CRischField α] [Algebra ℚ (CFieldSpec.K α)] [CPolyGcd DensePoly α]
  [LawfulCPolyGcd.{u, v} DensePoly α] in
/-- A lawful selected split factorization preserves nonzeroness of the canonical normal denominator. -/
theorem crNormDen_ne_zero_of_lawfulSplit [CPolySplitFactor DensePoly α]
    [LawfulCPolySplitFactor DensePoly α] (Dt a d : DensePoly α)
    (hd : toPoly d ≠ 0) : toPoly (crNormDen Dt a d) ≠ 0 := by
  have hsplit : @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (toPoly Dt)⟩
      (toPoly d) (toPoly (CPoly.splitFactor Dt d).2) (toPoly (CPoly.splitFactor Dt d).1) := by
    convert LawfulCPolySplitFactor.compute_isSplittingFactorizationGen' Dt d
      (by simpa only [toPoly_list_eq] using hd) using 1 <;> simp only [toPoly_list_eq]
  obtain ⟨hfac, _, _⟩ := hsplit
  have hnd : crNormDen Dt a d = (CPoly.splitFactor Dt d).1 := by
    simp only [crNormDen, canonicalRepresentationFast]
  rw [hnd]
  intro h
  exact hd (by rw [hfac, h, mul_zero])

omit [CRischField α] [Algebra ℚ (CFieldSpec.K α)] [CPolyGcd DensePoly α]
  [LawfulCPolyGcd.{u, v} DensePoly α] in
/-- A lawful selected split factorization makes the canonical normal fraction proper. -/
theorem crNormNum_degree_lt_crNormDen_of_lawfulSplit [CPolySplitFactor DensePoly α]
    [LawfulCPolySplitFactor DensePoly α] (Dt a d : DensePoly α)
    (hd : toPoly d ≠ 0) :
    (toPoly (crNormNum Dt a d)).degree < (toPoly (crNormDen Dt a d)).degree := by
  letI : Differential ((CFieldSpec.K α)[X]) := ⟨Differential.implicitDeriv (toPoly Dt)⟩
  have hsplit : @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (toPoly Dt)⟩
      (toPoly d) (toPoly (CPoly.splitFactor Dt d).2) (toPoly (CPoly.splitFactor Dt d).1) := by
    convert LawfulCPolySplitFactor.compute_isSplittingFactorizationGen' Dt d
      (by simpa only [toPoly_list_eq] using hd) using 1 <;> simp only [toPoly_list_eq]
  obtain ⟨hfac, hspec, hnorm⟩ := hsplit
  have hds0 : toPoly (CPoly.splitFactor Dt d).2 ≠ 0 := fun h => hd (by rw [hfac, h, zero_mul])
  have hdn0 : toPoly (CPoly.splitFactor Dt d).1 ≠ 0 := fun h => hd (by rw [hfac, h, mul_zero])
  have hds : cnorm (CPoly.splitFactor Dt d).2 ≠ [] := fun h => hds0 ((cnormG_eq_nil_iff _).mp h)
  have hdn : cnorm (CPoly.splitFactor Dt d).1 ≠ [] := fun h => hdn0 ((cnormG_eq_nil_iff _).mp h)
  have hcop : IsCoprime (toPoly (CPoly.splitFactor Dt d).2) (toPoly (CPoly.splitFactor Dt d).1) :=
    isCoprime_of_isSpecial_isNormalSqfree hds0 hspec hnorm
  have hgu' : IsUnit (toPoly (CPolyEuclidean.gcdExt (CPoly.splitFactor Dt d).1
      (CPoly.splitFactor Dt d).2).1) := by
    simpa only [toPoly_list_eq] using
      (CPolyEuclidean.gcdExt_isUnit_of_isCoprime (P := DensePoly)
        (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2
        (by simpa only [toPoly_list_eq] using hcop.symm))
  have hgdeg : (toPoly (CPolyEuclidean.gcdExt (CPoly.splitFactor Dt d).1
      (CPoly.splitFactor Dt d).2).1).natDegree = 0 := natDegree_eq_zero_of_isUnit hgu'
  have hgne : toPoly (CPolyEuclidean.gcdExt (CPoly.splitFactor Dt d).1
      (CPoly.splitFactor Dt d).2).1 ≠ 0 := hgu'.ne_zero
  have hbez : toPoly (CPoly.bezoutOne (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2).1
        * toPoly (CPoly.splitFactor Dt d).1
      + toPoly (CPoly.bezoutOne (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2).2
        * toPoly (CPoly.splitFactor Dt d).2 = 1 :=
    toPolyG_bezoutOne (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2 hgdeg hgne
  have hr : (toPoly (CPolyEuclidean.divmod a d).2).degree < (toPoly d).degree := by
    simpa only [CPolyEuclidean.mod, toPoly_list_eq] using
      (LawfulCPolyEuclidean.mod_degree_lt a d (by simpa only [toPoly_list_eq] using hd))
  have hnn : crNormNum Dt a d = (CPoly.extendedEuclideanSplit (CPoly.splitFactor Dt d).1
      (CPoly.splitFactor Dt d).2 (CPolyEuclidean.divmod a d).2
      (CPoly.bezoutOne (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2).1
      (CPoly.bezoutOne (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2).2).2 := by
    simp only [crNormNum, canonicalRepresentationFast]
  have hnd : crNormDen Dt a d = (CPoly.splitFactor Dt d).1 := by
    simp only [crNormDen, canonicalRepresentationFast]
  rw [hnn, hnd]
  exact extendedEuclideanSplit_snd_degree_lt (CPoly.splitFactor Dt d).1
    (CPoly.splitFactor Dt d).2 (CPolyEuclidean.divmod a d).2
    (CPoly.bezoutOne (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2).1
    (CPoly.bezoutOne (CPoly.splitFactor Dt d).1 (CPoly.splitFactor Dt d).2).2 d hds hdn hfac hbez hr

end DeepWiki.SymbolicIntegration
