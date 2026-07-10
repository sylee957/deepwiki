import DeepWiki.SymbolicIntegration.Engine.IntegratorAssembly
import DeepWiki.SymbolicIntegration.Engine.SplitFactorWfCorrect
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.SpecialNormalCoprime

/-! # Canonical reconstruction with the split conditions discharged (`CharZero`)

`canonicalReconstruction_of_charZero`: the canonical pieces recombine `⟦fₚ⟧ + ⟦b/dₛ⟧ + ⟦cₙ/dₙ⟧ = ⟦a/d⟧`
needing only `[CharZero]` + `CgcdBCorrect cgcdFFCoreWf` + `d ≠ 0` — the split identity, factor-nonvanishing, and
coprimality (`hsplit`/`hdn`/`hds`/`hgdeg`/`hgne` of `canonicalReconstruction`) are *derived* from
`cSplitFactorFastG_isSplittingFactorizationGen` (the abstract split correctness) and
`isCoprime_of_isSpecial_isNormalSqfree` (special ⊥ normal). No split hypothesis remains. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac Polynomial Classical
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

omit [CRischField α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **Canonical reconstruction, split conditions discharged.** From `[CharZero]`, the fraction-free gcd
correctness `CgcdBCorrect cgcdFFCoreWf`, and `d ≠ 0`, the split is a genuine coprime factorization (via
`cSplitFactorFastG_isSplittingFactorizationGen` + `isCoprime_of_isSpecial_isNormalSqfree`), so the
canonical pieces recombine to `⟦a/d⟧`. -/
theorem canonicalReconstruction_of_charZero (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (Dt a d : DensePoly α) (hd : toPoly d ≠ 0) :
    fieldFrac (crPoly Dt a d) [CCommRing.one]
        + fieldFrac (crSpecNum Dt a d) (crSpecDen Dt a d)
        + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d)
      = fieldFrac a d := by
  -- the canonical special/normal denominators are the split output
  have hspd : crSpecDen Dt a d = (cSplitFactorFast Dt d).2 := by
    simp only [crSpecDen, canonicalRepresentationFast]
  have hnd : crNormDen Dt a d = (cSplitFactorFast Dt d).1 := by
    simp only [crNormDen, canonicalRepresentationFast]
  -- abstract split correctness (special/normal factorization)
  letI : Differential ((CFieldSpec.K α)[X]) := ⟨Differential.implicitDeriv (toPoly Dt)⟩
  obtain ⟨hfac, hspec, hnorm⟩ := cSplitFactorFastG_isSplittingFactorizationGen hgcd Dt d hd
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
  -- gcd of the split parts is a unit ⇒ the computable gcd is a nonzero constant
  have hgu : IsUnit (gcd (toPoly (crNormDen Dt a d)) (toPoly (crSpecDen Dt a d))) :=
    gcd_isUnit_iff_isRelPrime.mpr (hcop.symm.isRelPrime)
  have hassoc : Associated (toPoly (cgcdWf (crNormDen Dt a d) (crSpecDen Dt a d)).1)
      (gcd (toPoly (crNormDen Dt a d)) (toPoly (crSpecDen Dt a d))) := by
    have h1 : Associated (toPoly (cgcdMonicWf (crNormDen Dt a d) (crSpecDen Dt a d)))
        (toPoly (cgcdWf (crNormDen Dt a d) (crSpecDen Dt a d)).1) := by
      rw [cgcdMonicWf]; exact associated_toPolyG_cmonicG _
    exact h1.symm.trans (associated_toPolyG_cgcdMonicWf _ _)
  have hgu' : IsUnit (toPoly (cgcdWf (crNormDen Dt a d) (crSpecDen Dt a d)).1) :=
    (Associated.isUnit_iff hassoc).mpr hgu
  have hgdeg : (toPoly (cgcdWf (crNormDen Dt a d) (crSpecDen Dt a d)).1).natDegree = 0 :=
    natDegree_eq_zero_of_isUnit hgu'
  have hgne : toPoly (cgcdWf (crNormDen Dt a d) (crSpecDen Dt a d)).1 ≠ 0 := hgu'.ne_zero
  exact canonicalReconstruction Dt a d hd hdn hds hsplit hgdeg hgne

omit [CRischField α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The canonical normal denominator is nonzero when `d ≠ 0`** (`[CharZero]` + `CgcdBCorrect cgcdFFCoreWf`): `dₙ` is a
factor of the split `d = dₛ·dₙ`, so `d ≠ 0 ⇒ dₙ ≠ 0`. -/
theorem crNormDen_ne_zero_of_charZero (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α)
    (hd : toPoly d ≠ 0) : toPoly (crNormDen Dt a d) ≠ 0 := by
  have hnd : crNormDen Dt a d = (cSplitFactorFast Dt d).1 := by
    simp only [crNormDen, canonicalRepresentationFast]
  letI : Differential ((CFieldSpec.K α)[X]) := ⟨Differential.implicitDeriv (toPoly Dt)⟩
  obtain ⟨hfac, _, _⟩ := cSplitFactorFastG_isSplittingFactorizationGen hgcd Dt d hd
  rw [hnd]; intro h; exact hd (by rw [hfac, h, mul_zero])

omit [CRischField α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The canonical normal part is proper** (`[CharZero]` + `CgcdBCorrect cgcdFFCoreWf`, `d ≠ 0`): `deg crNormNum <
deg crNormDen`. `crNormNum` is the second cofactor of `CPoly.extendedEuclideanSplit` over the normal denominator
`crNormDen = dₙ`, so `extendedEuclideanSplit_snd_degree_lt` gives properness — from the split `d = dₛ·dₙ`
(`cSplitFactorFastG_isSplittingFactorizationGen`), the special⊥normal Bézout identity
(`isCoprime_of_isSpecial_isNormalSqfree`, `toPolyG_bezoutOne`), and the remainder bound `deg (a mod d) <
deg d` (`cmodWf_length_lt`). The `degree` form holds unconditionally on `d ≠ 0` (incl. the trivial `crNormNum =
0` case, `⊥ < deg dₙ`); it is the never-done crNorm-properness cleanup target, the foundation of the Hermite
properness `hAD`. -/
theorem crNormNum_degree_lt_crNormDen (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α)
    (hd : toPoly d ≠ 0) :
    (toPoly (crNormNum Dt a d)).degree < (toPoly (crNormDen Dt a d)).degree := by
  letI : Differential ((CFieldSpec.K α)[X]) := ⟨Differential.implicitDeriv (toPoly Dt)⟩
  obtain ⟨hfac, hspec, hnorm⟩ := cSplitFactorFastG_isSplittingFactorizationGen hgcd Dt d hd
  -- factor nonvanishing (from `d = dₛ·dₙ`) and the derived `cnorm ≠ []` guards
  have hds0 : toPoly (cSplitFactorFast Dt d).2 ≠ 0 := fun h => hd (by rw [hfac, h, zero_mul])
  have hdn0 : toPoly (cSplitFactorFast Dt d).1 ≠ 0 := fun h => hd (by rw [hfac, h, mul_zero])
  have hds : cnorm (cSplitFactorFast Dt d).2 ≠ [] := fun h => hds0 ((cnormG_eq_nil_iff _).mp h)
  have hdn : cnorm (cSplitFactorFast Dt d).1 ≠ [] := fun h => hdn0 ((cnormG_eq_nil_iff _).mp h)
  have hcnd : cnorm d ≠ [] := fun h => hd ((cnormG_eq_nil_iff d).mp h)
  -- special ⊥ normal ⇒ the split parts are coprime ⇒ the computable gcd is a nonzero constant ⇒ Bézout
  have hcop : IsCoprime (toPoly (cSplitFactorFast Dt d).2) (toPoly (cSplitFactorFast Dt d).1) :=
    isCoprime_of_isSpecial_isNormalSqfree hds0 hspec hnorm
  have hgu : IsUnit (gcd (toPoly (cSplitFactorFast Dt d).1) (toPoly (cSplitFactorFast Dt d).2)) :=
    gcd_isUnit_iff_isRelPrime.mpr (hcop.symm.isRelPrime)
  have hassoc : Associated (toPoly (cgcdWf (cSplitFactorFast Dt d).1 (cSplitFactorFast Dt d).2).1)
      (gcd (toPoly (cSplitFactorFast Dt d).1) (toPoly (cSplitFactorFast Dt d).2)) := by
    have h1 : Associated (toPoly (cgcdMonicWf (cSplitFactorFast Dt d).1 (cSplitFactorFast Dt d).2))
        (toPoly (cgcdWf (cSplitFactorFast Dt d).1 (cSplitFactorFast Dt d).2).1) := by
      rw [cgcdMonicWf]; exact associated_toPolyG_cmonicG _
    exact h1.symm.trans (associated_toPolyG_cgcdMonicWf _ _)
  have hgu' : IsUnit (toPoly (cgcdWf (cSplitFactorFast Dt d).1 (cSplitFactorFast Dt d).2).1) :=
    (Associated.isUnit_iff hassoc).mpr hgu
  have hgdeg : (toPoly (cgcdWf (cSplitFactorFast Dt d).1 (cSplitFactorFast Dt d).2).1).natDegree = 0 :=
    natDegree_eq_zero_of_isUnit hgu'
  have hgne : toPoly (cgcdWf (cSplitFactorFast Dt d).1 (cSplitFactorFast Dt d).2).1 ≠ 0 := hgu'.ne_zero
  have hbez : toPoly (CPoly.bezoutOne (cSplitFactorFast Dt d).1 (cSplitFactorFast Dt d).2).1
        * toPoly (cSplitFactorFast Dt d).1
      + toPoly (CPoly.bezoutOne (cSplitFactorFast Dt d).1 (cSplitFactorFast Dt d).2).2
        * toPoly (cSplitFactorFast Dt d).2 = 1 :=
    toPolyG_bezoutOne (cSplitFactorFast Dt d).1 (cSplitFactorFast Dt d).2 hgdeg hgne
  -- the remainder `a mod d` is proper over `d`
  have hr : (toPoly (cdivmodWf a d).2).degree < (toPoly d).degree :=
    toPolyG_degree_lt_of_length_lt (cmodWf a d) d hcnd (cmodWf_length_lt a d hcnd)
  -- `crNormNum = (CPoly.extendedEuclideanSplit dₙ dₛ (a mod d) u w).2`, `crNormDen = dₙ`
  have hnn : crNormNum Dt a d = (CPoly.extendedEuclideanSplit (cSplitFactorFast Dt d).1
      (cSplitFactorFast Dt d).2 (cdivmodWf a d).2
      (CPoly.bezoutOne (cSplitFactorFast Dt d).1 (cSplitFactorFast Dt d).2).1
      (CPoly.bezoutOne (cSplitFactorFast Dt d).1 (cSplitFactorFast Dt d).2).2).2 := by
    simp only [crNormNum, canonicalRepresentationFast]
  have hnd : crNormDen Dt a d = (cSplitFactorFast Dt d).1 := by
    simp only [crNormDen, canonicalRepresentationFast]
  rw [hnn, hnd]
  exact extendedEuclideanSplit_snd_degree_lt (cSplitFactorFast Dt d).1
    (cSplitFactorFast Dt d).2 (cdivmodWf a d).2
    (CPoly.bezoutOne (cSplitFactorFast Dt d).1 (cSplitFactorFast Dt d).2).1
    (CPoly.bezoutOne (cSplitFactorFast Dt d).1 (cSplitFactorFast Dt d).2).2 d hds hdn hfac hbez hr

end DeepWiki.SymbolicIntegration
