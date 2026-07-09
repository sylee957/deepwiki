import DeepWiki.SymbolicIntegration.Engine.IntegratorAssembly
import DeepWiki.SymbolicIntegration.Engine.SplitFactorWfCorrect
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.SpecialNormalCoprime

/-! # Canonical reconstruction with the split conditions discharged (`CharZero`)

`canonicalReconstruction_of_charZero`: the canonical pieces recombine `⟦fₚ⟧ + ⟦b/dₛ⟧ + ⟦cₙ/dₙ⟧ = ⟦a/d⟧`
needing only `[CharZero]` + `GcdFFCorrect` + `d ≠ 0` — the split identity, factor-nonvanishing, and
coprimality (`hsplit`/`hdn`/`hds`/`hgdeg`/`hgne` of `canonicalReconstruction`) are *derived* from
`cSplitFactorFastG_isSplittingFactorizationGen` (the abstract split correctness) and
`isCoprime_of_isSpecial_isNormalSqfree` (special ⊥ normal). No split hypothesis remains. -/

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZG Polynomial Classical
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

omit [CRischField α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **Canonical reconstruction, split conditions discharged.** From `[CharZero]`, the fraction-free gcd
correctness `GcdFFCorrect`, and `d ≠ 0`, the split is a genuine coprime factorization (via
`cSplitFactorFastG_isSplittingFactorizationGen` + `isCoprime_of_isSpecial_isNormalSqfree`), so the
canonical pieces recombine to `⟦a/d⟧`. -/
theorem canonicalReconstruction_of_charZero (hgcd : GcdFFCorrect (α := α))
    (Dt a d : CPoly α) (hd : toPolyG d ≠ 0) :
    fieldFrac (crPoly Dt a d) [CField.one]
        + fieldFrac (crSpecNum Dt a d) (crSpecDen Dt a d)
        + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d)
      = fieldFrac a d := by
  -- the canonical special/normal denominators are the split output
  have hspd : crSpecDen Dt a d = (cSplitFactorFastG Dt d).2 := by
    simp only [crSpecDen, canonicalRepresentationFastG]
  have hnd : crNormDen Dt a d = (cSplitFactorFastG Dt d).1 := by
    simp only [crNormDen, canonicalRepresentationFastG]
  -- abstract split correctness (special/normal factorization)
  letI : Differential ((CFieldSpec.K α)[X]) := ⟨Differential.implicitDeriv (toPolyG Dt)⟩
  obtain ⟨hfac, hspec, hnorm⟩ := cSplitFactorFastG_isSplittingFactorizationGen hgcd Dt d hd
  -- factor nonvanishing
  have hds : toPolyG (crSpecDen Dt a d) ≠ 0 := by
    rw [hspd]; intro h; exact hd (by rw [hfac, h, zero_mul])
  have hdn : toPolyG (crNormDen Dt a d) ≠ 0 := by
    rw [hnd]; intro h; exact hd (by rw [hfac, h, mul_zero])
  have hsplit : toPolyG d = toPolyG (crSpecDen Dt a d) * toPolyG (crNormDen Dt a d) := by
    rw [hspd, hnd]; exact hfac
  -- special ⊥ normal coprimality
  have hcop : IsCoprime (toPolyG (crSpecDen Dt a d)) (toPolyG (crNormDen Dt a d)) := by
    rw [hspd, hnd]
    exact isCoprime_of_isSpecial_isNormalSqfree (by rw [← hspd]; exact hds) hspec hnorm
  -- gcd of the split parts is a unit ⇒ the computable gcd is a nonzero constant
  have hgu : IsUnit (gcd (toPolyG (crNormDen Dt a d)) (toPolyG (crSpecDen Dt a d))) :=
    gcd_isUnit_iff_isRelPrime.mpr (hcop.symm.isRelPrime)
  have hassoc : Associated (toPolyG (cgcdWf (crNormDen Dt a d) (crSpecDen Dt a d)).1)
      (gcd (toPolyG (crNormDen Dt a d)) (toPolyG (crSpecDen Dt a d))) := by
    have h1 : Associated (toPolyG (cgcdMonicWf (crNormDen Dt a d) (crSpecDen Dt a d)))
        (toPolyG (cgcdWf (crNormDen Dt a d) (crSpecDen Dt a d)).1) := by
      rw [cgcdMonicWf]; exact associated_toPolyG_cmonicG _
    exact h1.symm.trans (associated_toPolyG_cgcdMonicWf _ _)
  have hgu' : IsUnit (toPolyG (cgcdWf (crNormDen Dt a d) (crSpecDen Dt a d)).1) :=
    (Associated.isUnit_iff hassoc).mpr hgu
  have hgdeg : (toPolyG (cgcdWf (crNormDen Dt a d) (crSpecDen Dt a d)).1).natDegree = 0 :=
    natDegree_eq_zero_of_isUnit hgu'
  have hgne : toPolyG (cgcdWf (crNormDen Dt a d) (crSpecDen Dt a d)).1 ≠ 0 := hgu'.ne_zero
  exact canonicalReconstruction Dt a d hd hdn hds hsplit hgdeg hgne

omit [CRischField α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The canonical normal denominator is nonzero when `d ≠ 0`** (`[CharZero]` + `GcdFFCorrect`): `dₙ` is a
factor of the split `d = dₛ·dₙ`, so `d ≠ 0 ⇒ dₙ ≠ 0`. -/
theorem crNormDen_ne_zero_of_charZero (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPoly α)
    (hd : toPolyG d ≠ 0) : toPolyG (crNormDen Dt a d) ≠ 0 := by
  have hnd : crNormDen Dt a d = (cSplitFactorFastG Dt d).1 := by
    simp only [crNormDen, canonicalRepresentationFastG]
  letI : Differential ((CFieldSpec.K α)[X]) := ⟨Differential.implicitDeriv (toPolyG Dt)⟩
  obtain ⟨hfac, _, _⟩ := cSplitFactorFastG_isSplittingFactorizationGen hgcd Dt d hd
  rw [hnd]; intro h; exact hd (by rw [hfac, h, mul_zero])

omit [CRischField α] [Algebra ℚ (CFieldSpec.K α)] in
/-- **The canonical normal part is proper** (`[CharZero]` + `GcdFFCorrect`, `d ≠ 0`): `deg crNormNum <
deg crNormDen`. `crNormNum` is the second cofactor of `cextendedEuclideanSplitWf` over the normal denominator
`crNormDen = dₙ`, so `cextendedEuclideanSplitWf_snd_degree_lt` gives properness — from the split `d = dₛ·dₙ`
(`cSplitFactorFastG_isSplittingFactorizationGen`), the special⊥normal Bézout identity
(`isCoprime_of_isSpecial_isNormalSqfree`, `toPolyG_cbezoutOneWf`), and the remainder bound `deg (a mod d) <
deg d` (`cmodWf_length_lt`). The `degree` form holds unconditionally on `d ≠ 0` (incl. the trivial `crNormNum =
0` case, `⊥ < deg dₙ`); it is the never-done crNorm-properness cleanup target, the foundation of the Hermite
properness `hAD`. -/
theorem crNormNum_degree_lt_crNormDen (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPoly α)
    (hd : toPolyG d ≠ 0) :
    (toPolyG (crNormNum Dt a d)).degree < (toPolyG (crNormDen Dt a d)).degree := by
  letI : Differential ((CFieldSpec.K α)[X]) := ⟨Differential.implicitDeriv (toPolyG Dt)⟩
  obtain ⟨hfac, hspec, hnorm⟩ := cSplitFactorFastG_isSplittingFactorizationGen hgcd Dt d hd
  -- factor nonvanishing (from `d = dₛ·dₙ`) and the derived `cnormG ≠ []` guards
  have hds0 : toPolyG (cSplitFactorFastG Dt d).2 ≠ 0 := fun h => hd (by rw [hfac, h, zero_mul])
  have hdn0 : toPolyG (cSplitFactorFastG Dt d).1 ≠ 0 := fun h => hd (by rw [hfac, h, mul_zero])
  have hds : cnormG (cSplitFactorFastG Dt d).2 ≠ [] := fun h => hds0 ((cnormG_eq_nil_iff _).mp h)
  have hdn : cnormG (cSplitFactorFastG Dt d).1 ≠ [] := fun h => hdn0 ((cnormG_eq_nil_iff _).mp h)
  have hcnd : cnormG d ≠ [] := fun h => hd ((cnormG_eq_nil_iff d).mp h)
  -- special ⊥ normal ⇒ the split parts are coprime ⇒ the computable gcd is a nonzero constant ⇒ Bézout
  have hcop : IsCoprime (toPolyG (cSplitFactorFastG Dt d).2) (toPolyG (cSplitFactorFastG Dt d).1) :=
    isCoprime_of_isSpecial_isNormalSqfree hds0 hspec hnorm
  have hgu : IsUnit (gcd (toPolyG (cSplitFactorFastG Dt d).1) (toPolyG (cSplitFactorFastG Dt d).2)) :=
    gcd_isUnit_iff_isRelPrime.mpr (hcop.symm.isRelPrime)
  have hassoc : Associated (toPolyG (cgcdWf (cSplitFactorFastG Dt d).1 (cSplitFactorFastG Dt d).2).1)
      (gcd (toPolyG (cSplitFactorFastG Dt d).1) (toPolyG (cSplitFactorFastG Dt d).2)) := by
    have h1 : Associated (toPolyG (cgcdMonicWf (cSplitFactorFastG Dt d).1 (cSplitFactorFastG Dt d).2))
        (toPolyG (cgcdWf (cSplitFactorFastG Dt d).1 (cSplitFactorFastG Dt d).2).1) := by
      rw [cgcdMonicWf]; exact associated_toPolyG_cmonicG _
    exact h1.symm.trans (associated_toPolyG_cgcdMonicWf _ _)
  have hgu' : IsUnit (toPolyG (cgcdWf (cSplitFactorFastG Dt d).1 (cSplitFactorFastG Dt d).2).1) :=
    (Associated.isUnit_iff hassoc).mpr hgu
  have hgdeg : (toPolyG (cgcdWf (cSplitFactorFastG Dt d).1 (cSplitFactorFastG Dt d).2).1).natDegree = 0 :=
    natDegree_eq_zero_of_isUnit hgu'
  have hgne : toPolyG (cgcdWf (cSplitFactorFastG Dt d).1 (cSplitFactorFastG Dt d).2).1 ≠ 0 := hgu'.ne_zero
  have hbez : toPolyG (cbezoutOneWf (cSplitFactorFastG Dt d).1 (cSplitFactorFastG Dt d).2).1
        * toPolyG (cSplitFactorFastG Dt d).1
      + toPolyG (cbezoutOneWf (cSplitFactorFastG Dt d).1 (cSplitFactorFastG Dt d).2).2
        * toPolyG (cSplitFactorFastG Dt d).2 = 1 :=
    toPolyG_cbezoutOneWf (cSplitFactorFastG Dt d).1 (cSplitFactorFastG Dt d).2 hgdeg hgne
  -- the remainder `a mod d` is proper over `d`
  have hr : (toPolyG (cdivmodWf a d).2).degree < (toPolyG d).degree :=
    toPolyG_degree_lt_of_length_lt (cmodWf a d) d hcnd (cmodWf_length_lt a d hcnd)
  -- `crNormNum = (cextendedEuclideanSplitWf dₙ dₛ (a mod d) u w).2`, `crNormDen = dₙ`
  have hnn : crNormNum Dt a d = (cextendedEuclideanSplitWf (cSplitFactorFastG Dt d).1
      (cSplitFactorFastG Dt d).2 (cdivmodWf a d).2
      (cbezoutOneWf (cSplitFactorFastG Dt d).1 (cSplitFactorFastG Dt d).2).1
      (cbezoutOneWf (cSplitFactorFastG Dt d).1 (cSplitFactorFastG Dt d).2).2).2 := by
    simp only [crNormNum, canonicalRepresentationFastG]
  have hnd : crNormDen Dt a d = (cSplitFactorFastG Dt d).1 := by
    simp only [crNormDen, canonicalRepresentationFastG]
  rw [hnn, hnd]
  exact cextendedEuclideanSplitWf_snd_degree_lt (cSplitFactorFastG Dt d).1
    (cSplitFactorFastG Dt d).2 (cdivmodWf a d).2
    (cbezoutOneWf (cSplitFactorFastG Dt d).1 (cSplitFactorFastG Dt d).2).1
    (cbezoutOneWf (cSplitFactorFastG Dt d).1 (cSplitFactorFastG Dt d).2).2 d hds hdn hfac hbez hr

end DeepWiki.SymbolicIntegration
