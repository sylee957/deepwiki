import DeepWiki.SymbolicIntegration.Engine.RischDE.Completeness
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded

/-! # RDE normal-denominator completeness

Completeness bridges for the normal-denominator step of the Wf Risch differential equation solver. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

universe u v

/-! ## Engine guard -/

section WfEngineLayer

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CPolyGcd DensePoly α]

/-- The multiplicity factor `h = gcd(eₙ,eₙ')/gcd(p,p')`. -/
def rdeNormHWf (Dt : DensePoly α) (fden gden : DensePoly α) : DensePoly α :=
  let en := (CPoly.splitFactor Dt gden).1
  let dn := (CPoly.splitFactor Dt fden).1
  let p := CPolyGcd.compute dn en
  CPolyEuclidean.div (CPolyGcd.compute en (DensePoly.cderiv en))
    (CPolyGcd.compute p (DensePoly.cderiv p))

/-- The dividend `dₙ·h²`. -/
def rdeNormDnh2Wf (Dt : DensePoly α) (fden gden : DensePoly α) : DensePoly α :=
  let dn := (CPoly.splitFactor Dt fden).1
  let h := rdeNormHWf Dt fden gden
  DensePoly.cmul (DensePoly.cmul dn h) h

omit [CFieldSpec α] in
/-- The normal-denominator step's `isSome` is exactly its `CPolyEuclidean.dvd` divisibility guard. -/
theorem cRdeNormalDenominatorG_isSome_iff (Dt : DensePoly α) (fnum fden gnum gden : DensePoly α) :
    (DensePoly.cRdeNormalDenominator Dt fnum fden gnum gden).isSome = true ↔
      CPolyEuclidean.dvd (CPoly.splitFactor Dt gden).1 (rdeNormDnh2Wf Dt fden gden) = true := by
  rw [DensePoly.cRdeNormalDenominator]
  simp only [rdeNormDnh2Wf, rdeNormHWf]
  split <;> simp_all

omit [CDiffField α] [CPolyGcd DensePoly α] in
/-- Mathematical divisibility `toPoly q ∣ toPoly p` forces `CPolyEuclidean.dvd q p = true`. -/
theorem dvd_eq_true_of_toPoly_dvd (q p : DensePoly α) (hq0 : DensePoly.cnorm q ≠ [])
    (hdvd : toPoly q ∣ toPoly p) :
    CPolyEuclidean.dvd q p = true := by
  have hqDense : DensePoly.toPoly q ≠ 0 :=
    fun h => hq0 ((DensePoly.cnormG_eq_nil_iff q).mpr h)
  have hq0' : CPoly.toPoly q ≠ 0 := by
    simpa only [toPoly_list_eq] using hqDense
  have hdvd' : CPoly.toPoly q ∣ CPoly.toPoly p := by
    simpa only [toPoly_list_eq] using hdvd
  by_cases h : CPolyEuclidean.dvd q p = true
  · exact h
  · have hfalse : CPolyEuclidean.dvd q p = false := Bool.eq_false_iff.mpr h
    exact False.elim ((CPolyEuclidean.not_toPoly_dvd_of_dvd_eq_false q p hq0' hfalse) hdvd')

/-- The normal-denominator step returns `some` from the mathematical divisibility `eₙ ∣ dₙh²`. -/
theorem cRdeNormalDenominatorG_isSome_of_dvd (Dt : DensePoly α)
    (fnum fden gnum gden : DensePoly α)
    (hen0 : DensePoly.cnorm (CPoly.splitFactor Dt gden).1 ≠ [])
    (hdvd : toPoly (CPoly.splitFactor Dt gden).1 ∣ toPoly (rdeNormDnh2Wf Dt fden gden)) :
    (DensePoly.cRdeNormalDenominator Dt fnum fden gnum gden).isSome = true :=
  (cRdeNormalDenominatorG_isSome_iff Dt fnum fden gnum gden).mpr
    (dvd_eq_true_of_toPoly_dvd _ _ hen0 hdvd)

end WfEngineLayer


/-! ## Divisibility residual -/

section DivisibilityResidualWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CPolyGcd DensePoly α]
  [CRischField α]

/-- `RdeNormalDivisibilityResidualWf` supplies `eₙ ∣ dₙh²` and nonzero `eₙ`. -/
structure RdeNormalDivisibilityResidualWf (Dt fnum fden gnum gden : DensePoly α) : Prop where
  /-- A polynomial solution forces `eₙ ∣ dₙh²`. -/
  hdvd : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    toPoly (CPoly.splitFactor Dt gden).1 ∣ toPoly (rdeNormDnh2Wf Dt fden gden)
  /-- The normal part `eₙ` of `gden` is nonzero. -/
  hen0 : DensePoly.cnorm (CPoly.splitFactor Dt gden).1 ≠ []

omit [CRischField α] in
/-- `hnorm` from the divisibility residual: the normal-denominator step preserves solvability. -/
theorem hnormWf_of_divisibilityResidualWf (Dt fnum fden gnum gden : DensePoly α)
    (hres : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominator Dt fnum fden gnum gden).isSome = true := by
  intro hsol
  exact cRdeNormalDenominatorG_isSome_of_dvd Dt fnum fden gnum gden
    hres.hen0 (hres.hdvd hsol)

omit [CDiffFieldSpec α] [CRischField α] in
/-- `eₙ ∣ dₙ` implies `eₙ ∣ dₙh²`. -/
theorem dvd_dnh2Wf_of_en_dvd_dn (Dt : DensePoly α) (fden gden : DensePoly α)
    (hdvd : toPoly (CPoly.splitFactor Dt gden).1 ∣ toPoly (CPoly.splitFactor Dt fden).1) :
    toPoly (CPoly.splitFactor Dt gden).1 ∣ toPoly (rdeNormDnh2Wf Dt fden gden) := by
  rw [rdeNormDnh2Wf]
  simp only [denote]
  exact (hdvd.mul_right _).mul_right _

omit [CRischField α] in
/-- The `hdvd` clause holds unconditionally when `eₙ ∣ dₙ`. -/
theorem hdvdWf_free_of_en_dvd_dn (Dt fnum fden gnum gden : DensePoly α)
    (hdvd : toPoly (CPoly.splitFactor Dt gden).1 ∣ toPoly (CPoly.splitFactor Dt fden).1) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      toPoly (CPoly.splitFactor Dt gden).1 ∣ toPoly (rdeNormDnh2Wf Dt fden gden) :=
  fun _ => dvd_dnh2Wf_of_en_dvd_dn Dt fden gden hdvd

end DivisibilityResidualWf

/-! ## Clearing divisibility clauses -/

section ClearingDivisibility

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CPolyGcd DensePoly β]

/-- If `fden ∣ dₙ·h0`, then `fden` divides the `B`-numerator `dₙh·fnum - dₙ·Dh·fden`. -/
theorem hdvdB_of_dvd_wf (Dt : DensePoly β) (fnum fden h0 : DensePoly β)
    (hdvd : toPoly fden ∣ toPoly (DensePoly.cmul (CPoly.splitFactor Dt fden).1 h0)) :
    toPoly fden ∣ toPoly (DensePoly.csub
        (DensePoly.cmul (DensePoly.cmul (CPoly.splitFactor Dt fden).1 h0) fnum)
        (DensePoly.cmul (DensePoly.cmul (CPoly.splitFactor Dt fden).1
          (CPolyEngine.monomialDeriv Dt h0)) fden)) := by
  simp only [denote] at hdvd ⊢
  apply dvd_sub
  · exact hdvd.mul_right _
  · exact Dvd.intro_left _ rfl

/-- If `gden ∣ dₙ·h0·h0`, then `gden` divides the `C`-numerator `dₙh²·gnum`. -/
theorem hdvdC_of_dvd_wf (Dt : DensePoly β) (gnum fden gden h0 : DensePoly β)
    (hdvd : toPoly gden ∣ toPoly (DensePoly.cmul
      (DensePoly.cmul (CPoly.splitFactor Dt fden).1 h0) h0)) :
    toPoly gden ∣ toPoly (DensePoly.cmul
        (DensePoly.cmul (DensePoly.cmul (CPoly.splitFactor Dt fden).1 h0) h0) gnum) := by
  simp only [denote] at hdvd ⊢
  exact hdvd.mul_right _

/-- `fden ∣ dₙh` when `fden` equals its own normal part. -/
theorem dvd_dn_h_of_normal_wf (Dt : DensePoly β) (fden h0 : DensePoly β)
    (hnormal : toPoly (CPoly.splitFactor Dt fden).1 = toPoly fden) :
    toPoly fden ∣ toPoly (DensePoly.cmul (CPoly.splitFactor Dt fden).1 h0) := by
  simp only [denote]
  rw [hnormal]
  exact Dvd.intro _ rfl

end ClearingDivisibility

/-- `fden ∣ dₙh` for the shape `fden = [1]`. -/
theorem dvd_dn_h_one_wf {β : Type u} [CField β] [CFieldSpec.{u,v} β] [CDiffField β]
    [CPolyGcd DensePoly β] [LawfulCPolyGcd.{u,v} DensePoly β] (h0 : DensePoly β) :
    toPoly ([CCommRing.one] : DensePoly β)
      ∣ toPoly (DensePoly.cmul (CPoly.splitFactor ([CCommRing.one] : DensePoly β) [CCommRing.one]).1 h0) := by
  rw [CPoly.splitFactor_one_eq]
  have hone : toPoly ([CCommRing.one] : DensePoly β) = 1 := by
    simp only [denote]
    simp
  rw [hone]
  exact one_dvd _


/-! ## Inner completeness assembly -/

section AssembleWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- `RischDEInnerCompletenessWf` with `hnorm` discharged from the normal-denominator residual. -/
theorem rischDEInnerCompletenessWf_of_norm_bound_solve (Dt fnum fden gnum gden : DensePoly α)
    (hnormRes : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden)
    (hbound : ∀ a0 b0 c0 h0 : DensePoly α,
      cRdeNormalDenominator Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      ∀ q : DensePoly α,
        IsReducedRdeSol Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1 q →
        cdeg q ≤ cRdeBoundDegree Dt
          (cRdeSpecialDenominator Dt a0 b0 c0).1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1)
    (hsolve : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRischDE Dt fnum fden gnum gden).isSome = true) :
    RischDEInnerCompletenessWf Dt fnum fden gnum gden where
  hnorm := hnormWf_of_divisibilityResidualWf Dt fnum fden gnum gden hnormRes
  hbound := hbound
  hsolve := hsolve

end AssembleWf

/-! ### Restatements -/

-- The Wf engine bridge: mathematical divisibility forces the Wf normal-denominator step to succeed.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CPolyGcd DensePoly α]
    (Dt fnum fden gnum gden : DensePoly α)
    (hen0 : DensePoly.cnorm (CPoly.splitFactor Dt gden).1 ≠ [])
    (hdvd : toPoly (CPoly.splitFactor Dt gden).1 ∣ toPoly (rdeNormDnh2Wf Dt fden gden)) :
    (cRdeNormalDenominator Dt fnum fden gnum gden).isSome = true :=
  cRdeNormalDenominatorG_isSome_of_dvd Dt fnum fden gnum gden hen0 hdvd

-- The Wf residual produces exactly the `RischDEInnerCompletenessWf.hnorm` field shape.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
    [CRischField α] (Dt fnum fden gnum gden : DensePoly α)
    (hres : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominator Dt fnum fden gnum gden).isSome = true :=
  hnormWf_of_divisibilityResidualWf Dt fnum fden gnum gden hres

/-! ### Axiom audit -/

#print axioms cRdeNormalDenominatorG_isSome_iff
#print axioms dvd_eq_true_of_toPoly_dvd
#print axioms cRdeNormalDenominatorG_isSome_of_dvd
#print axioms hnormWf_of_divisibilityResidualWf
#print axioms rischDEInnerCompletenessWf_of_norm_bound_solve

end DeepWiki.SymbolicIntegration
