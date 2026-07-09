import DeepWiki.SymbolicIntegration.Engine.RischDE.Completeness
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded

/-! # RDE normal-denominator completeness

Completeness bridges for the normal-denominator step of the Wf Risch differential equation solver. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZG


/-! ## Engine guard -/

section WfEngineLayer

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CFracGcdCoreWf α]

/-- The normal part `eₙ` of the `g`-denominator. -/
def rdeNormEnWf (Dt : CPoly α) (gden : CPoly α) : CPoly α :=
  (CPoly.cSplitFactorFast Dt gden).1

/-- The normal part `dₙ` of the `f`-denominator. -/
def rdeNormDnWf (Dt : CPoly α) (fden : CPoly α) : CPoly α :=
  (CPoly.cSplitFactorFast Dt fden).1

/-- The multiplicity factor `h = gcd(eₙ,eₙ')/gcd(p,p')`. -/
def rdeNormHWf (Dt : CPoly α) (fden gden : CPoly α) : CPoly α :=
  CPoly.cdivWf
    (CFracGcdCoreWf.cgcdFFCoreWf (rdeNormEnWf Dt gden) (CPoly.cderiv (rdeNormEnWf Dt gden)))
    (CFracGcdCoreWf.cgcdFFCoreWf
      (CFracGcdCoreWf.cgcdFFCoreWf (rdeNormDnWf Dt fden) (rdeNormEnWf Dt gden))
      (CPoly.cderiv (CFracGcdCoreWf.cgcdFFCoreWf
        (rdeNormDnWf Dt fden) (rdeNormEnWf Dt gden))))

/-- The dividend `dₙ·h²`. -/
def rdeNormDnh2Wf (Dt : CPoly α) (fden gden : CPoly α) : CPoly α :=
  CPoly.cmul (CPoly.cmul (rdeNormDnWf Dt fden) (rdeNormHWf Dt fden gden))
    (rdeNormHWf Dt fden gden)

omit [CFieldSpec α] in
/-- The normal-denominator step's `isSome` is exactly its `cdvd` divisibility guard. -/
theorem cRdeNormalDenominatorG_isSome_iff (Dt : CPoly α) (fnum fden gnum gden : CPoly α) :
    (CPoly.cRdeNormalDenominator Dt fnum fden gnum gden).isSome = true ↔
      CPoly.cdvd (rdeNormEnWf Dt gden) (rdeNormDnh2Wf Dt fden gden) = true := by
  rw [CPoly.cRdeNormalDenominator]
  simp only [rdeNormDnh2Wf, rdeNormHWf, rdeNormDnWf, rdeNormEnWf]
  split <;> simp_all

omit [CDiffField α] [CFracGcdCoreWf α] in
/-- Mathematical divisibility `toPoly q ∣ toPoly p` forces `cdvd q p = true`. -/
theorem cdvdG_of_dvd (q p : CPoly α) (hq0 : CPoly.cnorm q ≠ [])
    (hdvd : toPoly q ∣ toPoly p) :
    CPoly.cdvd q p = true := by
  by_cases h : CPoly.cdvd q p = true
  · exact h
  · have hfalse : CPoly.cdvd q p = false := Bool.eq_false_iff.mpr h
    exact False.elim ((CPoly.not_dvd_of_cdvdG_false q p hq0 hfalse) hdvd)

/-- The normal-denominator step returns `some` from the mathematical divisibility `eₙ ∣ dₙh²`. -/
theorem cRdeNormalDenominatorG_isSome_of_dvd (Dt : CPoly α)
    (fnum fden gnum gden : CPoly α)
    (hen0 : CPoly.cnorm (rdeNormEnWf Dt gden) ≠ [])
    (hdvd : toPoly (rdeNormEnWf Dt gden) ∣ toPoly (rdeNormDnh2Wf Dt fden gden)) :
    (CPoly.cRdeNormalDenominator Dt fnum fden gnum gden).isSome = true :=
  (cRdeNormalDenominatorG_isSome_iff Dt fnum fden gnum gden).mpr
    (cdvdG_of_dvd _ _ hen0 hdvd)

end WfEngineLayer


/-! ## Divisibility residual -/

section DivisibilityResidualWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- `RdeNormalDivisibilityResidualWf` supplies `eₙ ∣ dₙh²` and nonzero `eₙ`. -/
structure RdeNormalDivisibilityResidualWf (Dt fnum fden gnum gden : CPoly α) : Prop where
  /-- A polynomial solution forces `eₙ ∣ dₙh²`. -/
  hdvd : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    toPoly (rdeNormEnWf Dt gden) ∣ toPoly (rdeNormDnh2Wf Dt fden gden)
  /-- The normal part `eₙ` of `gden` is nonzero. -/
  hen0 : CPoly.cnorm (rdeNormEnWf Dt gden) ≠ []

omit [CRischField α] in
/-- `hnorm` from the divisibility residual: the normal-denominator step preserves solvability. -/
theorem hnormWf_of_divisibilityResidualWf (Dt fnum fden gnum gden : CPoly α)
    (hres : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominator Dt fnum fden gnum gden).isSome = true := by
  intro hsol
  exact cRdeNormalDenominatorG_isSome_of_dvd Dt fnum fden gnum gden
    hres.hen0 (hres.hdvd hsol)

omit [CDiffFieldSpec α] [CRischField α] in
/-- `eₙ ∣ dₙ` implies `eₙ ∣ dₙh²`. -/
theorem dvd_dnh2Wf_of_en_dvd_dn (Dt : CPoly α) (fden gden : CPoly α)
    (hdvd : toPoly (rdeNormEnWf Dt gden) ∣ toPoly (rdeNormDnWf Dt fden)) :
    toPoly (rdeNormEnWf Dt gden) ∣ toPoly (rdeNormDnh2Wf Dt fden gden) := by
  rw [rdeNormDnh2Wf]
  simp only [denote]
  exact (hdvd.mul_right _).mul_right _

omit [CRischField α] in
/-- The `hdvd` clause holds unconditionally when `eₙ ∣ dₙ`. -/
theorem hdvdWf_free_of_en_dvd_dn (Dt fnum fden gnum gden : CPoly α)
    (hdvd : toPoly (rdeNormEnWf Dt gden) ∣ toPoly (rdeNormDnWf Dt fden)) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      toPoly (rdeNormEnWf Dt gden) ∣ toPoly (rdeNormDnh2Wf Dt fden gden) :=
  fun _ => dvd_dnh2Wf_of_en_dvd_dn Dt fden gden hdvd

end DivisibilityResidualWf

/-! ## Clearing divisibility clauses -/

section ClearingDivisibility

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β]

/-- If `fden ∣ dₙ·h0`, then `fden` divides the `B`-numerator `dₙh·fnum - dₙ·Dh·fden`. -/
theorem hdvdB_of_dvd_wf (Dt : CPoly β) (fnum fden h0 : CPoly β)
    (hdvd : toPoly fden ∣ toPoly (CPoly.cmul (CPoly.cSplitFactorFast Dt fden).1 h0)) :
    toPoly fden ∣ toPoly (CPoly.csub
        (CPoly.cmul (CPoly.cmul (CPoly.cSplitFactorFast Dt fden).1 h0) fnum)
        (CPoly.cmul (CPoly.cmul (CPoly.cSplitFactorFast Dt fden).1
          (CPoly.cmonomialDeriv Dt h0)) fden)) := by
  simp only [denote] at hdvd ⊢
  apply dvd_sub
  · exact hdvd.mul_right _
  · exact Dvd.intro_left _ rfl

/-- If `gden ∣ dₙ·h0·h0`, then `gden` divides the `C`-numerator `dₙh²·gnum`. -/
theorem hdvdC_of_dvd_wf (Dt : CPoly β) (gnum fden gden h0 : CPoly β)
    (hdvd : toPoly gden ∣ toPoly (CPoly.cmul
      (CPoly.cmul (CPoly.cSplitFactorFast Dt fden).1 h0) h0)) :
    toPoly gden ∣ toPoly (CPoly.cmul
        (CPoly.cmul (CPoly.cmul (CPoly.cSplitFactorFast Dt fden).1 h0) h0) gnum) := by
  simp only [denote] at hdvd ⊢
  exact hdvd.mul_right _

/-- `fden ∣ dₙh` when `fden` equals its own normal part. -/
theorem dvd_dn_h_of_normal_wf (Dt : CPoly β) (fden h0 : CPoly β)
    (hnormal : toPoly (CPoly.cSplitFactorFast Dt fden).1 = toPoly fden) :
    toPoly fden ∣ toPoly (CPoly.cmul (CPoly.cSplitFactorFast Dt fden).1 h0) := by
  simp only [denote]
  rw [hnormal]
  exact Dvd.intro _ rfl

end ClearingDivisibility

/-- `fden ∣ dₙh` for the shape `fden = [1]`. -/
theorem dvd_dn_h_one_wf {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFracGcdCoreWf β]
    [CTowerGcdWitnessWf β] (h0 : CPoly β) :
    toPoly ([CField.one] : CPoly β)
      ∣ toPoly (CPoly.cmul (CPoly.cSplitFactorFast ([CField.one] : CPoly β) [CField.one]).1 h0) := by
  rw [cSplitFactorFastG_one_eq]
  simp only [denote, toPolyG_cone_eq_one_wf]
  exact one_dvd _


/-! ## Inner completeness assembly -/

section AssembleWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- `RischDEInnerCompletenessWf` with `hnorm` discharged from the normal-denominator residual. -/
theorem rischDEInnerCompletenessWf_of_norm_bound_solve (Dt fnum fden gnum gden : CPoly α)
    (hnormRes : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden)
    (hbound : ∀ a0 b0 c0 h0 : CPoly α,
      cRdeNormalDenominator Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      ∀ q : CPoly α,
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
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CFracGcdCoreWf α]
    (Dt fnum fden gnum gden : CPoly α)
    (hen0 : CPoly.cnorm (rdeNormEnWf Dt gden) ≠ [])
    (hdvd : toPoly (rdeNormEnWf Dt gden) ∣ toPoly (rdeNormDnh2Wf Dt fden gden)) :
    (cRdeNormalDenominator Dt fnum fden gnum gden).isSome = true :=
  cRdeNormalDenominatorG_isSome_of_dvd Dt fnum fden gnum gden hen0 hdvd

-- The Wf residual produces exactly the `RischDEInnerCompletenessWf.hnorm` field shape.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
    [CRischField α] (Dt fnum fden gnum gden : CPoly α)
    (hres : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominator Dt fnum fden gnum gden).isSome = true :=
  hnormWf_of_divisibilityResidualWf Dt fnum fden gnum gden hres

/-! ### Axiom audit -/

#print axioms cRdeNormalDenominatorG_isSome_iff
#print axioms cdvdG_of_dvd
#print axioms cRdeNormalDenominatorG_isSome_of_dvd
#print axioms hnormWf_of_divisibilityResidualWf
#print axioms rischDEInnerCompletenessWf_of_norm_bound_solve

end DeepWiki.SymbolicIntegration
