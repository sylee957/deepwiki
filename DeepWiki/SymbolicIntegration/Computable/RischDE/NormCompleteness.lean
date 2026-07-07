import DeepWiki.SymbolicIntegration.Computable.RischDE.Completeness
import DeepWiki.SymbolicIntegration.Computable.Tower.RischDEWellFounded

/-! # RDE normal-denominator completeness

Completeness bridges for the normal-denominator step of the Wf Risch differential equation solver. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG


/-! ## Engine guard -/

section WfEngineLayer

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CFracGcdCoreWf α]

/-- The normal part `eₙ` of the `g`-denominator. -/
def rdeNormEnWf (Dt : CPolyG α) (gden : CPolyG α) : CPolyG α :=
  (CPolyG.cSplitFactorFastGWf Dt gden).1

/-- The normal part `dₙ` of the `f`-denominator. -/
def rdeNormDnWf (Dt : CPolyG α) (fden : CPolyG α) : CPolyG α :=
  (CPolyG.cSplitFactorFastGWf Dt fden).1

/-- The multiplicity factor `h = gcd(eₙ,eₙ')/gcd(p,p')`. -/
def rdeNormHWf (Dt : CPolyG α) (fden gden : CPolyG α) : CPolyG α :=
  CPolyG.cdivWf
    (CFracGcdCoreWf.cgcdFFCoreWf (rdeNormEnWf Dt gden) (CPolyG.cderivG (rdeNormEnWf Dt gden)))
    (CFracGcdCoreWf.cgcdFFCoreWf
      (CFracGcdCoreWf.cgcdFFCoreWf (rdeNormDnWf Dt fden) (rdeNormEnWf Dt gden))
      (CPolyG.cderivG (CFracGcdCoreWf.cgcdFFCoreWf
        (rdeNormDnWf Dt fden) (rdeNormEnWf Dt gden))))

/-- The dividend `dₙ·h²`. -/
def rdeNormDnh2Wf (Dt : CPolyG α) (fden gden : CPolyG α) : CPolyG α :=
  CPolyG.cmulG (CPolyG.cmulG (rdeNormDnWf Dt fden) (rdeNormHWf Dt fden gden))
    (rdeNormHWf Dt fden gden)

omit [CFieldSpec α] in
/-- The normal-denominator step's `isSome` is exactly its `cdvdGWf` divisibility guard. -/
theorem cRdeNormalDenominatorGWf_isSome_iff (Dt : CPolyG α) (fnum fden gnum gden : CPolyG α) :
    (CPolyG.cRdeNormalDenominatorGWf Dt fnum fden gnum gden).isSome = true ↔
      CPolyG.cdvdGWf (rdeNormEnWf Dt gden) (rdeNormDnh2Wf Dt fden gden) = true := by
  rw [CPolyG.cRdeNormalDenominatorGWf]
  simp only [rdeNormDnh2Wf, rdeNormHWf, rdeNormDnWf, rdeNormEnWf]
  split <;> simp_all

omit [CDiffField α] [CFracGcdCoreWf α] in
/-- Mathematical divisibility `toPolyG q ∣ toPolyG p` forces `cdvdGWf q p = true`. -/
theorem cdvdGWf_of_dvd (q p : CPolyG α) (hq0 : CPolyG.cnormG q ≠ [])
    (hdvd : toPolyG q ∣ toPolyG p) :
    CPolyG.cdvdGWf q p = true := by
  by_cases h : CPolyG.cdvdGWf q p = true
  · exact h
  · have hfalse : CPolyG.cdvdGWf q p = false := Bool.eq_false_iff.mpr h
    exact False.elim ((CPolyG.not_dvd_of_cdvdGWf_false q p hq0 hfalse) hdvd)

/-- The normal-denominator step returns `some` from the mathematical divisibility `eₙ ∣ dₙh²`. -/
theorem cRdeNormalDenominatorGWf_isSome_of_dvd (Dt : CPolyG α)
    (fnum fden gnum gden : CPolyG α)
    (hen0 : CPolyG.cnormG (rdeNormEnWf Dt gden) ≠ [])
    (hdvd : toPolyG (rdeNormEnWf Dt gden) ∣ toPolyG (rdeNormDnh2Wf Dt fden gden)) :
    (CPolyG.cRdeNormalDenominatorGWf Dt fnum fden gnum gden).isSome = true :=
  (cRdeNormalDenominatorGWf_isSome_iff Dt fnum fden gnum gden).mpr
    (cdvdGWf_of_dvd _ _ hen0 hdvd)

end WfEngineLayer


/-! ## Divisibility residual -/

section DivisibilityResidualWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- `RdeNormalDivisibilityResidualWf` supplies `eₙ ∣ dₙh²` and nonzero `eₙ`. -/
structure RdeNormalDivisibilityResidualWf (Dt fnum fden gnum gden : CPolyG α) : Prop where
  /-- A polynomial solution forces `eₙ ∣ dₙh²`. -/
  hdvd : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    toPolyG (rdeNormEnWf Dt gden) ∣ toPolyG (rdeNormDnh2Wf Dt fden gden)
  /-- The normal part `eₙ` of `gden` is nonzero. -/
  hen0 : CPolyG.cnormG (rdeNormEnWf Dt gden) ≠ []

omit [CRischField α] in
/-- `hnorm` from the divisibility residual: the normal-denominator step preserves solvability. -/
theorem hnormWf_of_divisibilityResidualWf (Dt fnum fden gnum gden : CPolyG α)
    (hres : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominatorGWf Dt fnum fden gnum gden).isSome = true := by
  intro hsol
  exact cRdeNormalDenominatorGWf_isSome_of_dvd Dt fnum fden gnum gden
    hres.hen0 (hres.hdvd hsol)

omit [CDiffFieldSpec α] [CRischField α] in
/-- `eₙ ∣ dₙ` implies `eₙ ∣ dₙh²`. -/
theorem dvd_dnh2Wf_of_en_dvd_dn (Dt : CPolyG α) (fden gden : CPolyG α)
    (hdvd : toPolyG (rdeNormEnWf Dt gden) ∣ toPolyG (rdeNormDnWf Dt fden)) :
    toPolyG (rdeNormEnWf Dt gden) ∣ toPolyG (rdeNormDnh2Wf Dt fden gden) := by
  rw [rdeNormDnh2Wf]
  simp only [denote]
  exact (hdvd.mul_right _).mul_right _

omit [CRischField α] in
/-- The `hdvd` clause holds unconditionally when `eₙ ∣ dₙ`. -/
theorem hdvdWf_free_of_en_dvd_dn (Dt fnum fden gnum gden : CPolyG α)
    (hdvd : toPolyG (rdeNormEnWf Dt gden) ∣ toPolyG (rdeNormDnWf Dt fden)) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      toPolyG (rdeNormEnWf Dt gden) ∣ toPolyG (rdeNormDnh2Wf Dt fden gden) :=
  fun _ => dvd_dnh2Wf_of_en_dvd_dn Dt fden gden hdvd

end DivisibilityResidualWf


/-! ## Inner completeness assembly -/

section AssembleWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- `RischDEInnerCompletenessWf` with `hnorm` discharged from the normal-denominator residual. -/
theorem rischDEInnerCompletenessWf_of_norm_bound_solve (Dt fnum fden gnum gden : CPolyG α)
    (hnormRes : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden)
    (hbound : ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorGWf Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      ∀ q : CPolyG α,
        IsReducedRdeSol Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1 q →
        cdegG q ≤ cRdeBoundDegreeG Dt
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1)
    (hsolve : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRischDEGWf Dt fnum fden gnum gden).isSome = true) :
    RischDEInnerCompletenessWf Dt fnum fden gnum gden where
  hnorm := hnormWf_of_divisibilityResidualWf Dt fnum fden gnum gden hnormRes
  hbound := hbound
  hsolve := hsolve

end AssembleWf

/-! ### Restatements -/

-- The Wf engine bridge: mathematical divisibility forces the Wf normal-denominator step to succeed.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CFracGcdCoreWf α]
    (Dt fnum fden gnum gden : CPolyG α)
    (hen0 : CPolyG.cnormG (rdeNormEnWf Dt gden) ≠ [])
    (hdvd : toPolyG (rdeNormEnWf Dt gden) ∣ toPolyG (rdeNormDnh2Wf Dt fden gden)) :
    (cRdeNormalDenominatorGWf Dt fnum fden gnum gden).isSome = true :=
  cRdeNormalDenominatorGWf_isSome_of_dvd Dt fnum fden gnum gden hen0 hdvd

-- The Wf residual produces exactly the `RischDEInnerCompletenessWf.hnorm` field shape.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
    [CRischField α] (Dt fnum fden gnum gden : CPolyG α)
    (hres : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominatorGWf Dt fnum fden gnum gden).isSome = true :=
  hnormWf_of_divisibilityResidualWf Dt fnum fden gnum gden hres

/-! ### Axiom audit -/

#print axioms cRdeNormalDenominatorGWf_isSome_iff
#print axioms cdvdGWf_of_dvd
#print axioms cRdeNormalDenominatorGWf_isSome_of_dvd
#print axioms hnormWf_of_divisibilityResidualWf
#print axioms rischDEInnerCompletenessWf_of_norm_bound_solve

end DeepWiki.SymbolicIntegration
