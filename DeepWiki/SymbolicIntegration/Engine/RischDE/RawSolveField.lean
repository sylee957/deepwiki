import DeepWiki.SymbolicIntegration.Engine.RischDE.SolveSoundWf
import DeepWiki.SymbolicIntegration.Engine.RischDE.Structural

/-! # Field-level soundness of the raw RDE solve `crischDERawSolveWf`

A successful `crischDERawSolveWf` returns a `cRischDEG [1]`-success pair, so the field-level
Risch-DE identity follows from the isolated residual `RawSolveResidualWf`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

section RawSolveField

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

omit [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFracGcdCoreWf β] [CRischField β]
  [Algebra ℚ (CFieldSpec.K β)] in
/-- `cdegG [CField.one] = 0` over a `CFieldDomain`: the constant `[1]` has degree `0` (primitive regime). -/
theorem cdegG_one_eq_zero_wf : cdegG ([CField.one] : CPolyG β) = 0 := by
  have hnz : CPolyG.cisZeroG ([CField.one] : CPolyG β) = false := CFieldDomain.nz_one
  rw [CPolyG.cisZeroG, List.isEmpty_eq_false_iff_exists_mem] at hnz
  have hcn : CPolyG.cnormG ([CField.one] : CPolyG β) = [CField.one] := by
    show (if CField.isZero (CField.one : β) then ([] : CPolyG β) else [CField.one]) = [CField.one]
    by_cases h1 : CField.isZero (CField.one : β) = true
    · exfalso
      obtain ⟨a, ha⟩ := hnz
      rw [show CPolyG.cnormG ([CField.one] : CPolyG β)
          = (if CField.isZero (CField.one : β) then ([] : CPolyG β) else [CField.one]) from rfl,
        if_pos h1] at ha
      exact absurd ha (List.not_mem_nil)
    · rw [if_neg (by simpa using h1)]
  rw [cdegG, hcn]; rfl

/-- Residual hypotheses for `crischDERawSolveWf` field soundness: the structural residual, the
positive-`deg(bbar)` dispatcher side-condition, and the two input-denominator nonzero facts. -/
structure RawSolveResidualWf (ftilde gtilde : QFunNZG β) : Prop where
  /-- The structural residual on the base solve, for the matching normal-denominator output. -/
  hres : ∀ a0 b0 c0 h0 : CPolyG β,
    cRdeNormalDenominatorG ([CField.one] : CPolyG β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2
        = some (a0, b0, c0, h0) →
      RischDEStructuralResidualWf ([CField.one] : CPolyG β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2
        a0 b0 c0 h0
  /-- The positive-`deg(bbar)` dispatcher side-condition (non-cancellation routing). -/
  hdb : ∀ a0 b0 c0 bbar cbar : CPolyG β, ∀ m : ℤ, ∀ α' β' : CPolyG β,
    cSPDEG ([CField.one] : CPolyG β)
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) a0 b0 c0).1
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) a0 b0 c0).2.1
        (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) a0 b0 c0).2.2.1
        (cRdeBoundDegreeG ([CField.one] : CPolyG β)
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) a0 b0 c0).1
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) a0 b0 c0).2.1
          (cRdeSpecialDenominatorG ([CField.one] : CPolyG β) a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β') → 0 < cdegG bbar
  /-- The input `ftilde`'s denominator is nonzero. -/
  hfden : toPolyG ftilde.1.2 ≠ 0
  /-- The input `gtilde`'s denominator is nonzero. -/
  hgden : toPolyG gtilde.1.2 ≠ 0

/-- If `crischDERawSolveWf ftilde gtilde = some y` and `RawSolveResidualWf ftilde gtilde` holds, then
`y = ynum/yden` solves the field-level Risch DE `D(Y) + F·Y = G` over `RatFunc (CFieldSpec.K β)`. -/
theorem crischDERawSolveWf_field_of_residual (ftilde gtilde y : QFunNZG β)
    (hsolve : crischDERawSolveWf ftilde gtilde = some y)
    (hres : RawSolveResidualWf ftilde gtilde) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG ftilde.1.1) / amG β (toPolyG ftilde.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG gtilde.1.1) / amG β (toPolyG gtilde.1.2) := by
  -- unfold the raw solve to the bare `cRischDEG [1]` success
  rw [show crischDERawSolveWf ftilde gtilde
      = (match CPolyG.cRischDEG ([CField.one] : CPolyG β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 with
         | none => none
         | some (ynum, yden) =>
           if h : CPolyG.cisZeroG yden = false then some ⟨(ynum, yden), h⟩ else none) from rfl] at hsolve
  rcases hsucc : CPolyG.cRischDEG ([CField.one] : CPolyG β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2
    with _ | ⟨ynum, yden⟩ <;> rw [hsucc] at hsolve
  · exact absurd hsolve (by simp)
  · simp only at hsolve
    by_cases hyz : CPolyG.cisZeroG yden = false
    · rw [dif_pos hyz, Option.some.injEq] at hsolve
      have hy1 : y.1.1 = ynum := by rw [← hsolve]
      have hy2 : y.1.2 = yden := by rw [← hsolve]
      have hydenne : toPolyG yden ≠ 0 := by
        intro h; exact absurd ((cisZeroG_iff yden).mpr h) (by simpa using hyz)
      rw [hy1, hy2]
      exact crischDEWf_field_of_success_and_residual ([CField.one] : CPolyG β)
        ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 ynum yden cdegG_one_eq_zero_wf hsucc
        hres.hres hres.hdb hres.hfden hres.hgden hydenne
    · rw [dif_neg hyz] at hsolve; exact absurd hsolve (by simp)

end RawSolveField

/-! ### Axiom audit -/

#print axioms crischDERawSolveWf_field_of_residual

end DeepWiki.SymbolicIntegration
