import DeepWiki.SymbolicIntegration.Engine.RischDE.SolveSoundWf
import DeepWiki.SymbolicIntegration.Engine.RischDE.Structural

/-! # Field-level soundness of the raw RDE solve `crischDERawSolveWf`

A successful `crischDERawSolveWf` returns a `cRischDE [1]`-success pair, so the field-level
Risch-DE identity follows from the isolated residual `RawSolveResidualWf`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

section RawSolveField

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

omit [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFracGcdCoreWf β] [CRischField β]
  [Algebra ℚ (CFieldSpec.K β)] in
/-- `cdeg [CCommRing.one] = 0` over a `CFieldDomain`: the constant `[1]` has degree `0` (primitive regime). -/
theorem cdegG_one_eq_zero_wf : cdeg ([CCommRing.one] : DensePoly β) = 0 := by
  have hnz : DensePoly.cisZero ([CCommRing.one] : DensePoly β) = false := CFieldDomain.nz_one
  rw [DensePoly.cisZero, List.isEmpty_eq_false_iff_exists_mem] at hnz
  have hcn : DensePoly.cnorm ([CCommRing.one] : DensePoly β) = [CCommRing.one] := by
    show (if CCommRing.isZero (CCommRing.one : β) then ([] : DensePoly β) else [CCommRing.one]) = [CCommRing.one]
    by_cases h1 : CCommRing.isZero (CCommRing.one : β) = true
    · exfalso
      obtain ⟨a, ha⟩ := hnz
      rw [show DensePoly.cnorm ([CCommRing.one] : DensePoly β)
          = (if CCommRing.isZero (CCommRing.one : β) then ([] : DensePoly β) else [CCommRing.one]) from rfl,
        if_pos h1] at ha
      exact absurd ha (List.not_mem_nil)
    · rw [if_neg (by simpa using h1)]
  rw [cdeg, hcn]; rfl

/-- Residual hypotheses for `crischDERawSolveWf` field soundness: the structural residual, the
positive-`deg(bbar)` dispatcher side-condition, and the two input-denominator nonzero facts. -/
structure RawSolveResidualWf (ftilde gtilde : CFrac β) : Prop where
  /-- The structural residual on the base solve, for the matching normal-denominator output. -/
  hres : ∀ a0 b0 c0 h0 : DensePoly β,
    cRdeNormalDenominator ([CCommRing.one] : DensePoly β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2
        = some (a0, b0, c0, h0) →
      RischDEStructuralResidualWf ([CCommRing.one] : DensePoly β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2
        a0 b0 c0 h0
  /-- The positive-`deg(bbar)` dispatcher side-condition (non-cancellation routing). -/
  hdb : ∀ a0 b0 c0 bbar cbar : DensePoly β, ∀ m : ℤ, ∀ α' β' : DensePoly β,
    cSPDE ([CCommRing.one] : DensePoly β)
        (cRdeSpecialDenominator ([CCommRing.one] : DensePoly β) a0 b0 c0).1
        (cRdeSpecialDenominator ([CCommRing.one] : DensePoly β) a0 b0 c0).2.1
        (cRdeSpecialDenominator ([CCommRing.one] : DensePoly β) a0 b0 c0).2.2.1
        (cRdeBoundDegree ([CCommRing.one] : DensePoly β)
          (cRdeSpecialDenominator ([CCommRing.one] : DensePoly β) a0 b0 c0).1
          (cRdeSpecialDenominator ([CCommRing.one] : DensePoly β) a0 b0 c0).2.1
          (cRdeSpecialDenominator ([CCommRing.one] : DensePoly β) a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β') → 0 < cdeg bbar
  /-- The input `ftilde`'s denominator is nonzero. -/
  hfden : toPoly ftilde.1.2 ≠ 0
  /-- The input `gtilde`'s denominator is nonzero. -/
  hgden : toPoly gtilde.1.2 ≠ 0

/-- If `crischDERawSolveWf ftilde gtilde = some y` and `RawSolveResidualWf ftilde gtilde` holds, then
`y = ynum/yden` solves the field-level Risch DE `D(Y) + F·Y = G` over `RatFunc (CFieldSpec.K β)`. -/
theorem crischDERawSolveWf_field_of_residual (ftilde gtilde y : CFrac β)
    (hsolve : crischDERawSolveWf ftilde gtilde = some y)
    (hres : RawSolveResidualWf ftilde gtilde) :
    towerFractionFieldDeriv ([CCommRing.one] : DensePoly β)
          (am β (toPoly y.1.1) / am β (toPoly y.1.2))
        + am β (toPoly ftilde.1.1) / am β (toPoly ftilde.1.2)
          * (am β (toPoly y.1.1) / am β (toPoly y.1.2))
      = am β (toPoly gtilde.1.1) / am β (toPoly gtilde.1.2) := by
  -- unfold the raw solve to the bare `cRischDE [1]` success
  rw [show crischDERawSolveWf ftilde gtilde
      = (match DensePoly.cRischDE ([CCommRing.one] : DensePoly β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 with
         | none => none
         | some (ynum, yden) =>
           if h : DensePoly.cisZero yden = false then
             some (CFrac.ofFraction ynum yden h)
           else none) from rfl] at hsolve
  rcases hsucc : DensePoly.cRischDE ([CCommRing.one] : DensePoly β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2
    with _ | ⟨ynum, yden⟩ <;> rw [hsucc] at hsolve
  · exact absurd hsolve (by simp)
  · simp only at hsolve
    by_cases hyz : DensePoly.cisZero yden = false
    · rw [dif_pos hyz, Option.some.injEq] at hsolve
      have hy1 : y.1.1 = ynum := by
        change CFrac.num y = ynum
        simpa using congrArg CFrac.num hsolve.symm
      have hy2 : y.1.2 = yden := by
        change CFrac.den y = yden
        simpa using congrArg CFrac.den hsolve.symm
      have hydenne : toPoly yden ≠ 0 := by
        intro h; exact absurd ((cisZeroG_iff yden).mpr h) (by simpa using hyz)
      rw [hy1, hy2]
      exact crischDEWf_field_of_success_and_residual ([CCommRing.one] : DensePoly β)
        ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 ynum yden cdegG_one_eq_zero_wf hsucc
        hres.hres hres.hdb hres.hfden hres.hgden hydenne
    · rw [dif_neg hyz] at hsolve; exact absurd hsolve (by simp)

end RawSolveField

/-! ### Axiom audit -/

#print axioms crischDERawSolveWf_field_of_residual

end DeepWiki.SymbolicIntegration
