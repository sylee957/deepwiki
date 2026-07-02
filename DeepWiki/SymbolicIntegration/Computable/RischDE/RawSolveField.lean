import DeepWiki.SymbolicIntegration.Computable.RischDE.SolveSoundWf
import DeepWiki.SymbolicIntegration.Computable.RischDE.Structural

/-! # Field-level soundness of the fuel-free raw RDE solve `crischDERawSolveWf`

The fuel-free analogue of `crischDESolve_field_of_witness_residual` (`SoundnessCapstone`), but for the
**fuel-free** raw solver `crischDERawSolveWf` (which runs `cRischDEGWf [1]` in place of the fuel'd
`cRischDEG [1] towerRischDEFuel`). Composes the Phase-P1 headline
`crischDEWf_field_of_success_and_residual` (`RischDE.Structural`) with the raw-solve unfold: a successful
`crischDERawSolveWf` returns exactly a `cRischDEGWf [1]`-success pair, so the field identity follows from the
residual with **no fuel, no tower-gcd witness, no `native_decide`**.

This is the standalone soundness the fuel-free instance switch (`docs/rischde-wf-migration.md` Phase P2)
needs: it exhibits, on the exact runtime shape the rebased `CRischField (QFunNZG β)` instance will use, that
a successful gated solve satisfies the field-level Risch-DE identity. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

section RawSolveField

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

omit [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFracGcdCoreWf β] [CRischField β]
  [Algebra ℚ (CFieldSpec.K β)] in
/-- **`cdegG [1] = 0`** over a `CFieldDomain` (fuel-free re-derivation, kept independent of the fuel'd
`SoundnessCapstone`): the monomial derivative `Ds = [CField.one]` the recursive fuel-free RDE solve uses is a
constant, so it is in the **primitive** regime — the `hδ` side-condition the Phase-P1 headline needs. -/
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

/-- **The residual for the fuel-free raw RDE solve** `RawSolveResidualWf ftilde gtilde`: the hypotheses of
the Phase-P1 headline `crischDEWf_field_of_success_and_residual`, specialized to the recursive base solve
`cRischDEGWf ([1] : CPolyG β)` on `(ftilde, gtilde)`. Bundles the primitive-regime structural residual
`RischDEStructuralResidualWf` on the normal-denominator output, the positive-`deg(bbar)` dispatcher
side-condition, and the two input-denominator nonzero facts — exactly what a bare `crischDERawSolveWf`
success does NOT self-certify. Fuel-free analogue of `RischDESuccessResidual`. -/
structure RawSolveResidualWf (ftilde gtilde : QFunNZG β) : Prop where
  /-- The primitive-regime §6 structural residual on the level-`β` base solve, for the matching
  normal-denominator output. -/
  hres : ∀ a0 b0 c0 h0 : CPolyG β,
    cRdeNormalDenominatorGWf ([CField.one] : CPolyG β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2
        = some (a0, b0, c0, h0) →
      RischDEStructuralResidualWf ([CField.one] : CPolyG β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2
        a0 b0 c0 h0
  /-- The positive-`deg(bbar)` dispatcher side-condition (Lemma 6.5.1 non-cancellation routing). -/
  hdb : ∀ a0 b0 c0 bbar cbar : CPolyG β, ∀ m : ℤ, ∀ α' β' : CPolyG β,
    cSPDEGWf ([CField.one] : CPolyG β)
        (cRdeSpecialDenominatorGWf ([CField.one] : CPolyG β) a0 b0 c0).1
        (cRdeSpecialDenominatorGWf ([CField.one] : CPolyG β) a0 b0 c0).2.1
        (cRdeSpecialDenominatorGWf ([CField.one] : CPolyG β) a0 b0 c0).2.2.1
        (cRdeBoundDegreeG ([CField.one] : CPolyG β)
          (cRdeSpecialDenominatorGWf ([CField.one] : CPolyG β) a0 b0 c0).1
          (cRdeSpecialDenominatorGWf ([CField.one] : CPolyG β) a0 b0 c0).2.1
          (cRdeSpecialDenominatorGWf ([CField.one] : CPolyG β) a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β') → 0 < cdegG bbar
  /-- The input `ftilde`'s denominator is nonzero. -/
  hfden : toPolyG ftilde.1.2 ≠ 0
  /-- The input `gtilde`'s denominator is nonzero. -/
  hgden : toPolyG gtilde.1.2 ≠ 0

/-- **★ The fuel-free raw RDE solve is field-level sound, from bare success + the isolated residual**: if
`crischDERawSolveWf ftilde gtilde = some y` then, under the residual `RawSolveResidualWf ftilde gtilde`, the
returned `y = ynum/yden` solves the field-level Risch DE `D(Y) + F·Y = G` for `(ftilde, gtilde)` over
`RatFunc (CFieldSpec.K β)`. Unfolds `crischDERawSolveWf` to the bare `cRischDEGWf [1]` success and applies the
Phase-P1 headline `crischDEWf_field_of_success_and_residual` (primitive regime via `cdegG_one_eq_zero_wf`).
Fuel-free analogue of `crischDESolve_field_of_witness_residual`; NO fuel, NO tower-gcd witness, NO
`native_decide`. -/
theorem crischDERawSolveWf_field_of_residual (ftilde gtilde y : QFunNZG β)
    (hsolve : crischDERawSolveWf ftilde gtilde = some y)
    (hres : RawSolveResidualWf ftilde gtilde) :
    towerFractionFieldDerivG ([CField.one] : CPolyG β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG ftilde.1.1) / amG β (toPolyG ftilde.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG gtilde.1.1) / amG β (toPolyG gtilde.1.2) := by
  -- unfold the raw solve to the bare `cRischDEGWf [1]` success
  rw [show crischDERawSolveWf ftilde gtilde
      = (match CPolyG.cRischDEGWf ([CField.one] : CPolyG β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 with
         | none => none
         | some (ynum, yden) =>
           if h : CPolyG.cisZeroG yden = false then some ⟨(ynum, yden), h⟩ else none) from rfl] at hsolve
  rcases hsucc : CPolyG.cRischDEGWf ([CField.one] : CPolyG β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2
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

/-! ### Axiom audit (fuel-free field soundness of the raw solve, NO `native_decide`) -/

#print axioms crischDERawSolveWf_field_of_residual

end DeepWiki.SymbolicIntegration
