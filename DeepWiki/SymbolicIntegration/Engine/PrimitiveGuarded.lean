import DeepWiki.SymbolicIntegration.Engine.OneShotSoundness
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv
import DeepWiki.SymbolicIntegration.Engine.IntegratorAssembly
import DeepWiki.SymbolicIntegration.Engine.ResidueSource
import DeepWiki.SymbolicIntegration.Engine.LrtMonomialCase

/-! # Guarded primitive special integration

The primitive `b = 0` poly-RDE `cPolyRischDE Dt [] fp` is term-by-term integration, correct only for
`Dt = 1` (canonical primitive) with constant coefficients (`mapCoeffs (toPoly fp) = 0`). Rather than
assume the resulting field identity (`hspecialField`), `primitiveGuardedCase` guards the hook on those
two conditions — both *computable* (`cisZero (csub Dt [1])` and `cisZero (CPolyEngine.mapDeriv fp)`) — so a
successful special integration a-priori *guarantees* the identity. Declining outside the domain is honest:
the algorithm is sound and complete for the constant-coefficient canonical-primitive case, while the
non-constant case belongs to the general primitive recursion. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

omit [CRischField α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)] in
/-- `cisZero (CPolyEngine.mapDeriv fp) = true` proves that `fp` has constant coefficients. -/
theorem mapCoeffs_eq_zero_of_cisZeroG_cmapDeriv (fp : DensePoly α)
    (h : cisZero (CPolyEngine.mapDeriv fp) = true) : Differential.mapCoeffs (toPoly fp) = 0 := by
  have hzero : toPoly (CPolyEngine.mapDeriv fp) = 0 := (cisZeroG_iff _).mp h
  simpa only [denote] using hzero

/-- The poly-RDE field identity holds for any `Dt` with `toPoly Dt = 1`. -/
theorem field_identity_Dt1 (Dt c q : DensePoly α) (n : ℤ)
    (hDt1 : toPoly Dt = 1) (hc : cisZero c = false) (hdeg : (cdeg c : ℤ) + 1 ≤ n)
    (hsome : cPolyRischDE Dt ([] : DensePoly α) c n = some q)
    (hconst : Differential.mapCoeffs (toPoly c) = 0) :
    towerFractionFieldDeriv Dt (am α (toPoly q) / am α (toPoly ([CCommRing.one] : DensePoly α)))
      = am α (toPoly c) / am α (toPoly ([CCommRing.one] : DensePoly α)) := by
  have hcongr : towerFractionFieldDeriv Dt = towerFractionFieldDeriv ([CCommRing.one] : DensePoly α) := by
    unfold towerFractionFieldDeriv
    simp only [hDt1, denote, map_one, mul_zero, add_zero]
  have hsome1 : cPolyRischDE ([CCommRing.one] : DensePoly α) ([] : DensePoly α) c n = some q := by
    rw [cPolyRischDEG_nil_eq _ c n hc hdeg]
    rw [cPolyRischDEG_nil_eq _ c n hc hdeg] at hsome; exact hsome
  rw [hcongr]
  exact cPolyRischDEG_nil_field_identity c q n hc hdeg hsome1 hconst

/-- The primitive special-part identity holds under the guarded regime. -/
theorem primitive_special_identity (Dt fp qp : DensePoly α)
    (hDt1 : toPoly Dt = 1) (hconst : Differential.mapCoeffs (toPoly fp) = 0)
    (hsome : cPolyRischDE Dt ([] : DensePoly α) fp ((cdeg fp : ℤ) + 1) = some qp) :
    towerFractionFieldDeriv Dt (am α (toPoly qp) / am α (toPoly ([CCommRing.one] : DensePoly α)))
      = am α (toPoly fp) / am α (toPoly ([CCommRing.one] : DensePoly α)) := by
  by_cases hfp : cisZero fp = true
  · -- `fp = 0`: the poly-RDE returns `[]`, both sides vanish
    have hbnil : cisZero ([] : DensePoly α) = true := by rw [cisZeroG_iff, toPolyG_nil]
    have hnil : cPolyRischDE Dt ([] : DensePoly α) fp ((cdeg fp : ℤ) + 1) = some [] := by
      rw [cPolyRischDE]; simp only [hbnil, if_true, hfp]
    rw [hnil] at hsome
    obtain rfl : qp = [] := (Option.some.injEq _ _).mp hsome.symm
    have hfp0 : toPoly fp = 0 := (cisZeroG_iff fp).mp hfp
    rw [toPolyG_nil, hfp0, map_zero, zero_div, map_zero]
  · exact field_identity_Dt1 Dt fp qp _ hDt1 (by simpa using hfp) (le_refl _) hsome hconst

/-- Rational kernel shared by the generic and LRT guarded primitive special stages. -/
private def primitiveGuardedRationalSpecial (Dt fp b : DensePoly α) :
    Option (DensePoly α × DensePoly α) :=
    if cisZero b && cisZero (csub Dt [CCommRing.one]) && cisZero (CPolyEngine.mapDeriv fp) then
      match cPolyRischDE Dt [] fp ((cdeg fp : ℤ) + 1) with
      | none => none
      | some qp => some (qp, [CCommRing.one])
    else none

/-- The guarded primitive monomial case. -/
def primitiveGuardedCase : CMonomialCase DensePoly α where
  integrateSpecial Dt fp b _ds :=
    (primitiveGuardedRationalSpecial Dt fp b).map fun rational => { rational, logs := [] }
  postprocessNormal _Dt nrm :=
    if nrm.logs.all (fun cv => cisZero [CDiffField.cderiv cv.1]) then some nrm else none

/-- The guarded primitive hook satisfies the sound monomial-case contract. -/
instance instLawfulCMonomialCasePrimitiveGuarded :
    LawfulCMonomialCase (primitiveGuardedCase (α := α)) where
  special_sound Dt fp b ds res hsome := by
    simp only [primitiveGuardedCase, primitiveGuardedRationalSpecial] at hsome
    by_cases hguard : (cisZero b && cisZero (csub Dt [CCommRing.one]) &&
        cisZero (CPolyEngine.mapDeriv fp)) = true
    · rw [if_pos hguard] at hsome
      rw [Bool.and_eq_true, Bool.and_eq_true] at hguard
      obtain ⟨⟨hb, hDt1g⟩, hconstg⟩ := hguard
      rcases hqp : cPolyRischDE Dt [] fp ((cdeg fp : ℤ) + 1) with _ | qp
      · rw [hqp] at hsome
        simp at hsome
      · rw [hqp] at hsome
        simp only [Option.map_some, Option.some.injEq] at hsome
        subst res
        have hDt1 : toPoly Dt = 1 := by
          have hzero := (cisZeroG_iff (csub Dt [CCommRing.one])).mp hDt1g
          simpa only [denote, map_one, mul_zero, add_zero, sub_eq_zero] using hzero
        have hconst := mapCoeffs_eq_zero_of_cisZeroG_cmapDeriv fp hconstg
        have hpoly := primitive_special_identity Dt fp qp hDt1 hconst hqp
        have hb0 : toPoly b = 0 := (cisZeroG_iff b).mp hb
        constructor
        · change CPoly.toPoly (CPoly.one : DensePoly α) ≠ 0
          rw [CPoly.toPoly_one]
          exact one_ne_zero
        · simp only [fieldFracP, towerFractionFieldDerivP, toPoly_list_eq,
            logResidueSumP_nil, add_zero]
          rw [show (CPoly.one : DensePoly α) = [CCommRing.one] from rfl]
          rw [hb0, map_zero, zero_div, add_zero]
          simpa only [towerFractionFieldDeriv] using hpoly
    · rw [if_neg hguard] at hsome
      simp at hsome
  postprocessNormal_sound _ _ _ before after _ hpost := by
    simp only [primitiveGuardedCase] at hpost
    split at hpost <;> simp_all
  postprocessNormal_den_nonzero _ before after hden hpost := by
    simp only [primitiveGuardedCase] at hpost
    split at hpost <;> simp_all

/-- Rational-only guarded primitive special stage used by the root-free LRT assembler. -/
def primitiveGuardedLrtCase : CLrtMonomialCase DensePoly α where
  integrateSpecial Dt fp b _ds := primitiveGuardedRationalSpecial Dt fp b

/-- The rational-only primitive stage satisfies the LRT monomial contract. -/
instance instLawfulCLrtMonomialCasePrimitiveGuarded :
    LawfulCLrtMonomialCase (primitiveGuardedLrtCase (α := α)) where
  special_sound Dt fp b ds snum sden hrun := by
    have hfull : primitiveGuardedCase.integrateSpecial Dt fp b ds =
        some ({ rational := (snum, sden), logs := [] } : IntegralResult α) := by
      simp only [primitiveGuardedCase, primitiveGuardedLrtCase] at hrun ⊢
      rw [hrun]
      rfl
    have hsound := LawfulCMonomialCase.special_sound (C := primitiveGuardedCase)
      Dt fp b ds ({ rational := (snum, sden), logs := [] } : IntegralResult α) hfull
    exact ⟨hsound.1, by simpa only [logResidueSumP_nil, add_zero] using hsound.2⟩

end DeepWiki.SymbolicIntegration
