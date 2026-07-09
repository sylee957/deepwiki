import DeepWiki.SymbolicIntegration.Engine.OneShotSoundness
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv
import DeepWiki.SymbolicIntegration.Engine.IntegratorAssembly

/-! # Guarded primitive special integration

The primitive `b = 0` poly-RDE `cPolyRischDE Dt [] fp` is term-by-term integration, correct only for
`Dt = 1` (canonical primitive) with constant coefficients (`mapCoeffs (toPoly fp) = 0`). Rather than
assume the resulting field identity (`hspecialField`), `primitiveGuardedCase` guards the hook on those
two conditions — both *computable* (`cisZero (csub Dt [1])` and `cisZero (cmapDeriv fp)`) — so a
successful special integration a-priori *guarantees* the identity. Declining outside the domain is honest:
the algorithm is sound and complete for the constant-coefficient canonical-primitive case, while the
non-constant case belongs to the general primitive recursion. -/

namespace DeepWiki.SymbolicIntegration

open CPoly CFrac Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

/-- Rational `p/q ∈ α` (`p : ℤ`, `q : ℕ`) via the `[CField α]` casts — `p.natAbs` lifted, negated when
`p < 0`, divided by `q`. -/
def CPoly.cRat (p : ℤ) (q : ℕ) : α :=
  CField.div (if p < 0 then CField.neg (CPoly.cnatCast p.natAbs) else CPoly.cnatCast p.natAbs)
    (CPoly.cnatCast q)

/-- Automatic residue candidates from the bounded rational sweep `{p/q : |p| ≤ bound, 1 ≤ q ≤ bound}`.
`cRationalResidues` filters these to the actual residues (roots of the residue resultant), so the reduced
integrator needs *no externally supplied* candidate list for small-rational residues — `candidates` becomes
a fixed computable function. Completeness is bounded (large / non-rational residues need a bigger sweep or
root-finding); soundness is unaffected (any candidate list is filtered to genuine roots). -/
def CPoly.defaultResidueCandidates (bound : ℕ) : List α :=
  (List.range (2 * bound + 1)).flatMap (fun i =>
    (List.range bound).map (fun j => CPoly.cRat ((i : ℤ) - (bound : ℤ)) (j + 1)))

omit [CRischField α] [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)] in
/-- `cisZero (cmapDeriv fp) = true` proves that `fp` has constant coefficients. -/
theorem mapCoeffs_eq_zero_of_cisZeroG_cmapDeriv (fp : CPoly α)
    (h : cisZero (cmapDeriv fp) = true) : Differential.mapCoeffs (toPoly fp) = 0 := by
  have hzero : toPoly (cmapDeriv fp) = 0 := (cisZeroG_iff _).mp h
  simpa only [denote] using hzero

omit [CFracGcdCoreWf α] in
/-- The poly-RDE field identity holds for any `Dt` with `toPoly Dt = 1`. -/
theorem field_identity_Dt1 (Dt c q : CPoly α) (n : ℤ)
    (hDt1 : toPoly Dt = 1) (hc : cisZero c = false) (hdeg : (cdeg c : ℤ) + 1 ≤ n)
    (hsome : cPolyRischDE Dt ([] : CPoly α) c n = some q)
    (hconst : Differential.mapCoeffs (toPoly c) = 0) :
    towerFractionFieldDeriv Dt (am α (toPoly q) / am α (toPoly ([CField.one] : CPoly α)))
      = am α (toPoly c) / am α (toPoly ([CField.one] : CPoly α)) := by
  have hcongr : towerFractionFieldDeriv Dt = towerFractionFieldDeriv ([CField.one] : CPoly α) := by
    unfold towerFractionFieldDeriv
    simp only [hDt1, denote, map_one, mul_zero, add_zero]
  have hsome1 : cPolyRischDE ([CField.one] : CPoly α) ([] : CPoly α) c n = some q := by
    rw [cPolyRischDEG_nil_eq _ c n hc hdeg]
    rw [cPolyRischDEG_nil_eq _ c n hc hdeg] at hsome; exact hsome
  rw [hcongr]
  exact cPolyRischDEG_nil_field_identity c q n hc hdeg hsome1 hconst

omit [CFracGcdCoreWf α] in
/-- The primitive special-part identity holds under the guarded regime. -/
theorem primitive_special_identity (Dt fp qp : CPoly α)
    (hDt1 : toPoly Dt = 1) (hconst : Differential.mapCoeffs (toPoly fp) = 0)
    (hsome : cPolyRischDE Dt ([] : CPoly α) fp ((cdeg fp : ℤ) + 1) = some qp) :
    towerFractionFieldDeriv Dt (am α (toPoly qp) / am α (toPoly ([CField.one] : CPoly α)))
      = am α (toPoly fp) / am α (toPoly ([CField.one] : CPoly α)) := by
  by_cases hfp : cisZero fp = true
  · -- `fp = 0`: the poly-RDE returns `[]`, both sides vanish
    have hbnil : cisZero ([] : CPoly α) = true := by rw [cisZeroG_iff, toPolyG_nil]
    have hnil : cPolyRischDE Dt ([] : CPoly α) fp ((cdeg fp : ℤ) + 1) = some [] := by
      rw [cPolyRischDE]; simp only [hbnil, if_true, hfp]
    rw [hnil] at hsome
    obtain rfl : qp = [] := (Option.some.injEq _ _).mp hsome.symm
    have hfp0 : toPoly fp = 0 := (cisZeroG_iff fp).mp hfp
    rw [toPolyG_nil, hfp0, map_zero, zero_div, map_zero]
  · exact field_identity_Dt1 Dt fp qp _ hDt1 (by simpa using hfp) (le_refl _) hsome hconst

/-- The guarded primitive monomial case. -/
def primitiveGuardedCase : MonomialCase α where
  integrateSpecial Dt fp b _ds :=
    if cisZero b && cisZero (csub Dt [CField.one]) && cisZero (cmapDeriv fp) then
      match cPolyRischDE Dt [] fp ((cdeg fp : ℤ) + 1) with
      | none => none
      | some qp => some (qp, [CField.one])
    else none
  reducedCorrect _Dt nrm :=
    if nrm.logs.all (fun cv => cisZero [CDiffField.cderiv cv.1]) then some nrm else none

end DeepWiki.SymbolicIntegration
