import DeepWiki.SymbolicIntegration.Engine.OneShotSoundness
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv
import DeepWiki.SymbolicIntegration.Engine.IntegratorAssembly

/-! # Guarded primitive special integration

The primitive `b = 0` poly-RDE `cPolyRischDEGWf Dt [] fp` is term-by-term integration, correct only for
`Dt = 1` (canonical primitive) with constant coefficients (`mapCoeffs (toPolyG fp) = 0`). Rather than
assume the resulting field identity (`hspecialField`), `primitiveGuardedCase` guards the hook on those
two conditions — both *computable* (`cisZeroG (csubG Dt [1])` and `cisZeroG (cmapDeriv fp)`) — so a
successful special integration a-priori *guarantees* the identity. Declining outside the domain is honest:
the algorithm is sound and complete for the constant-coefficient canonical-primitive case, while the
non-constant case belongs to the general primitive recursion. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

/-- Rational `p/q ∈ α` (`p : ℤ`, `q : ℕ`) via the `[CField α]` casts — `p.natAbs` lifted, negated when
`p < 0`, divided by `q`. -/
def CPolyG.cRatG (p : ℤ) (q : ℕ) : α :=
  CField.div (if p < 0 then CField.neg (CPolyG.cnatCastG p.natAbs) else CPolyG.cnatCastG p.natAbs)
    (CPolyG.cnatCastG q)

/-- Automatic residue candidates from the bounded rational sweep `{p/q : |p| ≤ bound, 1 ≤ q ≤ bound}`.
`cRationalResiduesGWf` filters these to the actual residues (roots of the residue resultant), so the reduced
integrator needs *no externally supplied* candidate list for small-rational residues — `candidates` becomes
a fixed computable function. Completeness is bounded (large / non-rational residues need a bigger sweep or
root-finding); soundness is unaffected (any candidate list is filtered to genuine roots). -/
def CPolyG.defaultResidueCandidates (bound : ℕ) : List α :=
  (List.range (2 * bound + 1)).flatMap (fun i =>
    (List.range bound).map (fun j => CPolyG.cRatG ((i : ℤ) - (bound : ℤ)) (j + 1)))

omit [CRischField α] [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)] in
/-- `cisZeroG (cmapDeriv fp) = true` proves that `fp` has constant coefficients. -/
theorem mapCoeffs_eq_zero_of_cisZeroG_cmapDeriv (fp : CPolyG α)
    (h : cisZeroG (cmapDeriv fp) = true) : Differential.mapCoeffs (toPolyG fp) = 0 := by
  have hzero : toPolyG (cmapDeriv fp) = 0 := (cisZeroG_iff _).mp h
  simpa only [denote] using hzero

omit [CFracGcdCoreWf α] in
/-- The poly-RDE field identity holds for any `Dt` with `toPolyG Dt = 1`. -/
theorem field_identity_Dt1 (Dt c q : CPolyG α) (n : ℤ)
    (hDt1 : toPolyG Dt = 1) (hc : cisZeroG c = false) (hdeg : (cdegG c : ℤ) + 1 ≤ n)
    (hsome : cPolyRischDEGWf Dt ([] : CPolyG α) c n = some q)
    (hconst : Differential.mapCoeffs (toPolyG c) = 0) :
    towerFractionFieldDerivG Dt (amG α (toPolyG q) / amG α (toPolyG ([CField.one] : CPolyG α)))
      = amG α (toPolyG c) / amG α (toPolyG ([CField.one] : CPolyG α)) := by
  have hcongr : towerFractionFieldDerivG Dt = towerFractionFieldDerivG ([CField.one] : CPolyG α) := by
    unfold towerFractionFieldDerivG
    simp only [hDt1, denote, map_one, mul_zero, add_zero]
  have hsome1 : cPolyRischDEGWf ([CField.one] : CPolyG α) ([] : CPolyG α) c n = some q := by
    rw [cPolyRischDEGWf_nil_eq _ c n hc hdeg]
    rw [cPolyRischDEGWf_nil_eq _ c n hc hdeg] at hsome; exact hsome
  rw [hcongr]
  exact cPolyRischDEGWf_nil_field_identity c q n hc hdeg hsome1 hconst

omit [CFracGcdCoreWf α] in
/-- The primitive special-part identity holds under the guarded regime. -/
theorem primitive_special_identity (Dt fp qp : CPolyG α)
    (hDt1 : toPolyG Dt = 1) (hconst : Differential.mapCoeffs (toPolyG fp) = 0)
    (hsome : cPolyRischDEGWf Dt ([] : CPolyG α) fp ((cdegG fp : ℤ) + 1) = some qp) :
    towerFractionFieldDerivG Dt (amG α (toPolyG qp) / amG α (toPolyG ([CField.one] : CPolyG α)))
      = amG α (toPolyG fp) / amG α (toPolyG ([CField.one] : CPolyG α)) := by
  by_cases hfp : cisZeroG fp = true
  · -- `fp = 0`: the poly-RDE returns `[]`, both sides vanish
    have hbnil : cisZeroG ([] : CPolyG α) = true := by rw [cisZeroG_iff, toPolyG_nil]
    have hnil : cPolyRischDEGWf Dt ([] : CPolyG α) fp ((cdegG fp : ℤ) + 1) = some [] := by
      rw [cPolyRischDEGWf]; simp only [hbnil, if_true, hfp]
    rw [hnil] at hsome
    obtain rfl : qp = [] := (Option.some.injEq _ _).mp hsome.symm
    have hfp0 : toPolyG fp = 0 := (cisZeroG_iff fp).mp hfp
    rw [toPolyG_nil, hfp0, map_zero, zero_div, map_zero]
  · exact field_identity_Dt1 Dt fp qp _ hDt1 (by simpa using hfp) (le_refl _) hsome hconst

/-- The guarded primitive monomial case. -/
def primitiveGuardedCase : MonomialCase α where
  integrateSpecial Dt fp b _ds :=
    if cisZeroG b && cisZeroG (csubG Dt [CField.one]) && cisZeroG (cmapDeriv fp) then
      match cPolyRischDEGWf Dt [] fp ((cdegG fp : ℤ) + 1) with
      | none => none
      | some qp => some (qp, [CField.one])
    else none
  reducedCorrect _Dt nrm :=
    if nrm.logs.all (fun cv => cisZeroG [CDiffField.cderiv cv.1]) then some nrm else none

end DeepWiki.SymbolicIntegration
