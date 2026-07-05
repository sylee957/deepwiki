import DeepWiki.SymbolicIntegration.Computable.OneShotSoundness
import DeepWiki.SymbolicIntegration.Computable.MonomialDeriv
import DeepWiki.SymbolicIntegration.Computable.IntegratorAssembly

/-! # The guarded primitive special hook (P2: `hspecialField` becomes an algorithm guarantee)

The primitive `b = 0` poly-RDE `cPolyRischDEGWf Dt [] fp` is term-by-term integration, correct **only** for
`Dt = 1` (canonical primitive) with **constant coefficients** (`mapCoeffs (toPolyG fp) = 0`). Rather than
assume the resulting field identity (`hspecialField`), `primitiveGuardedCase` **guards** the hook on those
two conditions — both *computable* (`cisZeroG (csubG Dt [1])` and `cisZeroG (cmapDeriv fp)`) — so a
successful special integration a-priori *guarantees* the identity. Declining outside the domain is honest:
the algorithm is sound + complete for the constant-coefficient canonical-primitive case; the general
non-constant case needs the P2 recursion. -/

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

/-- **Automatic residue candidates**: the bounded rational sweep `{p/q : |p| ≤ bound, 1 ≤ q ≤ bound}`.
`cRationalResiduesGWf` filters these to the actual residues (roots of the residue resultant), so the reduced
integrator needs *no externally supplied* candidate list for small-rational residues — `candidates` becomes
a fixed computable function. Completeness is bounded (large / non-rational residues need a bigger sweep or
root-finding); soundness is unaffected (any candidate list is filtered to genuine roots). -/
def CPolyG.defaultResidueCandidates (bound : ℕ) : List α :=
  (List.range (2 * bound + 1)).flatMap (fun i =>
    (List.range bound).map (fun j => CPolyG.cRatG ((i : ℤ) - (bound : ℤ)) (j + 1)))

omit [CRischField α] [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)] in
/-- **Computable constant-coefficient guard soundness.** `cisZeroG (cmapDeriv fp) = true` (the coefficientwise
derivative vanishes) implies `mapCoeffs (toPolyG fp) = 0` (coefficients are differential constants). -/
theorem mapCoeffs_eq_zero_of_cisZeroG_cmapDeriv (fp : CPolyG α)
    (h : cisZeroG (cmapDeriv fp) = true) : Differential.mapCoeffs (toPolyG fp) = 0 := by
  rw [← toPolyG_cmapDeriv]; exact (cisZeroG_iff _).mp h

omit [CFracGcdCoreWf α] in
/-- **Generalized poly-RDE field identity for `toPolyG Dt = 1`.** The `Dt = [CField.one]` identity
`cPolyRischDEGWf_nil_field_identity` lifts to any `Dt` with `toPolyG Dt = 1`, since `towerFractionFieldDerivG`
depends only on `toPolyG Dt` and the `b = 0` branch is `Dt`-independent. -/
theorem field_identity_Dt1 (Dt c q : CPolyG α) (n : ℤ)
    (hDt1 : toPolyG Dt = 1) (hc : cisZeroG c = false) (hdeg : (cdegG c : ℤ) + 1 ≤ n)
    (hsome : cPolyRischDEGWf Dt ([] : CPolyG α) c n = some q)
    (hconst : Differential.mapCoeffs (toPolyG c) = 0) :
    towerFractionFieldDerivG Dt (amG α (toPolyG q) / amG α (toPolyG ([CField.one] : CPolyG α)))
      = amG α (toPolyG c) / amG α (toPolyG ([CField.one] : CPolyG α)) := by
  have hcongr : towerFractionFieldDerivG Dt = towerFractionFieldDerivG ([CField.one] : CPolyG α) := by
    unfold towerFractionFieldDerivG; rw [hDt1, toPolyG_one_singleton]
  have hsome1 : cPolyRischDEGWf ([CField.one] : CPolyG α) ([] : CPolyG α) c n = some q := by
    rw [cPolyRischDEGWf_nil_eq _ c n hc hdeg]
    rw [cPolyRischDEGWf_nil_eq _ c n hc hdeg] at hsome; exact hsome
  rw [hcongr]
  exact cPolyRischDEGWf_nil_field_identity c q n hc hdeg hsome1 hconst

omit [CFracGcdCoreWf α] in
/-- **The primitive special-part identity, unconditional on the guarded regime.** If `toPolyG Dt = 1`, the
coefficients of `fp` are constant, and the poly-RDE returns `qp`, then `qp/1` differentiates to `⟦fp⟧` —
covering both `fp = 0` (`qp = 0`, trivial) and `fp ≠ 0` (`field_identity_Dt1`). -/
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

/-- **The guarded primitive monomial case.** `integrateSpecial` runs the `b = 0` poly-RDE only when the
computable guards hold: `b = 0`, `toPolyG Dt = 1` (`cisZeroG (csubG Dt [1])`), and constant coefficients
(`cisZeroG (cmapDeriv fp)`). Otherwise it declines. `reducedCorrect` applies the **integrability guard**
(Bronstein §5.6): the reduced log part is a valid antiderivative only when each residue `c` is a constant
(`D c = 0`) — otherwise `D(c·log v)` carries a spurious `Dc·log v` — so it accepts iff every residue is
constant (`cisZeroG [D c]`), declining non-elementary reduced parts. The root-free analogue of the hyperexp
`∑cᵢ = 0` guard. -/
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
