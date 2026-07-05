import DeepWiki.SymbolicIntegration.Computable.RischTowerPrimitiveLrt
import DeepWiki.SymbolicIntegration.Computable.IntegratorAssembly

/-! # The one-level LRT (root-free) assembler core

Combines the special/polynomial part (a rational fraction `snum/sden`, identical to the rational assembler)
with the reduced LRT result (`cIntegrateReducedLrtG`, symbolic algebraic-residue logs) into a single
`LrtResultG`, and proves the combined soundness `IsIntegralResultLrtG`. The LRT analogue of `combineSN` /
`combineSN_isIntegralResult`: the only new content over the rational assembler is transferring the special-part
reconstruction from `K` to each splitting extension `E` via `ratFuncBaseChange` (exactly as `hherm_lrt_E` does
for the Hermite half). -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Combine a special-part fraction `snum/sden` with a reduced LRT result `r = gnum/gden + symbolic logs`:
`(snum·gden + gnum·sden)/(sden·gden) + logs`. The LRT analogue of `combineSN` (same rational combine, symbolic
log list carried through). -/
def combineSNLrt (snum sden : CPolyG α) (r : LrtResultG α) : LrtResultG α :=
  ⟨(caddG (cmulG snum r.rational.2) (cmulG r.rational.1 sden), cmulG sden r.rational.2), r.logs⟩

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `amGExt (toPolyG p) ≠ 0` when `toPolyG p ≠ 0`: base change (`φ` injective) and the fraction-field
embedding are injective. -/
theorem amGExt_ne_zero {E : Type*} [Field E] [Algebra (CFieldSpec.K α) E]
    {p : (CFieldSpec.K α)[X]} (hp : p ≠ 0) : amGExt (E := E) p ≠ 0 := by
  rw [amGExt, Ne, map_eq_zero_iff _ (IsFractionRing.injective E[X] (RatFunc E))]
  exact (Polynomial.map_ne_zero_iff (algebraMap (CFieldSpec.K α) E).injective).mpr hp

/-- **The one-level LRT assembler soundness core.** Purely from interface data — a special-part fraction
`snum/sden` and reconstruction `Δ(snum/sden) + cn/dn = a/d` (`hspecK`, over `K`, exactly as `specialSound`
supplies), plus the reduced LRT soundness `IsIntegralResultLrtG Dt cn dn r` (`hNrmField`) — the combined LRT
result `combineSNLrt snum sden r` is an antiderivative of `a/d` over **every** algebraically-closed
differential extension `E`. The base-change of `hspecK` to `E` (`ratFuncBaseChange`) is the only step beyond
`combineSN_isIntegralResult`. -/
theorem combineSNLrt_isIntegralResultLrt (Dt a d cn dn snum sden : CPolyG α)
    (r : LrtResultG α) (hsden : toPolyG sden ≠ 0) (hgden : toPolyG r.rational.2 ≠ 0)
    (hspecK : towerFractionFieldDerivG Dt (fieldFrac snum sden) + fieldFrac cn dn = fieldFrac a d)
    (hNrmField : IsIntegralResultLrtG Dt cn dn r) :
    IsIntegralResultLrtG Dt a d (combineSNLrt snum sden r) := by
  intro F _ _ _ _ _ _
  have hNE := hNrmField F
  have hspecE := congrArg (ratFuncBaseChange F) hspecK
  simp only [fieldFrac] at hspecE
  rw [map_add, ratFuncBaseChange_towerFractionFieldDerivG, ratFuncBaseChange_amG_div,
    ratFuncBaseChange_amG_div] at hspecE
  have hAsden : amGExt (E := F) (toPolyG sden) ≠ 0 := amGExt_ne_zero hsden
  have hAgden : amGExt (E := F) (toPolyG r.rational.2) ≠ 0 := amGExt_ne_zero hgden
  simp only [combineSNLrt]
  have e1 : amGExt (E := F) (toPolyG (caddG (cmulG snum r.rational.2) (cmulG r.rational.1 sden)))
      = amGExt (E := F) (toPolyG snum) * amGExt (E := F) (toPolyG r.rational.2)
        + amGExt (E := F) (toPolyG r.rational.1) * amGExt (E := F) (toPolyG sden) := by
    simp only [amGExt, toPolyG_caddG, toPolyG_cmulG, Polynomial.map_add, Polynomial.map_mul,
      map_add, map_mul]
  have e2 : amGExt (E := F) (toPolyG (cmulG sden r.rational.2))
      = amGExt (E := F) (toPolyG sden) * amGExt (E := F) (toPolyG r.rational.2) := by
    simp only [amGExt, toPolyG_cmulG, Polynomial.map_mul, map_mul]
  have hcombine : amGExt (E := F) (toPolyG (caddG (cmulG snum r.rational.2) (cmulG r.rational.1 sden)))
        / amGExt (E := F) (toPolyG (cmulG sden r.rational.2))
      = amGExt (E := F) (toPolyG snum) / amGExt (E := F) (toPolyG sden)
        + amGExt (E := F) (toPolyG r.rational.1) / amGExt (E := F) (toPolyG r.rational.2) := by
    rw [e1, e2, div_add_div _ _ hAsden hAgden]; congr 1; ring
  rw [hcombine, map_add, add_assoc, hNE]
  exact hspecE

/-- **The one-level primitive LRT case integrator.** Canonical split (`canonicalRepresentationFastGWf`) →
special part via the case hook `C.integrateSpecial` (rational, shared with the rational solver) → reduced
normal part via the root-free `cIntegrateReducedLrtG` → combined with `combineSNLrt`. The LRT analogue of
`cIntegrateCase` (no candidate sweep, no `reducedCorrect` post-processing: the primitive LRT reduced
integrator is direct). -/
def cIntegrateCaseLrt [CFracGcdCoreWf α] (C : MonomialCase α) (Dt a d : CPolyG α) :
    Option (LrtResultG α) :=
  let (fp, (b, ds), (cn, dn)) := canonicalRepresentationFastGWf Dt a d
  match C.integrateSpecial Dt fp b ds with
  | none => none
  | some (snum, sden) => some (combineSNLrt snum sden (cIntegrateReducedLrtG Dt cn dn))

open Classical in
/-- **Generic primitive LRT assembler soundness.** If `cIntegrateCaseLrt C` returns `res`, the special hook
gives `(snum, sden)` with `Δ(snum/sden) = specialVal` and reconstruction `specialVal + cn/dn = a/d`, and the
reduced LRT part is sound (`hNrmField`), then `res` is an antiderivative of `a/d` over every alg-closed `E`.
The LRT analogue of `cIntegrateCase_sound`; the reduced-denominator nonvanishing is *proven* here
(`toPolyG_cHermiteReduceTowerGWf_den_ne_zero` from `dₙ ≠ 0`). -/
theorem cIntegrateCaseLrt_sound [CharZero (CFieldSpec.K α)] [CFracGcdCoreWf α]
    (hgcd : GcdFFCorrect (α := α))
    (C : MonomialCase α) (Dt a d : CPolyG α) (res : LrtResultG α) (snum sden : CPolyG α)
    (specialVal : RatFunc (CFieldSpec.K α)) (hd0 : toPolyG d ≠ 0)
    (hSpec : C.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d) = some (snum, sden))
    (hsome : cIntegrateCaseLrt C Dt a d = some res) (hsden : toPolyG sden ≠ 0)
    (hSpecField : towerFractionFieldDerivG Dt (fieldFrac snum sden) = specialVal)
    (hNrmField : IsIntegralResultLrtG Dt (crNormNum Dt a d) (crNormDen Dt a d)
      (cIntegrateReducedLrtG Dt (crNormNum Dt a d) (crNormDen Dt a d)))
    (hrecon : specialVal + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d) :
    IsIntegralResultLrtG Dt a d res := by
  have hgden : toPolyG (cIntegrateReducedLrtG Dt (crNormNum Dt a d) (crNormDen Dt a d)).rational.2 ≠ 0 :=
    toPolyG_cHermiteReduceTowerGWf_den_ne_zero hgcd Dt (crNormNum Dt a d) (crNormDen Dt a d)
      (crNormDen_ne_zero_of_charZero hgcd Dt a d hd0) (Polynomial.primPart_ne_zero _)
  have hshape : res
      = combineSNLrt snum sden (cIntegrateReducedLrtG Dt (crNormNum Dt a d) (crNormDen Dt a d)) := by
    have hexp : cIntegrateCaseLrt C Dt a d
        = some (combineSNLrt snum sden (cIntegrateReducedLrtG Dt (crNormNum Dt a d) (crNormDen Dt a d))) := by
      rw [cIntegrateCaseLrt]
      simp only [crPoly, crSpecNum, crSpecDen, crNormNum, crNormDen] at hSpec ⊢
      rcases hcrep : canonicalRepresentationFastGWf Dt a d with ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
      rw [hcrep] at hSpec
      dsimp only at hSpec ⊢
      rw [hSpec]
    rw [hexp] at hsome
    exact (Option.some.injEq _ _ ▸ hsome).symm
  rw [hshape]
  refine combineSNLrt_isIntegralResultLrt Dt a d (crNormNum Dt a d) (crNormDen Dt a d) snum sden
    (cIntegrateReducedLrtG Dt (crNormNum Dt a d) (crNormDen Dt a d)) hsden hgden ?_ hNrmField
  rw [hSpecField]; exact hrecon

end DeepWiki.SymbolicIntegration
