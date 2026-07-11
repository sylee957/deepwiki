import DeepWiki.SymbolicIntegration.Engine.RischTowerPrimitiveLrt
import DeepWiki.SymbolicIntegration.Engine.IntegratorAssembly

/-! # The one-level LRT (root-free) assembler core

Combines the special/polynomial part (a rational fraction `snum/sden`, identical to the rational assembler)
with the reduced LRT result (`cIntegrateReducedLrt`, symbolic algebraic-residue logs) into a single
`LrtResult`, and proves the combined soundness `IsIntegralResultLrt`. The LRT analogue of `combineSN` /
`combineSN_isIntegralResult`: the only new content over the rational assembler is transferring the special-part
reconstruction from `K` to each splitting extension `E` via `ratFuncBaseChange` (exactly as `hherm_lrt_E` does
for the Hermite half). -/

namespace DeepWiki.SymbolicIntegration

universe u v

open DensePoly CFrac Polynomial
open scoped Differential

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Combine a special-part fraction with an LRT result in any polynomial representation. -/
def combineSNLrt {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] (snum sden : P α) (r : LrtResult α P) : LrtResult α P :=
  ⟨combineRationalParts snum sden r.rational.1 r.rational.2, r.logs⟩

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `amGExt (toPoly p) ≠ 0` when `toPoly p ≠ 0`: base change (`φ` injective) and the fraction-field
embedding are injective. -/
private theorem amGExt_ne_zero {E : Type*} [Field E] [Algebra (CFieldSpec.K α) E]
    {p : (CFieldSpec.K α)[X]} (hp : p ≠ 0) : amGExt (E := E) p ≠ 0 := by
  rw [amGExt, Ne, map_eq_zero_iff _ (IsFractionRing.injective E[X] (RatFunc E))]
  exact (Polynomial.map_ne_zero_iff (algebraMap (CFieldSpec.K α) E).injective).mpr hp

/-- **The one-level LRT assembler soundness core.** Purely from interface data — a special-part fraction
`snum/sden` and reconstruction `Δ(snum/sden) + cn/dn = a/d` (`hspecK`, over `K`, exactly as `specialSound`
supplies), plus the reduced LRT soundness `IsIntegralResultLrt Dt cn dn r` (`hNrmField`) — the combined LRT
result `combineSNLrt snum sden r` is an antiderivative of `a/d` over **every** algebraically-closed
differential extension `E`. The base-change of `hspecK` to `E` (`ratFuncBaseChange`) is the only step beyond
`combineSN_isIntegralResult`. -/
theorem combineSNLrt_isIntegralResultLrt (Dt a d cn dn snum sden : DensePoly α)
    (r : LrtResult α) (hsden : toPoly sden ≠ 0) (hgden : toPoly r.rational.2 ≠ 0)
    (hspecK : towerFractionFieldDeriv Dt (fieldFrac snum sden) + fieldFrac cn dn = fieldFrac a d)
    (hNrmField : IsIntegralResultLrt Dt cn dn r) :
    IsIntegralResultLrt Dt a d (combineSNLrt snum sden r) := by
  intro F _ _ _ _ _ _
  have hNE := hNrmField F
  have hspecE := congrArg (ratFuncBaseChange F) hspecK
  simp only [fieldFrac] at hspecE
  rw [map_add, ratFuncBaseChange_towerFractionFieldDerivG, ratFuncBaseChange_amG_div,
    ratFuncBaseChange_amG_div] at hspecE
  have hAsden : amGExt (E := F) (toPoly sden) ≠ 0 := amGExt_ne_zero hsden
  have hAgden : amGExt (E := F) (toPoly r.rational.2) ≠ 0 := amGExt_ne_zero hgden
  simp only [combineSNLrt, combineRationalParts, CPolyEngine.add_dense_eq,
    CPolyEngine.mul_dense_eq]
  have e1 : amGExt (E := F) (toPoly (cadd (cmul snum r.rational.2) (cmul r.rational.1 sden)))
      = amGExt (E := F) (toPoly snum) * amGExt (E := F) (toPoly r.rational.2)
        + amGExt (E := F) (toPoly r.rational.1) * amGExt (E := F) (toPoly sden) := by
    simp only [amGExt, denote, Polynomial.map_add, Polynomial.map_mul, map_add, map_mul]
  have e2 : amGExt (E := F) (toPoly (cmul sden r.rational.2))
      = amGExt (E := F) (toPoly sden) * amGExt (E := F) (toPoly r.rational.2) := by
    simp only [amGExt, denote, Polynomial.map_mul, map_mul]
  have hcombine : amGExt (E := F) (toPoly (cadd (cmul snum r.rational.2) (cmul r.rational.1 sden)))
        / amGExt (E := F) (toPoly (cmul sden r.rational.2))
      = amGExt (E := F) (toPoly snum) / amGExt (E := F) (toPoly sden)
        + amGExt (E := F) (toPoly r.rational.1) / amGExt (E := F) (toPoly r.rational.2) := by
    rw [e1, e2, div_add_div _ _ hAsden hAgden]; congr 1; ring
  rw [hcombine, map_add, add_assoc, hNE]
  exact hspecE

/-- **The one-level primitive LRT case integrator.** Canonical split (`canonicalRepresentationFast`) →
special part via the case hook `C.integrateSpecial` (rational, shared with the rational solver) → reduced
normal part via the root-free `cIntegrateReducedLrt` → combined with `combineSNLrt`. Unlike the retired
candidate-sweep assembler, it has no candidate sweep or `postprocessNormal` step: the primitive LRT reduced
integrator is direct). -/
def cIntegrateCaseLrt [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    (C : CMonomialCase DensePoly α) (Dt a d : DensePoly α) :
    Option (LrtResult α) :=
  -- **Primitive-case runtime guard** (`Dθ ∈ k`, i.e. `deg Dt = 0`): the LRT reduced integrator is
  -- primitive-specific, so a successful run *decides* `deg Dt = 0` — discharging `hDt0` from the branch
  -- rather than carrying it as a frontier hypothesis.
  if cdeg Dt = 0 then
    let (fp, (b, ds), (cn, dn)) := canonicalRepresentationFast Dt a d
    match C.integrateSpecial Dt fp b ds with
    | none => none
    | some (snum, sden) => some (combineSNLrt snum sden (cIntegrateReducedLrt Dt cn dn))
  else none

open Classical in
/-- **Generic primitive LRT assembler soundness.** If `cIntegrateCaseLrt C` returns `res`, the special hook
gives `(snum, sden)` with `Δ(snum/sden) = specialVal` and reconstruction `specialVal + cn/dn = a/d`, while the
reduced LRT output is both sound and denominator-certified, then `res` is an antiderivative of `a/d` over every
alg-closed `E`. The composition consumes this result-level contract; it does not name a Hermite implementation. -/
theorem cIntegrateCaseLrt_sound [CharZero (CFieldSpec.K α)]
    [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    (C : CMonomialCase DensePoly α) (Dt a d : DensePoly α) (res : LrtResult α) (snum sden : DensePoly α)
    (specialVal : RatFunc (CFieldSpec.K α))
    (hSpec : C.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d) = some (snum, sden))
    (hsome : cIntegrateCaseLrt C Dt a d = some res) (hsden : toPoly sden ≠ 0)
    (hSpecField : towerFractionFieldDeriv Dt (fieldFrac snum sden) = specialVal)
    (hNrmField : (toPoly Dt).natDegree = 0 → IsIntegralResultLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)
      (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)))
    (hredDen : (toPoly Dt).natDegree = 0 →
      toPoly (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)).rational.2 ≠ 0)
    (hrecon : specialVal + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d) :
    IsIntegralResultLrt Dt a d res := by
  -- the primitive-case guard is *decided* by a successful run: `cIntegrateCaseLrt = some res ⟹ deg Dt = 0`
  have hguard : cdeg Dt = 0 := by
    by_contra h; rw [cIntegrateCaseLrt, if_neg h] at hsome; simp at hsome
  have hDt0 : (toPoly Dt).natDegree = 0 := by rw [← cdegG_eq_natDegree]; exact hguard
  have hshape : res
      = combineSNLrt snum sden (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)) := by
    have hexp : cIntegrateCaseLrt C Dt a d
        = some (combineSNLrt snum sden (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d))) := by
      rw [cIntegrateCaseLrt, if_pos hguard]
      simp only [crPoly, crSpecNum, crSpecDen, crNormNum, crNormDen] at hSpec ⊢
      rcases hcrep : canonicalRepresentationFast Dt a d with ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
      rw [hcrep] at hSpec
      dsimp only at hSpec ⊢
      rw [hSpec]
    rw [hexp] at hsome
    exact (Option.some.injEq _ _ ▸ hsome).symm
  rw [hshape]
  refine combineSNLrt_isIntegralResultLrt Dt a d (crNormNum Dt a d) (crNormDen Dt a d) snum sden
    (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)) hsden (hredDen hDt0) ?_
      (hNrmField hDt0)
  rw [hSpecField]; exact hrecon

end DeepWiki.SymbolicIntegration
