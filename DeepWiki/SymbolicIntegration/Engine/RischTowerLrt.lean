import DeepWiki.SymbolicIntegration.Engine.RischTowerPrimitive
import DeepWiki.SymbolicIntegration.Engine.LrtAssembly
import DeepWiki.SymbolicIntegration.Engine.LrtAlgebraicClosure
import DeepWiki.SymbolicIntegration.Engine.PrimitiveLrtDecision
import DeepWiki.SymbolicIntegration.Engine.LimitedIntegrateSingle

/-! # Recursive LRT (algebraic-residue) Risch-level interface

The re-based analogue of `LawfulRischLevel`: same `X`/`LawfulX` idiom, but the assembled solver produces an
`LrtResult` (symbolic algebraic-residue logs `Σ_{Rᵢ(c)=0} c·log Sᵢ(c,t)`) via the root-free assembler
`cIntegrateCaseLrt`. The payoff is that its reduced-part frontier is the **dischargeable** `PrimitiveFrontierLrt`
(closed to `LrtReducedGenuineData` by `hreducedLrt_of_genuineAll`) rather than the rational `PrimitiveFrontier`,
which is *not* universally dischargeable — the rational reduced soundness `IsIntegralResult` forces the reduced
denominator to split over `K`, false when the residues are algebraic. The special/polynomial part is unchanged
(`specialSound`, a `K`-level identity, shared verbatim with the rational solver).

Materialize one `CRischLevelLrt` operation and its `LawfulCRischLevelLrt` contract; the assembled integrator
and soundness theorem then compose them directly. The base is `instCRischLevelLrtPrimitive` (from
`[PrimitiveFrontierLrt α]`, reusing
`primitiveGuardedCase_specialSound` — no coefficient recursion at the base); the tower step (the recursion into
the coefficient field) is built in `RischSolverTowerLrt.lean`. See `docs/recursive-lrt-typeclass.md`. -/

namespace DeepWiki.SymbolicIntegration

universe u v

open DensePoly CFrac Polynomial
open scoped Differential

/-- Prop-free executable capability for Bronstein's single-generator limited integration. -/
class CLimitedIntegrateSingleLrt (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)] where
  /-- Attempt `(anum/aden) = D(bnum/bden) + c·(ηnum/ηden)`. -/
  run : DensePoly α → DensePoly α → DensePoly α → DensePoly α →
    Option ((DensePoly α × DensePoly α) × α)

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

/-- Prop-free executable hooks for one recursive algebraic-residue Risch level. -/
class CRischLevelLrt (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)] where
  /-- The per-monomial-case computable hooks for this level (the special/polynomial-part integrator). -/
  case : CMonomialCase DensePoly α

/-- Soundness contract for a single-generator limited-integration capability. -/
class LawfulCLimitedIntegrateSingleLrt {α : Type*} [CField α] [CFieldSpec α] [CDiffField α]
    [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    (C : CLimitedIntegrateSingleLrt α) : Prop where
  /-- Every successful run returns a valid limited-integration decomposition. -/
  sound : ∀ (anum aden ηnum ηden bnum bden : DensePoly α) (c : α),
    toPoly aden ≠ 0 → toPoly ηden ≠ 0 →
    C.run anum aden ηnum ηden = some ((bnum, bden), c) →
      DensePoly.IsLimitedIntegrateSingleResult anum aden ηnum ηden bnum bden c

/-- Semantic domain on which a single-generator limited solver is required to be complete. -/
abbrev LimitedIntegrateSingleDomain (α : Type*) :=
  DensePoly α → DensePoly α → DensePoly α → DensePoly α → Prop

/-- A single-generator limited problem admits a denotational solution. -/
def IsLimitedIntegrateSingleIntegrable
    (anum aden ηnum ηden : DensePoly α) : Prop :=
  ∃ bnum bden c, DensePoly.IsLimitedIntegrateSingleResult
    anum aden ηnum ηden bnum bden c

/-- Domain-relative completeness contract for a single-generator limited solver. -/
class CompleteCLimitedIntegrateSingleLrt (C : CLimitedIntegrateSingleLrt α)
    (domain : LimitedIntegrateSingleDomain α) [LawfulCLimitedIntegrateSingleLrt C] : Prop where
  /-- Every domain problem admitting a semantic solution is accepted with a certified result. -/
  complete : ∀ (anum aden ηnum ηden : DensePoly α),
    domain anum aden ηnum ηden → IsLimitedIntegrateSingleIntegrable anum aden ηnum ηden →
      ∃ bnum bden c, C.run anum aden ηnum ηden = some ((bnum, bden), c) ∧
        DensePoly.IsLimitedIntegrateSingleResult anum aden ηnum ηden bnum bden c

/-- Certified base-field limited integration over `ℚ`. -/
@[reducible] def limitedIntegrateSingleLrtBase : CLimitedIntegrateSingleLrt ℚ where
  run := DensePoly.checkedLimitedIntegrateSingleBaseNumDen

/-- The certified base limited-integration capability satisfies its semantic contract. -/
instance instLawfulCLimitedIntegrateSingleLrtBase :
    LawfulCLimitedIntegrateSingleLrt limitedIntegrateSingleLrtBase where
  sound := DensePoly.checkedLimitedIntegrateSingleBaseNumDen_sound

/-- The checked base solver is complete on its exact executable acceptance domain. -/
instance instCompleteCLimitedIntegrateSingleLrtBase :
    CompleteCLimitedIntegrateSingleLrt limitedIntegrateSingleLrtBase
      DensePoly.CheckedLimitedIntegrateSingleBaseDomain where
  complete anum aden ηnum ηden hdomain _ := by
    obtain ⟨⟨⟨bnum, bden⟩, c⟩, hrun⟩ := hdomain
    refine ⟨bnum, bden, c, hrun, ?_⟩
    apply DensePoly.checkedLimitedIntegrateSingleBaseNumDen_sound anum aden ηnum ηden
      bnum bden c
    · by_contra hzero
      have hz : CPolyEngine.cisZero aden = true :=
        (LawfulCPolyEngine.cisZero_iff (P := DensePoly) aden).2 (by
          simpa only [toPoly_list_eq] using hzero)
      unfold DensePoly.checkedLimitedIntegrateSingleBaseNumDen at hrun
      unfold DensePoly.limitedIntegrateSingleBaseNumDen at hrun
      have hzDense : DensePoly.cisZero aden = true := hz
      have hguard : ¬ DensePoly.cisZero aden = false := by
        rw [hzDense]
        decide
      simp only [dif_neg hguard, Option.bind_none] at hrun
      contradiction
    · by_contra hzero
      have hz : CPolyEngine.cisZero ηden = true :=
        (LawfulCPolyEngine.cisZero_iff (P := DensePoly) ηden).2 (by
          simpa only [toPoly_list_eq] using hzero)
      unfold DensePoly.checkedLimitedIntegrateSingleBaseNumDen at hrun
      unfold DensePoly.limitedIntegrateSingleBaseNumDen at hrun
      split at hrun
      · have hzDense : DensePoly.cisZero ηden = true := hz
        have hguard : ¬ DensePoly.cisZero ηden = false := by
          rw [hzDense]
          decide
        simp only [dif_neg hguard, Option.bind_none] at hrun
        contradiction
      · simp at hrun
    · exact hrun

/-- Conservative fallback when no specialized limited integrator is available. -/
instance instCLimitedIntegrateSingleLrtNone : CLimitedIntegrateSingleLrt α where
  run := fun _ _ _ _ => none

/-- The conservative fallback is sound because it never returns a result. -/
instance instLawfulCLimitedIntegrateSingleLrtNone :
    LawfulCLimitedIntegrateSingleLrt (inferInstance : CLimitedIntegrateSingleLrt α) where
  sound := by
    intro anum aden ηnum ηden bnum bden c _ _ h
    change (none : Option ((DensePoly α × DensePoly α) × α)) = some ((bnum, bden), c) at h
    contradiction

/-- The checked rational-base implementation of single-generator limited integration. -/
instance instCLimitedIntegrateSingleLrtRat : CLimitedIntegrateSingleLrt ℚ :=
  limitedIntegrateSingleLrtBase

example :
    ((inferInstance : CLimitedIntegrateSingleLrt ℚ).run [1, 1] [0, 1] [1] [0, 1]).map
      (fun r => (CPoly.normalizeFracPair r.1.1 r.1.2, r.2)) = some (([0, 1], [1]), 1) := by
  ccompute

/-- Denotation-level soundness contract for a recursive LRT operation. -/
class LawfulCRischLevelLrt {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    (C : CRischLevelLrt α) : Prop where
  /-- Special-part reconstruction for `C`. -/
  specialSound : ∀ (Dt a d snum sden : DensePoly α), toPoly d ≠ 0 →
    C.case.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d) = some (snum, sden) →
    toPoly sden ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K α),
      towerFractionFieldDeriv Dt (fieldFrac snum sden) = v ∧
      v + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d
  /-- Algebraic-residue soundness for `C`'s reduced part. -/
  reducedSoundLrt : ∀ (Dt a d : DensePoly α), toPoly d ≠ 0 → (toPoly Dt).natDegree = 0 →
    IsIntegralResultLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)
      (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d))
  /-- The selected reduced LRT rational denominator is nonzero. -/
  reducedDenNonzero : ∀ (Dt a d : DensePoly α), toPoly d ≠ 0 → (toPoly Dt).natDegree = 0 →
    toPoly (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)).rational.2 ≠ 0

namespace CRischLevelLrt

/-- **The assembled LRT integrator** — a function of `(Dt, a, d)` alone, via the root-free assembler
`cIntegrateCaseLrt` (no candidate sweep). **Guards on `d ≠ 0`**, so a successful run supplies `d ≠ 0` to the
soundness laws. -/
def integrate [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] [CPolySubresultant DensePoly] (C : CRischLevelLrt α)
    (Dt a d : DensePoly α) : Option (LrtResult α) :=
  if cisZero d then none else cIntegrateCaseLrt C.case Dt a d

end CRischLevelLrt

/-- Semantic domain predicate for a recursive algebraic-residue Risch level. -/
abbrev RischLevelLrtDomain (α : Type u) := DensePoly α → DensePoly α → DensePoly α → Prop

/-- Primitive-level domain with an explicit special-stage decomposition witness. -/
def primitiveRischLevelLrtDomain [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    (C : CRischLevelLrt α) : RischLevelLrtDomain α :=
  fun Dt a d => (toPoly Dt).natDegree = 0 ∧
    (IsElementaryIntegrableLrt Dt a d →
      ∃ snum sden, C.case.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d)
        (crSpecDen Dt a d) = some (snum, sden))

namespace CRischLevelLrt

/-- **Formal LRT soundness.** Any successful run satisfies the algebraic-residue log-derivative identity
`IsIntegralResultLrt` — over every alg-closed differential extension `E`, `D_E(rational) + Σ residue logs =
a/d`. Composed from the instance's `specialSound` + `reducedSoundLrt` through the assembler soundness
`cIntegrateCaseLrt_sound`. -/
theorem soundFormalLrt [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    (C : CRischLevelLrt α) [LawfulCRischLevelLrt C] (Dt a d : DensePoly α) (res : LrtResult α)
    (h : C.integrate Dt a d = some res) : IsIntegralResultLrt Dt a d res := by
  rw [integrate] at h
  by_cases hdz : cisZero d = true
  · rw [if_pos hdz] at h; simp at h
  · rw [if_neg hdz] at h
    have hd0 : toPoly d ≠ 0 := fun hh => hdz ((cisZeroG_iff d).mpr hh)
    have h0 : cIntegrateCaseLrt C.case Dt a d = some res := h
    rw [cIntegrateCaseLrt] at h
    rcases hcrep : canonicalRepresentationFast Dt a d with ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
    rw [hcrep] at h
    dsimp only at h
    rcases hspec : C.case.integrateSpecial Dt fp b ds with _ | ⟨snum, sden⟩
    · rw [hspec] at h; simp at h
    · rw [hspec] at h
      have hSpec : C.case.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d)
          = some (snum, sden) := by
        simp only [crPoly, crSpecNum, crSpecDen, hcrep]; exact hspec
      obtain ⟨hsden, v, hSpecField, hrecon⟩ := LawfulCRischLevelLrt.specialSound Dt a d snum sden hd0 hSpec
      have hNrm := LawfulCRischLevelLrt.reducedSoundLrt C Dt a d hd0
      have hredDen := LawfulCRischLevelLrt.reducedDenNonzero C Dt a d hd0
      exact cIntegrateCaseLrt_sound C.case Dt a d res snum sden v
        hSpec h0 hsden hSpecField hNrm hredDen hrecon

end CRischLevelLrt

/-- Relative-completeness contract for a lawful recursive algebraic-residue Risch level. -/
class CompleteCRischLevelLrt [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    (C : CRischLevelLrt α) (domain : RischLevelLrtDomain α) [LawfulCRischLevelLrt C] : Prop where
  /-- Every genuinely integrable input in the explicit domain is accepted. -/
  relative_complete : ∀ (Dt a d : DensePoly α),
    domain Dt a d → toPoly d ≠ 0 → IsElementaryIntegrableLrt Dt a d →
      ∃ res, C.integrate Dt a d = some res

/-- The recursive LRT assembler is relatively complete from its special-stage decomposition witness. -/
instance instCompleteCRischLevelLrtPrimitiveDomain
    [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    (C : CRischLevelLrt α) [LawfulCRischLevelLrt C] :
    CompleteCRischLevelLrt C (primitiveRischLevelLrtDomain C) where
  relative_complete Dt a d hdomain hd hintegrable := by
    obtain ⟨snum, sden, hspecial⟩ := hdomain.2 hintegrable
    refine ⟨combineSNLrt snum sden
      (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)), ?_⟩
    have hdz : cisZero d = false := by
      rw [Bool.eq_false_iff]
      intro hzero
      exact hd ((cisZeroG_iff d).mp hzero)
    have hdegree : cdeg Dt = 0 := by
      rw [cdegG_eq_natDegree]
      exact hdomain.1
    rw [CRischLevelLrt.integrate, hdz, cIntegrateCaseLrt, if_pos hdegree]
    simp only [crPoly, crSpecNum, crSpecDen, crNormNum, crNormDen] at hspecial ⊢
    rcases hcanonical : canonicalRepresentationFast Dt a d with
      ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
    rw [hcanonical] at hspecial
    simp [hspecial]

/-- On the explicit decomposition domain, the lawful LRT assembler succeeds exactly on integrable inputs. -/
theorem rischLevelLrt_succeeds_iff_integrable
    [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    (C : CRischLevelLrt α) [LawfulCRischLevelLrt C]
    (domain : RischLevelLrtDomain α) [CompleteCRischLevelLrt C domain]
    (Dt a d : DensePoly α) (hdomain : domain Dt a d) (hd : toPoly d ≠ 0) :
    IsElementaryIntegrableLrt Dt a d ↔ ∃ res, C.integrate Dt a d = some res := by
  constructor
  · exact CompleteCRischLevelLrt.relative_complete Dt a d hdomain hd
  · rintro ⟨res, hrun⟩
    exact ⟨res, C.soundFormalLrt Dt a d res hrun⟩

namespace CRischLevelLrt

/-- **Derived broad elementary integrability.** A successful LRT run certifies `a/d` is elementary integrable in
the broad (algebraic-residue) sense — `IsElementaryIntegrableLrt`, via `soundFormalLrt`. -/
theorem isElementaryIntegrableLrt_of_run [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    (C : CRischLevelLrt α) [LawfulCRischLevelLrt C] (Dt a d : DensePoly α)
    (res : LrtResult α) (h : C.integrate Dt a d = some res) : IsElementaryIntegrableLrt Dt a d :=
  ⟨res, C.soundFormalLrt Dt a d res h⟩

/-- **Limited (log-free) LRT integration** — `integrate` restricted to results with **no** algebraic-residue
logs. A log-free antiderivative is purely rational, so it needs no algebraic closure to state — making this the
right coefficient integrator for the tower recursion (the LRT analogue of the rational `integrateRational`). -/
def integrateRationalLrt [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    (C : CRischLevelLrt α) (Dt a d : DensePoly α) : Option (DensePoly α × DensePoly α) :=
  (C.integrate Dt a d).bind fun r => if r.logs.isEmpty then some r.rational else none

/-- **★ K-level soundness of the log-free LRT integrator** — the ∀E ⇒ K descent for log-free results. A
successful `integrateRationalLrt` run gives the **base-level** identity `D_tower(num/den) = a/d` in
`RatFunc (CFieldSpec.K α)`, with no algebraic-closure extension. The `∀E` LRT soundness instantiates at the
algebraic closure (`isIntegralResultLrtG_algebraicClosure`); the empty log part drops (`logResidueSumLrtG_nil`);
the two sides are base-changes of the `K`-level fractions (`ratFuncBaseChange_towerFractionFieldDerivG`,
`ratFuncBaseChange_amG_div`), so the `K`-identity follows by **injectivity of the field hom `ratFuncBaseChange`**.
This is the `intR`-soundness the tower coefficient recursion consumes — descent-free `K`-level, exactly like
`integrateRational_sound` on the rational side. -/
theorem integrateRationalLrt_sound [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    (C : CRischLevelLrt α) [LawfulCRischLevelLrt C] (Dt a d num den : DensePoly α)
    (h : C.integrateRationalLrt Dt a d = some (num, den)) :
    towerFractionFieldDeriv Dt (am α (toPoly num) / am α (toPoly den))
      = am α (toPoly a) / am α (toPoly d) := by
  unfold integrateRationalLrt at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨r, hint, hguard⟩ := h
  split at hguard
  · rename_i hemp
    have hrat : r.rational = (num, den) := (Option.some.injEq _ _).mp hguard
    have hnum : r.rational.1 = num := by rw [hrat]
    have hden : r.rational.2 = den := by rw [hrat]
    have hlogs : r.logs = [] := List.isEmpty_iff.mp hemp
    -- the `∀E` identity, instantiated at the canonical algebraic closure
    have hE := isIntegralResultLrtG_algebraicClosure Dt a d r (C.soundFormalLrt Dt a d r hint)
    rw [hlogs, logResidueSumLrtG_nil, add_zero, hnum, hden] at hE
    -- both sides are `ratFuncBaseChange` of the `K`-level fractions; invert and use injectivity
    rw [← ratFuncBaseChange_towerFractionFieldDerivG, ← ratFuncBaseChange_amG_div] at hE
    exact (ratFuncBaseChange (AlgebraicClosure (CFieldSpec.K α))).injective hE
  · exact absurd hguard (by simp)

/-- **★ Derived decision procedure — completeness meets soundness at the class.** The *same* instance that
gives `soundFormalLrt` also **decides** genuine (algebraic-residue) elementary integrability of the reduced
normal part `cₙ/dₙ`, once the Liouville completeness frontier `[LrtLiouvilleFrontier α]` is available:
integrability **iff** the root-free residue guard passes. The `←` (sufficiency) draws on the instance's own
`reducedSoundLrt`; the `→` (necessity/completeness) on the frontier. The completeness frontier is an *instance
argument*, never a class field — so `soundFormalLrt` stays independent of it (the deliberate decoupling). -/
theorem reducedDecides [CFracGcdCoreWf α] [LawfulCPolyGcd.{u,v} DensePoly α]
    (C : CRischLevelLrt α) [LawfulCRischLevelLrt C] [LrtLiouvilleFrontier α]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0) (hDt0 : (toPoly Dt).natDegree = 0)
    (hR0 : toPoly (cResidueResultantTower Dt
        (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.1
        (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.2) ≠ 0) :
    IsElementaryIntegrableGenuineLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)
      ↔ cResidueConstantGuard Dt (crNormNum Dt a d) (crNormDen Dt a d) = true := by
  exact primitiveLrtDecides_of_setup hgcd Dt (crNormNum Dt a d) (crNormDen Dt a d)
    (crNormDen_ne_zero_of_charZero Dt a d hd0) hR0
      (LawfulCRischLevelLrt.reducedSoundLrt C Dt a d hd0 hDt0)

/-- **Derived completeness certificate at the class.** From `reducedDecides`: if the residue guard *fails*, the
reduced normal part is not genuinely elementary integrable — a decidable non-integrability certificate that the
solver's class produces directly (given the Liouville frontier). -/
theorem not_isElementaryIntegrable_reduced [CFracGcdCoreWf α]
    [LawfulCPolyGcd.{u,v} DensePoly α] (C : CRischLevelLrt α) [LawfulCRischLevelLrt C]
    [LrtLiouvilleFrontier α]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hDt0 : (toPoly Dt).natDegree = 0)
    (hR0 : toPoly (cResidueResultantTower Dt
        (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.1
        (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.2) ≠ 0)
    (hguard : cResidueConstantGuard Dt (crNormNum Dt a d) (crNormDen Dt a d) = false) :
    ¬ IsElementaryIntegrableGenuineLrt Dt (crNormNum Dt a d) (crNormDen Dt a d) := by
  rw [C.reducedDecides hgcd Dt a d hd0 hDt0 hR0, hguard]; simp

end CRischLevelLrt

/-- **The primitive LRT base instance — assembled from `PrimitiveFrontierLrt` by resolution.** Materialize one
`PrimitiveFrontierLrt α` and the whole LRT solver resolves. The `case` is `primitiveGuardedCase`, so
`specialSound` is the proven `primitiveGuardedCase_specialSound` (the `Dθ = 1` special identity + the
`canonicalReconstruction_of_charZero`, `b = 0` special term vanishing); `reducedSoundLrt` is the frontier field
`PrimitiveFrontierLrt.hreducedLrt`. No coefficient recursion — the primitive base has constant-coefficient
special parts. -/
instance instCRischLevelLrtPrimitive [CRischField α] [CPolyGcd DensePoly α]
    [CPolySplitFactor DensePoly α] [LawfulCPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    [PrimitiveFrontierLrt α] :
    CRischLevelLrt α where
  case := primitiveGuardedCase

/-- The primitive LRT operation satisfies its algebraic-residue soundness contract. -/
instance instLawfulCRischLevelLrtPrimitive [CRischField α] [CPolyGcd DensePoly α]
    [CPolySplitFactor DensePoly α] [LawfulCPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    [PrimitiveFrontierLrt α] :
    LawfulCRischLevelLrt (inferInstance : CRischLevelLrt α) where
  specialSound := fun Dt a d snum sden hd0 hhook =>
    primitiveGuardedCase_specialSound Dt a d snum sden hd0 hhook
  reducedSoundLrt := fun Dt a d hd0 hDt0 => PrimitiveFrontierLrt.hreducedLrt Dt a d hd0 hDt0
  reducedDenNonzero := fun Dt a d hd0 hDt0 =>
    PrimitiveFrontierLrt.hreducedDenNonzero Dt a d hd0 hDt0

/-- **Validation: the base LRT solver resolves from selected operations and the reduced frontier.** -/
example [CRischField α] [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [LawfulCPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    [PrimitiveFrontierLrt α] : LawfulCRischLevelLrt (inferInstance : CRischLevelLrt α) := inferInstance

end DeepWiki.SymbolicIntegration
