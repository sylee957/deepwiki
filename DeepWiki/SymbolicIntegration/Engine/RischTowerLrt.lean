import DeepWiki.SymbolicIntegration.Engine.RischTowerPrimitive
import DeepWiki.SymbolicIntegration.Engine.LrtAssembly
import DeepWiki.SymbolicIntegration.Engine.LrtAlgebraicClosure
import DeepWiki.SymbolicIntegration.Engine.PrimitiveLrtDecision

/-! # `LawfulRischLevelLrt` — the recursive LRT (algebraic-residue) Risch-solver abstraction

The re-based analogue of `LawfulRischLevel`: same `X`/`LawfulX` idiom, but the assembled solver produces an
`LrtResult` (symbolic algebraic-residue logs `Σ_{Rᵢ(c)=0} c·log Sᵢ(c,t)`) via the root-free assembler
`cIntegrateCaseLrt`. The payoff is that its reduced-part frontier is the **dischargeable** `PrimitiveFrontierLrt`
(closed to `LrtReducedGenuineData` by `hreducedLrt_of_genuineAll`) rather than the rational `PrimitiveFrontier`,
which is *not* universally dischargeable — the rational reduced soundness `IsIntegralResult` forces the reduced
denominator to split over `K`, false when the residues are algebraic. The special/polynomial part is unchanged
(`specialSound`, a `K`-level identity, shared verbatim with the rational solver).

Materialize one `LawfulRischLevelLrt` instance and the assembled integrator `integrate` / `soundFormalLrt`
resolve parameter-free. The base is `instLawfulRischLevelLrtPrimitive` (from `[PrimitiveFrontierLrt α]`, reusing
`primitiveGuardedCase_specialSound` — no coefficient recursion at the base); the tower step (the recursion into
the coefficient field) is built in `RischSolverTowerLrt.lean`. See `docs/recursive-lrt-typeclass.md`. -/

namespace DeepWiki.SymbolicIntegration

universe u v

open DensePoly CFrac Polynomial
open scoped Differential

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
  [LawfulCPolyGcd.{u,v} DensePoly α]
  [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))]

/-- **The recursive LRT Risch solver as a class.** The computable data (`case`) plus the two soundness laws:
`specialSound` (the special/polynomial part reconstructs `a/d`, a `K`-level identity — shared with the rational
solver) and `reducedSoundLrt` (the reduced normal part integrates to `cIntegrateReducedLrt` with algebraic
residues, `IsIntegralResultLrt` over every alg-closed extension `E`). One `instance` assembles `integrate` /
`soundFormalLrt` by resolution. The reduced law is the *dischargeable* frontier `PrimitiveFrontierLrt` — no
rational-residue restriction. -/
class LawfulRischLevelLrt (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)] where
  /-- The per-monomial-case computable hooks for this level (the special/polynomial-part integrator). -/
  case : MonomialCase α
  /-- Special-part soundness + reconstruction (`K`-level, existential special value — identical to the rational
  solver's `specialSound`). The `d ≠ 0` precondition is supplied by the integrator's guard. -/
  specialSound : ∀ (Dt a d snum sden : DensePoly α), toPoly d ≠ 0 →
    case.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d) = some (snum, sden) →
    toPoly sden ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K α),
      towerFractionFieldDeriv Dt (fieldFrac snum sden) = v ∧
      v + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d
  /-- Reduced-part soundness with algebraic residues: `cₙ/dₙ` integrates to `cIntegrateReducedLrt …` over every
  alg-closed differential extension `E`. This is exactly `PrimitiveFrontierLrt.hreducedLrt` — the dischargeable
  frontier (no rational-residue restriction). -/
  reducedSoundLrt : ∀ (Dt a d : DensePoly α), toPoly d ≠ 0 → (toPoly Dt).natDegree = 0 →
    IsIntegralResultLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)
      (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d))
  /-- The selected reduced LRT rational part has a nonzero stored denominator. -/
  reducedDenNonzero : ∀ (Dt a d : DensePoly α), toPoly d ≠ 0 → (toPoly Dt).natDegree = 0 →
    toPoly (cIntegrateReducedLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)).rational.2 ≠ 0
  /-- **Optional single-`w` limited integrator** (Bronstein §5.8/§5.12) — `(anum, aden, ηnum, ηden) ↦
  ((bnum, bden), c)` with `anum/aden = D(bnum/bden) + c·(ηnum/ηden)` over `α(s)`. Feeds the degree-raising
  coefficient recursion `cIntegratePrimPolyDegRaise` its `c` (the `c·tᵐ⁺¹/(m+1)` term). Defaults to `none` ⟹
  the tower recursion falls back to the log-free coefficient integrator (`c = 0`), so existing instances are
  unaffected; a `(b,c)` instance (base = `CFrac.limitedIntegrateSingleBase`) flips on degree-raising. Soundness is
  telescoping (`cIntegratePrimPolyDegRaiseG_sound` needs no correctness law on this). -/
  limitedIntegrateSingle : DensePoly α → DensePoly α → DensePoly α → DensePoly α → Option ((DensePoly α × DensePoly α) × α) :=
    fun _ _ _ _ => none

namespace LawfulRischLevelLrt

omit [CFracGcdCoreWf α] [LawfulCPolyGcd.{u, v} DensePoly α]
  [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))] in
/-- **The assembled LRT integrator** — a function of `(Dt, a, d)` alone, via the root-free assembler
`cIntegrateCaseLrt` (no candidate sweep). **Guards on `d ≠ 0`**, so a successful run supplies `d ≠ 0` to the
soundness laws. -/
def integrate [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] [CPolySquarefree DensePoly α]
    [CPolyResultant DensePoly] [CPolySubresultant DensePoly] [LawfulRischLevelLrt α]
    (Dt a d : DensePoly α) : Option (LrtResult α) :=
  if cisZero d then none else cIntegrateCaseLrt case Dt a d

omit [CFracGcdCoreWf α] [LawfulCPolyGcd.{u, v} DensePoly α]
  [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))] in
/-- **Formal LRT soundness.** Any successful run satisfies the algebraic-residue log-derivative identity
`IsIntegralResultLrt` — over every alg-closed differential extension `E`, `D_E(rational) + Σ residue logs =
a/d`. Composed from the instance's `specialSound` + `reducedSoundLrt` through the assembler soundness
`cIntegrateCaseLrt_sound`. -/
theorem soundFormalLrt [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    [LawfulRischLevelLrt α] (Dt a d : DensePoly α) (res : LrtResult α)
    (h : integrate Dt a d = some res) : IsIntegralResultLrt Dt a d res := by
  rw [integrate] at h
  by_cases hdz : cisZero d = true
  · rw [if_pos hdz] at h; simp at h
  · rw [if_neg hdz] at h
    have hd0 : toPoly d ≠ 0 := fun hh => hdz ((cisZeroG_iff d).mpr hh)
    have h0 : cIntegrateCaseLrt case Dt a d = some res := h
    rw [cIntegrateCaseLrt] at h
    rcases hcrep : canonicalRepresentationFast Dt a d with ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
    rw [hcrep] at h
    dsimp only at h
    rcases hspec : case.integrateSpecial Dt fp b ds with _ | ⟨snum, sden⟩
    · rw [hspec] at h; simp at h
    · rw [hspec] at h
      have hSpec : case.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d) (crSpecDen Dt a d)
          = some (snum, sden) := by
        simp only [crPoly, crSpecNum, crSpecDen, hcrep]; exact hspec
      obtain ⟨hsden, v, hSpecField, hrecon⟩ := specialSound Dt a d snum sden hd0 hSpec
      have hNrm := reducedSoundLrt Dt a d hd0
      have hredDen := reducedDenNonzero Dt a d hd0
      exact cIntegrateCaseLrt_sound case Dt a d res snum sden v
        hSpec h0 hsden hSpecField hNrm hredDen hrecon

omit [CFracGcdCoreWf α] [LawfulCPolyGcd.{u, v} DensePoly α]
  [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))] in
/-- **Derived broad elementary integrability.** A successful LRT run certifies `a/d` is elementary integrable in
the broad (algebraic-residue) sense — `IsElementaryIntegrableLrt`, via `soundFormalLrt`. -/
theorem isElementaryIntegrableLrt_of_run [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    [LawfulRischLevelLrt α] (Dt a d : DensePoly α)
    (res : LrtResult α) (h : integrate Dt a d = some res) : IsElementaryIntegrableLrt Dt a d :=
  ⟨res, soundFormalLrt Dt a d res h⟩

omit [CFracGcdCoreWf α] [LawfulCPolyGcd.{u, v} DensePoly α]
  [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))] in
/-- **Limited (log-free) LRT integration** — `integrate` restricted to results with **no** algebraic-residue
logs. A log-free antiderivative is purely rational, so it needs no algebraic closure to state — making this the
right coefficient integrator for the tower recursion (the LRT analogue of the rational `integrateRational`). -/
def integrateRationalLrt [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α]
    [CPolySquarefree DensePoly α] [CPolyResultant DensePoly] [CPolySubresultant DensePoly]
    [LawfulRischLevelLrt α] (Dt a d : DensePoly α) : Option (DensePoly α × DensePoly α) :=
  (integrate Dt a d).bind fun r => if r.logs.isEmpty then some r.rational else none

omit [CFracGcdCoreWf α] [LawfulCPolyGcd.{u, v} DensePoly α]
  [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))] in
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
    [LawfulRischLevelLrt α] (Dt a d num den : DensePoly α)
    (h : integrateRationalLrt Dt a d = some (num, den)) :
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
    have hE := isIntegralResultLrtG_algebraicClosure Dt a d r (soundFormalLrt Dt a d r hint)
    rw [hlogs, logResidueSumLrtG_nil, add_zero, hnum, hden] at hE
    -- both sides are `ratFuncBaseChange` of the `K`-level fractions; invert and use injectivity
    rw [← ratFuncBaseChange_towerFractionFieldDerivG, ← ratFuncBaseChange_amG_div] at hE
    exact (ratFuncBaseChange (AlgebraicClosure (CFieldSpec.K α))).injective hE
  · exact absurd hguard (by simp)

omit [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))] in
/-- **★ Derived decision procedure — completeness meets soundness at the class.** The *same* instance that
gives `soundFormalLrt` also **decides** genuine (algebraic-residue) elementary integrability of the reduced
normal part `cₙ/dₙ`, once the Liouville completeness frontier `[LrtLiouvilleFrontier α]` is available:
integrability **iff** the root-free residue guard passes. The `←` (sufficiency) draws on the instance's own
`reducedSoundLrt`; the `→` (necessity/completeness) on the frontier. The completeness frontier is an *instance
argument*, never a class field — so `soundFormalLrt` stays independent of it (the deliberate decoupling). -/
theorem reducedDecides [LawfulRischLevelLrt α] [LrtLiouvilleFrontier α] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0) (hDt0 : (toPoly Dt).natDegree = 0)
    (hR0 : toPoly (cResidueResultantTower Dt
        (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.1
        (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.2) ≠ 0) :
    IsElementaryIntegrableGenuineLrt Dt (crNormNum Dt a d) (crNormDen Dt a d)
      ↔ cResidueConstantGuard Dt (crNormNum Dt a d) (crNormDen Dt a d) = true := by
  exact primitiveLrtDecides_of_setup hgcd Dt (crNormNum Dt a d) (crNormDen Dt a d)
    (crNormDen_ne_zero_of_charZero Dt a d hd0) hR0 (reducedSoundLrt Dt a d hd0 hDt0)

omit [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))] in
/-- **Derived completeness certificate at the class.** From `reducedDecides`: if the residue guard *fails*, the
reduced normal part is not genuinely elementary integrable — a decidable non-integrability certificate that the
solver's class produces directly (given the Liouville frontier). -/
theorem not_isElementaryIntegrable_reduced [LawfulRischLevelLrt α] [LrtLiouvilleFrontier α]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hDt0 : (toPoly Dt).natDegree = 0)
    (hR0 : toPoly (cResidueResultantTower Dt
        (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.1
        (cHermiteReduceTower Dt (crNormNum Dt a d) (crNormDen Dt a d)).2.2) ≠ 0)
    (hguard : cResidueConstantGuard Dt (crNormNum Dt a d) (crNormDen Dt a d) = false) :
    ¬ IsElementaryIntegrableGenuineLrt Dt (crNormNum Dt a d) (crNormDen Dt a d) := by
  rw [reducedDecides hgcd Dt a d hd0 hDt0 hR0, hguard]; simp

end LawfulRischLevelLrt

/-- **The primitive LRT base instance — assembled from `PrimitiveFrontierLrt` by resolution.** Materialize one
`PrimitiveFrontierLrt α` and the whole LRT solver resolves. The `case` is `primitiveGuardedCase`, so
`specialSound` is the proven `primitiveGuardedCase_specialSound` (the `Dθ = 1` special identity + the
`canonicalReconstruction_of_charZero`, `b = 0` special term vanishing); `reducedSoundLrt` is the frontier field
`PrimitiveFrontierLrt.hreducedLrt`. No coefficient recursion — the primitive base has constant-coefficient
special parts. -/
instance instLawfulRischLevelLrtPrimitive [CRischField α] [PrimitiveFrontierLrt α] :
    LawfulRischLevelLrt α where
  case := primitiveGuardedCase
  specialSound := fun Dt a d snum sden hd0 hhook =>
    primitiveGuardedCase_specialSound Dt a d snum sden hd0 hhook
  reducedSoundLrt := fun Dt a d hd0 hDt0 => PrimitiveFrontierLrt.hreducedLrt Dt a d hd0 hDt0
  reducedDenNonzero := fun Dt a d hd0 hDt0 =>
    PrimitiveFrontierLrt.hreducedDenNonzero Dt a d hd0 hDt0

/-- **Validation: the base LRT solver resolves from the reduced frontier.** Given `[PrimitiveFrontierLrt α]`,
`LawfulRischLevelLrt α` resolves parameter-free — the base of the recursive LRT tower. -/
example [CRischField α] [PrimitiveFrontierLrt α] : LawfulRischLevelLrt α := inferInstance

end DeepWiki.SymbolicIntegration
