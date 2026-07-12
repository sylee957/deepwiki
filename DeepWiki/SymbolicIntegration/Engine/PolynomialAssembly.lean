import DeepWiki.SymbolicIntegration.Engine.Assemble
import DeepWiki.SymbolicIntegration.Engine.PolyPartTower

/-! # Contract-based one-level Risch assembly

This module composes canonical representation, polynomial reduction, normal reduction, and a
monomial-case solver. Its soundness and relative-completeness theorems use only stage contracts. -/

namespace DeepWiki.SymbolicIntegration

open CFrac Polynomial

universe u

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,u} P]
variable {α : Type u} [CField α] [CFieldSpec.{u,u} α] [CDiffField α] [CDiffFieldSpec.{u,u} α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Add a polynomial antiderivative to a represented special fraction's numerator. -/
def polynomialSpecialNumerator (q snum sden : P α) : P α :=
  CPolyEngine.add (CPolyEngine.mul q sden) snum

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The represented fraction built by `polynomialSpecialNumerator` is `q + snum / sden`. -/
theorem fieldFracP_polynomialSpecialNumerator (q snum sden : P α)
    (hsden : CPoly.toPoly sden ≠ 0) :
    fieldFracP (polynomialSpecialNumerator q snum sden) sden =
      fieldFracP q CPoly.one + fieldFracP snum sden := by
  have hden : CFrac.am α (CPoly.toPoly sden) ≠ 0 := CFrac.am_ne_zero hsden
  have hnum : CFrac.am α (CPoly.toPoly (polynomialSpecialNumerator q snum sden)) =
      CFrac.am α (CPoly.toPoly q) * CFrac.am α (CPoly.toPoly sden) +
        CFrac.am α (CPoly.toPoly snum) := by
    rw [polynomialSpecialNumerator, LawfulCPolyEngine.toPoly_add,
      LawfulCPolyEngine.toPoly_mul, map_add, map_mul]
  rw [fieldFracP, fieldFracP, fieldFracP, CPoly.toPoly_one, map_one, div_one, hnum]
  field_simp [hden]

set_option linter.unusedSectionVars false in
/-- A polynomial-reduction reconstruction equation yields the corresponding polynomial derivative identity. -/
theorem polynomialReduction_antiderivative_sound (Dt p q r : P α)
    (hreduce : CPoly.toPoly p = Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly q)
      + CPoly.toPoly r) :
    towerFractionFieldDerivP Dt (fieldFracP q CPoly.one) =
      fieldFracP p CPoly.one - fieldFracP r CPoly.one := by
  simp only [fieldFracP, CPoly.toPoly_one, map_one, div_one]
  rw [towerFractionFieldDerivP, extendDeriv_algebraMap]
  change CFrac.am α (Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly q)) = _
  have hmap := congrArg (CFrac.am α) hreduce
  rw [map_add] at hmap
  exact eq_sub_iff_add_eq.mpr hmap.symm

/-- Execute one-level Risch assembly from explicit polynomial- and normal-reduction operations. -/
def assembleOneLevel (R : CPolynomialReduction P α) (kind : PolynomialReductionKind)
    (N : CNormalReduction P α) (fuel : ℕ) (C : CMonomialCase P α)
    [CCanonicalRepresentation P α]
    (Dt a d : P α) : Option (IntegralResult α P) := do
  let stageFuel := Nat.unpair fuel
  let split := canonicalResult Dt a d
  let reduced ← R.reduce kind Dt stageFuel.1 split.polynomial
  let special ← C.integrateSpecial stageFuel.2 Dt reduced.remainder split.specialNum split.specialDen
  let before ← N.reduce Dt split.normalNum split.normalDen
  let normal ← C.postprocessNormal Dt before
  let polynomialSpecial := combineSN reduced.antiderivative CPoly.one special
  pure (combineIntegralResults polynomialSpecial normal)

/-- Inputs shared by polynomial reduction and the monomial-special branch of one Risch level. -/
structure PolynomialSpecialInput (P : Type u → Type u) [CPoly P]
    (α : Type u) [CField α] [CFieldSpec α] where
  /-- The requested polynomial normal form. -/
  kind : PolynomialReductionKind
  /-- The derivative of the current monomial. -/
  derivative : P α
  /-- Polynomial component of the canonical decomposition. -/
  polynomial : P α
  /-- Numerator of the special component. -/
  specialNum : P α
  /-- Denominator of the special component. -/
  specialDen : P α
  /-- The represented special denominator is nonzero. -/
  specialDen_nonzero : CPoly.toPoly specialDen ≠ 0

/-- Turn a polynomial-special input into the polynomial reducer's input. -/
def PolynomialSpecialInput.toPolynomialReductionInput (input : PolynomialSpecialInput P α) :
    PolynomialReductionInput P α :=
  ⟨input.kind, input.derivative, input.polynomial⟩

/-- Pass a polynomial-reduction remainder to the monomial-special solver. -/
def PolynomialSpecialInput.toMonomialSpecialInput (input : PolynomialSpecialInput P α)
    (remainder : P α) : MonomialSpecialInput P α :=
  ⟨input.derivative, remainder, input.specialNum, input.specialDen, input.specialDen_nonzero⟩

/-- The semantic contract obtained by composing polynomial reduction with special integration. -/
def IsPolynomialSpecialAssembly (input : PolynomialSpecialInput P α)
    (antiderivative : P α) (special : IntegralResult α P) : Prop :=
  ∃ remainder,
    IsPolynomialReduction input.kind input.derivative input.polynomial ⟨antiderivative, remainder⟩ ∧
      IsMonomialSpecialResult input.derivative remainder input.specialNum input.specialDen special

/-- A polynomial reduction result packaged as the precisely corresponding special-stage input. -/
def IsPolynomialSpecialHandoff (input : PolynomialSpecialInput P α)
    (antiderivative : P α) (next : MonomialSpecialInput P α) : Prop :=
  IsPolynomialReduction input.kind input.derivative input.polynomial
      ⟨antiderivative, next.polynomial⟩ ∧
    next.derivative = input.derivative ∧ next.specialNum = input.specialNum ∧
      next.specialDen = input.specialDen

/-- Semantic domain for the polynomial-special pipeline, including the reduction-to-special handoff. -/
def PolynomialSpecialDomain (polynomialDomain : PolynomialReductionDomain P α)
    (specialDomain : MonomialSpecialDomain P α) (input : PolynomialSpecialInput P α) : Prop :=
  polynomialDomain input.kind input.derivative input.polynomial ∧
    ∀ antiderivative remainder,
      IsPolynomialReduction input.kind input.derivative input.polynomial ⟨antiderivative, remainder⟩ →
        specialDomain input.derivative remainder input.specialNum input.specialDen

/-- Relative integrability for polynomial reduction followed by monomial-special integration. -/
def IsPolynomialSpecialIntegrable (input : PolynomialSpecialInput P α) : Prop :=
  (∃ reduced, IsPolynomialReduction input.kind input.derivative input.polynomial reduced) ∧
    ∀ antiderivative remainder,
      IsPolynomialReduction input.kind input.derivative input.polynomial ⟨antiderivative, remainder⟩ →
        ∃ special,
          IsMonomialSpecialResult input.derivative remainder input.specialNum input.specialDen special

/-- Export polynomial reduction with its remainder packaged as the next special-stage input. -/
noncomputable def CPolynomialReduction.asSpecialHandoffStage
    (C : CPolynomialReduction P α) (domain : PolynomialReductionDomain P α)
    [LawfulCPolynomialReduction C] [CompleteCPolynomialReduction C domain] :
    RemainderIntegrationStage (PolynomialSpecialInput P α) (P α) (MonomialSpecialInput P α)
      (fun input => ∃ out,
        IsPolynomialReduction input.kind input.derivative input.polynomial out)
      IsPolynomialSpecialHandoff :=
  { stage :=
      { run := fun fuel input =>
          (C.reduce input.kind input.derivative fuel input.polynomial).map fun out =>
            ⟨out.antiderivative, input.toMonomialSpecialInput out.remainder⟩
        domain := fun input => domain input.kind input.derivative input.polynomial
        sound := by
          intro fuel input result hdomain hrun
          obtain ⟨out, hout, rfl⟩ := Option.map_eq_some_iff.mp hrun
          exact ⟨⟨LawfulCPolynomialReduction.sound input.kind input.derivative fuel input.polynomial
              out hout,
              LawfulCPolynomialReduction.normal_form input.kind input.derivative fuel input.polynomial
                out hout⟩,
            rfl, rfl, rfl⟩
        complete := by
          intro input hdomain hintegrable
          obtain ⟨fuel, out, hrun, _⟩ := CompleteCPolynomialReduction.relative_complete
            (C := C) (domain := domain) input.kind input.derivative input.polynomial
              hdomain hintegrable
          exact ⟨fuel, ⟨out.antiderivative, input.toMonomialSpecialInput out.remainder⟩,
            by simp [hrun]⟩ } }

/-- Compose certified polynomial reduction and monomial-special integration through a typed remainder. -/
noncomputable def CPolynomialReduction.asPolynomialSpecialRemainderStage
    (C : CPolynomialReduction P α) (polynomialDomain : PolynomialReductionDomain P α)
    [LawfulCPolynomialReduction C] [CompleteCPolynomialReduction C polynomialDomain]
    (M : CMonomialCase P α) (specialDomain : MonomialSpecialDomain P α)
    [LawfulCMonomialCase M] [LawfulGenuineCMonomialCase M]
    [CompleteCMonomialCase M specialDomain] :
    RemainderIntegrationStage (PolynomialSpecialInput P α) (P α × IntegralResult α P) Unit
      IsPolynomialSpecialIntegrable
      (fun input output _ => IsPolynomialSpecialAssembly input output.1 output.2) := by
  let reduction := C.asSpecialHandoffStage polynomialDomain
  let special := M.asRemainderIntegrationStage specialDomain
  exact reduction.compose special
    (PolynomialSpecialDomain polynomialDomain specialDomain)
    IsPolynomialSpecialIntegrable
    (by
      intro input hdomain
      exact hdomain.1)
    (by
      intro input antiderivative next hdomain hcorrect
      rcases hcorrect with ⟨hreduction, hderivative, hnum, hden⟩
      change specialDomain next.derivative next.polynomial next.specialNum next.specialDen
      simpa [hderivative, hnum, hden] using
        hdomain.2 antiderivative next.polynomial hreduction)
    (by
      intro input hintegrable
      refine ⟨hintegrable.1, ?_⟩
      intro antiderivative next hcorrect
      rcases hcorrect with ⟨hreduction, hderivative, hnum, hden⟩
      simpa [hderivative, hnum, hden] using
        hintegrable.2 antiderivative next.polynomial hreduction)
    (by
      intro input antiderivative next specialResult _ hreduction hspecial
      rcases hreduction with ⟨hpoly, hderivative, hnum, hden⟩
      refine ⟨next.polynomial, hpoly, ?_⟩
      simpa [hderivative, hnum, hden] using hspecial)

/-- The two independent canonical branches supplied to the one-level remainder pipeline. -/
structure OneLevelBranchInput (P : Type u → Type u) [CPoly P]
    (α : Type u) [CField α] [CFieldSpec α] where
  /-- Numerator of the original one-level input fraction. -/
  numerator : P α
  /-- Denominator of the original one-level input fraction. -/
  denominator : P α
  /-- The original denominator is nonzero. -/
  denominator_nonzero : CPoly.toPoly denominator ≠ 0
  /-- Requested polynomial-reduction form. -/
  kind : PolynomialReductionKind
  /-- Derivative of the current monomial. -/
  derivative : P α
  /-- Polynomial branch of the canonical decomposition. -/
  polynomial : P α
  /-- Special-branch numerator. -/
  specialNum : P α
  /-- Special-branch denominator. -/
  specialDen : P α
  /-- Normal-branch numerator. -/
  normalNum : P α
  /-- Normal-branch denominator. -/
  normalDen : P α
  /-- The special denominator is nonzero. -/
  specialDen_nonzero : CPoly.toPoly specialDen ≠ 0
  /-- The normal denominator is nonzero. -/
  normalDen_nonzero : CPoly.toPoly normalDen ≠ 0

/-- View the polynomial-special half of a canonical split as its typed pipeline input. -/
def OneLevelBranchInput.toPolynomialSpecialInput (input : OneLevelBranchInput P α) :
    PolynomialSpecialInput P α :=
  ⟨input.kind, input.derivative, input.polynomial, input.specialNum, input.specialDen,
    input.specialDen_nonzero⟩

/-- View the normal half of a canonical split as its typed reduction input. -/
def OneLevelBranchInput.toNormalReductionInput (input : OneLevelBranchInput P α) :
    NormalReductionInput P α :=
  ⟨input.derivative, input.normalNum, input.normalDen, input.normalDen_nonzero⟩

/-- The two branch certificates retained before their final rational-and-logarithmic reconstruction. -/
def IsOneLevelBranchAssembly (input : OneLevelBranchInput P α)
    (polynomialSpecial : P α × IntegralResult α P) (normal : IntegralResult α P) : Prop :=
  IsPolynomialSpecialAssembly input.toPolynomialSpecialInput polynomialSpecial.1 polynomialSpecial.2 ∧
    CertifiedNormalResult input.derivative input.normalNum input.normalDen normal

/-- A full represented fraction before its canonical one-level split. -/
structure OneLevelInput (P : Type u → Type u) [CPoly P]
    (α : Type u) [CField α] [CFieldSpec α] where
  /-- Derivative of the current monomial. -/
  derivative : P α
  /-- Numerator of the input fraction. -/
  numerator : P α
  /-- Denominator of the input fraction. -/
  denominator : P α
  /-- The represented denominator is nonzero. -/
  denominator_nonzero : CPoly.toPoly denominator ≠ 0

/-- Compute the typed branch input selected by canonical decomposition. -/
noncomputable def canonicalOneLevelBranch (kind : PolynomialReductionKind)
    [CCanonicalRepresentation P α] [LawfulCCanonicalRepresentation (P := P) (α := α)]
    (input : OneLevelInput P α) : OneLevelBranchInput P α :=
  let split := canonicalResult input.derivative input.numerator input.denominator
  ⟨input.numerator, input.denominator, input.denominator_nonzero, kind, input.derivative,
    split.polynomial, split.specialNum, split.specialDen, split.normalNum, split.normalDen,
    LawfulCCanonicalRepresentation.specialDen_nonzero input.derivative input.numerator input.denominator
      input.denominator_nonzero,
    LawfulCCanonicalRepresentation.normalDen_nonzero input.derivative input.numerator input.denominator
      input.denominator_nonzero⟩

/-- Canonical decomposition is a certified zero-fuel stage producing the exact branch input. -/
noncomputable def canonicalOneLevelRemainderStage (kind : PolynomialReductionKind)
    [CCanonicalRepresentation P α] [LawfulCCanonicalRepresentation (P := P) (α := α)] :
    RemainderIntegrationStage (OneLevelInput P α) Unit (OneLevelBranchInput P α)
      (fun _ => True)
      (fun input output branch => output = () ∧ branch = canonicalOneLevelBranch kind input) :=
  { stage :=
      { run := fun _ input => some ⟨(), canonicalOneLevelBranch kind input⟩
        domain := fun _ => True
        sound := by
          intro _ input result _ hrun
          simp only [Option.some.injEq] at hrun
          subst result
          exact ⟨rfl, rfl⟩
        complete := by
          intro input _ _
          exact ⟨0, ⟨(), canonicalOneLevelBranch kind input⟩, rfl⟩ } }

/-- Reindex the polynomial-special pipeline to the polynomial half of a canonical split. -/
noncomputable def CPolynomialReduction.asOneLevelBranchStage
    (C : CPolynomialReduction P α) (polynomialDomain : PolynomialReductionDomain P α)
    [LawfulCPolynomialReduction C] [CompleteCPolynomialReduction C polynomialDomain]
    (M : CMonomialCase P α) (specialDomain : MonomialSpecialDomain P α)
    [LawfulCMonomialCase M] [LawfulGenuineCMonomialCase M]
    [CompleteCMonomialCase M specialDomain] :
    RemainderIntegrationStage (OneLevelBranchInput P α) (P α × IntegralResult α P) Unit
      (fun input => IsPolynomialSpecialIntegrable input.toPolynomialSpecialInput)
      (fun input output _ =>
        IsPolynomialSpecialAssembly input.toPolynomialSpecialInput output.1 output.2) :=
  (C.asPolynomialSpecialRemainderStage polynomialDomain M specialDomain).precompose
    OneLevelBranchInput.toPolynomialSpecialInput

/-- Reindex the postprocessed normal pipeline to the normal half of a canonical split. -/
noncomputable def CNormalReduction.asOneLevelBranchStage
    (N : CNormalReduction P α) (normalDomain : NormalReductionDomain P α)
    [LawfulCNormalReduction N normalDomain] [LawfulGenuineCNormalReduction N normalDomain]
    [CompleteCNormalReduction N normalDomain]
    (M : CMonomialCase P α) (specialDomain : MonomialSpecialDomain P α)
    [LawfulCMonomialCase M] [LawfulGenuineCMonomialCase M]
    [CompleteCMonomialCase M specialDomain] :
    RemainderIntegrationStage (OneLevelBranchInput P α) (IntegralResult α P) Unit
      (fun input => IsNormalPartIntegrable input.derivative input.normalNum input.normalDen)
      (fun input result _ =>
        CertifiedNormalResult input.derivative input.normalNum input.normalDen result) :=
  (N.asPostprocessedRemainderStage normalDomain M specialDomain).precompose
    OneLevelBranchInput.toNormalReductionInput

/-- Run the polynomial-special and postprocessed normal pipelines independently on one canonical split. -/
noncomputable def CPolynomialReduction.asParallelOneLevelBranchStage
    (C : CPolynomialReduction P α) (polynomialDomain : PolynomialReductionDomain P α)
    [LawfulCPolynomialReduction C] [CompleteCPolynomialReduction C polynomialDomain]
    (N : CNormalReduction P α) (normalDomain : NormalReductionDomain P α)
    [LawfulCNormalReduction N normalDomain] [LawfulGenuineCNormalReduction N normalDomain]
    [CompleteCNormalReduction N normalDomain]
    (M : CMonomialCase P α) (specialDomain : MonomialSpecialDomain P α)
    [LawfulCMonomialCase M] [LawfulGenuineCMonomialCase M]
    [CompleteCMonomialCase M specialDomain] :
    RemainderIntegrationStage (OneLevelBranchInput P α)
      ((P α × IntegralResult α P) × IntegralResult α P) (Unit × Unit)
      (fun input =>
        IsPolynomialSpecialIntegrable input.toPolynomialSpecialInput ∧
          IsNormalPartIntegrable input.derivative input.normalNum input.normalDen)
      (fun input output _ =>
        IsOneLevelBranchAssembly input output.1 output.2) := by
  let special := C.asOneLevelBranchStage polynomialDomain M specialDomain
  let normal := N.asOneLevelBranchStage normalDomain M specialDomain
  exact special.product normal

/-- Compose canonical decomposition with the parallel polynomial-special and normal pipelines. -/
noncomputable def CPolynomialReduction.asCanonicalOneLevelBranchStage
    (C : CPolynomialReduction P α) (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain P α)
    [LawfulCPolynomialReduction C] [CompleteCPolynomialReduction C polynomialDomain]
    (N : CNormalReduction P α) (normalDomain : NormalReductionDomain P α)
    [LawfulCNormalReduction N normalDomain] [LawfulGenuineCNormalReduction N normalDomain]
    [CompleteCNormalReduction N normalDomain]
    (M : CMonomialCase P α) (specialDomain : MonomialSpecialDomain P α)
    [LawfulCMonomialCase M] [LawfulGenuineCMonomialCase M]
    [CompleteCMonomialCase M specialDomain]
    [CCanonicalRepresentation P α] [LawfulCCanonicalRepresentation (P := P) (α := α)] :
    RemainderIntegrationStage (OneLevelInput P α)
      ((P α × IntegralResult α P) × IntegralResult α P) (Unit × Unit)
      (fun input =>
        IsPolynomialSpecialIntegrable (canonicalOneLevelBranch kind input).toPolynomialSpecialInput ∧
          IsNormalPartIntegrable input.derivative (canonicalOneLevelBranch kind input).normalNum
            (canonicalOneLevelBranch kind input).normalDen)
      (fun input output _ =>
        IsOneLevelBranchAssembly (canonicalOneLevelBranch kind input) output.1 output.2) := by
  let canonical := canonicalOneLevelRemainderStage (P := P) (α := α) kind
  let branches := C.asParallelOneLevelBranchStage polynomialDomain N normalDomain M specialDomain
  let composed :
      RemainderIntegrationStage (OneLevelInput P α)
        (Unit × ((P α × IntegralResult α P) × IntegralResult α P)) (Unit × Unit)
        (fun input =>
          IsPolynomialSpecialIntegrable (canonicalOneLevelBranch kind input).toPolynomialSpecialInput ∧
            IsNormalPartIntegrable input.derivative (canonicalOneLevelBranch kind input).normalNum
              (canonicalOneLevelBranch kind input).normalDen)
        (fun input output _ =>
          output.1 = () ∧
            IsOneLevelBranchAssembly (canonicalOneLevelBranch kind input) output.2.1 output.2.2) :=
    canonical.compose branches
      (fun input =>
        PolynomialSpecialDomain polynomialDomain specialDomain (canonicalOneLevelBranch kind input).toPolynomialSpecialInput ∧
          normalDomain input.derivative (canonicalOneLevelBranch kind input).normalNum
            (canonicalOneLevelBranch kind input).normalDen)
      (fun input =>
        IsPolynomialSpecialIntegrable (canonicalOneLevelBranch kind input).toPolynomialSpecialInput ∧
          IsNormalPartIntegrable input.derivative (canonicalOneLevelBranch kind input).normalNum
            (canonicalOneLevelBranch kind input).normalDen)
      (by
        intro _ _
        trivial)
      (by
        intro input _ branch hdomain hcanonical
        rcases hcanonical with ⟨_, hcanonical⟩
        subst branch
        exact hdomain)
      (by
        intro _ hintegrable
        refine ⟨True.intro, ?_⟩
        intro _ branch hcanonical
        rcases hcanonical with ⟨_, hcanonical⟩
        subst branch
        exact hintegrable)
      (by
        intro input first branch output remainder hcanonical hbranches
        rcases hcanonical with ⟨hunit, hcanonical⟩
        subst branch
        exact ⟨hunit, hbranches⟩)
  exact composed.mapOutput Prod.snd (by
    intro input output _ hcorrect
    exact hcorrect.2)

/-- Recombine the two independently certified one-level branches. -/
def reconstructOneLevelBranches (branches : (P α × IntegralResult α P) × IntegralResult α P) :
    IntegralResult α P :=
  combineIntegralResults (combineSN branches.1.1 CPoly.one branches.1.2) branches.2

/-- The final one-level result has the formal integral identity and genuine logarithmic terms. -/
def IsGenuineOneLevelResult (input : OneLevelInput P α) (result : IntegralResult α P) : Prop :=
  IsIntegralResultP input.derivative input.numerator input.denominator result ∧
    (∀ cv ∈ result.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
      ∀ cv ∈ result.logs, CPoly.toPoly cv.2 ≠ 0

/-- A polynomial-special and normal branch reconstruct an integral result when their split reconstructs the input. -/
theorem oneLevelBranchAssembly_sound (input : OneLevelBranchInput P α)
    (branches : (P α × IntegralResult α P) × IntegralResult α P)
    (hreconstruct :
      fieldFracP input.polynomial CPoly.one + fieldFracP input.specialNum input.specialDen +
          fieldFracP input.normalNum input.normalDen = fieldFracP input.numerator input.denominator)
    (hbranches : IsOneLevelBranchAssembly input branches.1 branches.2) :
    IsIntegralResultP input.derivative input.numerator input.denominator
      (reconstructOneLevelBranches branches) := by
  obtain ⟨remainder, hreduce, hspecial⟩ := hbranches.1
  obtain ⟨hspecialDen, _hspecialConstants, _hspecialArguments, hspecialIdentity⟩ := hspecial
  have hpoly : towerFractionFieldDerivP input.derivative
      (fieldFracP branches.1.1 CPoly.one) =
      fieldFracP input.polynomial CPoly.one - fieldFracP remainder CPoly.one :=
    polynomialReduction_antiderivative_sound input.derivative input.polynomial branches.1.1 remainder
      hreduce.1
  have hone : CPoly.toPoly (CPoly.one : P α) ≠ 0 := by
    rw [CPoly.toPoly_one]
    exact one_ne_zero
  have hpolynomialSpecial : towerFractionFieldDerivP input.derivative
      (fieldFracP (combineSN branches.1.1 CPoly.one branches.1.2).rational.1
        (combineSN branches.1.1 CPoly.one branches.1.2).rational.2) +
        logResidueSumP input.derivative (combineSN branches.1.1 CPoly.one branches.1.2).logs =
      fieldFracP input.polynomial CPoly.one + fieldFracP input.specialNum input.specialDen := by
    rw [combineSN_value input.derivative branches.1.1 CPoly.one branches.1.2
      (fieldFracP input.polynomial CPoly.one - fieldFracP remainder CPoly.one)
      (fieldFracP remainder CPoly.one + fieldFracP input.specialNum input.specialDen)
      hone hspecialDen hpoly hspecialIdentity]
    ring
  have hleftDen : CPoly.toPoly (combineSN branches.1.1 CPoly.one branches.1.2).rational.2 ≠ 0 := by
    simp only [combineSN, combineRationalParts, LawfulCPolyEngine.toPoly_mul, CPoly.toPoly_one]
    exact mul_ne_zero one_ne_zero hspecialDen
  have hnormal : IsIntegralResultP input.derivative input.normalNum input.normalDen branches.2 :=
    hbranches.2.integral
  refine combineIntegralResults_isIntegralResultP input.derivative input.numerator input.denominator
    input.normalNum input.normalDen (combineSN branches.1.1 CPoly.one branches.1.2) branches.2
    (fieldFracP input.polynomial CPoly.one + fieldFracP input.specialNum input.specialDen)
    hleftDen hbranches.2.rationalDen_nonzero hpolynomialSpecial hnormal ?_
  simpa only [add_assoc] using hreconstruct

omit [LawfulCPolyEngine P] in
/-- Genuine logarithmic coefficients and arguments survive one-level branch reconstruction. -/
theorem oneLevelBranchAssembly_logs_genuine (input : OneLevelBranchInput P α)
    (branches : (P α × IntegralResult α P) × IntegralResult α P)
    (hbranches : IsOneLevelBranchAssembly input branches.1 branches.2) :
    (∀ cv ∈ (reconstructOneLevelBranches branches).logs,
      CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
      ∀ cv ∈ (reconstructOneLevelBranches branches).logs, CPoly.toPoly cv.2 ≠ 0 := by
  obtain ⟨_remainder, _hreduce, hspecial⟩ := hbranches.1
  obtain ⟨_hspecialDen, hspecialConstants, hspecialArguments, _hspecialIdentity⟩ := hspecial
  constructor
  · intro cv hcv
    change cv ∈ branches.1.2.logs ++ branches.2.logs at hcv
    rw [List.mem_append] at hcv
    exact hcv.elim (hspecialConstants cv) (hbranches.2.coefficients_constant cv)
  · intro cv hcv
    change cv ∈ branches.1.2.logs ++ branches.2.logs at hcv
    rw [List.mem_append] at hcv
    exact hcv.elim (hspecialArguments cv) (hbranches.2.arguments_nonzero cv)

omit [LawfulCPolyEngine P] [Algebra ℚ (CFieldSpec.K α)] in
/-- The canonical branch selected from a full input satisfies the canonical reconstruction equation. -/
theorem canonicalOneLevelBranch_reconstruction (kind : PolynomialReductionKind)
    [CCanonicalRepresentation P α] [LawfulCCanonicalRepresentation (P := P) (α := α)]
    (input : OneLevelInput P α) :
    fieldFracP (canonicalOneLevelBranch kind input).polynomial CPoly.one +
        fieldFracP (canonicalOneLevelBranch kind input).specialNum
          (canonicalOneLevelBranch kind input).specialDen +
        fieldFracP (canonicalOneLevelBranch kind input).normalNum
          (canonicalOneLevelBranch kind input).normalDen =
      fieldFracP input.numerator input.denominator := by
  exact LawfulCCanonicalRepresentation.reconstruction input.derivative input.numerator input.denominator
    input.denominator_nonzero

/-- Finish the canonical one-level pipeline by reconstructing its two certified branch results. -/
noncomputable def CPolynomialReduction.asOneLevelRemainderStage
    (C : CPolynomialReduction P α) (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain P α)
    [LawfulCPolynomialReduction C] [CompleteCPolynomialReduction C polynomialDomain]
    (N : CNormalReduction P α) (normalDomain : NormalReductionDomain P α)
    [LawfulCNormalReduction N normalDomain] [LawfulGenuineCNormalReduction N normalDomain]
    [CompleteCNormalReduction N normalDomain]
    (M : CMonomialCase P α) (specialDomain : MonomialSpecialDomain P α)
    [LawfulCMonomialCase M] [LawfulGenuineCMonomialCase M]
    [CompleteCMonomialCase M specialDomain]
    [CCanonicalRepresentation P α] [LawfulCCanonicalRepresentation (P := P) (α := α)] :
    RemainderIntegrationStage (OneLevelInput P α) (IntegralResult α P) (Unit × Unit)
      (fun input =>
        IsPolynomialSpecialIntegrable (canonicalOneLevelBranch kind input).toPolynomialSpecialInput ∧
          IsNormalPartIntegrable input.derivative (canonicalOneLevelBranch kind input).normalNum
            (canonicalOneLevelBranch kind input).normalDen)
      (fun input result _ => IsGenuineOneLevelResult input result) := by
  let branches := C.asCanonicalOneLevelBranchStage kind polynomialDomain N normalDomain M specialDomain
  exact branches.mapOutput reconstructOneLevelBranches (by
    intro input output _ hcorrect
    refine ⟨oneLevelBranchAssembly_sound (canonicalOneLevelBranch kind input) output
      (canonicalOneLevelBranch_reconstruction kind input) hcorrect,
      oneLevelBranchAssembly_logs_genuine (canonicalOneLevelBranch kind input) output hcorrect⟩)

/-- Explicit stage-decomposed hypotheses under which contract-based one-level assembly is complete. -/
structure OneLevelAssemblyWitness (R : CPolynomialReduction P α)
    (kind : PolynomialReductionKind) (polynomialDomain : PolynomialReductionDomain P α)
    (normalDomain : NormalReductionDomain P α)
    (specialDomain : MonomialSpecialDomain P α)
    (Dt a d : P α) [CCanonicalRepresentation P α] : Prop where
  /-- The canonical polynomial branch lies in the selected reduction stage's domain. -/
  polynomial_domain : polynomialDomain kind Dt (canonicalResult Dt a d).polynomial
  /-- The requested polynomial normal form exists. -/
  polynomial_reduction_exists :
    ∃ reduced, IsPolynomialReduction kind Dt (canonicalResult Dt a d).polynomial reduced
  /-- Every selected polynomial reduction leaves a special part in the monomial solver's domain. -/
  special_domain : ∀ (fuel : ℕ) (reduced : PolynomialReductionResult P α),
    R.reduce kind Dt fuel (canonicalResult Dt a d).polynomial = some reduced →
      specialDomain Dt reduced.remainder (canonicalResult Dt a d).specialNum
        (canonicalResult Dt a d).specialDen
  /-- Every reduction selected by the executable stage leaves a solvable monomial special part. -/
  special_antiderivative : ∀ (fuel : ℕ) (reduced : PolynomialReductionResult P α),
    R.reduce kind Dt fuel (canonicalResult Dt a d).polynomial = some reduced →
      ∃ res : IntegralResult α P,
        CPoly.toPoly res.rational.2 ≠ 0 ∧
        towerFractionFieldDerivP Dt (fieldFracP res.rational.1 res.rational.2) +
            logResidueSumP Dt res.logs =
          fieldFracP reduced.remainder CPoly.one +
            fieldFracP (canonicalResult Dt a d).specialNum
              (canonicalResult Dt a d).specialDen
  /-- The canonical normal branch lies in the selected normal reducer's semantic domain. -/
  normal_domain : normalDomain Dt (canonicalResult Dt a d).normalNum
    (canonicalResult Dt a d).normalDen
  /-- The canonical normal branch has a certified normal-form antiderivative. -/
  normal_integrable : IsNormalPartIntegrable Dt (canonicalResult Dt a d).normalNum
    (canonicalResult Dt a d).normalDen

omit [LawfulCPolyEngine P] in
/-- Complete stage contracts compose into eventual success of contract-based one-level assembly. -/
theorem assembleOneLevel_complete (R : CPolynomialReduction P α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain P α)
    [CompleteCPolynomialReduction R polynomialDomain] (N : CNormalReduction P α)
    (normalDomain : NormalReductionDomain P α)
    [LawfulCNormalReduction N normalDomain] [CompleteCNormalReduction N normalDomain]
    (C : CMonomialCase P α) (specialDomain : MonomialSpecialDomain P α)
    [LawfulCMonomialCase C] [CompleteCMonomialCase C specialDomain]
    [CCanonicalRepresentation P α]
    [LawfulCCanonicalRepresentation (P := P) (α := α)]
    (Dt a d : P α) (hd : CPoly.toPoly d ≠ 0)
    (hwitness : OneLevelAssemblyWitness R kind polynomialDomain normalDomain specialDomain Dt a d) :
    ∃ fuel out, assembleOneLevel R kind N fuel C Dt a d = some out := by
  obtain ⟨fuel, reduced, hreduce, _hnormal⟩ := CompleteCPolynomialReduction.relative_complete
    (C := R) kind Dt (canonicalResult Dt a d).polynomial
      hwitness.polynomial_domain hwitness.polynomial_reduction_exists
  obtain ⟨specialWitness, hspecialDen, hspecialSemantic⟩ :=
    hwitness.special_antiderivative fuel reduced hreduce
  obtain ⟨specialFuel, special, hspecial⟩ := CompleteCMonomialCase.special_complete (C := C) Dt
    reduced.remainder (canonicalResult Dt a d).specialNum
    (canonicalResult Dt a d).specialDen specialWitness
      (hwitness.special_domain fuel reduced hreduce) hspecialDen hspecialSemantic
  have hnormalDen := LawfulCCanonicalRepresentation.normalDen_nonzero Dt a d hd
  obtain ⟨before, hnormal, hbefore⟩ := CompleteCNormalReduction.relative_complete (N := N)
    Dt
    (canonicalResult Dt a d).normalNum (canonicalResult Dt a d).normalDen
    hwitness.normal_domain hnormalDen hwitness.normal_integrable
  obtain ⟨normal, hpost⟩ := CompleteCMonomialCase.postprocess_complete (C := C) specialDomain Dt
    (canonicalResult Dt a d).normalNum (canonicalResult Dt a d).normalDen before hbefore
  refine ⟨Nat.pair fuel specialFuel, combineIntegralResults
    (combineSN reduced.antiderivative CPoly.one special) normal, ?_⟩
  simp only [assembleOneLevel, Nat.unpair_pair, hreduce, hspecial, hnormal, hpost, Option.bind_eq_bind,
    Option.bind_some]
  rfl

set_option maxHeartbeats 800000 in
/-- A successful contract-based one-level assembly is an integral result of its input. -/
theorem assembleOneLevel_sound (R : CPolynomialReduction P α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind) (fuel : ℕ)
    (N : CNormalReduction P α) (normalDomain : NormalReductionDomain P α)
    [LawfulCNormalReduction N normalDomain] (C : CMonomialCase P α)
    [CCanonicalRepresentation P α]
    [LawfulCCanonicalRepresentation (P := P) (α := α)] [LawfulCMonomialCase C]
    (Dt a d : P α) (out : IntegralResult α P)
    (hd : CPoly.toPoly d ≠ 0)
    (hnormalDomain : normalDomain Dt (canonicalResult Dt a d).normalNum
      (canonicalResult Dt a d).normalDen)
    (hrun : assembleOneLevel R kind N fuel C Dt a d = some out) :
    IsIntegralResultP Dt a d out := by
  cases hreduce : R.reduce kind Dt (Nat.unpair fuel).1
      (canonicalResult Dt a d).polynomial with
  | none => simp [assembleOneLevel, hreduce] at hrun
  | some reduced =>
    cases hspecial : C.integrateSpecial (Nat.unpair fuel).2 Dt reduced.remainder
        (canonicalResult Dt a d).specialNum (canonicalResult Dt a d).specialDen with
    | none => simp [assembleOneLevel, hreduce, hspecial] at hrun
    | some special =>
      cases hnormal : N.reduce Dt (canonicalResult Dt a d).normalNum
          (canonicalResult Dt a d).normalDen with
      | none => simp [assembleOneLevel, hreduce, hnormal] at hrun
      | some before =>
        cases hpost : C.postprocessNormal Dt before with
        | none => simp [assembleOneLevel, hreduce, hnormal, hpost] at hrun
        | some normal =>
          have hout : combineIntegralResults
              (combineSN reduced.antiderivative CPoly.one special) normal = out := by
            simpa [assembleOneLevel, hreduce, hspecial, hnormal, hpost] using hrun
          subst out
          have hred := LawfulCPolynomialReduction.sound (C := R) kind Dt (Nat.unpair fuel).1
            (canonicalResult Dt a d).polynomial reduced hreduce
          have hq := polynomialReduction_antiderivative_sound Dt
            (canonicalResult Dt a d).polynomial reduced.antiderivative reduced.remainder hred
          obtain ⟨hspecialDen, hspecialField⟩ := LawfulCMonomialCase.special_sound (C := C)
            (Nat.unpair fuel).2 Dt
            reduced.remainder (canonicalResult Dt a d).specialNum
            (canonicalResult Dt a d).specialDen special hspecial
          have hone : CPoly.toPoly (CPoly.one : P α) ≠ 0 := by
            rw [CPoly.toPoly_one]
            exact one_ne_zero
          have hspecialFull : towerFractionFieldDerivP Dt
              (fieldFracP (combineSN reduced.antiderivative CPoly.one special).rational.1
                (combineSN reduced.antiderivative CPoly.one special).rational.2) +
              logResidueSumP Dt (combineSN reduced.antiderivative CPoly.one special).logs =
              fieldFracP (canonicalResult Dt a d).polynomial CPoly.one +
                fieldFracP (canonicalResult Dt a d).specialNum
                  (canonicalResult Dt a d).specialDen := by
            rw [combineSN_value Dt reduced.antiderivative CPoly.one special
              (fieldFracP (canonicalResult Dt a d).polynomial CPoly.one -
                fieldFracP reduced.remainder CPoly.one)
              (fieldFracP reduced.remainder CPoly.one +
                fieldFracP (canonicalResult Dt a d).specialNum
                  (canonicalResult Dt a d).specialDen)
              hone hspecialDen hq hspecialField]
            ring
          have hnormalDen := LawfulCCanonicalRepresentation.normalDen_nonzero Dt a d hd
          have hbefore := LawfulCNormalReduction.sound (N := N) Dt
            (canonicalResult Dt a d).normalNum
            (canonicalResult Dt a d).normalDen before hnormalDomain hnormalDen hnormal
          have hbeforeDen := LawfulCNormalReduction.rationalDen_nonzero (N := N) Dt
            (canonicalResult Dt a d).normalNum
            (canonicalResult Dt a d).normalDen before hnormalDomain hnormalDen hnormal
          have hnormalResult := LawfulCMonomialCase.postprocessNormal_sound (C := C) Dt
            (canonicalResult Dt a d).normalNum (canonicalResult Dt a d).normalDen before normal hbefore hpost
          have hnormalResultDen := LawfulCMonomialCase.postprocessNormal_den_nonzero (C := C) Dt
            before normal hbeforeDen hpost
          have hcanonical := LawfulCCanonicalRepresentation.reconstruction Dt a d hd
          refine combineIntegralResults_isIntegralResultP Dt a d
            (canonicalResult Dt a d).normalNum (canonicalResult Dt a d).normalDen
            (combineSN reduced.antiderivative CPoly.one special) normal
            (fieldFracP (canonicalResult Dt a d).polynomial CPoly.one +
              fieldFracP (canonicalResult Dt a d).specialNum
                (canonicalResult Dt a d).specialDen)
            ?_ hnormalResultDen hspecialFull hnormalResult ?_
          · simp only [combineSN, combineRationalParts, LawfulCPolyEngine.toPoly_mul,
              CPoly.toPoly_one]
            exact mul_ne_zero one_ne_zero hspecialDen
          simpa only [add_assoc] using hcanonical

omit [LawfulCPolyEngine P] in
/-- Successful one-level assembly preserves genuine logarithmic coefficients and arguments. -/
theorem assembleOneLevel_logs_genuine (R : CPolynomialReduction P α)
    (kind : PolynomialReductionKind) (fuel : ℕ)
    (N : CNormalReduction P α) (normalDomain : NormalReductionDomain P α)
    [LawfulCNormalReduction N normalDomain] [LawfulGenuineCNormalReduction N normalDomain]
    (C : CMonomialCase P α) [CCanonicalRepresentation P α]
    [LawfulCCanonicalRepresentation (P := P) (α := α)] [LawfulCMonomialCase C]
    [LawfulGenuineCMonomialCase C]
    (Dt a d : P α) (out : IntegralResult α P) (hd : CPoly.toPoly d ≠ 0)
    (hnormalDomain : normalDomain Dt (canonicalResult Dt a d).normalNum
      (canonicalResult Dt a d).normalDen)
    (hrun : assembleOneLevel R kind N fuel C Dt a d = some out) :
    (∀ cv ∈ out.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
      ∀ cv ∈ out.logs, CPoly.toPoly cv.2 ≠ 0 := by
  cases hreduce : R.reduce kind Dt (Nat.unpair fuel).1
      (canonicalResult Dt a d).polynomial with
  | none => simp [assembleOneLevel, hreduce] at hrun
  | some reduced =>
    cases hspecial : C.integrateSpecial (Nat.unpair fuel).2 Dt reduced.remainder
        (canonicalResult Dt a d).specialNum (canonicalResult Dt a d).specialDen with
    | none => simp [assembleOneLevel, hreduce, hspecial] at hrun
    | some special =>
      cases hnormal : N.reduce Dt (canonicalResult Dt a d).normalNum
          (canonicalResult Dt a d).normalDen with
      | none => simp [assembleOneLevel, hreduce, hnormal] at hrun
      | some before =>
        cases hpost : C.postprocessNormal Dt before with
        | none => simp [assembleOneLevel, hreduce, hnormal, hpost] at hrun
        | some normal =>
          have hout : combineIntegralResults
              (combineSN reduced.antiderivative CPoly.one special) normal = out := by
            simpa [assembleOneLevel, hreduce, hspecial, hnormal, hpost] using hrun
          subst out
          have hspecialConstants := LawfulGenuineCMonomialCase.special_coefficients_constant
            (C := C) (Nat.unpair fuel).2 Dt reduced.remainder
              (canonicalResult Dt a d).specialNum (canonicalResult Dt a d).specialDen special hspecial
          have hspecialArguments := LawfulGenuineCMonomialCase.special_arguments_nonzero
            (C := C) (Nat.unpair fuel).2 Dt reduced.remainder
              (canonicalResult Dt a d).specialNum (canonicalResult Dt a d).specialDen special hspecial
          have hnormalDen := LawfulCCanonicalRepresentation.normalDen_nonzero Dt a d hd
          have hbeforeConstants := LawfulGenuineCNormalReduction.coefficients_constant (N := N) Dt
            (canonicalResult Dt a d).normalNum (canonicalResult Dt a d).normalDen before
              hnormalDomain hnormalDen hnormal
          have hbeforeArguments := LawfulGenuineCNormalReduction.arguments_nonzero (N := N) Dt
            (canonicalResult Dt a d).normalNum (canonicalResult Dt a d).normalDen before
              hnormalDomain hnormalDen hnormal
          have hnormalConstants := LawfulGenuineCMonomialCase.postprocessNormal_coefficients_constant
            (C := C) Dt before normal hbeforeConstants hpost
          have hnormalArguments := LawfulGenuineCMonomialCase.postprocessNormal_arguments_nonzero
            (C := C) Dt before normal hbeforeArguments hpost
          constructor
          · intro cv hcv
            change cv ∈ special.logs ++ normal.logs at hcv
            rw [List.mem_append] at hcv
            exact hcv.elim (hspecialConstants cv) (hnormalConstants cv)
          · intro cv hcv
            change cv ∈ special.logs ++ normal.logs at hcv
            rw [List.mem_append] at hcv
            exact hcv.elim (hspecialArguments cv) (hnormalArguments cv)

end DeepWiki.SymbolicIntegration
