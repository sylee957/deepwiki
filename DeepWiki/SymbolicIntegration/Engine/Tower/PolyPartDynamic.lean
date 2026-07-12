import DeepWiki.SymbolicIntegration.Engine.PolyPartTower

/-! # Explicit-derivation polynomial reduction

The legacy polynomial kernels select coefficient differentiation through `[CDiffField α]`. These
counterparts take `CFieldDerivation α` explicitly, so a mixed tower can use the derivative selected
by `DifferentialTowerPresentation` without changing the dense or sparse polynomial representation.
-/

namespace DeepWiki.SymbolicIntegration

universe u

namespace DynamicPolynomialReduction

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
variable {α : Type u} [CField α]

/-- Fuel-bounded nonlinear polynomial reduction under an explicit coefficient derivation. -/
def nonlinear (derivation : CFieldDerivation α) (Dt : P α) : ℕ → P α → P α × P α
  | 0, p => (CPoly.czero, CPolyEngine.cnorm p)
  | fuel + 1, p =>
    let p := CPolyEngine.cnorm p
    let delta := CPolyEngine.cdeg Dt
    if CPolyEngine.cisZero p || decide (CPolyEngine.cdeg p < delta) then
      (CPoly.czero, p)
    else
      let n := CPolyEngine.cdeg p
      let m := n - delta + 1
      let lam := CPolyEngine.clead Dt
      let c := CField.div (CPolyEngine.clead p)
        (CCommRing.mul (CField.natCast m) lam)
      let q0 := CPolyEngine.monomial (P := P) c m
      let p' := CPolyEngine.sub p (CPolyEngine.monomialDerivWith derivation Dt q0)
      let (q, r) := nonlinear derivation Dt fuel p'
      (CPolyEngine.add q0 q, r)

/-- Fuel-bounded primitive polynomial reduction under an explicit coefficient derivation. -/
def primitive (derivation : CFieldDerivation α) (Dt : P α) : ℕ → P α → P α × P α
  | 0, p => (CPoly.czero, CPolyEngine.cnorm p)
  | fuel + 1, p =>
    let p := CPolyEngine.cnorm p
    if CPolyEngine.cisZero p || decide (CPolyEngine.cdeg p = 0) then
      (CPoly.czero, p)
    else
      let m := CPolyEngine.cdeg p
      let am := CPolyEngine.clead p
      let mp1 : α := CField.natCast (m + 1)
      let dtConst := CPolyEngine.clead Dt
      let c := CField.div am (CCommRing.mul mp1 dtConst)
      let q0 := CPolyEngine.monomial (P := P) c (m + 1)
      let p' := CPolyEngine.sub p (CPolyEngine.monomialDerivWith derivation Dt q0)
      let (q, r) := primitive derivation Dt fuel p'
      (CPolyEngine.add q0 q, r)

/-- Boolean reconstruction check for an explicit-derivation polynomial reduction candidate. -/
def check (derivation : CFieldDerivation α) (Dt p : P α)
    (out : PolynomialReductionResult P α) : Bool :=
  CPolyEngine.cisZero
    (CPolyEngine.sub
      (CPolyEngine.add (CPolyEngine.monomialDerivWith derivation Dt out.antiderivative)
        out.remainder) p)

section Soundness

variable [LawfulCPolyEngine.{u,u} P]
variable [CFieldSpec.{u,u} α]

/-- A passed explicit-derivation reduction check has its denotational reconstruction meaning. -/
theorem check_sound (derivation : CFieldDerivation α)
    (diffK : Differential (CFieldSpec.K α)) [LawfulCFieldDerivation α derivation diffK]
    (Dt p : P α) (out : PolynomialReductionResult P α)
    (h : check derivation Dt p out = true) :
    letI : Differential (CRingSpec.R α) := diffK
    CPoly.toPoly p =
      Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly out.antiderivative) +
        CPoly.toPoly out.remainder := by
  letI : Differential (CRingSpec.R α) := diffK
  have hzero : CPoly.toPoly
      (CPolyEngine.sub
        (CPolyEngine.add (CPolyEngine.monomialDerivWith derivation Dt out.antiderivative)
          out.remainder) p) = 0 :=
    (LawfulCPolyEngine.cisZero_iff _).mp h
  rw [CPolyEngine.toPoly_sub, LawfulCPolyEngine.toPoly_add,
    CPolyEngine.toPoly_monomialDerivWith derivation diffK] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- A passed polynomial normal-form check has its denotation-level meaning. -/
theorem normalCheck_sound (kind : PolynomialReductionKind) (Dt : P α)
    (out : PolynomialReductionResult P α)
    (h : polynomialReductionNormalCheck kind Dt out = true) :
    match kind with
    | .nonlinear => (CPoly.toPoly out.remainder).natDegree < (CPoly.toPoly Dt).natDegree
    | .primitive => (CPoly.toPoly out.remainder).natDegree = 0 := by
  cases kind <;> simp only [polynomialReductionNormalCheck] at h
  · simpa only [LawfulCPolyEngine.cdeg_eq_natDegree] using of_decide_eq_true h
  · simpa only [LawfulCPolyEngine.cdeg_eq_natDegree] using of_decide_eq_true h

end Soundness

/-! ### Explicit polynomial-reduction stage -/

/-- Prop-free polynomial reduction selected for one explicit coefficient derivation. -/
structure CDifferentialPolynomialReduction (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] (derivation : CFieldDerivation α) where
  /-- Attempt the selected reduction at a finite fuel budget. -/
  reduce : PolynomialReductionKind → P α → ℕ → P α → Option (PolynomialReductionResult P α)

/-- Denotation-level polynomial reduction under an explicitly selected coefficient differential. -/
def IsDifferentialPolynomialReduction [CFieldSpec.{u,u} α]
    (diffK : Differential (CFieldSpec.K α)) (kind : PolynomialReductionKind) (Dt p : P α)
    (out : PolynomialReductionResult P α) : Prop :=
  letI : Differential (CRingSpec.R α) := diffK
  CPoly.toPoly p = Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly out.antiderivative)
      + CPoly.toPoly out.remainder
    ∧ match kind with
      | .nonlinear => (CPoly.toPoly out.remainder).natDegree < (CPoly.toPoly Dt).natDegree
      | .primitive => (CPoly.toPoly out.remainder).natDegree = 0

/-- Soundness law for an explicit-differential polynomial reducer. -/
class LawfulCDifferentialPolynomialReduction [CFieldSpec.{u,u} α]
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    (C : CDifferentialPolynomialReduction P α derivation) : Prop where
  /-- Every accepted reduction reconstructs its input and reaches its requested normal form. -/
  sound : ∀ (kind : PolynomialReductionKind) (Dt : P α) (fuel : ℕ) (p : P α)
      (out : PolynomialReductionResult P α),
    C.reduce kind Dt fuel p = some out →
      IsDifferentialPolynomialReduction diffK kind Dt p out

/-- Semantic domain on which an explicit polynomial reducer is relatively complete. -/
abbrev DifferentialPolynomialReductionDomain (P : Type u → Type u) (α : Type u) :=
  PolynomialReductionKind → P α → P α → Prop

/-- Relative-completeness law for an explicit-differential polynomial reducer. -/
class CompleteCDifferentialPolynomialReduction [CFieldSpec.{u,u} α]
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    (C : CDifferentialPolynomialReduction P α derivation)
    (domain : DifferentialPolynomialReductionDomain P α)
    [LawfulCDifferentialPolynomialReduction derivation diffK C] : Prop where
  /-- Every in-domain polynomial with a requested explicit normal form is eventually accepted. -/
  relative_complete : ∀ (kind : PolynomialReductionKind) (Dt p : P α),
    domain kind Dt p → (∃ out, IsDifferentialPolynomialReduction diffK kind Dt p out) →
      ∃ fuel out, C.reduce kind Dt fuel p = some out ∧
        IsDifferentialPolynomialReduction diffK kind Dt p out

/-- Export an explicit polynomial reducer through the common output-remainder stage contract. -/
noncomputable def CDifferentialPolynomialReduction.asRemainderIntegrationStage
    [CFieldSpec.{u,u} α] (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    (C : CDifferentialPolynomialReduction P α derivation)
    (domain : DifferentialPolynomialReductionDomain P α)
    [LawfulCDifferentialPolynomialReduction derivation diffK C]
    [CompleteCDifferentialPolynomialReduction derivation diffK C domain] :
    RemainderIntegrationStage (PolynomialReductionInput P α) (P α) (P α)
      (fun input => ∃ out,
        IsDifferentialPolynomialReduction diffK input.kind input.derivative input.polynomial out)
      (fun input antiderivative remainder =>
        IsDifferentialPolynomialReduction diffK input.kind input.derivative input.polynomial
          ⟨antiderivative, remainder⟩) :=
  { stage :=
      { run := fun fuel input =>
          (C.reduce input.kind input.derivative fuel input.polynomial).map fun out =>
            ⟨out.antiderivative, out.remainder⟩
        domain := fun input => domain input.kind input.derivative input.polynomial
        sound := by
          intro fuel input result hdomain hrun
          obtain ⟨out, hout, rfl⟩ := Option.map_eq_some_iff.mp hrun
          exact LawfulCDifferentialPolynomialReduction.sound input.kind input.derivative fuel
            input.polynomial out hout
        complete := by
          intro input hdomain hintegrable
          obtain ⟨fuel, out, hrun, _⟩ := CompleteCDifferentialPolynomialReduction.relative_complete
            (C := C) (domain := domain) input.kind input.derivative input.polynomial hdomain hintegrable
          exact ⟨fuel, ⟨out.antiderivative, out.remainder⟩, by simp [hrun]⟩ } }

/-- The raw output of the selected dynamic polynomial-reduction kernel. -/
def kernel (derivation : CFieldDerivation α) (kind : PolynomialReductionKind)
    (Dt : P α) (fuel : ℕ) (p : P α) : PolynomialReductionResult P α :=
  match kind with
  | .nonlinear =>
    let pair := nonlinear derivation Dt fuel p
    ⟨pair.1, pair.2⟩
  | .primitive =>
    let pair := primitive derivation Dt fuel p
    ⟨pair.1, pair.2⟩

/-- Checked dynamic polynomial reduction, using the explicit nonlinear and primitive kernels. -/
def checked (derivation : CFieldDerivation α) : CDifferentialPolynomialReduction P α derivation where
  reduce kind Dt fuel p :=
    let out := kernel derivation kind Dt fuel p
    if check derivation Dt p out && polynomialReductionNormalCheck kind Dt out then some out else none

section CheckedSoundness

variable [LawfulCPolyEngine.{u,u} P]
variable [CFieldSpec.{u,u} α]

/-- Every accepted checked dynamic reduction satisfies the explicit reconstruction and normal form. -/
theorem checked_sound (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    [LawfulCFieldDerivation α derivation diffK]
    (kind : PolynomialReductionKind) (Dt : P α) (fuel : ℕ) (p : P α)
    (out : PolynomialReductionResult P α)
    (hrun : (checked derivation).reduce kind Dt fuel p = some out) :
    IsDifferentialPolynomialReduction diffK kind Dt p out := by
  change
    (if check derivation Dt p (kernel derivation kind Dt fuel p) &&
        polynomialReductionNormalCheck kind Dt (kernel derivation kind Dt fuel p) then
      some (kernel derivation kind Dt fuel p)
    else none) = some out at hrun
  by_cases haccepted : (check derivation Dt p (kernel derivation kind Dt fuel p) &&
      polynomialReductionNormalCheck kind Dt (kernel derivation kind Dt fuel p)) = true
  · rw [if_pos haccepted] at hrun
    injection hrun with hout
    subst out
    rw [Bool.and_eq_true] at haccepted
    obtain ⟨hcheck, hnormal⟩ := haccepted
    refine ⟨check_sound derivation diffK Dt p _ hcheck, ?_⟩
    cases kind <;> exact normalCheck_sound _ Dt _ hnormal
  · rw [if_neg haccepted] at hrun
    simp at hrun

/-- The checked dynamic reducer satisfies the explicit polynomial-reduction soundness class. -/
@[reducible] noncomputable def checkedLawful
    (derivation : CFieldDerivation α) (diffK : Differential (CFieldSpec.K α))
    [LawfulCFieldDerivation α derivation diffK] :
    LawfulCDifferentialPolynomialReduction derivation diffK (checked derivation) where
  sound := checked_sound derivation diffK

end CheckedSoundness

end DynamicPolynomialReduction

end DeepWiki.SymbolicIntegration
