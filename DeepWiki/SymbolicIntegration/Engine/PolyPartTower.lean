import DeepWiki.SymbolicIntegration.Engine.Tower.Deriv
import DeepWiki.ComputableAlgebra.PolyEngine

/-! # Computable polynomial reduction and primitive-case integration over ℚ(x)[t]

`cPolyReduceTower` reduces `p ∈ k[t]` for a nonlinear monomial to `(q, r)` with `p = D(q) + r`,
`deg(r) < deg(Dt)`; `cPrimitivePolyIntegrate` integrates a polynomial part for a primitive
monomial in the constant-coefficient sub-case. Both generic over `[CField α] [CDiffField α]`. -/

namespace DeepWiki.SymbolicIntegration

universe u

/-! ### Polynomial-reduction stage interface

The reduction kernels below are intentionally fuel-bounded.  A caller must therefore not treat a
raw pair as a theorem.  `CPolynomialReduction` is the Prop-free operation boundary; its companion
contract records the reconstruction equation, while normal-form completeness is a separate capability.
The executable `towerPolynomialReduction` realizes the operation by checking the equation before exposing
a result. -/

/-- The normal form requested from a polynomial-reduction stage. -/
inductive PolynomialReductionKind where
  /-- Reduce modulo a nonlinear monomial derivative, leaving degree below `deg Dt`. -/
  | nonlinear
  /-- Reduce a primitive polynomial part to a constant remainder. -/
  | primitive
deriving DecidableEq, Repr

/-- The quotient and unreduced remainder emitted by polynomial reduction. -/
structure PolynomialReductionResult (P : Type u → Type u) [CPoly P]
    (α : Type u) [CField α] where
  /-- The polynomial whose monomial derivative has been removed. -/
  antiderivative : P α
  /-- The residual polynomial. -/
  remainder : P α

/-- Prop-free polynomial-reduction operations.  `none` means that the supplied fuel did not certify
a reduction; callers may increase fuel without changing the interface. -/
structure CPolynomialReduction (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] [CDiffField α] where
  /-- Attempt the selected polynomial reduction with a finite fuel budget. -/
  reduce : PolynomialReductionKind → P α → ℕ → P α → Option (PolynomialReductionResult P α)

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,u} P]
  {α : Type u} [CField α] [CFieldSpec.{u,u} α] [CDiffField α] [CDiffFieldSpec.{u,u} α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Denotation-level normal-form predicate for a polynomial-reduction output. -/
def IsPolynomialReduction (kind : PolynomialReductionKind) (Dt p : P α)
    (out : PolynomialReductionResult P α) : Prop :=
  CPoly.toPoly p = Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly out.antiderivative)
      + CPoly.toPoly out.remainder
    ∧ match kind with
      | .nonlinear => (CPoly.toPoly out.remainder).natDegree < (CPoly.toPoly Dt).natDegree
      | .primitive => (CPoly.toPoly out.remainder).natDegree = 0

/-- Denotation-level soundness contract for a polynomial-reduction operation. -/
class LawfulCPolynomialReduction (C : CPolynomialReduction P α) : Prop where
  /-- Every successful reduction reconstructs its input. -/
  sound : ∀ (kind : PolynomialReductionKind) (Dt : P α) (fuel : ℕ) (p : P α)
      (out : PolynomialReductionResult P α),
    C.reduce kind Dt fuel p = some out →
      CPoly.toPoly p = Differential.implicitDeriv (CPoly.toPoly Dt)
          (CPoly.toPoly out.antiderivative) + CPoly.toPoly out.remainder
  /-- Every successful reduction reaches the requested remainder normal form. -/
  normal_form : ∀ (kind : PolynomialReductionKind) (Dt : P α) (fuel : ℕ) (p : P α)
      (out : PolynomialReductionResult P α),
    C.reduce kind Dt fuel p = some out →
      match kind with
      | .nonlinear => (CPoly.toPoly out.remainder).natDegree < (CPoly.toPoly Dt).natDegree
      | .primitive => (CPoly.toPoly out.remainder).natDegree = 0

/-- Semantic domain on which a polynomial-reduction operation is required to be complete. -/
abbrev PolynomialReductionDomain (P : Type u → Type u) (α : Type u) :=
  PolynomialReductionKind → P α → P α → Prop

/-- Relative completeness contract for a polynomial-reduction operation on a selected domain. -/
class CompleteCPolynomialReduction (C : CPolynomialReduction P α)
    (domain : PolynomialReductionDomain P α) [LawfulCPolynomialReduction C] : Prop where
  /-- If an in-domain requested normal form exists, some finite fuel budget returns a normal-form result. -/
  relative_complete : ∀ (kind : PolynomialReductionKind) (Dt p : P α),
    domain kind Dt p → (∃ out, IsPolynomialReduction kind Dt p out) →
      ∃ fuel out, C.reduce kind Dt fuel p = some out ∧ IsPolynomialReduction kind Dt p out

/-- The exact acceptance domain of a selected polynomial-reduction operation. -/
def polynomialReductionAcceptanceDomain (C : CPolynomialReduction P α) :
    PolynomialReductionDomain P α := fun kind Dt p =>
  ∃ fuel out, C.reduce kind Dt fuel p = some out ∧ IsPolynomialReduction kind Dt p out

/-- Every selected polynomial-reduction operation is complete on its explicit acceptance domain. -/
instance instCompleteCPolynomialReductionAcceptance (C : CPolynomialReduction P α)
    [LawfulCPolynomialReduction C] :
    CompleteCPolynomialReduction C (polynomialReductionAcceptanceDomain C) where
  relative_complete _kind _Dt _p hdomain _ := hdomain

/-- Boolean reconstruction check for a candidate polynomial reduction. -/
def polynomialReductionCheck (Dt p : P α) (out : PolynomialReductionResult P α) : Bool :=
  CPolyEngine.cisZero
    (CPolyEngine.sub
      (CPolyEngine.add (CPolyEngine.monomialDeriv Dt out.antiderivative) out.remainder) p)

/-- Executable normal-form check for the requested polynomial-reduction branch. -/
def polynomialReductionNormalCheck (kind : PolynomialReductionKind) (Dt : P α)
    (out : PolynomialReductionResult P α) : Bool :=
  match kind with
  | .nonlinear => decide (CPolyEngine.cdeg out.remainder < CPolyEngine.cdeg Dt)
  | .primitive => decide (CPolyEngine.cdeg out.remainder = 0)

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- A passed polynomial-reduction normal-form check has its denotation-level meaning. -/
theorem polynomialReductionNormalCheck_sound (kind : PolynomialReductionKind) (Dt : P α)
    (out : PolynomialReductionResult P α)
    (h : polynomialReductionNormalCheck kind Dt out = true) :
    match kind with
    | .nonlinear => (CPoly.toPoly out.remainder).natDegree < (CPoly.toPoly Dt).natDegree
    | .primitive => (CPoly.toPoly out.remainder).natDegree = 0 := by
  cases kind <;> simp only [polynomialReductionNormalCheck] at h
  · simpa only [LawfulCPolyEngine.cdeg_eq_natDegree] using (of_decide_eq_true h)
  · simpa only [LawfulCPolyEngine.cdeg_eq_natDegree] using (of_decide_eq_true h)

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- A passed polynomial-reduction reconstruction check has its denotation-level meaning. -/
theorem polynomialReductionCheck_sound (Dt p : P α) (out : PolynomialReductionResult P α)
    (h : polynomialReductionCheck Dt p out = true) :
    CPoly.toPoly p = Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly out.antiderivative)
      + CPoly.toPoly out.remainder := by
  have hzero : CPoly.toPoly
      (CPolyEngine.sub
        (CPolyEngine.add (CPolyEngine.monomialDeriv Dt out.antiderivative) out.remainder) p) = 0 :=
    (LawfulCPolyEngine.cisZero_iff _).mp h
  rw [CPolyEngine.toPoly_sub, LawfulCPolyEngine.toPoly_add,
    CPolyEngine.toPoly_monomialDeriv] at hzero
  exact (sub_eq_zero.mp hzero).symm

namespace DensePoly

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,u} P]
  {α : Type u} [CField α] [CDiffField α]

/-! ### The polynomial reduction

For a nonlinear monomial `t` (`δ(t) = deg(Dt) ≥ 2`, `λ(t) = lc(Dt)`), every `p ∈ k[t]` splits as
`p = D(q) + r` with `deg(r) < δ(t)`, peeling the leading term one step at a time. -/

/-- **Computable polynomial reduction** `cPolyReduceTower Dt fuel p = (q, r)` for a **nonlinear**
monomial `t` (`δ(t) = deg(Dt) ≥ 2`, `λ(t) = lc(Dt)`): `p = D(q) + r` with `deg(r) < δ(t)`, peeling
`q₀ = (lc(p)/(m·λ(t)))·tᵐ` (`m = deg(p) − δ(t) + 1`) whose monomial derivative `D(q₀)`
(`CPolyEngine.monomialDeriv Dt`) cancels the top of `p`, then recursing on `p − D(q₀)`. Fuel-bounded; generic. -/
def cPolyReduceTower (Dt : P α) : ℕ → P α → P α × P α
  | 0, p => (CPoly.czero, CPolyEngine.cnorm p)
  | fuel + 1, p =>
    let p := CPolyEngine.cnorm p
    let delta := CPolyEngine.cdeg Dt                               -- `δ(t) = deg(Dt)`
    if CPolyEngine.cisZero p || decide (CPolyEngine.cdeg p < delta) then
      (CPoly.czero, p)                                             -- `deg(p) < δ(t)` ⇒ done
    else
      let n := CPolyEngine.cdeg p
      let m := n - delta + 1                                       -- `m = deg(p) − δ(t) + 1`
      let lam := CPolyEngine.clead Dt                              -- `λ(t) = lc(Dt)`
      let c := CField.div (CPolyEngine.clead p) (CCommRing.mul (CField.natCast m) lam) -- `lc(p)/(m·λ(t))`
      let q0 := CPolyEngine.monomial (P := P) c m                  -- `c·tᵐ`
      let p' := CPolyEngine.sub p (CPolyEngine.monomialDeriv Dt q0)           -- `p − D(q₀)`
      let (q, r) := cPolyReduceTower Dt fuel p'
      (CPolyEngine.add q0 q, r)

/-! ### The primitive-case reduced-element integration

For a **primitive** monomial `t` (`Dt ∈ k`, `δ(t) = 0`, e.g. `t = log x`), integrating `p = ∑ aᵢtⁱ`
proceeds top-down. We implement the **constant-coefficient sub-case** `c = aₘ/((m+1)·Dt)`, `b = 0`. -/

/-- **Primitive-case polynomial integration** `cPrimitivePolyIntegrate Dt fuel p = (q, rem)` for a
**primitive** monomial `t` (`Dt ∈ k`, `δ(t) = 0`, e.g. `t = log x`, `Dt = 1/x`): integrate `p = ∑ aᵢtⁱ`
top-down by peeling `q₀ = c·t^(m+1)/(m+1)` for each leading term `aₘ` with `c = aₘ/((m+1)·Dt)`
(constant-coefficient sub-case `b = 0`). Returns `(q, rem)` with `D(q) + rem = p`, peeling all degrees
`≥ 1` (the degree-`0` term stays in `rem`). Fuel-bounded; generic. -/
def cPrimitivePolyIntegrate (Dt : P α) : ℕ → P α → P α × P α
  | 0, p => (CPoly.czero, CPolyEngine.cnorm p)
  | fuel + 1, p =>
    let p := CPolyEngine.cnorm p
    if CPolyEngine.cisZero p || decide (CPolyEngine.cdeg p = 0) then
      (CPoly.czero, p)                                             -- only the `t⁰` term left ⇒ done
    else
      let m := CPolyEngine.cdeg p                                  -- current top degree `m ≥ 1`
      let am := CPolyEngine.clead p                                -- leading coefficient `aₘ`
      -- `q₀ = c·t^(m+1)/(m+1)` with `c = aₘ/((m+1)·Dt)` (constant-coeff `LimitedIntegrate`, `b = 0`).
      let mp1 : α := CField.natCast (m + 1)
      -- `Dt ∈ k` is a constant `t`-polynomial; use its constant coefficient `Dt(0) = lc(Dt)`.
      let dtConst := CPolyEngine.clead Dt
      let c := CField.div am (CCommRing.mul mp1 dtConst)
      let q0 := CPolyEngine.monomial (P := P) c (m + 1)            -- `c·t^(m+1)`
      let p' := CPolyEngine.sub p (CPolyEngine.monomialDeriv Dt q0)           -- `p − D(q₀)`
      let (q, rem) := cPrimitivePolyIntegrate Dt fuel p'
      (CPolyEngine.add q0 q, rem)

/-- The existing tower polynomial kernels exposed as a checked `CPolynomialReduction` operation.
An insufficient fuel budget returns `none` rather than an uncertified pair. -/
def towerPolynomialReduction : CPolynomialReduction P α where
  reduce kind Dt fuel p :=
    let out : PolynomialReductionResult P α :=
      match kind with
      | .nonlinear =>
        let raw := cPolyReduceTower Dt fuel p
        ⟨raw.1, raw.2⟩
      | .primitive =>
        let raw := cPrimitivePolyIntegrate Dt fuel p
        ⟨raw.1, raw.2⟩
    if polynomialReductionCheck Dt p out && polynomialReductionNormalCheck kind Dt out then some out else none

variable [CFieldSpec α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]

/-- The checked tower polynomial reduction satisfies the reconstruction contract. -/
instance instLawfulCPolynomialReductionTower :
    LawfulCPolynomialReduction (towerPolynomialReduction (P := P) (α := α)) where
  sound kind Dt fuel p out hrun := by
    cases kind <;> simp only [towerPolynomialReduction] at hrun
    all_goals
      split at hrun
      · rename_i hcheck
        have hout := Option.some.inj hrun
        subst out
        rw [Bool.and_eq_true] at hcheck
        exact polynomialReductionCheck_sound Dt p _ hcheck.1
      · contradiction
  normal_form kind Dt fuel p out hrun := by
    cases kind with
    | nonlinear =>
      simp only [towerPolynomialReduction] at hrun
      split at hrun
      · rename_i hcheck
        have hout := Option.some.inj hrun
        subst out
        rw [Bool.and_eq_true] at hcheck
        exact polynomialReductionNormalCheck_sound .nonlinear Dt _ hcheck.2
      · contradiction
    | primitive =>
      simp only [towerPolynomialReduction] at hrun
      split at hrun
      · rename_i hcheck
        have hout := Option.some.inj hrun
        subst out
        rw [Bool.and_eq_true] at hcheck
        exact polynomialReductionNormalCheck_sound .primitive Dt _ hcheck.2
      · contradiction

end DensePoly

end DeepWiki.SymbolicIntegration
