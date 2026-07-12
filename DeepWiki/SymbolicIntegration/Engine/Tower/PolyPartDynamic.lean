import DeepWiki.SymbolicIntegration.Engine.PolyPartTower

/-! # Explicit-derivation polynomial reduction

The legacy polynomial kernels select coefficient differentiation through `[CDiffField α]`. These
counterparts take `CFieldDerivation α` explicitly, so a mixed tower can use the derivative selected
by `DifferentialTowerPresentation` without changing the dense or sparse polynomial representation.
-/

namespace DeepWiki.SymbolicIntegration

universe u v

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

variable [LawfulCPolyEngine.{u,v} P]
variable [CFieldSpec.{u,v} α]

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

end Soundness

end DynamicPolynomialReduction

end DeepWiki.SymbolicIntegration
