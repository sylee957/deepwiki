import DeepWiki.ComputableAlgebra.PolyReprBridge
import DeepWiki.ComputableAlgebra.PolyReprSparse

/-! # `CPolyEngine` — a migration-ready polynomial interface

`CPoly` is the thin representation interface (`coeff`/`degBound`/`ofFn`). `CPolyEngine` carries the
polynomial *operations as class fields*, while `LawfulCPolyEngine` carries their denotation squares.
Crucially the `List` instance supplies the **existing engine ops**
(`DensePoly.cadd`/`cmul`/`cnorm`/…), so `CPolyEngine.add (p : List α) = DensePoly.cadd p` **definitionally**
— a declaration re-parametrised over `[CPoly P] [CPolyEngine P]` computes *exactly* the engine's list output at the
`List` instance, so `native_decide` is preserved. This is what makes the engine call-site migration a
behaviour-preserving, defeq-safe re-point (module by module). The `SparsePoly` instance supplies the
generic `ofFn`-based ops, so a migrated module also runs on the sparse carrier. See
`docs/representation-independent-poly.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u

/-- The Prop-free polynomial-engine operations supplied by a concrete representation. -/
class CPolyEngine (P : Type u → Type u) where
  /-- Addition. -/
  add : {α : Type u} → [CCommRing α] → P α → P α → P α
  /-- Multiplication. -/
  mul : {α : Type u} → [CCommRing α] → P α → P α → P α
  /-- Negation. -/
  neg : {α : Type u} → [CCommRing α] → P α → P α
  /-- Formal derivative. -/
  deriv : {α : Type u} → [CField α] → P α → P α
  /-- Scalar multiplication. -/
  scale : {α : Type u} → [CCommRing α] → α → P α → P α
  /-- Trailing-zero-free canonical form. -/
  cnorm : {α : Type u} → [CCommRing α] → P α → P α
  /-- Zero test. -/
  cisZero : {α : Type u} → [CCommRing α] → P α → Bool
  /-- Honest degree. -/
  cdeg : {α : Type u} → [CCommRing α] → P α → ℕ
  /-- Leading coefficient. -/
  clead : {α : Type u} → [CCommRing α] → P α → α

/-- Denotation laws for a `CPolyEngine`, separated from its computable operations. -/
class LawfulCPolyEngine (P : Type u → Type u) [CPoly P] [CPolyEngine P] : Prop where
  toPoly_add : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p q : P α),
    CPoly.toPoly (CPolyEngine.add p q) = CPoly.toPoly p + CPoly.toPoly q
  toPoly_mul : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p q : P α),
    CPoly.toPoly (CPolyEngine.mul p q) = CPoly.toPoly p * CPoly.toPoly q
  toPoly_neg : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p : P α),
    CPoly.toPoly (CPolyEngine.neg p) = - CPoly.toPoly p
  toPoly_deriv : ∀ {α : Type u} [CField α] [CFieldSpec.{u,u} α] (p : P α),
    CPoly.toPoly (CPolyEngine.deriv p) = (CPoly.toPoly p).derivative
  toPoly_scale : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (c : α) (p : P α),
    CPoly.toPoly (CPolyEngine.scale c p) = Polynomial.C (CRingSpec.toR c) * CPoly.toPoly p
  toPoly_cnorm : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p : P α),
    CPoly.toPoly (CPolyEngine.cnorm p) = CPoly.toPoly p
  cisZero_iff : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p : P α),
    CPolyEngine.cisZero p = true ↔ CPoly.toPoly p = 0
  cdeg_eq_natDegree : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p : P α),
    CPolyEngine.cdeg p = (CPoly.toPoly p).natDegree
  toR_clead_eq_leadingCoeff : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p : P α),
    CRingSpec.toR (CPolyEngine.clead p) = (CPoly.toPoly p).leadingCoeff

namespace CPolyEngine

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
  {α : Type u} [CCommRing α]

/-- Subtraction derived from the engine's addition and negation. -/
def sub (p q : P α) : P α := add p (neg q)

/-- Engine subtraction denotes polynomial subtraction. -/
theorem toPoly_sub [LawfulCPolyEngine P] [CRingSpec.{u,u} α] (p q : P α) :
    CPoly.toPoly (sub p q) = CPoly.toPoly p - CPoly.toPoly q := by
  rw [sub, LawfulCPolyEngine.toPoly_add, LawfulCPolyEngine.toPoly_neg, sub_eq_add_neg]

end CPolyEngine

/-- **The `List` instance IS the concrete engine** — its ops are `DensePoly.c*`, defeq to the engine's,
so a migrated declaration computes the same list output (⇒ `native_decide`-preserving). -/
instance instEngineList : CPolyEngine List where
  add := DensePoly.cadd
  mul := DensePoly.cmul
  neg := DensePoly.cneg
  deriv := DensePoly.cderiv
  scale := DensePoly.cscale
  cnorm := DensePoly.cnorm
  cisZero := DensePoly.cisZero
  cdeg := DensePoly.cdeg
  clead := DensePoly.clead

/-- The concrete dense engine operations satisfy the generic denotation laws. -/
instance instLawfulEngineList : LawfulCPolyEngine List where
  toPoly_add p q := by
    change CPoly.toPoly (DensePoly.cadd p q) = _
    rw [toPoly_list_eq, DensePoly.toPolyG_caddG, ← toPoly_list_eq, ← toPoly_list_eq]
  toPoly_mul p q := by
    change CPoly.toPoly (DensePoly.cmul p q) = _
    rw [toPoly_list_eq, DensePoly.toPolyG_cmulG, ← toPoly_list_eq, ← toPoly_list_eq]
  toPoly_neg p := by
    change CPoly.toPoly (DensePoly.cneg p) = _
    rw [toPoly_list_eq, DensePoly.toPolyG_cnegG, ← toPoly_list_eq]
  toPoly_deriv p := by
    change CPoly.toPoly (DensePoly.cderiv p) = _
    rw [toPoly_list_eq, DensePoly.toPolyG_cderivG, ← toPoly_list_eq]
  toPoly_scale c p := by
    change CPoly.toPoly (DensePoly.cscale c p) = _
    rw [toPoly_list_eq, DensePoly.toPolyG_cscaleG, ← toPoly_list_eq]
  toPoly_cnorm p := by
    change CPoly.toPoly (DensePoly.cnorm p) = _
    rw [toPoly_list_eq, DensePoly.toPolyG_cnormG, ← toPoly_list_eq]
  cisZero_iff p := by
    change DensePoly.cisZero p = true ↔ _
    rw [toPoly_list_eq]; exact DensePoly.cisZeroG_iff p
  cdeg_eq_natDegree p := by
    change DensePoly.cdeg p = _
    rw [toPoly_list_eq]; exact DensePoly.cdegG_eq_natDegree p
  toR_clead_eq_leadingCoeff p := by
    change CRingSpec.toR (DensePoly.clead p) = _
    rw [toPoly_list_eq]; exact DensePoly.toR_cleadG_eq_leadingCoeff p

namespace CPolyEngine

/-- The engine degree on the dense representation is the concrete dense degree. -/
@[simp] theorem cdeg_dense_eq {α : Type u} [CCommRing α] (p : DensePoly α) :
    CPolyEngine.cdeg p = DensePoly.cdeg p := rfl

/-- Engine scaling on the dense representation is concrete dense scaling. -/
@[simp] theorem scale_dense_eq {α : Type u} [CCommRing α] (c : α) (p : DensePoly α) :
    CPolyEngine.scale c p = DensePoly.cscale c p := rfl

/-- Engine normalization on the dense representation is concrete dense normalization. -/
@[simp] theorem cnorm_dense_eq {α : Type u} [CCommRing α] (p : DensePoly α) :
    CPolyEngine.cnorm p = DensePoly.cnorm p := rfl

/-- Engine differentiation on the dense representation is concrete dense differentiation. -/
@[simp] theorem deriv_dense_eq {α : Type u} [CField α] (p : DensePoly α) :
    CPolyEngine.deriv p = DensePoly.cderiv p := rfl

/-- Engine subtraction on the dense representation is concrete dense subtraction. -/
@[simp] theorem sub_dense_eq {α : Type u} [CCommRing α] (p q : DensePoly α) :
    CPolyEngine.sub p q = DensePoly.csub p q := rfl

end CPolyEngine

/-- **The `SparsePoly` instance** supplies the generic `ofFn`-based ops, so a migrated declaration also
runs on the sparse carrier — the representation-independence payoff at the engine level. -/
instance instEngineSparse : CPolyEngine CPoly.SparsePoly where
  add := CPoly.add
  mul := CPoly.mul
  neg := CPoly.neg
  deriv := CPoly.cderiv
  scale := CPoly.scale
  cnorm := CPoly.cnorm
  cisZero := CPoly.cisZero
  cdeg := CPoly.cdeg
  clead := CPoly.clead

/-- The generic sparse engine operations satisfy the generic denotation laws. -/
instance instLawfulEngineSparse : LawfulCPolyEngine CPoly.SparsePoly where
  toPoly_add p q := by change CPoly.toPoly (CPoly.add p q) = _; exact CPoly.toPoly_add p q
  toPoly_mul p q := by change CPoly.toPoly (CPoly.mul p q) = _; exact CPoly.toPoly_mul p q
  toPoly_neg p := by change CPoly.toPoly (CPoly.neg p) = _; exact CPoly.toPoly_neg p
  toPoly_deriv p := by
    change CPoly.toPoly (CPoly.cderiv p) = (CPoly.toPoly p).derivative
    exact CPoly.toPoly_cderiv p
  toPoly_scale c p := by change CPoly.toPoly (CPoly.scale c p) = _; exact CPoly.toPoly_scale c p
  toPoly_cnorm p := by change CPoly.toPoly (CPoly.cnorm p) = _; exact CPoly.toPoly_cnorm p
  cisZero_iff p := by change CPoly.cisZero p = true ↔ _; exact CPoly.cisZero_iff p
  cdeg_eq_natDegree p := by change CPoly.cdeg p = _; exact CPoly.cdeg_eq_natDegree p
  toR_clead_eq_leadingCoeff p := by
    change CRingSpec.toR (CPoly.clead p) = _
    exact CPoly.toR_clead_eq_leadingCoeff p

/-! ### The engine ops are the `List`-instance ops (defeq), so `native_decide` is preserved -/

/-- A declaration re-parametrised over `[CPoly P] [CPolyEngine P]` computes exactly the engine output at `List`. -/
example : (CPolyEngine.mul (CPolyEngine.add ([1,2] : List ℚ) [3,4]) [1])
    = DensePoly.cmul (DensePoly.cadd [1,2] [3,4]) [1] := by native_decide

end DeepWiki.SymbolicIntegration
