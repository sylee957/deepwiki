import DeepWiki.ComputableAlgebra.PolyReprBridge
import DeepWiki.ComputableAlgebra.PolyReprSparse

/-! # `CPolyEngine` — the fat, migration-ready polynomial interface

`CPolyRepr` is the thin representation interface (`coeff`/`degBound`/`ofFn`). `CPolyEngine` extends it
with the polynomial *operations as class fields* — so an instance supplies its **own efficient ops** and
proves their denotation squares as specs. Crucially the `List` instance supplies the **existing engine
ops** (`CPoly.cadd`/`cmul`/`cnorm`/…), so `CPolyEngine.add (p : List α) = CPoly.cadd p` **definitionally**
— a declaration re-parametrised over `[CPolyEngine P]` computes *exactly* the engine's list output at the
`List` instance, so `native_decide` is preserved. This is what makes the engine call-site migration a
behaviour-preserving, defeq-safe re-point (module by module). The `SparsePoly` instance supplies the
generic `ofFn`-based ops, so a migrated module also runs on the sparse carrier. See
`docs/representation-independent-poly.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u

/-- The fat polynomial-engine interface: the operations are fields (an instance provides its own), with
the denotation squares as specs. `CRingSpec.{u,u}` pins the coefficient ring to the same universe (which
every actual coefficient — `ℚ`, `CFrac β`, … — satisfies). -/
class CPolyEngine (P : Type u → Type u) extends CPolyRepr P where
  /-- Addition. -/
  add : {α : Type u} → [CCommRing α] → P α → P α → P α
  /-- Multiplication. -/
  mul : {α : Type u} → [CCommRing α] → P α → P α → P α
  /-- Negation. -/
  neg : {α : Type u} → [CCommRing α] → P α → P α
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
  toPoly_add : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p q : P α),
    CPolyRepr.toPoly (add p q) = CPolyRepr.toPoly p + CPolyRepr.toPoly q
  toPoly_mul : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p q : P α),
    CPolyRepr.toPoly (mul p q) = CPolyRepr.toPoly p * CPolyRepr.toPoly q
  toPoly_neg : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p : P α),
    CPolyRepr.toPoly (neg p) = - CPolyRepr.toPoly p
  toPoly_scale : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (c : α) (p : P α),
    CPolyRepr.toPoly (scale c p) = Polynomial.C (CRingSpec.toR c) * CPolyRepr.toPoly p
  toPoly_cnorm : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p : P α),
    CPolyRepr.toPoly (cnorm p) = CPolyRepr.toPoly p
  cisZero_iff : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p : P α),
    cisZero p = true ↔ CPolyRepr.toPoly p = 0
  cdeg_eq_natDegree : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p : P α),
    cdeg p = (CPolyRepr.toPoly p).natDegree
  toR_clead_eq_leadingCoeff : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p : P α),
    CRingSpec.toR (clead p) = (CPolyRepr.toPoly p).leadingCoeff

/-- **The `List` instance IS the concrete engine** — its ops are `CPoly.c*`, defeq to the engine's,
so a migrated declaration computes the same list output (⇒ `native_decide`-preserving). -/
instance instEngineList : CPolyEngine List where
  add := CPoly.cadd
  mul := CPoly.cmul
  neg := CPoly.cneg
  scale := CPoly.cscale
  cnorm := CPoly.cnorm
  cisZero := CPoly.cisZero
  cdeg := CPoly.cdeg
  clead := CPoly.clead
  toPoly_add p q := by rw [toPoly_list_eq, CPoly.toPolyG_caddG, ← toPoly_list_eq, ← toPoly_list_eq]
  toPoly_mul p q := by rw [toPoly_list_eq, CPoly.toPolyG_cmulG, ← toPoly_list_eq, ← toPoly_list_eq]
  toPoly_neg p := by rw [toPoly_list_eq, CPoly.toPolyG_cnegG, ← toPoly_list_eq]
  toPoly_scale c p := by rw [toPoly_list_eq, CPoly.toPolyG_cscaleG, ← toPoly_list_eq]
  toPoly_cnorm p := by rw [toPoly_list_eq, CPoly.toPolyG_cnormG, ← toPoly_list_eq]
  cisZero_iff p := by rw [toPoly_list_eq]; exact CPoly.cisZeroG_iff p
  cdeg_eq_natDegree p := by rw [toPoly_list_eq]; exact CPoly.cdegG_eq_natDegree p
  toR_clead_eq_leadingCoeff p := by rw [toPoly_list_eq]; exact CPoly.toR_cleadG_eq_leadingCoeff p

/-- **The `SparsePoly` instance** supplies the generic `ofFn`-based ops, so a migrated declaration also
runs on the sparse carrier — the representation-independence payoff at the engine level. -/
instance instEngineSparse : CPolyEngine CPolyRepr.SparsePoly where
  add := CPolyRepr.add
  mul := CPolyRepr.mul
  neg := CPolyRepr.neg
  scale := CPolyRepr.scale
  cnorm := CPolyRepr.cnorm
  cisZero := CPolyRepr.cisZero
  cdeg := CPolyRepr.cdeg
  clead := CPolyRepr.clead
  toPoly_add p q := CPolyRepr.toPoly_add p q
  toPoly_mul p q := CPolyRepr.toPoly_mul p q
  toPoly_neg p := CPolyRepr.toPoly_neg p
  toPoly_scale c p := CPolyRepr.toPoly_scale c p
  toPoly_cnorm p := CPolyRepr.toPoly_cnorm p
  cisZero_iff p := CPolyRepr.cisZero_iff p
  cdeg_eq_natDegree p := CPolyRepr.cdeg_eq_natDegree p
  toR_clead_eq_leadingCoeff p := CPolyRepr.toR_clead_eq_leadingCoeff p

/-! ### The engine ops are the `List`-instance ops (defeq), so `native_decide` is preserved -/

/-- A declaration re-parametrised over `[CPolyEngine P]` computes exactly the engine output at `List`. -/
example : (CPolyEngine.mul (CPolyEngine.add ([1,2] : List ℚ) [3,4]) [1])
    = CPoly.cmul (CPoly.cadd [1,2] [3,4]) [1] := by native_decide

end DeepWiki.SymbolicIntegration
