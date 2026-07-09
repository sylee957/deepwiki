import DeepWiki.ComputableAlgebra.PolyReprBridge
import DeepWiki.ComputableAlgebra.PolyReprSparse

/-! # `CPolyEngine` — the fat, migration-ready polynomial interface

`CPoly` is the thin representation interface (`coeff`/`degBound`/`ofFn`). `CPolyEngine` extends it
with the polynomial *operations as class fields* — so an instance supplies its **own efficient ops** and
proves their denotation squares as specs. Crucially the `List` instance supplies the **existing engine
ops** (`DensePoly.cadd`/`cmul`/`cnorm`/…), so `CPolyEngine.add (p : List α) = DensePoly.cadd p` **definitionally**
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
class CPolyEngine (P : Type u → Type u) extends CPoly P where
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
    CPoly.toPoly (add p q) = CPoly.toPoly p + CPoly.toPoly q
  toPoly_mul : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p q : P α),
    CPoly.toPoly (mul p q) = CPoly.toPoly p * CPoly.toPoly q
  toPoly_neg : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p : P α),
    CPoly.toPoly (neg p) = - CPoly.toPoly p
  toPoly_scale : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (c : α) (p : P α),
    CPoly.toPoly (scale c p) = Polynomial.C (CRingSpec.toR c) * CPoly.toPoly p
  toPoly_cnorm : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p : P α),
    CPoly.toPoly (cnorm p) = CPoly.toPoly p
  cisZero_iff : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p : P α),
    cisZero p = true ↔ CPoly.toPoly p = 0
  cdeg_eq_natDegree : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p : P α),
    cdeg p = (CPoly.toPoly p).natDegree
  toR_clead_eq_leadingCoeff : ∀ {α : Type u} [CCommRing α] [CRingSpec.{u,u} α] (p : P α),
    CRingSpec.toR (clead p) = (CPoly.toPoly p).leadingCoeff

/-- **The `List` instance IS the concrete engine** — its ops are `DensePoly.c*`, defeq to the engine's,
so a migrated declaration computes the same list output (⇒ `native_decide`-preserving). -/
instance instEngineList : CPolyEngine List where
  add := DensePoly.cadd
  mul := DensePoly.cmul
  neg := DensePoly.cneg
  scale := DensePoly.cscale
  cnorm := DensePoly.cnorm
  cisZero := DensePoly.cisZero
  cdeg := DensePoly.cdeg
  clead := DensePoly.clead
  toPoly_add p q := by rw [toPoly_list_eq, DensePoly.toPolyG_caddG, ← toPoly_list_eq, ← toPoly_list_eq]
  toPoly_mul p q := by rw [toPoly_list_eq, DensePoly.toPolyG_cmulG, ← toPoly_list_eq, ← toPoly_list_eq]
  toPoly_neg p := by rw [toPoly_list_eq, DensePoly.toPolyG_cnegG, ← toPoly_list_eq]
  toPoly_scale c p := by rw [toPoly_list_eq, DensePoly.toPolyG_cscaleG, ← toPoly_list_eq]
  toPoly_cnorm p := by rw [toPoly_list_eq, DensePoly.toPolyG_cnormG, ← toPoly_list_eq]
  cisZero_iff p := by rw [toPoly_list_eq]; exact DensePoly.cisZeroG_iff p
  cdeg_eq_natDegree p := by rw [toPoly_list_eq]; exact DensePoly.cdegG_eq_natDegree p
  toR_clead_eq_leadingCoeff p := by rw [toPoly_list_eq]; exact DensePoly.toR_cleadG_eq_leadingCoeff p

/-- **The `SparsePoly` instance** supplies the generic `ofFn`-based ops, so a migrated declaration also
runs on the sparse carrier — the representation-independence payoff at the engine level. -/
instance instEngineSparse : CPolyEngine CPoly.SparsePoly where
  add := CPoly.add
  mul := CPoly.mul
  neg := CPoly.neg
  scale := CPoly.scale
  cnorm := CPoly.cnorm
  cisZero := CPoly.cisZero
  cdeg := CPoly.cdeg
  clead := CPoly.clead
  toPoly_add p q := CPoly.toPoly_add p q
  toPoly_mul p q := CPoly.toPoly_mul p q
  toPoly_neg p := CPoly.toPoly_neg p
  toPoly_scale c p := CPoly.toPoly_scale c p
  toPoly_cnorm p := CPoly.toPoly_cnorm p
  cisZero_iff p := CPoly.cisZero_iff p
  cdeg_eq_natDegree p := CPoly.cdeg_eq_natDegree p
  toR_clead_eq_leadingCoeff p := CPoly.toR_clead_eq_leadingCoeff p

/-! ### The engine ops are the `List`-instance ops (defeq), so `native_decide` is preserved -/

/-- A declaration re-parametrised over `[CPolyEngine P]` computes exactly the engine output at `List`. -/
example : (CPolyEngine.mul (CPolyEngine.add ([1,2] : List ℚ) [3,4]) [1])
    = DensePoly.cmul (DensePoly.cadd [1,2] [3,4]) [1] := by native_decide

end DeepWiki.SymbolicIntegration
