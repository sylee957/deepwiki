import DeepWiki.ComputableAlgebra.PolyReprDenote

/-! # Migration bridge: the interface agrees with the existing `CPoly` engine (Step 4)

The concrete `CPoly α := List α` engine and the representation-generic `CPolyRepr` interface, at the
dense `List` instance, denote **identically**: `CPolyRepr.toPoly p = CPoly.toPoly p`. Since every engine
correctness theorem is stated through `toPoly`, this bridge is exactly what lets the engine be migrated
onto the interface without touching a single proof of correctness — the generic ops agree with the
concrete ones under the denotation (`add`↔`cadd`, `mul`↔`cmul`), so call sites can be re-pointed
`CPoly.c* → CPolyRepr.*` incrementally, gate-green.

The remaining bulk — actually swapping the ~hundreds of engine call sites and their `toPolyG_*` proofs
onto the generic ops — is mechanical but large (a dedicated multi-session sweep). This file establishes
the foundation that makes it safe. See `docs/representation-independent-poly.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {α : Type u} [CCommRing α] [CRingSpec α]

/-- **The migration bridge:** the interface denotation at the dense `List` instance IS the concrete
engine denotation. Both read `(toPoly p).coeff k = toR (p.getD k 0)`. -/
theorem toPoly_list_eq (p : List α) : CPolyRepr.toPoly p = CPoly.toPoly p := by
  apply Polynomial.ext; intro k
  rw [CPolyRepr.coeff_toPoly, CPoly.toPolyG_coeff]
  rfl

/-- The generic `add` agrees with the engine `cadd` under the denotation — so a call site may swap
`CPoly.cadd` for `CPolyRepr.add` and every `toPoly`-stated theorem still holds. -/
theorem toPoly_add_eq_cadd (p q : List α) :
    CPoly.toPoly (CPolyRepr.add p q) = CPoly.toPoly (CPoly.cadd p q) := by
  rw [← toPoly_list_eq, CPolyRepr.toPoly_add, toPoly_list_eq, toPoly_list_eq,
    ← CPoly.toPolyG_caddG]

/-- The generic `mul` agrees with the engine `cmul` under the denotation. -/
theorem toPoly_mul_eq_cmul (p q : List α) :
    CPoly.toPoly (CPolyRepr.mul p q) = CPoly.toPoly (CPoly.cmul p q) := by
  rw [← toPoly_list_eq, CPolyRepr.toPoly_mul, toPoly_list_eq, toPoly_list_eq,
    ← CPoly.toPolyG_cmulG]

/-- The generic `neg` agrees with the engine `cneg` under the denotation. -/
theorem toPoly_neg_eq_cneg (p : List α) :
    CPoly.toPoly (CPolyRepr.neg p) = CPoly.toPoly (CPoly.cneg p) := by
  rw [← toPoly_list_eq, CPolyRepr.toPoly_neg, toPoly_list_eq, ← CPoly.toPolyG_cnegG]

end DeepWiki.SymbolicIntegration
