import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv

/-! # Executable zero-test reflection for computable polynomials

`RefinesPoly p q` says `p`'s denotation is `q` (`toPoly p = q`). Its use here is the
`native_decide`-friendly reflection of the executable zero test `cisZero` into semantic (in)equality
of the refined polynomials — the bridge that lets a decidable `cisZero (csub p q)` check discharge
`toPoly p = toPoly q`.

General denotation *transfer* (synthesizing the abstract meaning of a computable expression) lives in
`DeepWiki.Transfer` (`transfer%` / `transfer`); this file keeps only the zero-test reflection.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPoly

/-- `p` refines `q` when `p`'s denotation is `q`. -/
def RefinesPoly {α : Type*} [CField α] [CFieldSpec α]
    (p : CPoly α) (q : (CFieldSpec.K α)[X]) : Prop :=
  toPoly p = q

/-- Every computable polynomial refines its own denotation. -/
theorem refinesPolyG_self {α : Type*} [CField α] [CFieldSpec α] (p : CPoly α) :
    RefinesPoly p (toPoly p) := rfl

namespace RefinesPoly

variable {α : Type*} [CField α] [CFieldSpec α]
variable {p q : CPoly α} {p' q' : (CFieldSpec.K α)[X]}

/-- Introduce `RefinesPoly` from a denotation equality. -/
theorem intro (h : toPoly p = p') : RefinesPoly p p' := h

/-- Eliminate `RefinesPoly` to its denotation equality. -/
theorem denote_eq (h : RefinesPoly p p') : toPoly p = p' := h

/-- `csub` respects `RefinesPoly` — the one operation needed by the zero-test reflection below. -/
theorem sub (hp : RefinesPoly p p') (hq : RefinesPoly q q') :
    RefinesPoly (csub p q) (p' - q') := by
  rw [RefinesPoly] at hp hq ⊢
  simp only [denote]
  rw [hp, hq]

/-- A true executable zero test reflects to zero of any refined semantic polynomial. -/
theorem eq_zero_of_cisZero (hp : RefinesPoly p p') (hz : cisZero p = true) : p' = 0 := by
  rw [← hp]; exact (cisZeroG_iff p).mp hz

/-- A false executable zero test reflects to nonzero of any refined semantic polynomial. -/
theorem ne_zero_of_cisZero_false (hp : RefinesPoly p p') (hz : cisZero p = false) : p' ≠ 0 := by
  intro hzero
  have htrue : cisZero p = true := (cisZeroG_iff p).mpr (by rw [hp, hzero])
  simp [hz] at htrue

/-- A true executable zero test on `p - q` reflects semantic equality of refined polynomials. -/
theorem eq_of_csub_cisZero (hp : RefinesPoly p p') (hq : RefinesPoly q q')
    (hz : cisZero (csub p q) = true) : p' = q' :=
  sub_eq_zero.mp (eq_zero_of_cisZero (sub hp hq) hz)

/-- A false executable zero test on `p - q` reflects semantic inequality of refined polynomials. -/
theorem ne_of_csub_cisZero_false (hp : RefinesPoly p p') (hq : RefinesPoly q q')
    (hz : cisZero (csub p q) = false) : p' ≠ q' := fun h =>
  ne_zero_of_cisZero_false (sub hp hq) hz (sub_eq_zero.mpr h)

end RefinesPoly

end DeepWiki.SymbolicIntegration
