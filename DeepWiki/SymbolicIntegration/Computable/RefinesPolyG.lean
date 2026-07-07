import DeepWiki.SymbolicIntegration.Computable.MonomialDeriv

/-! # Executable zero-test reflection for computable polynomials

`RefinesPolyG p q` says `p`'s denotation is `q` (`toPolyG p = q`). Its use here is the
`native_decide`-friendly reflection of the executable zero test `cisZeroG` into semantic (in)equality
of the refined polynomials — the bridge that lets a decidable `cisZeroG (csubG p q)` check discharge
`toPolyG p = toPolyG q`.

General denotation *transfer* (synthesizing the abstract meaning of a computable expression) lives in
`DeepWiki.Transfer` (`transfer%` / `transfer`); this file keeps only the zero-test reflection.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-- `p` refines `q` when `p`'s denotation is `q`. -/
def RefinesPolyG {α : Type*} [CField α] [CFieldSpec α]
    (p : CPolyG α) (q : (CFieldSpec.K α)[X]) : Prop :=
  toPolyG p = q

/-- Every computable polynomial refines its own denotation. -/
theorem refinesPolyG_self {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) :
    RefinesPolyG p (toPolyG p) := rfl

namespace RefinesPolyG

variable {α : Type*} [CField α] [CFieldSpec α]
variable {p q : CPolyG α} {p' q' : (CFieldSpec.K α)[X]}

/-- Introduce `RefinesPolyG` from a denotation equality. -/
theorem intro (h : toPolyG p = p') : RefinesPolyG p p' := h

/-- Eliminate `RefinesPolyG` to its denotation equality. -/
theorem denote_eq (h : RefinesPolyG p p') : toPolyG p = p' := h

/-- `csubG` respects `RefinesPolyG` — the one operation needed by the zero-test reflection below. -/
theorem sub (hp : RefinesPolyG p p') (hq : RefinesPolyG q q') :
    RefinesPolyG (csubG p q) (p' - q') := by
  rw [RefinesPolyG] at hp hq ⊢
  simp only [denote]
  rw [hp, hq]

/-- A true executable zero test reflects to zero of any refined semantic polynomial. -/
theorem eq_zero_of_cisZero (hp : RefinesPolyG p p') (hz : cisZeroG p = true) : p' = 0 := by
  rw [← hp]; exact (cisZeroG_iff p).mp hz

/-- A false executable zero test reflects to nonzero of any refined semantic polynomial. -/
theorem ne_zero_of_cisZero_false (hp : RefinesPolyG p p') (hz : cisZeroG p = false) : p' ≠ 0 := by
  intro hzero
  have htrue : cisZeroG p = true := (cisZeroG_iff p).mpr (by rw [hp, hzero])
  simp [hz] at htrue

/-- A true executable zero test on `p - q` reflects semantic equality of refined polynomials. -/
theorem eq_of_csub_cisZero (hp : RefinesPolyG p p') (hq : RefinesPolyG q q')
    (hz : cisZeroG (csubG p q) = true) : p' = q' :=
  sub_eq_zero.mp (eq_zero_of_cisZero (sub hp hq) hz)

/-- A false executable zero test on `p - q` reflects semantic inequality of refined polynomials. -/
theorem ne_of_csub_cisZero_false (hp : RefinesPolyG p p') (hq : RefinesPolyG q q')
    (hz : cisZeroG (csubG p q) = false) : p' ≠ q' := fun h =>
  ne_zero_of_cisZero_false (sub hp hq) hz (sub_eq_zero.mpr h)

end RefinesPolyG

end DeepWiki.SymbolicIntegration
