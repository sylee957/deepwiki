import DeepWiki.SymbolicIntegration.Computable.MonomialDeriv

/-! # Refinement relation for generic computable polynomials

`RefinesPolyG p q` relates a computable coefficient list to its semantic polynomial reading.
The respect lemmas expose the existing denotation squares as a proof-side transfer API.
-/

open Polynomial
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-- `p` refines `q` when `p`'s denotation is `q`. -/
def RefinesPolyG {α : Type*} [CField α] [CFieldSpec α]
    (p : CPolyG α) (q : (CFieldSpec.K α)[X]) : Prop :=
  toPolyG p = q

/-- Prove refinement and denotation-equality goals by pushing `toPolyG` through computable operations. -/
macro "transfer" : tactic => `(tactic| simp_all [RefinesPolyG, denote])

namespace RefinesPolyG

variable {α : Type*} [CField α] [CFieldSpec α]
variable {p q : CPolyG α} {p' q' : (CFieldSpec.K α)[X]}

/-- Introduce `RefinesPolyG` from a denotation equality. -/
theorem intro (h : toPolyG p = p') : RefinesPolyG p p' := h

/-- Eliminate `RefinesPolyG` to its denotation equality. -/
theorem denote_eq (h : RefinesPolyG p p') : toPolyG p = p' := h

end RefinesPolyG

/-- Every computable polynomial refines its own denotation. -/
theorem refinesPolyG_self {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) :
    RefinesPolyG p (toPolyG p) :=
  rfl

namespace RefinesPolyG

variable {α : Type*} [CField α] [CFieldSpec α]
variable {p q : CPolyG α} {p' q' : (CFieldSpec.K α)[X]}

/-- The empty list refines the zero polynomial. -/
@[refines] theorem nil : RefinesPolyG ([] : CPolyG α) 0 := by
  simp [RefinesPolyG]

/-- A singleton list refines the corresponding constant polynomial. -/
@[refines] theorem const (c : α) : RefinesPolyG ([c] : CPolyG α) (Polynomial.C (CFieldSpec.toK c)) := by
  simp [RefinesPolyG]

/-- `[CField.zero]` refines the zero polynomial. -/
@[refines] theorem zero : RefinesPolyG ([CField.zero] : CPolyG α) 0 := by
  simp [RefinesPolyG, denote]

/-- `[CField.one]` refines the one polynomial. -/
@[refines] theorem one : RefinesPolyG ([CField.one] : CPolyG α) 1 := by
  simp [RefinesPolyG, denote]

/-- `caddG` respects `RefinesPolyG`. -/
@[refines] theorem add (hp : RefinesPolyG p p') (hq : RefinesPolyG q q') :
    RefinesPolyG (caddG p q) (p' + q') := by
  rw [RefinesPolyG] at hp hq ⊢
  rw [toPolyG_caddG, hp, hq]

/-- `cnegG` respects `RefinesPolyG`. -/
@[refines] theorem neg (hp : RefinesPolyG p p') :
    RefinesPolyG (cnegG p) (-p') := by
  rw [RefinesPolyG] at hp ⊢
  rw [toPolyG_cnegG, hp]

/-- `csubG` respects `RefinesPolyG`. -/
@[refines] theorem sub (hp : RefinesPolyG p p') (hq : RefinesPolyG q q') :
    RefinesPolyG (csubG p q) (p' - q') := by
  rw [RefinesPolyG] at hp hq ⊢
  rw [toPolyG_csubG, hp, hq]

/-- `cscaleG` respects `RefinesPolyG`. -/
@[refines] theorem scale (c : α) (hp : RefinesPolyG p p') :
    RefinesPolyG (cscaleG c p) (Polynomial.C (CFieldSpec.toK c) * p') := by
  rw [RefinesPolyG] at hp ⊢
  rw [toPolyG_cscaleG, hp]

/-- `cshiftG` respects `RefinesPolyG`. -/
@[refines] theorem shift (k : ℕ) (hp : RefinesPolyG p p') :
    RefinesPolyG (cshiftG k p) (X ^ k * p') := by
  rw [RefinesPolyG] at hp ⊢
  rw [toPolyG_cshiftG, hp]

/-- `cmulG` respects `RefinesPolyG`. -/
@[refines] theorem mul (hp : RefinesPolyG p p') (hq : RefinesPolyG q q') :
    RefinesPolyG (cmulG p q) (p' * q') := by
  rw [RefinesPolyG] at hp hq ⊢
  rw [toPolyG_cmulG, hp, hq]

/-- `cpowG` respects `RefinesPolyG`. -/
@[refines] theorem pow (hp : RefinesPolyG p p') (n : ℕ) :
    RefinesPolyG (cpowG p n) (p' ^ n) := by
  rw [RefinesPolyG] at hp ⊢
  rw [toPolyG_cpowG, hp]

/-- `cnormG` refines the original denotation. -/
@[refines] theorem norm : RefinesPolyG (cnormG p) (toPolyG p) := by
  rw [RefinesPolyG, toPolyG_cnormG]

/-- `cnormG` respects an existing `RefinesPolyG` proof. -/
@[refines] theorem norm_of (hp : RefinesPolyG p p') :
    RefinesPolyG (cnormG p) p' := by
  rw [RefinesPolyG] at hp ⊢
  rw [toPolyG_cnormG, hp]

/-- `cderivG` respects `RefinesPolyG`. -/
@[refines] theorem deriv (hp : RefinesPolyG p p') :
    RefinesPolyG (cderivG p) (Polynomial.derivative p') := by
  rw [RefinesPolyG] at hp ⊢
  rw [toPolyG_cderivG, hp]

variable [CDiffField α] [CDiffFieldSpec α]

/-- `cmapDeriv` respects `RefinesPolyG`. -/
@[refines] theorem mapDeriv (hp : RefinesPolyG p p') :
    RefinesPolyG (cmapDeriv p) (Differential.mapCoeffs p') := by
  rw [RefinesPolyG] at hp ⊢
  rw [toPolyG_cmapDeriv, hp]

/-- `cmonomialDeriv` respects `RefinesPolyG`. -/
@[refines] theorem monomialDeriv {Dt : CPolyG α} {Dt' : (CFieldSpec.K α)[X]}
    (hDt : RefinesPolyG Dt Dt') (hp : RefinesPolyG p p') :
    RefinesPolyG (cmonomialDeriv Dt p) (Differential.implicitDeriv Dt' p') := by
  rw [RefinesPolyG] at hDt hp ⊢
  rw [toPolyG_cmonomialDeriv, hDt, hp]

end RefinesPolyG

section Examples

variable {α : Type*} [CField α] [CFieldSpec α]

example (a b c : CPolyG α) :
    RefinesPolyG (cmulG (caddG a b) c) ((toPolyG a + toPolyG b) * toPolyG c) := by
  transfer

example (a b c : CPolyG α) :
    toPolyG (cmulG (caddG a b) c) = (toPolyG a + toPolyG b) * toPolyG c := by
  transfer

end Examples

end DeepWiki.SymbolicIntegration
