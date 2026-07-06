import DeepWiki.SymbolicIntegration.Computable.MonomialDeriv
import DeepWiki.SymbolicIntegration.Computable.DenoteHom

/-! # Refinement relation for generic computable polynomials

`RefinesPolyG p q` relates a computable coefficient list to its semantic polynomial reading.
Operations transfer through the CoqEAL-style parametricity classes `DenoteHom₁`/`DenoteHom₂`
(defined in `Computable.DenoteHom`): most instances are *generated* from the `@[denote]` square by
`derive_denote_hom`, so the generic respect lemmas `hom₁`/`hom₂` — and hence the `transfer` tactic —
handle each operation for free, with no per-operation respect lemma to hand-write.
-/

open Polynomial
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-- `p` refines `q` when `p`'s denotation is `q`. -/
def RefinesPolyG {α : Type*} [CField α] [CFieldSpec α]
    (p : CPolyG α) (q : (CFieldSpec.K α)[X]) : Prop :=
  toPolyG p = q

/-- Prove refinement and denotation-equality goals by transfer: `simp [denote]` for goals with an
explicit abstract side, else aesop over the `Refines` respect-rule set to *synthesize* the abstract
polynomial (metavariable RHS) by recursion on the computable expression down to atoms. -/
macro "transfer" : tactic =>
  `(tactic| first
      | (simp_all [RefinesPolyG, denote]; done)
      | (aesop (rule_sets := [Refines]) (config := { enableSimp := false })))

-- No-parameter operations: the `DenoteHom` instances are GENERATED from their denotation squares.
derive_denote_hom toPolyG_caddG
derive_denote_hom toPolyG_csubG
derive_denote_hom toPolyG_cmulG
derive_denote_hom toPolyG_cnegG
derive_denote_hom toPolyG_cderivG
derive_denote_hom toPolyG_cmapDeriv
derive_denote_hom toPolyG_cmonomialDeriv

section Instances

variable {α : Type*} [CField α] [CFieldSpec α]

-- Parameterized operations (extra scalar/exponent argument): kept as explicit instances.
/-- `cscaleG c` denotes scaling by `C (toK c)`. -/
instance (c : α) : DenoteHom₁ (cscaleG c) (fun p => Polynomial.C (CFieldSpec.toK c) * p) :=
  ⟨fun p => toPolyG_cscaleG c p⟩
/-- `cshiftG k` denotes multiplication by `X ^ k`. -/
instance (k : ℕ) : DenoteHom₁ (fun p : CPolyG α => cshiftG k p) (fun p => X ^ k * p) :=
  ⟨fun p => toPolyG_cshiftG k p⟩
/-- `cpowG · n` denotes `· ^ n`. -/
instance (n : ℕ) : DenoteHom₁ (fun p : CPolyG α => cpowG p n) (fun p => p ^ n) :=
  ⟨fun p => toPolyG_cpowG p n⟩

end Instances

namespace RefinesPolyG

variable {α : Type*} [CField α] [CFieldSpec α]
variable {p q : CPolyG α} {p' q' : (CFieldSpec.K α)[X]}

/-- Introduce `RefinesPolyG` from a denotation equality. -/
theorem intro (h : toPolyG p = p') : RefinesPolyG p p' := h

/-- Eliminate `RefinesPolyG` to its denotation equality. -/
theorem denote_eq (h : RefinesPolyG p p') : toPolyG p = p' := h

/-- Any registered unary operation respects `RefinesPolyG` (dispatches on the `DenoteHom₁` instance). -/
@[refines] theorem hom₁ {cop : CPolyG α → CPolyG α} {op} [DenoteHom₁ cop op]
    (h : RefinesPolyG p p') : RefinesPolyG (cop p) (op p') := by
  rw [RefinesPolyG] at h ⊢; rw [DenoteHom₁.square, h]

/-- Any registered binary operation respects `RefinesPolyG` (dispatches on the `DenoteHom₂` instance). -/
@[refines] theorem hom₂ {cop : CPolyG α → CPolyG α → CPolyG α} {op} [DenoteHom₂ cop op]
    (hp : RefinesPolyG p p') (hq : RefinesPolyG q q') : RefinesPolyG (cop p q) (op p' q') := by
  rw [RefinesPolyG] at hp hq ⊢; rw [DenoteHom₂.square, hp, hq]

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
  sub_eq_zero.mp (eq_zero_of_cisZero (hom₂ (cop := csubG) hp hq) hz)

/-- A false executable zero test on `p - q` reflects semantic inequality of refined polynomials. -/
theorem ne_of_csub_cisZero_false (hp : RefinesPolyG p p') (hq : RefinesPolyG q q')
    (hz : cisZeroG (csubG p q) = false) : p' ≠ q' := fun h =>
  ne_zero_of_cisZero_false (hom₂ hp hq) hz (sub_eq_zero.mpr h)

/-- The empty list refines the zero polynomial. -/
@[refines] theorem nil : RefinesPolyG ([] : CPolyG α) 0 := by simp [RefinesPolyG]

/-- A singleton list refines the corresponding constant polynomial. -/
@[refines] theorem const (c : α) :
    RefinesPolyG ([c] : CPolyG α) (Polynomial.C (CFieldSpec.toK c)) := by simp [RefinesPolyG]

/-- `[CField.zero]` refines the zero polynomial. -/
@[refines] theorem zero : RefinesPolyG ([CField.zero] : CPolyG α) 0 := by simp [RefinesPolyG, denote]

/-- `[CField.one]` refines the one polynomial. -/
@[refines] theorem one : RefinesPolyG ([CField.one] : CPolyG α) 1 := by simp [RefinesPolyG, denote]

/-- `cnormG` refines the original denotation. -/
@[refines] theorem norm : RefinesPolyG (cnormG p) (toPolyG p) := by rw [RefinesPolyG, toPolyG_cnormG]

/-- `cnormG` respects an existing `RefinesPolyG` proof. -/
@[refines] theorem norm_of (hp : RefinesPolyG p p') : RefinesPolyG (cnormG p) p' := by
  rw [RefinesPolyG] at hp ⊢; rw [toPolyG_cnormG, hp]

end RefinesPolyG

/-- Every computable polynomial refines its own denotation. -/
theorem refinesPolyG_self {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) :
    RefinesPolyG p (toPolyG p) := rfl

-- The generic respect rules `hom₁`/`hom₂` fire first (low penalty), dispatching on the registered
-- `DenoteHom₁`/`DenoteHom₂` instance to choose the abstract operation and decompose; the nullary and
-- extra-argument atoms close directly; `refinesPolyG_self` is the terminal atom-closer (high penalty).
attribute [aesop safe 1 apply (rule_sets := [Refines])]
  RefinesPolyG.hom₁ RefinesPolyG.hom₂
  RefinesPolyG.nil RefinesPolyG.const RefinesPolyG.zero RefinesPolyG.one
  RefinesPolyG.norm_of
attribute [aesop safe 99 apply (rule_sets := [Refines])] refinesPolyG_self

section Examples

variable {α : Type*} [CField α] [CFieldSpec α]

example (a b c : CPolyG α) :
    RefinesPolyG (cmulG (caddG a b) c) ((toPolyG a + toPolyG b) * toPolyG c) := by
  transfer

/-- `transfer` synthesizes the abstract polynomial from the computable structure (metavariable RHS),
which `simp [denote]` cannot drive — aesop applies the `hom₁`/`hom₂` rules, each dispatching on its
`DenoteHom` instance, down to atoms. -/
example (a b c : CPolyG α) : ∃ q, RefinesPolyG (cmulG (caddG a b) c) q := by
  transfer

-- The extra-argument ops (`cscaleG`/`cshiftG`/`cpowG`) also synthesize through their
-- parameterized `DenoteHom₁` instances — aesop's higher-order unification recovers `cop`.
example (a : CPolyG α) (c : α) : ∃ q, RefinesPolyG (cscaleG c (cpowG a 3)) q := by
  transfer

example (a b c : CPolyG α) :
    toPolyG (cmulG (caddG a b) c) = (toPolyG a + toPolyG b) * toPolyG c := by
  transfer

example :
    toPolyG (caddG ([1] : CPolyG ℚ) [0, 1]) =
      toPolyG (caddG ([0, 1] : CPolyG ℚ) [1]) := by
  refine RefinesPolyG.eq_of_csub_cisZero (refinesPolyG_self _) (refinesPolyG_self _) ?_
  native_decide

example :
    toPolyG (cmulG ([1, 1] : CPolyG ℚ) [1, -1]) =
      toPolyG (csubG ([1] : CPolyG ℚ) [0, 0, 1]) := by
  refine RefinesPolyG.eq_of_csub_cisZero (refinesPolyG_self _) (refinesPolyG_self _) ?_
  native_decide

example :
    toPolyG (cmulG ([1, 1] : CPolyG ℚ) [1, -1]) ≠
      toPolyG ([1, 0, 1] : CPolyG ℚ) := by
  refine RefinesPolyG.ne_of_csub_cisZero_false (refinesPolyG_self _) (refinesPolyG_self _) ?_
  native_decide

end Examples

end DeepWiki.SymbolicIntegration
