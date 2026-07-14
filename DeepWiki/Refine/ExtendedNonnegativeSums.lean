import DeepWiki.Refine.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Extended-domain transfer for nonnegative sums

Summable sequences of finite nonnegative reals embed into arbitrary sequences of extended
nonnegative reals.  Pointwise addition and infinite summation commute with this embedding, so the
unconditional additivity theorem in the extended domain transfers back to summable sequences. -/

namespace DeepWiki.Refine

open scoped ENNReal NNReal

/-- A sequence of nonnegative real numbers together with a proof that it is summable. -/
def SummableNNSequence := {u : Nat → ℝ≥0 // Summable u}

/-- An arbitrary sequence of extended nonnegative real numbers. -/
abbrev ExtendedNNSequence := Nat → ℝ≥0∞

namespace SummableNNSequence

/-- Pointwise addition of summable nonnegative sequences. -/
def add (u v : SummableNNSequence) : SummableNNSequence :=
  ⟨fun n ↦ u.1 n + v.1 n, u.2.add v.2⟩

/-- Summable nonnegative sequences inherit pointwise addition. -/
instance : Add SummableNNSequence := ⟨add⟩

/-- Pointwise evaluation of addition of summable nonnegative sequences. -/
@[simp] theorem add_apply (u v : SummableNNSequence) (n : Nat) :
    (u + v).1 n = u.1 n + v.1 n :=
  rfl

/-- The finite-valued infinite sum of a summable nonnegative sequence. -/
noncomputable def sum (u : SummableNNSequence) : ℝ≥0 :=
  ∑' n, u.1 n

/-- Embed a summable nonnegative sequence pointwise into the extended nonnegative reals. -/
def extend (u : SummableNNSequence) : ExtendedNNSequence :=
  fun n ↦ (u.1 n : ℝ≥0∞)

/-- Pointwise evaluation of the extended-domain embedding. -/
@[simp] theorem extend_apply (u : SummableNNSequence) (n : Nat) :
    u.extend n = (u.1 n : ℝ≥0∞) :=
  rfl

/-- Extending pointwise addition agrees with pointwise addition after extension. -/
theorem extend_add (u v : SummableNNSequence) :
    (u + v).extend = u.extend + v.extend := by
  funext n
  simp [ENNReal.coe_add]

end SummableNNSequence

/-- The infinite sum of an extended nonnegative sequence, including the value `∞`. -/
noncomputable def extendedNNSum (u : ExtendedNNSequence) : ℝ≥0∞ :=
  ∑' n, u n

/-- Finite values refine extended values when the latter is the canonical embedding of the former. -/
def FiniteENNRealRel : ℝ≥0 → ℝ≥0∞ → Prop :=
  DenoteRel fun x : ℝ≥0 ↦ (x : ℝ≥0∞)

/-- Summable finite sequences refine extended sequences through the pointwise embedding. -/
def SummableNNSequenceRel : SummableNNSequence → ExtendedNNSequence → Prop :=
  DenoteRel SummableNNSequence.extend

/-- The finite-value relation is equality with the canonical extended value. -/
theorem finiteENNRealRel_iff (x : ℝ≥0) (y : ℝ≥0∞) :
    FiniteENNRealRel x y ↔ (x : ℝ≥0∞) = y :=
  Iff.rfl

/-- The sequence relation is pointwise equality after the canonical embedding. -/
theorem summableNNSequenceRel_iff (u : SummableNNSequence) (v : ExtendedNNSequence) :
    SummableNNSequenceRel u v ↔ ∀ n, (u.1 n : ℝ≥0∞) = v n := by
  constructor
  · intro h n
    exact congrFun h n
  · intro h
    funext n
    exact h n

/-- Every summable sequence refines its own extended-domain embedding. -/
theorem refines_summableNNSequence_extend (u : SummableNNSequence) :
    Refines SummableNNSequenceRel u u.extend :=
  ⟨rfl⟩

/-- Pointwise addition respects the relation between summable and extended sequences. -/
theorem refines_summableNNSequence_add :
    Refines
      (SummableNNSequenceRel ⟹ SummableNNSequenceRel ⟹ SummableNNSequenceRel)
      (fun u v : SummableNNSequence ↦ u + v)
      (fun u v : ExtendedNNSequence ↦ u + v) :=
  ⟨by
    intro u u' hu v v' hv
    change (u + v).extend = u' + v'
    rw [SummableNNSequence.extend_add, hu, hv]⟩

/-- Infinite summation respects the relation between summable and extended sequences. -/
theorem refines_summableNNSequence_sum :
    Refines
      (SummableNNSequenceRel ⟹ FiniteENNRealRel)
      SummableNNSequence.sum
      extendedNNSum :=
  ⟨by
    intro u u' hu
    change (SummableNNSequence.sum u : ℝ≥0∞) = extendedNNSum u'
    rw [← hu]
    exact ENNReal.coe_tsum u.2⟩

/-- Infinite sums of extended nonnegative sequences are unconditionally additive. -/
theorem extendedNNSum_add (u v : ExtendedNNSequence) :
    extendedNNSum (u + v) = extendedNNSum u + extendedNNSum v :=
  ENNReal.tsum_add

/-- The sum of two summable nonnegative sequences is the sum of their sums. -/
theorem summableNNSequence_sum_add (u v : SummableNNSequence) :
    SummableNNSequence.sum (u + v) =
      SummableNNSequence.sum u + SummableNNSequence.sum v := by
  have hu := Refines.app refines_summableNNSequence_sum
    (refines_summableNNSequence_extend u)
  have hv := Refines.app refines_summableNNSequence_sum
    (refines_summableNNSequence_extend v)
  have huv := Refines.app refines_summableNNSequence_sum
    (Refines.app
      (Refines.app refines_summableNNSequence_add
        (refines_summableNNSequence_extend u))
      (refines_summableNNSequence_extend v))
  apply ENNReal.coe_injective
  calc
    (SummableNNSequence.sum (u + v) : ℝ≥0∞) =
        extendedNNSum (u.extend + v.extend) := huv.prf
    _ = extendedNNSum u.extend + extendedNNSum v.extend := extendedNNSum_add _ _
    _ = (SummableNNSequence.sum u : ℝ≥0∞) +
        (SummableNNSequence.sum v : ℝ≥0∞) :=
      congrArg₂ (fun x y ↦ x + y) hu.prf.symm hv.prf.symm
    _ = (SummableNNSequence.sum u + SummableNNSequence.sum v : ℝ≥0) := by
      rw [ENNReal.coe_add]

example (u v : SummableNNSequence) :
    SummableNNSequence.sum (u + v) =
      SummableNNSequence.sum u + SummableNNSequence.sum v :=
  summableNNSequence_sum_add u v

end DeepWiki.Refine
