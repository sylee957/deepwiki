import DeepWiki.Refine.ExtendedNonnegativeSums
import DeepWiki.Refine.FunctionalRelation

/-! # Nested refinement for summable sequences

Finite nonnegative values embed into extended nonnegative values, while sequences whose extended
sum is finite embed into arbitrary extended-valued sequences.  The two graph relations carry
explicit directional map structure and transport additivity of infinite sums through both layers.
-/

namespace DeepWiki.Refine

open scoped ENNReal NNReal

noncomputable section

/-- Nonnegative sequences whose extended-valued infinite sum is finite. -/
def FiniteSumNNSequence :=
  {u : Nat → ℝ≥0 // extendedNNSum (fun n ↦ (u n : ℝ≥0∞)) ≠ ∞}

namespace FiniteSumNNSequence

/-- Read a finite-sum sequence as a Mathlib-summable nonnegative sequence. -/
def toSummable (u : FiniteSumNNSequence) : SummableNNSequence :=
  ⟨u.1, ENNReal.tsum_coe_ne_top_iff_summable.mp u.2⟩

/-- Build a finite-sum sequence from a Mathlib-summable nonnegative sequence. -/
def ofSummable (u : SummableNNSequence) : FiniteSumNNSequence :=
  ⟨u.1, ENNReal.tsum_coe_ne_top_iff_summable.mpr u.2⟩

/-- The finiteness and Mathlib summability presentations of nonnegative sequences are equivalent. -/
def equivSummableNNSequence : FiniteSumNNSequence ≃ SummableNNSequence where
  toFun := toSummable
  invFun := ofSummable
  left_inv u := by
    apply Subtype.ext
    rfl
  right_inv u := by
    apply Subtype.ext
    rfl

/-- Pointwise addition preserves finiteness of the extended-valued infinite sum. -/
def add (u v : FiniteSumNNSequence) : FiniteSumNNSequence :=
  ⟨fun n ↦ u.1 n + v.1 n,
    ENNReal.tsum_coe_ne_top_iff_summable.mpr
      ((ENNReal.tsum_coe_ne_top_iff_summable.mp u.2).add
        (ENNReal.tsum_coe_ne_top_iff_summable.mp v.2))⟩

/-- Finite-sum nonnegative sequences inherit pointwise addition. -/
instance : Add FiniteSumNNSequence := ⟨add⟩

/-- Pointwise evaluation of addition of finite-sum sequences. -/
@[simp] theorem add_apply (u v : FiniteSumNNSequence) (n : Nat) :
    (u + v).1 n = u.1 n + v.1 n :=
  rfl

/-- The constantly zero sequence has finite extended-valued sum. -/
def zero : FiniteSumNNSequence :=
  ⟨fun _ ↦ 0, by simp [extendedNNSum]⟩

/-- Embed a finite-sum sequence pointwise into extended nonnegative values. -/
def extend (u : FiniteSumNNSequence) : ExtendedNNSequence :=
  fun n ↦ (u.1 n : ℝ≥0∞)

/-- Pointwise evaluation of the sequence embedding. -/
@[simp] theorem extend_apply (u : FiniteSumNNSequence) (n : Nat) :
    u.extend n = (u.1 n : ℝ≥0∞) :=
  rfl

/-- Extending pointwise addition agrees with pointwise addition after extension. -/
theorem extend_add (u v : FiniteSumNNSequence) :
    (u + v).extend = u.extend + v.extend := by
  funext n
  simp [ENNReal.coe_add]

/-- Sum a finite-sum sequence by truncating its extended-valued infinite sum. -/
noncomputable def sum (u : FiniteSumNNSequence) : ℝ≥0 :=
  (extendedNNSum u.extend).toNNReal

/-- Embedding the truncated sum recovers the finite extended-valued sum. -/
theorem coe_sum (u : FiniteSumNNSequence) :
    (u.sum : ℝ≥0∞) = extendedNNSum u.extend := by
  exact ENNReal.coe_toNNReal u.2

end FiniteSumNNSequence

/-- Truncate an arbitrary extended sequence, defaulting to zero when the result is not summable. -/
noncomputable def truncateExtendedNNSequence
    (v : ExtendedNNSequence) : FiniteSumNNSequence :=
  if h : extendedNNSum (fun n ↦ (v n).toNNReal) ≠ ∞ then
    ⟨fun n ↦ (v n).toNNReal, h⟩
  else
    FiniteSumNNSequence.zero

/-- Truncating the pointwise extension of a finite-sum sequence recovers that sequence. -/
theorem truncateExtendedNNSequence_extend (u : FiniteSumNNSequence) :
    truncateExtendedNNSequence u.extend = u := by
  have hfinite : extendedNNSum (fun n ↦ (u.extend n).toNNReal) ≠ ∞ := by
    simpa using u.2
  unfold truncateExtendedNNSequence
  rw [dif_pos hfinite]
  apply Subtype.ext
  funext n
  exact ENNReal.toNNReal_coe (u.1 n)

/-- The proof-relevant equality graph of the finite-value embedding. -/
abbrev FiniteENNRealGraph (x : ℝ≥0) (y : ℝ≥0∞) : Type :=
  EqualityGraph (fun r : ℝ≥0 ↦ (r : ℝ≥0∞)) x y

/-- Finite values and extended values carry a coherent `(4, 2b)` relation class. -/
def finiteENNRealGraphClass :
    RelationClass Annotation.section FiniteENNRealGraph :=
  ⟨.four (equalityGraphIsUmap (fun r : ℝ≥0 ↦ (r : ℝ≥0∞))),
    .twoB
      { map := ENNReal.toNNReal
        relToGraph := fun y x related ↦ by
          rw [← related.down.down]
          exact ENNReal.toNNReal_coe x }⟩

/-- The `(4, 2b)` structured relation from finite to extended nonnegative values. -/
def finiteENNRealStructuredRelation :
    StructuredRelation Annotation.section ℝ≥0 ℝ≥0∞ :=
  ⟨FiniteENNRealGraph, finiteENNRealGraphClass⟩

/-- The proof-relevant equality graph of pointwise sequence extension. -/
abbrev FiniteSumNNSequenceGraph
    (u : FiniteSumNNSequence) (v : ExtendedNNSequence) : Type :=
  EqualityGraph FiniteSumNNSequence.extend u v

/-- Finite-sum and arbitrary extended sequences carry a coherent `(4, 2b)` relation class. -/
noncomputable def finiteSumNNSequenceGraphClass :
    RelationClass Annotation.section FiniteSumNNSequenceGraph :=
  ⟨.four (equalityGraphIsUmap FiniteSumNNSequence.extend),
    .twoB
      { map := truncateExtendedNNSequence
        relToGraph := fun v u related ↦ by
          rw [← related.down.down]
          exact truncateExtendedNNSequence_extend u }⟩

/-- The `(4, 2b)` structured graph relation used for finite-sum sequence transfer. -/
noncomputable def finiteSumNNSequenceStructuredRelation :
    StructuredRelation Annotation.section FiniteSumNNSequence ExtendedNNSequence :=
  ⟨FiniteSumNNSequenceGraph, finiteSumNNSequenceGraphClass⟩

/-- The sequence graph weakened to its coherent forward-map structure. -/
noncomputable def finiteSumNNSequenceForwardRelation :
    StructuredRelation Annotation.univalentMap FiniteSumNNSequence ExtendedNNSequence :=
  StructuredRelation.weaken
    (low := Annotation.univalentMap) (high := Annotation.section)
    (by constructor <;> decide) finiteSumNNSequenceStructuredRelation

/-- Addition preserves the proof-relevant finite-to-extended value relation. -/
def finiteENNRealGraph_add
    (x₁ x₂ : ℝ≥0) (y₁ y₂ : ℝ≥0∞)
    (h₁ : FiniteENNRealGraph x₁ y₁) (h₂ : FiniteENNRealGraph x₂ y₂) :
    FiniteENNRealGraph (x₁ + x₂) (y₁ + y₂) := by
  refine ⟨⟨?_⟩⟩
  change ((x₁ + x₂ : ℝ≥0) : ℝ≥0∞) = y₁ + y₂
  calc
    ((x₁ + x₂ : ℝ≥0) : ℝ≥0∞) =
        (x₁ : ℝ≥0∞) + (x₂ : ℝ≥0∞) := by rw [ENNReal.coe_add]
    _ = y₁ + y₂ :=
      congrArg₂ (fun a b : ℝ≥0∞ ↦ a + b) h₁.down.down h₂.down.down

/-- Pointwise addition preserves the proof-relevant sequence-extension relation. -/
def finiteSumNNSequenceGraph_add
    (u₁ u₂ : FiniteSumNNSequence) (v₁ v₂ : ExtendedNNSequence)
    (h₁ : FiniteSumNNSequenceGraph u₁ v₁)
    (h₂ : FiniteSumNNSequenceGraph u₂ v₂) :
    FiniteSumNNSequenceGraph (u₁ + u₂) (v₁ + v₂) := by
  refine ⟨⟨?_⟩⟩
  rw [FiniteSumNNSequence.extend_add, h₁.down.down, h₂.down.down]

/-- Infinite summation maps related finite-sum and extended sequences to related values. -/
def finiteSumNNSequenceGraph_sum
    (u : FiniteSumNNSequence) (v : ExtendedNNSequence)
    (h : FiniteSumNNSequenceGraph u v) :
    FiniteENNRealGraph u.sum (extendedNNSum v) := by
  refine ⟨⟨?_⟩⟩
  rw [← h.down.down]
  exact FiniteSumNNSequence.coe_sum u

/-- Infinite sums of arbitrary extended nonnegative sequences commute with pointwise addition. -/
theorem extendedNNSequenceSum_add (u v : ExtendedNNSequence) :
    extendedNNSum (u + v) = extendedNNSum u + extendedNNSum v :=
  extendedNNSum_add u v

/-- Truncated sums of finite-sum nonnegative sequences commute with pointwise addition. -/
theorem FiniteSumNNSequence.sum_add (u v : FiniteSumNNSequence) :
    (u + v).sum = u.sum + v.sum := by
  let ue := u.extend
  let ve := v.extend
  have hu : FiniteSumNNSequenceGraph u ue := ⟨⟨rfl⟩⟩
  have hv : FiniteSumNNSequenceGraph v ve := ⟨⟨rfl⟩⟩
  have huv : FiniteSumNNSequenceGraph (u + v) (ue + ve) :=
    finiteSumNNSequenceGraph_add u v ue ve hu hv
  have hsumuv : FiniteENNRealGraph (u + v).sum (extendedNNSum (ue + ve)) :=
    finiteSumNNSequenceGraph_sum (u + v) (ue + ve) huv
  have hsumu : FiniteENNRealGraph u.sum (extendedNNSum ue) :=
    finiteSumNNSequenceGraph_sum u ue hu
  have hsumv : FiniteENNRealGraph v.sum (extendedNNSum ve) :=
    finiteSumNNSequenceGraph_sum v ve hv
  have hsumadd :
      FiniteENNRealGraph (u.sum + v.sum) (extendedNNSum ue + extendedNNSum ve) :=
    finiteENNRealGraph_add u.sum v.sum (extendedNNSum ue) (extendedNNSum ve) hsumu hsumv
  apply ENNReal.coe_injective
  exact hsumuv.down.down.trans
    ((extendedNNSequenceSum_add ue ve).trans hsumadd.down.down.symm)

example (u v : ExtendedNNSequence) :
    extendedNNSum (u + v) = extendedNNSum u + extendedNNSum v :=
  extendedNNSequenceSum_add u v

example (u v : FiniteSumNNSequence) :
    (u + v).sum = u.sum + v.sum :=
  FiniteSumNNSequence.sum_add u v

example :
    StructuredRelation Annotation.section ℝ≥0 ℝ≥0∞ :=
  finiteENNRealStructuredRelation

example :
    StructuredRelation Annotation.univalentMap FiniteSumNNSequence ExtendedNNSequence :=
  finiteSumNNSequenceForwardRelation

end

end DeepWiki.Refine
