import DeepWiki.Refine.ArrowRelationStructure
import DeepWiki.Refine.FunctionalRelation
import Mathlib.Data.ZMod.Basic

/-! # Integer reduction as a modular retraction

The quotient map from integers to `ZMod modulus` has a canonical right inverse.  Its equality
graph therefore carries the `(4, 2a)` structure of a retraction, and integer multiplication and
equality modulo the modulus respect that relation. -/

set_option linter.defProp false

namespace DeepWiki.Refine

universe u v w

/-- Relate an integer to the modular value obtained by casting it. -/
abbrev IntZModRelation (modulus : Nat) : ℤ → ZMod modulus → Type :=
  EqualityGraph (fun value : ℤ ↦ (value : ZMod modulus))

/-- The canonical integer representative of a modular value. -/
def intZModRepresentative {modulus : Nat} (value : ZMod modulus) : ℤ :=
  ZMod.cast value

/-- Casting a canonical integer representative recovers the modular value. -/
@[simp] theorem intZModRepresentative_rightInverse (modulus : Nat) :
    Function.RightInverse (@intZModRepresentative modulus)
      (fun value : ℤ ↦ (value : ZMod modulus)) :=
  ZMod.intCast_rightInverse

/-- Integer reduction modulo `modulus` is a structured retraction for every modulus. -/
def intZModRetraction (modulus : Nat) :
    StructuredRelation.{0, 0, 0} Annotation.retraction ℤ (ZMod modulus) :=
  rightInverseStructuredRelation
    (fun value : ℤ ↦ (value : ZMod modulus))
    intZModRepresentative
    (intZModRepresentative_rightInverse modulus)

/-- The integer-to-modular retraction uses the canonical casting relation. -/
@[simp] theorem intZModRetraction_rel (modulus : Nat) :
    (intZModRetraction modulus).rel = IntZModRelation modulus :=
  rfl

/-- Integer zero and modular zero are related by reduction. -/
def intZModZero_related (modulus : Nat) :
    IntZModRelation modulus 0 0 :=
  ⟨⟨Int.cast_zero⟩⟩

/-- Integer and modular multiplication form a respectful binary operation. -/
def intZModMul_related (modulus : Nat) :
    ArrowRelation (IntZModRelation modulus)
      (ArrowRelation (IntZModRelation modulus) (IntZModRelation modulus))
      ((· * ·) : ℤ → ℤ → ℤ)
      ((· * ·) : ZMod modulus → ZMod modulus → ZMod modulus) := by
  rintro m x ⟨⟨hm⟩⟩ n y ⟨⟨hn⟩⟩
  refine ⟨⟨?_⟩⟩
  simpa only [Int.cast_mul] using congrArg₂ (fun a b : ZMod modulus ↦ a * b) hm hn

/-- Equality of related modular values implies equality modulo the modulus of the integers. -/
def intZModEq_related (modulus : Nat) :
    ∀ (m : ℤ) (x : ZMod modulus), IntZModRelation modulus m x →
      ∀ (n : ℤ) (y : ZMod modulus), IntZModRelation modulus n y →
        x = y → (m : ZMod modulus) = (n : ZMod modulus) := by
  rintro m x ⟨⟨hm⟩⟩ n y ⟨⟨hn⟩⟩ hxy
  exact hm.trans (hxy.trans hn.symm)

/-- A universal zero-product implication in `ZMod modulus` transfers to modular equality on `ℤ`. -/
theorem intReductionModZMod (modulus : Nat)
    (hypothesis : ∀ m n p : ZMod modulus, m = n * p → m = 0) :
    ∀ m n p : ℤ, m = n * p → (m : ZMod modulus) = 0 := by
  intro m n p hmnp
  let mMod : ZMod modulus := m
  let nMod : ZMod modulus := n
  let pMod : ZMod modulus := p
  have hm : IntZModRelation modulus m mMod := ⟨⟨rfl⟩⟩
  have hn : IntZModRelation modulus n nMod := ⟨⟨rfl⟩⟩
  have hp : IntZModRelation modulus p pMod := ⟨⟨rfl⟩⟩
  have hzero := intZModZero_related modulus
  have hmul := intZModMul_related modulus n nMod hn p pMod hp
  have hmodProduct : mMod = nMod * pMod := by
    exact (congrArg (fun value : ℤ ↦ (value : ZMod modulus)) hmnp).trans hmul.down.down
  have hmodZero : mMod = 0 := hypothesis mMod nMod pMod hmodProduct
  simpa only [Int.cast_zero] using
    intZModEq_related modulus m mMod hm 0 0 hzero hmodZero

example {A : Type u} {B : Type v} (forward : A → B) (backward : B → A)
    (rightInverse : Function.RightInverse backward forward) :
    StructuredRelation.{u, v, w} Annotation.retraction A B :=
  rightInverseStructuredRelation forward backward rightInverse

example (modulus : Nat) :
    StructuredRelation.{0, 0, 0} Annotation.retraction ℤ (ZMod modulus) :=
  intZModRetraction modulus

example (modulus : Nat) :
    Function.RightInverse (@intZModRepresentative modulus)
      (fun value : ℤ ↦ (value : ZMod modulus)) :=
  intZModRepresentative_rightInverse modulus

example (modulus : Nat) : IntZModRelation modulus 0 0 :=
  intZModZero_related modulus

example (modulus : Nat) :
    ∀ (m : ℤ) (x : ZMod modulus), IntZModRelation modulus m x →
      ∀ (n : ℤ) (y : ZMod modulus), IntZModRelation modulus n y →
        IntZModRelation modulus (m * n) (x * y) :=
  intZModMul_related modulus

example (modulus : Nat) :
    ∀ (m : ℤ) (x : ZMod modulus), IntZModRelation modulus m x →
      ∀ (n : ℤ) (y : ZMod modulus), IntZModRelation modulus n y →
        x = y → (m : ZMod modulus) = (n : ZMod modulus) :=
  intZModEq_related modulus

example (modulus : Nat)
    (hypothesis : ∀ m n p : ZMod modulus, m = n * p → m = 0) :
    ∀ m n p : ℤ, m = n * p → (m : ZMod modulus) = 0 :=
  intReductionModZMod modulus hypothesis

end DeepWiki.Refine
