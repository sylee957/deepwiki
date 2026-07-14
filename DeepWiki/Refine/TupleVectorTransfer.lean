import DeepWiki.Refine.IntegerModularRetraction
import Mathlib.Data.Vector.Basic

/-! # Iterated tuples and fixed-length vectors

Iterated products are equivalent to fixed-length list vectors. Elementwise relations lift through
constant vectors, heads, and append, and retractions lift through the representation equivalence. -/

namespace DeepWiki.Refine

universe u v w

/-- The length-indexed iterated product with the newest element in the right component. -/
def IteratedTuple (A : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => IteratedTuple A n × A

/-- The constant iterated tuple of a given length. -/
def tupleConst {A : Type u} (value : A) : (n : Nat) → IteratedTuple A n
  | 0 => PUnit.unit
  | n + 1 => (tupleConst value n, value)

/-- Read the newest component of a nonempty iterated tuple. -/
def tupleHead {A : Type u} {n : Nat} (tuple : IteratedTuple A (n + 1)) : A :=
  tuple.2

/-- Map a function componentwise over an iterated tuple. -/
def iteratedTupleMap {A : Type u} {B : Type v} (map : A → B) : {n : Nat} →
    IteratedTuple A n → IteratedTuple B n
  | 0, _ => PUnit.unit
  | _ + 1, tuple => (iteratedTupleMap map tuple.1, map tuple.2)

/-- Convert an iterated tuple to a vector, putting the newest component at the vector head. -/
def tupleToVector {A : Type u} : {n : Nat} → IteratedTuple A n → List.Vector A n
  | 0, _ => List.Vector.nil
  | _ + 1, tuple => List.Vector.cons tuple.2 (tupleToVector tuple.1)

/-- Convert a vector to the corresponding iterated tuple. -/
def vectorToTuple {A : Type u} : {n : Nat} → List.Vector A n → IteratedTuple A n
  | 0, _ => PUnit.unit
  | _ + 1, vector => (vectorToTuple vector.tail, vector.head)

/-- Append two iterated tuples in the order induced by vector concatenation. -/
def tupleAppend {A : Type u} {n₁ n₂ : Nat}
    (left : IteratedTuple A n₁) (right : IteratedTuple A n₂) :
    IteratedTuple A (n₁ + n₂) :=
  vectorToTuple (tupleToVector left ++ tupleToVector right)

/-- Converting an iterated tuple to a vector and back is the identity. -/
@[simp] theorem vectorToTuple_tupleToVector {A : Type u} {n : Nat}
    (tuple : IteratedTuple A n) : vectorToTuple (tupleToVector tuple) = tuple := by
  induction n with
  | zero =>
      cases tuple
      rfl
  | succ n induction =>
      rcases tuple with ⟨tail, head⟩
      change (vectorToTuple (tupleToVector tail), head) = (tail, head)
      rw [induction]

/-- Converting a vector to an iterated tuple and back is the identity. -/
@[simp] theorem tupleToVector_vectorToTuple {A : Type u} {n : Nat}
    (vector : List.Vector A n) : tupleToVector (vectorToTuple vector) = vector := by
  induction n with
  | zero =>
      exact vector.eq_nil.symm
  | succ n induction =>
      change List.Vector.cons vector.head (tupleToVector (vectorToTuple vector.tail)) = vector
      have tailIdentity : tupleToVector (vectorToTuple vector.tail) = vector.tail := by
        simpa only [Nat.add_one_sub_one] using induction vector.tail
      rw [tailIdentity]
      exact vector.cons_head_tail

/-- Iterated tuples and fixed-length vectors are equivalent representations. -/
def iteratedTupleVectorEquiv (A : Type u) (n : Nat) :
    IteratedTuple A n ≃ List.Vector A n where
  toFun := tupleToVector
  invFun := vectorToTuple
  left_inv := vectorToTuple_tupleToVector
  right_inv := tupleToVector_vectorToTuple

/-- Mapping a right inverse componentwise yields a right inverse on iterated tuples. -/
theorem iteratedTupleMap_rightInverse {A : Type u} {B : Type v}
    (forward : A → B) (backward : B → A)
    (rightInverse : Function.RightInverse backward forward) :
    ∀ {n : Nat}, Function.RightInverse
      (@iteratedTupleMap B A backward n) (@iteratedTupleMap A B forward n)
  | 0, PUnit.unit => rfl
  | _ + 1, ⟨tail, head⟩ => by
      change
        (iteratedTupleMap forward (iteratedTupleMap backward tail),
          forward (backward head)) = (tail, head)
      rw [iteratedTupleMap_rightInverse forward backward rightInverse tail,
        rightInverse head]

/-- Map an iterated tuple componentwise and expose it as a vector. -/
def tupleVectorMap {A : Type u} {B : Type v} (map : A → B) {n : Nat}
    (tuple : IteratedTuple A n) : List.Vector B n :=
  tupleToVector (iteratedTupleMap map tuple)

/-- Read a vector as an iterated tuple and map its components. -/
def vectorTupleMap {A : Type u} {B : Type v} (map : A → B) {n : Nat}
    (vector : List.Vector A n) : IteratedTuple B n :=
  iteratedTupleMap map (vectorToTuple vector)

/-- A component right inverse lifts through the vector-to-tuple representation map. -/
theorem vectorTupleMap_rightInverse {A : Type u} {B : Type v}
    (forward : A → B) (backward : B → A)
    (rightInverse : Function.RightInverse backward forward) (n : Nat) :
    Function.RightInverse (@tupleVectorMap B A backward n)
      (@vectorTupleMap A B forward n) := by
  intro tuple
  unfold tupleVectorMap vectorTupleMap
  rw [vectorToTuple_tupleToVector]
  exact iteratedTupleMap_rightInverse forward backward rightInverse tuple

/-- A component retraction induces a retraction from vectors to iterated tuples. -/
def mappedVectorTupleRetraction {A : Type u} {B : Type v}
    (forward : A → B) (backward : B → A)
    (rightInverse : Function.RightInverse backward forward) (n : Nat) :
    StructuredRelation.{u, v, 0} Annotation.retraction
      (List.Vector A n) (IteratedTuple B n) :=
  rightInverseStructuredRelation
    (@vectorTupleMap A B forward n)
    (@tupleVectorMap B A backward n)
    (vectorTupleMap_rightInverse forward backward rightInverse n)

/-- The equality graph of the tuple-to-vector equivalence. -/
abbrev TupleVectorGraph (A : Type u) (n : Nat) :
    IteratedTuple A n → List.Vector A n → Type :=
  EqualityGraph (@tupleToVector A n)

/-- The tuple-to-vector equality graph carries full equivalence structure. -/
def iteratedTupleVectorStructuredRelation (A : Type u) (n : Nat) :
    StructuredRelation.{u, u, 0} Annotation.equivalence
      (IteratedTuple A n) (List.Vector A n) :=
  let relation := FunctionalEquivalence.ofEquiv.{u, u, 0} (iteratedTupleVectorEquiv A n)
  ⟨relation.rel, .four relation.forward.toIsUmap, .four relation.backward.toIsUmap⟩

/-- The structured representation relation exposes the tuple-to-vector equality graph. -/
@[simp] theorem iteratedTupleVectorStructuredRelation_rel (A : Type u) (n : Nat) :
    (iteratedTupleVectorStructuredRelation A n).rel = TupleVectorGraph A n :=
  rfl

/-- Lift an element relation recursively to pairs of lists. -/
def ProofRelevantListRel {A : Type u} {B : Type v} (R : A → B → Type w) :
    List A → List B → Type w
  | [], [] => PUnit
  | left :: lefts, right :: rights => R left right × ProofRelevantListRel R lefts rights
  | [], _ :: _ => PEmpty
  | _ :: _, [] => PEmpty

/-- Lift an element relation between an iterated tuple and a vector in representation order. -/
abbrev TupleVectorRel {A : Type u} {B : Type v} (R : A → B → Type w)
    {n : Nat} (tuple : IteratedTuple A n) (vector : List.Vector B n) : Type w :=
  ProofRelevantListRel R (tupleToVector tuple).toList vector.toList

/-- Tuple-to-vector conversion commutes with append. -/
theorem tupleToVector_append {A : Type u} {n₁ n₂ : Nat}
    (left : IteratedTuple A n₁) (right : IteratedTuple A n₂) :
    tupleToVector (tupleAppend left right) = tupleToVector left ++ tupleToVector right := by
  unfold tupleAppend
  rw [tupleToVector_vectorToTuple]

/-- Tuple-to-vector conversion sends constant tuples to replicated vectors. -/
theorem tupleToVector_const {A : Type u} (value : A) (n : Nat) :
    tupleToVector (tupleConst value n) = List.Vector.replicate n value := by
  induction n with
  | zero => rfl
  | succ n induction =>
      rw [List.Vector.replicate_succ]
      change List.Vector.cons value (tupleToVector (tupleConst value n)) =
        List.Vector.cons value (List.Vector.replicate n value)
      rw [induction]

/-- Appending proof-relevantly related lists preserves their relation. -/
def ProofRelevantListRel.append {A : Type u} {B : Type v} {R : A → B → Type w}
    {left₁ : List A} {right₁ : List B} {left₂ : List A} {right₂ : List B}
    (related₁ : ProofRelevantListRel R left₁ right₁)
    (related₂ : ProofRelevantListRel R left₂ right₂) :
    ProofRelevantListRel R (left₁ ++ left₂) (right₁ ++ right₂) := by
  induction left₁ generalizing right₁ with
  | nil =>
      cases right₁ with
      | nil => exact related₂
      | cons _ _ => exact nomatch related₁
  | cons left lefts induction =>
      cases right₁ with
      | nil => exact nomatch related₁
      | cons right rights =>
          exact ⟨related₁.1, induction related₁.2⟩

/-- Related elements generate related constant tuples and vectors. -/
def tupleVectorConst_related {A : Type u} {B : Type v} {R : A → B → Type w}
    {left : A} {right : B} (related : R left right) (n : Nat) :
    TupleVectorRel R (tupleConst left n) (List.Vector.replicate n right) := by
  unfold TupleVectorRel
  rw [tupleToVector_const]
  induction n with
  | zero => exact PUnit.unit
  | succ n induction =>
      exact ⟨related, induction⟩

/-- The heads of related nonempty tuples and vectors are related. -/
def tupleVectorHead_related {A : Type u} {B : Type v} {R : A → B → Type w}
    {n : Nat} {tuple : IteratedTuple A (n + 1)} {vector : List.Vector B (n + 1)}
    (related : TupleVectorRel R tuple vector) : R (tupleHead tuple) vector.head := by
  rw [← vector.cons_head_tail] at related
  exact related.1

/-- Appending related tuples and vectors preserves their lifted relation. -/
def tupleVectorAppend_related {A : Type u} {B : Type v} {R : A → B → Type w}
    {n₁ n₂ : Nat} {left₁ : IteratedTuple A n₁} {right₁ : List.Vector B n₁}
    {left₂ : IteratedTuple A n₂} {right₂ : List.Vector B n₂}
    (related₁ : TupleVectorRel R left₁ right₁)
    (related₂ : TupleVectorRel R left₂ right₂) :
    TupleVectorRel R (tupleAppend left₁ left₂) (right₁ ++ right₂) := by
  unfold TupleVectorRel at related₁ related₂ ⊢
  rw [tupleToVector_append]
  simpa only [List.Vector.toList_append] using related₁.append related₂

/-- The head of a replicated nonempty vector is its repeated value. -/
theorem vectorHead_replicate {A : Type u} (value : A) (n : Nat) :
    (List.Vector.replicate (n + 1) value).head = value := by
  rw [List.Vector.replicate_succ]
  rfl

/-- The head of a constant nonempty iterated tuple is its repeated value. -/
theorem tupleHead_const {A : Type u} (value : A) (n : Nat) :
    tupleHead (tupleConst value (n + 1)) = value :=
  rfl

/-- Appending two constant tuples gives the constant tuple of the summed length. -/
theorem tupleAppend_const {A : Type u} (value : A) (n₁ n₂ : Nat) :
    tupleAppend (tupleConst value n₁) (tupleConst value n₂) =
      tupleConst value (n₁ + n₂) := by
  apply (iteratedTupleVectorEquiv A (n₁ + n₂)).injective
  change tupleToVector (tupleAppend (tupleConst value n₁) (tupleConst value n₂)) =
    tupleToVector (tupleConst value (n₁ + n₂))
  rw [tupleToVector_append, tupleToVector_const, tupleToVector_const,
    tupleToVector_const]
  apply List.Vector.eq
  change List.replicate n₁ value ++ List.replicate n₂ value =
    List.replicate (n₁ + n₂) value
  exact List.replicate_append_replicate

/-- Relate a modular value to an integer representative that reduces to it. -/
abbrev ModularIntegerRelation (modulus : Nat) : ZMod modulus → ℤ → Type :=
  fun modular integer => IntZModRelation modulus integer modular

/-- Every modular value is related to its canonical integer representative. -/
def modularIntegerRepresentative_related (modulus : Nat) (value : ZMod modulus) :
    ModularIntegerRelation modulus value (intZModRepresentative value) :=
  ⟨⟨intZModRepresentative_rightInverse modulus value⟩⟩

/-- Integer-vector reduction to modular tuples is a lifted retraction. -/
def integerVectorModularTupleRetraction (modulus n : Nat) :
    StructuredRelation.{0, 0, 0} Annotation.retraction
      (List.Vector ℤ n) (IteratedTuple (ZMod modulus) n) :=
  mappedVectorTupleRetraction
    (fun value : ℤ ↦ (value : ZMod modulus))
    intZModRepresentative
    (intZModRepresentative_rightInverse modulus)
    n

/-- The lifted integer-vector retraction uses reduction after vector-to-tuple conversion. -/
@[simp] theorem integerVectorModularTupleRetraction_rel (modulus n : Nat) :
    (integerVectorModularTupleRetraction modulus n).rel =
      EqualityGraph (@vectorTupleMap ℤ (ZMod modulus)
        (fun value : ℤ ↦ (value : ZMod modulus)) n) :=
  rfl

/-- The modular constant-tuple head law follows through its related integer-vector instance. -/
theorem modularTuple_head_const_viaInteger (modulus n : Nat) (value : ZMod modulus) :
    tupleHead (tupleConst value (n + 1)) = value := by
  let representative : ℤ := intZModRepresentative value
  have representativeRelated : ModularIntegerRelation modulus value representative :=
    modularIntegerRepresentative_related modulus value
  have constantsRelated :
      TupleVectorRel (ModularIntegerRelation modulus)
        (tupleConst value (n + 1)) (List.Vector.replicate (n + 1) representative) :=
    tupleVectorConst_related representativeRelated (n + 1)
  have headsRelated := tupleVectorHead_related constantsRelated
  have integerHead : (List.Vector.replicate (n + 1) representative).head = representative :=
    vectorHead_replicate representative n
  exact headsRelated.down.down.symm |>.trans
    ((congrArg (fun integer : ℤ ↦ (integer : ZMod modulus)) integerHead).trans
      representativeRelated.down.down)

example (A : Type u) (n : Nat) : IteratedTuple A n ≃ List.Vector A n :=
  iteratedTupleVectorEquiv A n

example (A : Type u) (n : Nat) :
    StructuredRelation.{u, u, 0} Annotation.equivalence
      (IteratedTuple A n) (List.Vector A n) :=
  iteratedTupleVectorStructuredRelation A n

example {A : Type u} {B : Type v} {R : A → B → Type w}
    {left : A} {right : B} (related : R left right) (n : Nat) :
    TupleVectorRel R (tupleConst left n) (List.Vector.replicate n right) :=
  tupleVectorConst_related related n

example {A : Type u} {B : Type v} {R : A → B → Type w}
    {n : Nat} {tuple : IteratedTuple A (n + 1)} {vector : List.Vector B (n + 1)}
    (related : TupleVectorRel R tuple vector) : R (tupleHead tuple) vector.head :=
  tupleVectorHead_related related

example {A : Type u} {B : Type v} {R : A → B → Type w}
    {n₁ n₂ : Nat} {left₁ : IteratedTuple A n₁} {right₁ : List.Vector B n₁}
    {left₂ : IteratedTuple A n₂} {right₂ : List.Vector B n₂}
    (related₁ : TupleVectorRel R left₁ right₁)
    (related₂ : TupleVectorRel R left₂ right₂) :
    TupleVectorRel R (tupleAppend left₁ left₂) (right₁ ++ right₂) :=
  tupleVectorAppend_related related₁ related₂

example (modulus n : Nat) :
    StructuredRelation.{0, 0, 0} Annotation.retraction
      (List.Vector ℤ n) (IteratedTuple (ZMod modulus) n) :=
  integerVectorModularTupleRetraction modulus n

example {A : Type u} (value : A) (n : Nat) :
    (List.Vector.replicate (n + 1) value).head = value :=
  vectorHead_replicate value n

example (n : Nat) (integer : ℤ) :
    (List.Vector.replicate (n + 1) integer).head = integer :=
  vectorHead_replicate integer n

example (modulus n : Nat) (value : ZMod modulus) :
    tupleHead (tupleConst value (n + 1)) = value :=
  modularTuple_head_const_viaInteger modulus n value

end DeepWiki.Refine
