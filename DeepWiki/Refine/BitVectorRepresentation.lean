import DeepWiki.Refine.FunctionalRelation
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Vector.Basic

/-! # Fixed-width bit-vector representations

Bounded naturals use direct bitwise reads and writes and are equivalent to little-endian Boolean
vectors. Their indexed operations commute with the representation relation. -/

namespace DeepWiki.Refine

universe u

/-- Naturals bounded by `2 ^ width`, represented by the finite type `Fin (2 ^ width)`. -/
abbrev BoundedNat (width : Nat) := Fin (2 ^ width)

/-- A fixed-width list vector of Boolean bits. -/
abbrev BitVector (width : Nat) := List.Vector Bool width

/-- Bounded naturals and little-endian Boolean vectors of the same width are equivalent. -/
def boundedNatBitVectorEquiv (width : Nat) : BoundedNat width ≃ BitVector width where
  toFun number := List.Vector.ofFn fun index => number.val.testBit index.val
  invFun vector := ⟨Nat.ofBits vector.get, Nat.ofBits_lt_two_pow vector.get⟩
  left_inv number := by
    apply Fin.ext
    change Nat.ofBits
      (List.Vector.ofFn fun index : Fin width => number.val.testBit index.val).get = number.val
    have getOfFn :
        (List.Vector.ofFn fun index : Fin width => number.val.testBit index.val).get =
          fun index : Fin width => number.val.testBit index.val := by
      funext index
      simp
    rw [getOfFn, Nat.ofBits_testBit, Nat.mod_eq_of_lt number.isLt]
  right_inv vector := by
    apply List.Vector.ext
    intro index
    simp

/-- The representation map reads each vector coordinate as the corresponding natural-number bit. -/
@[simp] theorem boundedNatBitVectorEquiv_get {width : Nat} (number : BoundedNat width)
    (index : Fin width) :
    (boundedNatBitVectorEquiv width number).get index = number.val.testBit index.val := by
  simp [boundedNatBitVectorEquiv]

/-- The proof-relevant equality relation used for values translated to themselves. -/
abbrev ProofRelevantEq {A : Type u} (left right : A) : Type u :=
  EqualityGraph.{u, u, u} (fun value : A => value) left right

/-- Reflexivity in the proof-relevant equality relation. -/
def proofRelevantEqRefl {A : Type u} (value : A) : ProofRelevantEq value value :=
  ⟨⟨rfl⟩⟩

/-- Equality of widths induces an equivalence between the corresponding Boolean-vector types. -/
def bitVectorCongrEquiv {width width' : Nat} (widthEq : width = width') :
    BitVector width ≃ BitVector width' := by
  cases widthEq
  exact Equiv.refl _

/-- Related widths induce an equivalence from bounded naturals to Boolean vectors. -/
def boundedNatBitVectorEquivOfRel {width width' : Nat}
    (widthRel : ProofRelevantEq width width') : BoundedNat width ≃ BitVector width' :=
  (boundedNatBitVectorEquiv width).trans (bitVectorCongrEquiv widthRel.down.down)

/-- Relate a bounded natural to a possibly transported Boolean vector through the representation map. -/
abbrev BoundedNatBitVectorRel {width width' : Nat}
    (widthRel : ProofRelevantEq width width')
    (number : BoundedNat width) (vector : BitVector width') : Type :=
  EqualityGraph (boundedNatBitVectorEquivOfRel widthRel) number vector

/-- Read an in-range bit of a Boolean vector and return `false` outside the vector. -/
def bitVectorGet {width : Nat} (vector : BitVector width) (index : Nat) : Bool :=
  if inRange : index < width then vector.get ⟨index, inRange⟩ else false

/-- Replace an in-range bit of a Boolean vector and leave the vector unchanged outside its range. -/
def bitVectorSet {width : Nat} (vector : BitVector width) (index : Nat) (bit : Bool) :
    BitVector width :=
  if inRange : index < width then vector.set ⟨index, inRange⟩ bit else vector

/-- `natSetBitTo number index bit` changes exactly bit `index` of `number` to `bit`. -/
def natSetBitTo (number index : Nat) (bit : Bool) : Nat :=
  if number.testBit index = bit then number else number ^^^ 2 ^ index

/-- Reading `query` after `natSetBitTo` returns the replacement exactly at `index`. -/
theorem natSetBitTo_testBit (number index query : Nat) (bit : Bool) :
    (natSetBitTo number index bit).testBit query =
      if index = query then bit else number.testBit query := by
  unfold natSetBitTo
  by_cases same : index = query
  · subst query
    cases currentBit : number.testBit index <;> cases bit <;>
      simp [currentBit, Nat.testBit_xor]
  · by_cases current : number.testBit index = bit
    · rw [if_pos current, if_neg same]
    · rw [if_neg current, Nat.testBit_xor, Nat.testBit_two_pow]
      simp [same]

/-- Replacing an in-range bit preserves a bound by the corresponding power of two. -/
theorem natSetBitTo_lt_two_pow {number index width : Nat} {bit : Bool}
    (numberBound : number < 2 ^ width) (indexBound : index < width) :
    natSetBitTo number index bit < 2 ^ width := by
  unfold natSetBitTo
  split
  · exact numberBound
  · exact Nat.xor_lt_two_pow numberBound
      (Nat.pow_lt_pow_of_lt (by decide) indexBound)

/-- Read a bounded-natural bit directly, returning `false` outside its width. -/
def boundedNatGet {width : Nat} (number : BoundedNat width) (index : Nat) : Bool :=
  if index < width then number.val.testBit index else false

/-- Replace an in-range bounded-natural bit directly by conditional bitwise XOR. -/
def boundedNatSet {width : Nat} (number : BoundedNat width) (index : Nat) (bit : Bool) :
    BoundedNat width :=
  if inRange : index < width then
    ⟨natSetBitTo number.val index bit, natSetBitTo_lt_two_pow number.isLt inRange⟩
  else
    number

/-- Direct bounded-natural reads commute with the little-endian vector representation. -/
theorem boundedNatBitVector_get_commutes {width : Nat} (number : BoundedNat width)
    (index : Nat) :
    boundedNatGet number index =
      bitVectorGet (boundedNatBitVectorEquiv width number) index := by
  by_cases inRange : index < width
  · simp [boundedNatGet, bitVectorGet, boundedNatBitVectorEquiv, inRange]
  · simp [boundedNatGet, bitVectorGet, inRange]

/-- Direct bounded-natural writes commute with the little-endian vector representation. -/
theorem boundedNatBitVector_set_commutes {width : Nat} (number : BoundedNat width)
    (index : Nat) (bit : Bool) :
    boundedNatBitVectorEquiv width (boundedNatSet number index bit) =
      bitVectorSet (boundedNatBitVectorEquiv width number) index bit := by
  by_cases inRange : index < width
  · apply List.Vector.ext
    intro query
    by_cases same : query.val = index
    · have queryEq : query = (⟨index, inRange⟩ : Fin width) := Fin.ext same
      subst query
      simp [boundedNatSet, bitVectorSet, boundedNatBitVectorEquiv, inRange,
        natSetBitTo_testBit]
    · have queryNe : (⟨index, inRange⟩ : Fin width) ≠ query := by
        intro equal
        exact same (congrArg Fin.val equal).symm
      rw [boundedNatBitVectorEquiv_get]
      simp only [boundedNatSet, bitVectorSet, dif_pos inRange]
      change (natSetBitTo number.val index bit).testBit query.val =
        ((boundedNatBitVectorEquiv width number).set ⟨index, inRange⟩ bit).get query
      rw [natSetBitTo_testBit, List.Vector.get_set_of_ne queryNe]
      simp [boundedNatBitVectorEquiv, Ne.symm same]
  · simp [boundedNatSet, bitVectorSet, inRange]

/-- The witness that vector reads respect representation and equality of indices. -/
def boundedNatBitVector_get_rel {width width' : Nat}
    (widthRel : ProofRelevantEq width width')
    (number : BoundedNat width) (vector : BitVector width')
    (representationRel : BoundedNatBitVectorRel widthRel number vector)
    (index index' : Nat) (indexRel : ProofRelevantEq index index') :
    ProofRelevantEq (boundedNatGet number index) (bitVectorGet vector index') := by
  rcases widthRel with ⟨⟨rfl⟩⟩
  rcases indexRel with ⟨⟨rfl⟩⟩
  rcases representationRel with ⟨⟨rfl⟩⟩
  exact ⟨⟨boundedNatBitVector_get_commutes number index⟩⟩

/-- The witness that vector writes respect representation and equality of inputs. -/
def boundedNatBitVector_set_rel {width width' : Nat}
    (widthRel : ProofRelevantEq width width')
    (number : BoundedNat width) (vector : BitVector width')
    (representationRel : BoundedNatBitVectorRel widthRel number vector)
    (index index' : Nat) (indexRel : ProofRelevantEq index index')
    (bit bit' : Bool) (bitRel : ProofRelevantEq bit bit') :
    BoundedNatBitVectorRel widthRel
      (boundedNatSet number index bit) (bitVectorSet vector index' bit') := by
  rcases widthRel with ⟨⟨rfl⟩⟩
  rcases indexRel with ⟨⟨rfl⟩⟩
  rcases bitRel with ⟨⟨rfl⟩⟩
  rcases representationRel with ⟨⟨rfl⟩⟩
  exact ⟨⟨boundedNatBitVector_set_commutes number index bit⟩⟩

/-- Reading an in-range vector bit immediately after writing it returns the written bit. -/
theorem bitVector_get_set_same {width : Nat} (vector : BitVector width)
    (index : Nat) (bit : Bool) (inRange : index < width) :
    bitVectorGet (bitVectorSet vector index bit) index = bit := by
  simp [bitVectorGet, bitVectorSet, inRange]

/-- Direct bounded-natural bit update satisfies get-after-set independently of vectors. -/
theorem boundedNat_get_set_same {width : Nat} (number : BoundedNat width)
    (index : Nat) (bit : Bool) (inRange : index < width) :
    boundedNatGet (boundedNatSet number index bit) index = bit := by
  simp [boundedNatGet, boundedNatSet, inRange, natSetBitTo_testBit]

/-- The bounded-natural get-after-set law transports back to Boolean vectors. -/
theorem bitVector_get_set_same_of_boundedNat {width : Nat} (vector : BitVector width)
    (index : Nat) (bit : Bool) (inRange : index < width) :
    bitVectorGet (bitVectorSet vector index bit) index = bit := by
  let number := (boundedNatBitVectorEquiv width).symm vector
  calc
    bitVectorGet (bitVectorSet vector index bit) index =
        bitVectorGet
          (bitVectorSet (boundedNatBitVectorEquiv width number) index bit) index := by
      simp [number]
    _ = bitVectorGet
        (boundedNatBitVectorEquiv width (boundedNatSet number index bit)) index := by
      rw [boundedNatBitVector_set_commutes]
    _ = boundedNatGet (boundedNatSet number index bit) index :=
      (boundedNatBitVector_get_commutes _ _).symm
    _ = bit := boundedNat_get_set_same number index bit inRange

/-- The related-width representation equivalence induces a top-level structured relation. -/
def boundedNatBitVectorStructuredRelation {width width' : Nat}
    (widthRel : ProofRelevantEq width width') :
    StructuredRelation Annotation.equivalence (BoundedNat width) (BitVector width') :=
  let relation := FunctionalEquivalence.ofEquiv (boundedNatBitVectorEquivOfRel widthRel)
  ⟨relation.rel, .four relation.forward.toIsUmap, .four relation.backward.toIsUmap⟩

/-- The structured relation exposes the bounded-natural-to-vector representation relation. -/
@[simp] theorem boundedNatBitVectorStructuredRelation_rel {width width' : Nat}
    (widthRel : ProofRelevantEq width width') :
    (boundedNatBitVectorStructuredRelation widthRel).rel = BoundedNatBitVectorRel widthRel :=
  rfl

example (width : Nat) : BoundedNat width ≃ BitVector width :=
  boundedNatBitVectorEquiv width

example {width width' : Nat} (widthRel : ProofRelevantEq width width') :
    StructuredRelation Annotation.equivalence (BoundedNat width) (BitVector width') :=
  boundedNatBitVectorStructuredRelation widthRel

example {width width' : Nat} (widthRel : ProofRelevantEq width width')
    (number : BoundedNat width) (vector : BitVector width')
    (representationRel : BoundedNatBitVectorRel widthRel number vector)
    (index index' : Nat) (indexRel : ProofRelevantEq index index') :
    ProofRelevantEq (boundedNatGet number index) (bitVectorGet vector index') :=
  boundedNatBitVector_get_rel widthRel number vector representationRel index index' indexRel

example {width width' : Nat} (widthRel : ProofRelevantEq width width')
    (number : BoundedNat width) (vector : BitVector width')
    (representationRel : BoundedNatBitVectorRel widthRel number vector)
    (index index' : Nat) (indexRel : ProofRelevantEq index index')
    (bit bit' : Bool) (bitRel : ProofRelevantEq bit bit') :
    BoundedNatBitVectorRel widthRel
      (boundedNatSet number index bit) (bitVectorSet vector index' bit') :=
  boundedNatBitVector_set_rel widthRel number vector representationRel index index' indexRel
    bit bit' bitRel

example {width : Nat} (number : BoundedNat width) (index : Nat) (bit : Bool) :
    index < width → boundedNatGet (boundedNatSet number index bit) index = bit :=
  boundedNat_get_set_same number index bit

example {width : Nat} (vector : BitVector width) (index : Nat) (bit : Bool) :
    index < width → bitVectorGet (bitVectorSet vector index bit) index = bit :=
  bitVector_get_set_same_of_boundedNat vector index bit

end DeepWiki.Refine
