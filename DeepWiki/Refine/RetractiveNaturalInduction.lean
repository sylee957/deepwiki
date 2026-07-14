import DeepWiki.Refine.BinaryNaturals
import DeepWiki.Refine.FunctionalRelation

/-! # Natural induction from a retractive representation

A carrier that retracts onto unary naturals and whose zero and successor commute with the
retraction inherits the dependent natural-number eliminator. The representation graph exposes
exactly the weakened directional structure used by the transfer. -/

namespace DeepWiki.Refine

universe u v w

/-- Relate a represented natural to a unary natural when encoding the unary value recovers it. -/
abbrev RetractiveNatRel {I : Type u} (ofNat : Nat → I) : I → Nat → Type w :=
  Converse (EqualityGraph ofNat)

/-- A retractive encoding gives its converse graph forward level `2a` and backward level `3`. -/
def retractiveNatRelationClass {I : Type u} (toNat : I → Nat) (ofNat : Nat → I)
    (leftInverse : Function.LeftInverse ofNat toNat) :
    RelationClass ⟨MapLevel.twoA, MapLevel.three⟩ (RetractiveNatRel.{u, w} ofNat) :=
  ⟨.twoA
      { map := toNat
        graphToRel := fun value n equal =>
          ⟨⟨by simpa only [← equal] using leftInverse value⟩⟩ },
    .three (equalityGraphIsUmap ofNat).toMapClass3⟩

/-- Package a retractive natural-number graph at annotation `(2a,3)`. -/
def retractiveNatStructuredRelation {I : Type u} (toNat : I → Nat) (ofNat : Nat → I)
    (leftInverse : Function.LeftInverse ofNat toNat) :
    StructuredRelation.{u, 0, w} ⟨MapLevel.twoA, MapLevel.three⟩ I Nat :=
  ⟨RetractiveNatRel ofNat, retractiveNatRelationClass toNat ofNat leftInverse⟩

/-- The retractive structured relation projects definitionally to the converse encoding graph. -/
@[simp] theorem retractiveNatStructuredRelation_rel {I : Type u}
    (toNat : I → Nat) (ofNat : Nat → I)
    (leftInverse : Function.LeftInverse ofNat toNat) :
    (retractiveNatStructuredRelation.{u, w} toNat ofNat leftInverse).rel =
      RetractiveNatRel ofNat :=
  rfl

/-- Compatible zeros are related by the retractive natural-number graph. -/
def retractiveNatZeroRelated {I : Type u} (zero : I) (ofNat : Nat → I)
    (mapZero : ofNat 0 = zero) : RetractiveNatRel.{u, w} ofNat zero 0 :=
  ⟨⟨mapZero⟩⟩

/-- Compatible successors preserve the retractive natural-number graph. -/
def retractiveNatSuccRelated {I : Type u} (succ : I → I) (ofNat : Nat → I)
    (mapSucc : ∀ n, ofNat (Nat.succ n) = succ (ofNat n))
    {value : I} {n : Nat} (related : RetractiveNatRel.{u, w} ofNat value n) :
    RetractiveNatRel.{u, w} ofNat (succ value) (Nat.succ n) :=
  ⟨⟨(mapSucc n).trans (congrArg succ related.down.down)⟩⟩

/-- A retractive natural-number representation inherits dependent elimination from `Nat`. -/
def retractiveNatEliminator {I : Type u} (zero : I) (succ : I → I)
    (toNat : I → Nat) (ofNat : Nat → I)
    (leftInverse : Function.LeftInverse ofNat toNat)
    (mapZero : ofNat 0 = zero)
    (mapSucc : ∀ n, ofNat (Nat.succ n) = succ (ofNat n)) :
    (NatSignature.mk I zero succ).Eliminator.{u, v} := by
  intro P base step value
  have encoded : P (ofNat (toNat value)) := by
    induction toNat value with
    | zero => simpa only [mapZero] using base
    | succ n ih =>
        simpa only [mapSucc] using step (ofNat n) ih
  simpa only [leftInverse value] using encoded

example {I : Type u} (toNat : I → Nat) (ofNat : Nat → I)
    (leftInverse : Function.LeftInverse ofNat toNat) :
    StructuredRelation.{u, 0, w} ⟨MapLevel.twoA, MapLevel.three⟩ I Nat :=
  retractiveNatStructuredRelation toNat ofNat leftInverse

example {I : Type u} (zero : I) (succ : I → I) (toNat : I → Nat) (ofNat : Nat → I)
    (leftInverse : Function.LeftInverse ofNat toNat)
    (mapZero : ofNat 0 = zero)
    (mapSucc : ∀ n, ofNat (Nat.succ n) = succ (ofNat n)) :
    (NatSignature.mk I zero succ).Eliminator.{u, v} :=
  retractiveNatEliminator zero succ toNat ofNat leftInverse mapZero mapSucc

end DeepWiki.Refine
