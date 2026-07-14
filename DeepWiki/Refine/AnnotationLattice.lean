import DeepWiki.Refine.RelationStructure
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Lattice

/-! # Relation-annotation lattice

The six directional map levels form a finite diamond lattice, and bidirectional annotations carry
its componentwise product lattice. -/

namespace DeepWiki.Refine

/-- Least upper bound of two directional map-structure levels. -/
protected def MapLevel.join : MapLevel → MapLevel → MapLevel
  | .zero, b => b
  | a, .zero => a
  | .four, _ => .four
  | _, .four => .four
  | .one, b => b
  | a, .one => a
  | .twoA, .twoA => .twoA
  | .twoA, .twoB => .three
  | .twoA, .three => .three
  | .twoB, .twoA => .three
  | .twoB, .twoB => .twoB
  | .twoB, .three => .three
  | .three, _ => .three

/-- Greatest lower bound of two directional map-structure levels. -/
protected def MapLevel.meet : MapLevel → MapLevel → MapLevel
  | .zero, _ => .zero
  | _, .zero => .zero
  | .four, b => b
  | a, .four => a
  | .one, _ => .one
  | _, .one => .one
  | .twoA, .twoA => .twoA
  | .twoA, .twoB => .one
  | .twoA, .three => .twoA
  | .twoB, .twoA => .one
  | .twoB, .twoB => .twoB
  | .twoB, .three => .twoB
  | .three, b => b

/-- The six map levels form a bounded diamond lattice. -/
instance : Lattice MapLevel where
  sup := MapLevel.join
  le_sup_left a b := by
    cases a <;> cases b <;> decide
  le_sup_right a b := by
    cases a <;> cases b <;> decide
  sup_le a b c hac hbc := by
    change MapLevel.le a c at hac
    change MapLevel.le b c at hbc
    change MapLevel.le (MapLevel.join a b) c
    cases a <;> cases b <;> cases c <;> simp_all [MapLevel.join, MapLevel.le]
  inf := MapLevel.meet
  inf_le_left a b := by
    cases a <;> cases b <;> decide
  inf_le_right a b := by
    cases a <;> cases b <;> decide
  le_inf a b c hab hac := by
    change MapLevel.le a b at hab
    change MapLevel.le a c at hac
    change MapLevel.le a (MapLevel.meet b c)
    cases a <;> cases b <;> cases c <;> simp_all [MapLevel.meet, MapLevel.le]

/-- Level `0` is the least directional map-structure level. -/
instance : OrderBot MapLevel where
  bot := .zero
  bot_le a := by
    cases a <;> trivial

/-- Level `4` is the greatest directional map-structure level. -/
instance : OrderTop MapLevel where
  top := .four
  le_top a := by
    cases a <;> trivial

/-- Componentwise least upper bound of two relation annotations. -/
protected def Annotation.join (α β : Annotation) : Annotation :=
  ⟨α.forward ⊔ β.forward, α.backward ⊔ β.backward⟩

/-- Componentwise greatest lower bound of two relation annotations. -/
protected def Annotation.meet (α β : Annotation) : Annotation :=
  ⟨α.forward ⊓ β.forward, α.backward ⊓ β.backward⟩

/-- Relation annotations form the componentwise product lattice of map levels. -/
instance : Lattice Annotation where
  sup := Annotation.join
  le_sup_left _ _ := ⟨le_sup_left, le_sup_left⟩
  le_sup_right _ _ := ⟨le_sup_right, le_sup_right⟩
  sup_le _ _ _ hαγ hβγ :=
    ⟨sup_le hαγ.1 hβγ.1, sup_le hαγ.2 hβγ.2⟩
  inf := Annotation.meet
  inf_le_left _ _ := ⟨inf_le_left, inf_le_left⟩
  inf_le_right _ _ := ⟨inf_le_right, inf_le_right⟩
  le_inf _ _ _ hαβ hαγ :=
    ⟨le_inf hαβ.1 hαγ.1, le_inf hαβ.2 hαγ.2⟩

/-- The bare annotation is the least relation annotation. -/
instance : OrderBot Annotation where
  bot := ⟨⊥, ⊥⟩
  bot_le _ := ⟨bot_le, bot_le⟩

/-- The fully coherent annotation is the greatest relation annotation. -/
instance : OrderTop Annotation where
  top := ⟨⊤, ⊤⟩
  le_top _ := ⟨le_top, le_top⟩

/-- The fully coherent equivalence annotation is the top annotation. -/
@[simp] theorem Annotation.equivalence_eq_top :
    Annotation.equivalence = (⊤ : Annotation) :=
  rfl

/-- The bottom annotation carries no directional map structure. -/
@[simp] theorem Annotation.bot_eq :
    (⊥ : Annotation) = ⟨MapLevel.zero, MapLevel.zero⟩ :=
  rfl

/-- The two level-`2` branches join at level `3`. -/
@[simp] theorem MapLevel.twoA_sup_twoB : MapLevel.twoA ⊔ MapLevel.twoB = .three :=
  rfl

/-- The two level-`2` branches meet at level `1`. -/
@[simp] theorem MapLevel.twoA_inf_twoB : MapLevel.twoA ⊓ MapLevel.twoB = .one :=
  rfl

/-- The forward component of annotation join is map-level join. -/
@[simp] theorem Annotation.forward_sup (α β : Annotation) :
    (α ⊔ β).forward = α.forward ⊔ β.forward :=
  rfl

/-- The backward component of annotation join is map-level join. -/
@[simp] theorem Annotation.backward_sup (α β : Annotation) :
    (α ⊔ β).backward = α.backward ⊔ β.backward :=
  rfl

/-- The forward component of annotation meet is map-level meet. -/
@[simp] theorem Annotation.forward_inf (α β : Annotation) :
    (α ⊓ β).forward = α.forward ⊓ β.forward :=
  rfl

/-- The backward component of annotation meet is map-level meet. -/
@[simp] theorem Annotation.backward_inf (α β : Annotation) :
    (α ⊓ β).backward = α.backward ⊓ β.backward :=
  rfl

example : MapLevel.twoB ⊔ MapLevel.twoA = .three := rfl

example : MapLevel.twoB ⊓ MapLevel.twoA = .one := rfl

example (m : MapLevel) : (⊥ : MapLevel) ≤ m ∧ m ≤ (⊤ : MapLevel) :=
  ⟨bot_le, le_top⟩

example (α : Annotation) : (⊥ : Annotation) ≤ α ∧ α ≤ (⊤ : Annotation) :=
  ⟨bot_le, le_top⟩

example : decide (MapLevel.twoA ≤ MapLevel.twoB) = false := rfl

end DeepWiki.Refine
