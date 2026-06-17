import Mathlib.Logic.Relation
import Mathlib.Data.Finite.Defs

/-! # Labelled transition systems
The operational model underlying CCS: a set of states (processes), a set of
actions (labels), and a transition relation for each action. The general theory
of this topic is developed over a loose transition relation
`step : Proc → Act → Proc → Prop`; `LTS` bundles one as the book's triple. -/

namespace DeepWiki.ReactiveSystems

/-- A labelled transition system: the book's triple
`(Proc, Act, {→ᵃ | a ∈ Act})`, here a transition relation `step p a q`
(read `p —a→ q`) over states `Proc` and labels `Act`. -/
structure LTS (Proc Act : Type*) where
  /-- The labelled transition relation: `step p a q` means `p —a→ q`. -/
  step : Proc → Act → Proc → Prop

/-- `L ⊢ p ⟶[a] q`: the transition `p —a→ q` in the LTS `L` (the book's
`p →ᵃ q`). -/
scoped notation:40 L:max " ⊢ " p:41 " ⟶[" a "] " q:41 => LTS.step L p a q

namespace LTS

variable {Proc Act : Type*}

/-- `L.Refuses p a` (the book's `p ↛ᵃ`): no `a`-labelled transition leaves `p`. -/
def Refuses (L : LTS Proc Act) (p : Proc) (a : Act) : Prop := ∀ q, ¬ L.step p a q

/-- `L.Refuses p a` unfolds to `∀ q, ¬ L.step p a q`: no `a`-transition leaves `p`. -/
@[simp] theorem refuses_iff (L : LTS Proc Act) (p : Proc) (a : Act) :
    L.Refuses p a ↔ ∀ q, ¬ L.step p a q := Iff.rfl

/-- One step under *some* label: `p` moves to `q` via at least one action. -/
def stepSome (L : LTS Proc Act) (p q : Proc) : Prop := ∃ a, L.step p a q

/-- `L.Reachable p q`: `q` is reachable from `p` by finitely many transitions. -/
def Reachable (L : LTS Proc Act) : Proc → Proc → Prop := Relation.ReflTransGen L.stepSome

/-- A state is reachable from itself. -/
@[refl] theorem reachable_refl (L : LTS Proc Act) (p : Proc) : L.Reachable p p :=
  Relation.ReflTransGen.refl

/-- A single transition makes the target reachable. -/
theorem reachable_single (L : LTS Proc Act) {p q : Proc} {a : Act} (h : L.step p a q) :
    L.Reachable p q := Relation.ReflTransGen.single ⟨a, h⟩

/-- Reachability is transitive. -/
theorem reachable_trans (L : LTS Proc Act) {p q r : Proc}
    (hpq : L.Reachable p q) (hqr : L.Reachable q r) : L.Reachable p r :=
  Relation.ReflTransGen.trans hpq hqr

/-- Extend a reachability by one more transition. -/
theorem reachable_tail (L : LTS Proc Act) {p q r : Proc} {a : Act}
    (hpq : L.Reachable p q) (h : L.step q a r) : L.Reachable p r :=
  Relation.ReflTransGen.tail hpq ⟨a, h⟩

/-- A labelled transition system is finite when both its state set and its
action set are finite. -/
def IsFinite (_L : LTS Proc Act) : Prop := Finite Proc ∧ Finite Act

/-- The LTS built from a `Bool`-valued edge relation: `p —a→ q` iff `e p a q`.
Reducible so finite example LTSs built with it keep decidable step facts. -/
@[reducible] def ofBool (e : Proc → Act → Proc → Bool) : LTS Proc Act :=
  ⟨fun p a q => e p a q = true⟩

/-- `(ofBool e).step p a q ↔ e p a q = true`: the step relation of a `Bool`-edge LTS. -/
@[simp] theorem ofBool_step (e : Proc → Act → Proc → Bool) (p : Proc) (a : Act) (q : Proc) :
    (ofBool e).step p a q ↔ e p a q = true := Iff.rfl

end LTS

end DeepWiki.ReactiveSystems
