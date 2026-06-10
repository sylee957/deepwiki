import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Order.WithTop
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Algebra.Order.Ring.WithTop

/-!
# `R̄max` analysis via the `EReal` identity cast

The book's extended real line `R̄max = WithBot (WithTop ℝ)` is *the same nesting*
as `EReal = WithBot (WithTop ℝ)` — defeq as a type — and its dioid product
(numeric `+`) is the *bot-absorbing* addition `(−∞)+(+∞) = −∞`, which is the
**same `Add` instance** as `EReal`'s. So the cast `toEReal` is the identity, the
orders coincide, and `toEReal_add` holds *unconditionally* (no collision
discrepancy, unlike the top-absorbing `R̄min`).

The cast still does work for *analysis*: `EReal`'s topology lives on the `def`
`EReal`, not on the bare synonym `WithBot (WithTop ℝ)`. We give the carrier
`EReal`'s topology by defeq (`scoped`, so it never leaks), making the identity an
honest homeomorphism, and transport `EReal.continuousAt_add`. `EReal` addition is
genuinely discontinuous at the collision pairs `(⊤,⊥)`, `(⊥,⊤)`, so the
continuity statement still carries an `AddDefinedExtMax` hypothesis excluding
them — even though *value* agreement is unconditional.
-/

namespace DeepWiki

open Topology Filter Set
open scoped Classical

namespace MaxPlusExt

/-- `EReal`'s topology, reused on the bare carrier `WithBot (WithTop ℝ)` by defeq,
behind `scoped` so it never leaks globally onto the Mathlib synonym. Bring it
into scope with `open scoped DeepWiki.MaxPlusExt`. -/
noncomputable scoped instance instTopologicalSpaceCarrier :
    TopologicalSpace (WithBot (WithTop ℝ)) :=
  (inferInstance : TopologicalSpace EReal)

/-- The carrier carries `EReal`'s order topology (scoped, see above). -/
scoped instance instOrderTopologyCarrier :
    OrderTopology (WithBot (WithTop ℝ)) :=
  (inferInstance : OrderTopology EReal)

open scoped MaxPlusExt

/-! ### The value cast `WithBot (WithTop ℝ) ↔ EReal` (defeq identity) -/

/-- Value cast `WithBot (WithTop ℝ) → EReal`: the identity (the carrier is
defeq to `EReal`). -/
def toEReal : WithBot (WithTop ℝ) → EReal := id

/-- `toEReal ⊤ = ⊤`. -/
@[simp] theorem toEReal_top : toEReal ⊤ = ⊤ := rfl
/-- `toEReal ⊥ = ⊥`. -/
@[simp] theorem toEReal_bot : toEReal ⊥ = ⊥ := rfl
/-- `toEReal` sends the carrier coercion of a real `r` to `(r : EReal)`. -/
@[simp] theorem toEReal_coe (r : ℝ) :
    toEReal (((r : WithTop ℝ) : WithBot (WithTop ℝ))) = (r : EReal) := rfl

/-- Inverse value cast `EReal → WithBot (WithTop ℝ)`: the identity. -/
def ofEReal : EReal → WithBot (WithTop ℝ) := id

/-- `ofEReal ⊤ = ⊤`. -/
@[simp] theorem ofEReal_top : ofEReal ⊤ = ⊤ := rfl
/-- `ofEReal ⊥ = ⊥`. -/
@[simp] theorem ofEReal_bot : ofEReal ⊥ = ⊥ := rfl
/-- `ofEReal` sends `(r : EReal)` to the carrier coercion of the real `r`. -/
@[simp] theorem ofEReal_coe (r : ℝ) :
    ofEReal ((r : EReal)) = (((r : WithTop ℝ) : WithBot (WithTop ℝ))) := rfl

/-- `ofEReal` is a left inverse of `toEReal`. -/
theorem ofEReal_toEReal (a : WithBot (WithTop ℝ)) : ofEReal (toEReal a) = a := rfl

/-- `ofEReal` is a right inverse of `toEReal`. -/
theorem toEReal_ofEReal (x : EReal) : toEReal (ofEReal x) = x := rfl

/-- `toEReal` is strictly monotone (it is the identity, orders coincide). -/
theorem toEReal_strictMono : StrictMono toEReal := fun _ _ h => h

/-- `toEReal` as an order isomorphism `WithBot (WithTop ℝ) ≃o EReal`. -/
def toERealOrderIso : WithBot (WithTop ℝ) ≃o EReal where
  toFun := toEReal
  invFun := ofEReal
  left_inv := ofEReal_toEReal
  right_inv := toEReal_ofEReal
  map_rel_iff' := Iff.rfl

/-- `toEReal` as a homeomorphism `WithBot (WithTop ℝ) ≃ₜ EReal`: the topologies
are *literally* `EReal`'s, so this is the identity homeomorphism. -/
noncomputable def toERealHomeo : WithBot (WithTop ℝ) ≃ₜ EReal := Homeomorph.refl _

/-- `toERealHomeo a = toEReal a`. -/
@[simp] theorem toERealHomeo_apply (a : WithBot (WithTop ℝ)) :
    toERealHomeo a = toEReal a := rfl

/-- `toERealHomeo.symm x = ofEReal x`. -/
@[simp] theorem toERealHomeo_symm_apply (x : EReal) :
    toERealHomeo.symm x = ofEReal x := rfl

/-- `toEReal` is injective. -/
theorem toEReal_injective : Function.Injective toEReal :=
  Function.LeftInverse.injective ofEReal_toEReal

/-- `toEReal a = ⊤ ↔ a = ⊤`. -/
@[simp] theorem toEReal_eq_top {a : WithBot (WithTop ℝ)} :
    toEReal a = ⊤ ↔ a = ⊤ := Iff.rfl

/-- `toEReal a = ⊥ ↔ a = ⊥`. -/
@[simp] theorem toEReal_eq_bot {a : WithBot (WithTop ℝ)} :
    toEReal a = ⊥ ↔ a = ⊥ := Iff.rfl

/-! ### Unconditional agreement of addition; continuity by transport -/

/-- `a + b` is at a continuity point of `R̄max` (bot-absorbing) addition: the
pair avoids the discontinuities `(⊤,⊥)`, `(⊥,⊤)` (no `(+∞)+(−∞)` collision).
The max-side analogue of `AddDefinedExt`; named to avoid clashing with it. -/
def AddDefinedExtMax (a b : WithBot (WithTop ℝ)) : Prop :=
  (a ≠ ⊤ ∨ b ≠ ⊥) ∧ (a ≠ ⊥ ∨ b ≠ ⊤)

/-- The dioid (bot-absorbing) `+` agrees with `EReal`'s `+` under the cast
*unconditionally* — the carrier's addition is the same instance as `EReal`'s, so
unlike the top-absorbing `R̄min` case there is no collision discrepancy and no
hypothesis is needed. -/
theorem toEReal_add (a b : WithBot (WithTop ℝ)) :
    toEReal (a + b) = toEReal a + toEReal b := rfl

/-- The pair-set on which `R̄max` addition is continuous is open (each `≠⊤`,
`≠⊥` half-condition is open). -/
theorem isOpen_addDefinedExtMax :
    IsOpen {p : WithBot (WithTop ℝ) × WithBot (WithTop ℝ) |
      AddDefinedExtMax p.1 p.2} := by
  have o1 : IsOpen {p : WithBot (WithTop ℝ) × WithBot (WithTop ℝ) | p.1 ≠ ⊤} :=
    isOpen_ne.preimage continuous_fst
  have o2 : IsOpen {p : WithBot (WithTop ℝ) × WithBot (WithTop ℝ) | p.2 ≠ ⊥} :=
    isOpen_ne.preimage continuous_snd
  have o3 : IsOpen {p : WithBot (WithTop ℝ) × WithBot (WithTop ℝ) | p.1 ≠ ⊥} :=
    isOpen_ne.preimage continuous_fst
  have o4 : IsOpen {p : WithBot (WithTop ℝ) × WithBot (WithTop ℝ) | p.2 ≠ ⊤} :=
    isOpen_ne.preimage continuous_snd
  have hset : {p : WithBot (WithTop ℝ) × WithBot (WithTop ℝ) | AddDefinedExtMax p.1 p.2} =
      ({p | p.1 ≠ ⊤} ∪ {p | p.2 ≠ ⊥}) ∩ ({p | p.1 ≠ ⊥} ∪ {p | p.2 ≠ ⊤}) := by
    ext p; simp only [AddDefinedExtMax, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_union]
  rw [hset]
  exact (o1.union o2).inter (o3.union o4)

/-- Bot-absorbing `R̄max` addition is continuous at any `AddDefinedExtMax` pair:
the carrier's topology and addition are definitionally `EReal`'s, so this is
`EReal.continuousAt_add` read through the identity cast. -/
theorem continuousAt_add_of_addDefinedExtMax {a b : WithBot (WithTop ℝ)}
    (h : AddDefinedExtMax a b) :
    ContinuousAt
      (fun p : WithBot (WithTop ℝ) × WithBot (WithTop ℝ) => p.1 + p.2) (a, b) :=
  EReal.continuousAt_add h.1 h.2

/-- `AddDefinedExtMax a b` makes `(+)` continuous at `(a, b)`. -/
theorem AddDefinedExtMax.continuousAt {a b : WithBot (WithTop ℝ)}
    (h : AddDefinedExtMax a b) :
    ContinuousAt
      (fun p : WithBot (WithTop ℝ) × WithBot (WithTop ℝ) => p.1 + p.2) (a, b) :=
  continuousAt_add_of_addDefinedExtMax h

end MaxPlusExt

end DeepWiki
