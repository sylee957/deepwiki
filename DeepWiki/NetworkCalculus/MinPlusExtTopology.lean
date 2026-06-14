import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Order.WithTop
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Algebra.Order.Ring.WithTop

/-!
# `R̄min` analysis via the `EReal` cast

The book's extended real line `R̄min = WithTop (WithBot ℝ)` has *top-absorbing*
addition (`(+∞)+(−∞) = +∞`), distinct from `EReal = WithBot (WithTop ℝ)` with
`(+∞)+(−∞) = −∞`. Rather than rebuild the order topology and continuity of
addition on this carrier, we reuse `EReal`'s analysis by *transport* through the
value cast `toEReal`: it is an order isomorphism (hence a homeomorphism), and the
two additions agree on the open set where `AddDefinedExt` holds (no `(+∞)+(−∞)`
collision). `EReal.continuousAt_add` then gives continuity of `R̄min` addition at
every `AddDefinedExt` pair, with no from-scratch case analysis.
-/

namespace DeepWiki

open Topology Filter Set
open scoped Classical

namespace MinPlusExt

/-- Order topology on the inner layer `WithBot ℝ`, behind `scoped` so it never
leaks globally onto a Mathlib type; `WithTop (WithBot ℝ)` then inherits the
order topology from Mathlib's `WithTop` instances. Bring it into scope with
`open scoped DeepWiki.MinPlusExt`. -/
scoped instance instTopologicalSpaceWithBotReal :
    TopologicalSpace (WithBot ℝ) := Preorder.topology _

/-- `WithBot ℝ` carries the order topology (scoped, see above). -/
scoped instance instOrderTopologyWithBotReal :
    OrderTopology (WithBot ℝ) := ⟨rfl⟩

end MinPlusExt

open scoped MinPlusExt

/-! ### The value cast `WithTop (WithBot ℝ) ↔ EReal` -/

/-- Value cast `WithTop (WithBot ℝ) → EReal`: identity on `[−∞,+∞]`. -/
noncomputable def toEReal : WithTop (WithBot ℝ) → EReal
  | ⊤ => ⊤
  | (⊥ : WithBot ℝ) => ⊥
  | ((r : ℝ) : WithBot ℝ) => (r : EReal)

/-- `toEReal ⊤ = ⊤`. -/
@[simp] theorem toEReal_top : toEReal ⊤ = ⊤ := rfl
/-- `toEReal ↑(⊥ : WithBot ℝ) = ⊥`: the coerced inner bottom maps to `⊥`. -/
@[simp] theorem toEReal_coe_bot :
    toEReal ((⊥ : WithBot ℝ) : WithTop (WithBot ℝ)) = ⊥ := rfl
/-- `toEReal ↑↑r = ↑r`: the cast is the identity on real values. -/
@[simp] theorem toEReal_coe (r : ℝ) :
    toEReal (((r : WithBot ℝ) : WithTop (WithBot ℝ))) = (r : EReal) := rfl
/-- `toEReal ⊥ = ⊥`. -/
@[simp] theorem toEReal_bot : toEReal (⊥ : WithTop (WithBot ℝ)) = ⊥ := by
  rw [← WithTop.coe_bot]; rfl

/-- Inverse value cast `EReal → WithTop (WithBot ℝ)`: identity on `[−∞,+∞]`. -/
noncomputable def ofEReal : EReal → WithTop (WithBot ℝ)
  | ⊤ => ⊤
  | ⊥ => ((⊥ : WithBot ℝ) : WithTop (WithBot ℝ))
  | ((r : ℝ) : EReal) => (((r : WithBot ℝ)) : WithTop (WithBot ℝ))

/-- `ofEReal ⊤ = ⊤`. -/
@[simp] theorem ofEReal_top : ofEReal ⊤ = ⊤ := rfl
/-- `ofEReal ⊥ = ↑(⊥ : WithBot ℝ)`: `⊥` maps to the coerced inner bottom. -/
@[simp] theorem ofEReal_bot :
    ofEReal ⊥ = ((⊥ : WithBot ℝ) : WithTop (WithBot ℝ)) := rfl
/-- `ofEReal ↑r = ↑↑r`: the inverse cast is the identity on real values. -/
@[simp] theorem ofEReal_coe (r : ℝ) :
    ofEReal ((r : EReal)) = (((r : WithBot ℝ)) : WithTop (WithBot ℝ)) := rfl

/-- `ofEReal` is a left inverse of `toEReal`. -/
theorem ofEReal_toEReal (a : WithTop (WithBot ℝ)) : ofEReal (toEReal a) = a := by
  cases a with
  | top => rfl
  | coe v => cases v with
    | bot => rfl
    | coe r => rfl

/-- `ofEReal` is a right inverse of `toEReal`. -/
theorem toEReal_ofEReal (x : EReal) : toEReal (ofEReal x) = x := by
  induction x with
  | bot => rfl
  | top => rfl
  | coe r => rfl

/-- `toEReal` is strictly monotone. -/
theorem toEReal_strictMono : StrictMono toEReal := by
  intro a b hab
  cases a with
  | top => exact absurd hab (by simp)
  | coe v => cases v with
    | bot =>
      cases b with
      | top => simp
      | coe w => cases w with
        | bot => exact absurd hab (by simp)
        | coe s => simp
    | coe r =>
      cases b with
      | top => simp
      | coe w => cases w with
        | bot => exact absurd hab (by simp)
        | coe s =>
          rw [WithTop.coe_lt_coe, WithBot.coe_lt_coe] at hab
          simpa using hab

/-- `toEReal` as an order isomorphism `WithTop (WithBot ℝ) ≃o EReal`. -/
noncomputable def toERealOrderIso : WithTop (WithBot ℝ) ≃o EReal where
  toFun := toEReal
  invFun := ofEReal
  left_inv := ofEReal_toEReal
  right_inv := toEReal_ofEReal
  map_rel_iff' := toEReal_strictMono.le_iff_le

/-- `toEReal` as a homeomorphism `WithTop (WithBot ℝ) ≃ₜ EReal` (order-iso
between order-topology spaces). -/
noncomputable def toERealHomeo : WithTop (WithBot ℝ) ≃ₜ EReal :=
  toERealOrderIso.toHomeomorph

/-- `toERealHomeo a = toEReal a`: the homeomorphism applies the value cast. -/
@[simp] theorem toERealHomeo_apply (a : WithTop (WithBot ℝ)) :
    toERealHomeo a = toEReal a := rfl

/-- `toERealHomeo.symm x = ofEReal x`: the inverse homeomorphism is `ofEReal`. -/
@[simp] theorem toERealHomeo_symm_apply (x : EReal) :
    toERealHomeo.symm x = ofEReal x := rfl

/-- `toEReal` is injective. -/
theorem toEReal_injective : Function.Injective toEReal :=
  Function.LeftInverse.injective ofEReal_toEReal

/-- `toEReal a = ⊤ ↔ a = ⊤`: the cast hits `⊤` only at `⊤`. -/
@[simp] theorem toEReal_eq_top {a : WithTop (WithBot ℝ)} :
    toEReal a = ⊤ ↔ a = ⊤ := by
  rw [show (⊤ : EReal) = toEReal ⊤ from rfl, toEReal_injective.eq_iff]

/-- `toEReal a = ⊥ ↔ a = ⊥`: the cast hits `⊥` only at `⊥`. -/
@[simp] theorem toEReal_eq_bot {a : WithTop (WithBot ℝ)} :
    toEReal a = ⊥ ↔ a = ⊥ := by
  rw [show (⊥ : EReal) = toEReal ⊥ from rfl, toEReal_injective.eq_iff]

/-! ### Conditional agreement of addition and continuity by transport -/

/-- `a + b` is at a continuity point of `R̄min` (top-absorbing) addition: the
pair avoids the discontinuities `(⊤,⊥)`, `(⊥,⊤)` (no `(+∞)+(−∞)` collision). -/
def AddDefinedExt (a b : WithTop (WithBot ℝ)) : Prop :=
  (a ≠ ⊤ ∨ b ≠ ⊥) ∧ (a ≠ ⊥ ∨ b ≠ ⊤)

/-- Off the collision, the dioid (top-absorbing) `+` agrees with `EReal`'s `+`
under the cast: `toEReal (a + b) = toEReal a + toEReal b`. -/
theorem toEReal_add {a b : WithTop (WithBot ℝ)} (h : AddDefinedExt a b) :
    toEReal (a + b) = toEReal a + toEReal b := by
  obtain ⟨h1, h2⟩ := h
  cases a with
  | top =>
    cases b with
    | top => simp
    | coe w => cases w with
      | bot => simp [WithTop.coe_bot] at h1
      | coe s => simp [WithTop.top_add]
  | coe v =>
    cases v with
    | bot =>
      cases b with
      | top => simp [WithTop.coe_bot] at h2
      | coe w => cases w with
        | bot => rw [← WithTop.coe_add, WithBot.bot_add]; simp
        | coe s => rw [← WithTop.coe_add, WithBot.bot_add]; simp
    | coe r =>
      cases b with
      | top => simp [WithTop.add_top]
      | coe w => cases w with
        | bot => rw [← WithTop.coe_add, WithBot.add_bot]; simp
        | coe s =>
          rw [← WithTop.coe_add, ← WithBot.coe_add, toEReal_coe,
            toEReal_coe, toEReal_coe, EReal.coe_add]

/-- The pair-set on which `R̄min` addition is well-defined is open (each `≠⊤`,
`≠⊥` half-condition is open). -/
theorem isOpen_addDefinedExt :
    IsOpen {p : WithTop (WithBot ℝ) × WithTop (WithBot ℝ) |
      AddDefinedExt p.1 p.2} := by
  have o1 : IsOpen {p : WithTop (WithBot ℝ) × WithTop (WithBot ℝ) | p.1 ≠ ⊤} :=
    isOpen_ne.preimage continuous_fst
  have o2 : IsOpen {p : WithTop (WithBot ℝ) × WithTop (WithBot ℝ) | p.2 ≠ ⊥} :=
    isOpen_ne.preimage continuous_snd
  have o3 : IsOpen {p : WithTop (WithBot ℝ) × WithTop (WithBot ℝ) | p.1 ≠ ⊥} :=
    isOpen_ne.preimage continuous_fst
  have o4 : IsOpen {p : WithTop (WithBot ℝ) × WithTop (WithBot ℝ) | p.2 ≠ ⊤} :=
    isOpen_ne.preimage continuous_snd
  have hset : {p : WithTop (WithBot ℝ) × WithTop (WithBot ℝ) | AddDefinedExt p.1 p.2} =
      ({p | p.1 ≠ ⊤} ∪ {p | p.2 ≠ ⊥}) ∩ ({p | p.1 ≠ ⊥} ∪ {p | p.2 ≠ ⊤}) := by
    ext p; simp only [AddDefinedExt, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_union]
  rw [hset]
  exact (o1.union o2).inter (o3.union o4)

/-- The conjugated `EReal` addition `p ↦ ofEReal (toEReal p.1 + toEReal p.2)`. -/
noncomputable def conjAdd
    (p : WithTop (WithBot ℝ) × WithTop (WithBot ℝ)) : WithTop (WithBot ℝ) :=
  ofEReal (toEReal p.1 + toEReal p.2)

/-- The conjugated addition is continuous at any `AddDefinedExt` pair, by
transport through the homeomorphism `toEReal` and `EReal.continuousAt_add`. -/
theorem continuousAt_conjAdd {a b : WithTop (WithBot ℝ)}
    (h : AddDefinedExt a b) : ContinuousAt conjAdd (a, b) := by
  have hpair : Continuous (fun p : WithTop (WithBot ℝ) × WithTop (WithBot ℝ) =>
      (toEReal p.1, toEReal p.2)) :=
    (toERealHomeo.continuous.comp continuous_fst).prodMk
      (toERealHomeo.continuous.comp continuous_snd)
  have hEReal : ContinuousAt (fun q : EReal × EReal => q.1 + q.2)
      (toEReal a, toEReal b) := by
    refine EReal.continuousAt_add ?_ ?_
    · rcases h.1 with ha | hb
      · exact Or.inl (by simpa using ha)
      · exact Or.inr (by simpa using hb)
    · rcases h.2 with ha | hb
      · exact Or.inl (by simpa using ha)
      · exact Or.inr (by simpa using hb)
  have hadd : ContinuousAt (fun p : WithTop (WithBot ℝ) × WithTop (WithBot ℝ) =>
      toEReal p.1 + toEReal p.2) (a, b) := by
    have := hEReal.comp (x := (a, b)) hpair.continuousAt
    simpa [Function.comp] using this
  have := (toERealHomeo.symm.continuous.continuousAt
    (x := toEReal a + toEReal b)).comp (x := (a, b)) hadd
  simpa [conjAdd, Function.comp] using this

/-- Top-absorbing `R̄min` addition is continuous at any `AddDefinedExt` pair,
proved by conjugation through the `EReal` cast (no from-scratch case analysis):
`conjAdd` agrees with `+` on the open `AddDefinedExt` neighborhood. -/
theorem continuousAt_add_of_addDefinedExt {a b : WithTop (WithBot ℝ)}
    (h : AddDefinedExt a b) :
    ContinuousAt
      (fun p : WithTop (WithBot ℝ) × WithTop (WithBot ℝ) => p.1 + p.2) (a, b) := by
  refine (continuousAt_conjAdd h).congr ?_
  filter_upwards [isOpen_addDefinedExt.mem_nhds h] with p hp
  show conjAdd p = p.1 + p.2
  unfold conjAdd
  rw [← toEReal_add hp, ofEReal_toEReal]

/-- `AddDefinedExt a b` makes `(+)` continuous at `(a, b)`. -/
theorem AddDefinedExt.continuousAt {a b : WithTop (WithBot ℝ)}
    (h : AddDefinedExt a b) :
    ContinuousAt
      (fun p : WithTop (WithBot ℝ) × WithTop (WithBot ℝ) => p.1 + p.2) (a, b) :=
  continuousAt_add_of_addDefinedExt h

end DeepWiki
