import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import DeepWiki.NetworkCalculus.BooleanSatisfiability

/-!
# Tableau variable schema for the Cook- and Levin-style reduction

Layer 3a of a Cook- and Levin-style formalization: the **variable schema** of the
computation tableau for a finite Turing machine `Turing.FinTM2`.  Over a time bound `T`
and a stack-size (space) bound `S`, the tableau has one Boolean variable per atomic fact
about the machine configuration at each time step `t ∈ Fin (T+1)`:

* `labelCoord t l` — at time `t` the label (control state) is `l : Option tm.Λ`;
* `stateCoord t s` — at time `t` the internal state is `s : tm.σ`;
* `cellCoord t k i c` — at time `t`, stack `k`, position `i : Fin S` holds
  `c : Option (tm.Γ k)` (`none` marks an empty position above the stack top).

The coordinate type `TableauCoord tm T S` is a *sum of `Fintype`s* (no dependent-inductive
`deriving`), so `Fintype`/`DecidableEq` are inherited from Mathlib's `⊕`/`×`/`Σ`/`Fin`/`Option`
instances.  `numVars tm T S := Fintype.card (TableauCoord tm T S)`, and `coordEquiv` /
`coordVar` give the `Fin (numVars …)` variable indices used by the eventual CNF formula.

## Assumption (fully-finite alphabet)

`Turing.FinTM2` only guarantees `Fintype (tm.Γ tm.k₀)` (the input stack), and bundles only
`DecidableEq tm.K` (not `tm.Λ`/`tm.σ`).  Everything here takes `[∀ k, Fintype (tm.Γ k)]`,
`[∀ k, DecidableEq (tm.Γ k)]`, `[DecidableEq tm.Λ]`, and `[DecidableEq tm.σ]` as hypotheses —
the *fully-finite-alphabet* case.  The general FinTM2 reduction (reachable stack symbols form
a finite set) is a **later** layer.

## Deferred

This chunk is **only** the variable schema.  The clause families (init/transition/accept/
consistency as `List (Clause (numVars …))`), the assignment-to-configuration readback, and
the reduction's correctness are **later** chunks; they consume the coordinates, `numVars`,
`coordVar`, and the slot families defined here.
-/

open Turing

namespace DeepWiki

namespace TableauSchema

-- The bundled `Fintype K`, `Fintype Λ`, `Fintype σ`, `DecidableEq K` of a `FinTM2` are made
-- available as instances throughout this section via the `tm`-projected fields.
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

variable (tm : FinTM2) (T S : ℕ)
variable [∀ k, Fintype (tm.Γ k)]

/-! ## (1) The coordinate type

The full-finiteness `DecidableEq` hypotheses (`[∀ k, DecidableEq (tm.Γ k)]`,
`[DecidableEq tm.Λ]`, `[DecidableEq tm.σ]`) are consumed *only* by the coordinate
`DecidableEq` instance, so they are scoped to it rather than the whole section. -/

/-- A **tableau coordinate**: an atomic fact about the configuration at some time step —
a label fact, a state fact, or a stack-cell fact.  Encoded as a sum of `Fintype`s so that
`Fintype`/`DecidableEq` are inherited automatically. -/
def TableauCoord : Type :=
  (Fin (T + 1) × Option tm.Λ) ⊕ (Fin (T + 1) × tm.σ) ⊕
    (Σ _ : Fin (T + 1), Σ k : tm.K, Fin S × Option (tm.Γ k))

/-- `TableauCoord tm T S` is a `Fintype` (inherited from `⊕`/`×`/`Σ`/`Fin`/`Option`). -/
instance : Fintype (TableauCoord tm T S) :=
  inferInstanceAs (Fintype ((Fin (T + 1) × Option tm.Λ) ⊕ (Fin (T + 1) × tm.σ) ⊕
    (Σ _ : Fin (T + 1), Σ k : tm.K, Fin S × Option (tm.Γ k))))

/-- `TableauCoord tm T S` has decidable equality (built from the component `DecidableEq`s;
the outer-`⊕` search needs the two summand instances supplied explicitly). -/
instance [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] :
    DecidableEq (TableauCoord tm T S) := by
  haveI := tm.decidableEqK
  haveI hL : DecidableEq (Fin (T + 1) × Option tm.Λ) := inferInstance
  haveI hR : DecidableEq
      ((Fin (T + 1) × tm.σ) ⊕ (Σ _ : Fin (T + 1), Σ k : tm.K, Fin S × Option (tm.Γ k))) :=
    inferInstance
  exact fun a b => instDecidableEqSum a b

/-- `TableauCoord tm T S` is inhabited (a label-`none` coordinate at time `0`). -/
instance : Inhabited (TableauCoord tm T S) :=
  ⟨Sum.inl (⟨0, Nat.succ_pos T⟩, none)⟩

/-! ## (2) Named coordinate constructors -/

variable {tm T S}

/-- The coordinate "at time `t` the label is `l`". -/
def labelCoord (t : Fin (T + 1)) (l : Option tm.Λ) : TableauCoord tm T S :=
  Sum.inl (t, l)

/-- The coordinate "at time `t` the internal state is `s`". -/
def stateCoord (t : Fin (T + 1)) (s : tm.σ) : TableauCoord tm T S :=
  Sum.inr (Sum.inl (t, s))

/-- The coordinate "at time `t`, stack `k`, position `i` holds `c`". -/
def cellCoord (t : Fin (T + 1)) (k : tm.K) (i : Fin S) (c : Option (tm.Γ k)) :
    TableauCoord tm T S :=
  Sum.inr (Sum.inr ⟨t, k, i, c⟩)

/-! The three constructor families land in disjoint summands, hence are pairwise distinct
and individually injective. -/

omit [∀ k, Fintype (tm.Γ k)] in
/-- Label and state coordinates are always distinct. -/
theorem labelCoord_ne_stateCoord (t : Fin (T + 1)) (l : Option tm.Λ)
    (t' : Fin (T + 1)) (s : tm.σ) :
    (labelCoord t l : TableauCoord tm T S) ≠ stateCoord t' s :=
  fun h => Sum.inl_ne_inr h

omit [∀ k, Fintype (tm.Γ k)] in
/-- Label and cell coordinates are always distinct. -/
theorem labelCoord_ne_cellCoord (t : Fin (T + 1)) (l : Option tm.Λ)
    (t' : Fin (T + 1)) (k : tm.K) (i : Fin S) (c : Option (tm.Γ k)) :
    (labelCoord t l : TableauCoord tm T S) ≠ cellCoord t' k i c :=
  fun h => Sum.inl_ne_inr h

omit [∀ k, Fintype (tm.Γ k)] in
/-- State and cell coordinates are always distinct. -/
theorem stateCoord_ne_cellCoord (t : Fin (T + 1)) (s : tm.σ)
    (t' : Fin (T + 1)) (k : tm.K) (i : Fin S) (c : Option (tm.Γ k)) :
    (stateCoord t s : TableauCoord tm T S) ≠ cellCoord t' k i c :=
  fun h => Sum.inl_ne_inr (Sum.inr.inj h)

omit [∀ k, Fintype (tm.Γ k)] in
/-- `labelCoord` is injective in `(t, l)`. -/
theorem labelCoord_inj {t t' : Fin (T + 1)} {l l' : Option tm.Λ}
    (h : (labelCoord t l : TableauCoord tm T S) = labelCoord t' l') :
    t = t' ∧ l = l' :=
  Prod.mk.injEq .. ▸ (Sum.inl.inj h)

omit [∀ k, Fintype (tm.Γ k)] in
/-- `stateCoord` is injective in `(t, s)`. -/
theorem stateCoord_inj {t t' : Fin (T + 1)} {s s' : tm.σ}
    (h : (stateCoord t s : TableauCoord tm T S) = stateCoord t' s') :
    t = t' ∧ s = s' :=
  Prod.mk.injEq .. ▸ (Sum.inl.inj (Sum.inr.inj h))

/-! ## (3) Variable count and indexing -/

variable (tm T S)

/-- The **number of Boolean variables** of the tableau: the cardinality of the coordinate
type. -/
def numVars : ℕ := Fintype.card (TableauCoord tm T S)

/-- The coordinate-to-index equivalence `TableauCoord tm T S ≃ Fin (numVars tm T S)`. -/
noncomputable def coordEquiv : TableauCoord tm T S ≃ Fin (numVars tm T S) :=
  Fintype.equivFin _

variable {tm T S}

/-- The `Fin (numVars …)` variable **index** of a coordinate. -/
noncomputable def coordVar (c : TableauCoord tm T S) : Fin (numVars tm T S) :=
  coordEquiv tm T S c

/-- The variable index map is injective (distinct coordinates get distinct indices). -/
theorem coordVar_injective :
    Function.Injective (coordVar : TableauCoord tm T S → Fin (numVars tm T S)) :=
  fun _ _ h => (coordEquiv tm T S).injective h

/-- `coordVar c = coordVar c'` iff `c = c'`. -/
@[simp] theorem coordVar_inj {c c' : TableauCoord tm T S} :
    coordVar c = coordVar c' ↔ c = c' :=
  ⟨fun h => coordVar_injective h, fun h => h ▸ rfl⟩

/-! ## (4) Slot families

A *slot* is the list of variable indices that the eventual consistency clauses force to be
"exactly one true" — the indices for all possible values of a single fact at a single
position.  Each is `Finset.univ.toList.map (coordVar ∘ …)`. -/

/-- The **label slot** at time `t`: the variable indices for every possible label value. -/
noncomputable def labelSlot (t : Fin (T + 1)) : List (Fin (numVars tm T S)) :=
  (Finset.univ : Finset (Option tm.Λ)).toList.map (fun l => coordVar (labelCoord t l))

/-- The **state slot** at time `t`: the variable indices for every possible internal state. -/
noncomputable def stateSlot (t : Fin (T + 1)) : List (Fin (numVars tm T S)) :=
  (Finset.univ : Finset tm.σ).toList.map (fun s => coordVar (stateCoord t s))

/-- The **cell slot** at time `t`, stack `k`, position `i`: the variable indices for every
possible cell value. -/
noncomputable def cellSlot (t : Fin (T + 1)) (k : tm.K) (i : Fin S) :
    List (Fin (numVars tm T S)) :=
  (Finset.univ : Finset (Option (tm.Γ k))).toList.map (fun c => coordVar (cellCoord t k i c))

/-- Every label coordinate at time `t` appears in `labelSlot t`. -/
theorem mem_labelSlot (t : Fin (T + 1)) (l : Option tm.Λ) :
    coordVar (labelCoord t l) ∈ labelSlot (tm := tm) (S := S) t := by
  simp only [labelSlot, List.mem_map]
  exact ⟨l, Finset.mem_toList.2 (Finset.mem_univ l), rfl⟩

/-- Every state coordinate at time `t` appears in `stateSlot t`. -/
theorem mem_stateSlot (t : Fin (T + 1)) (s : tm.σ) :
    coordVar (stateCoord t s) ∈ stateSlot (tm := tm) (S := S) t := by
  simp only [stateSlot, List.mem_map]
  exact ⟨s, Finset.mem_toList.2 (Finset.mem_univ s), rfl⟩

/-- Every cell coordinate at `(t, k, i)` appears in `cellSlot t k i`. -/
theorem mem_cellSlot (t : Fin (T + 1)) (k : tm.K) (i : Fin S) (c : Option (tm.Γ k)) :
    coordVar (cellCoord t k i c) ∈ cellSlot (tm := tm) t k i := by
  simp only [cellSlot, List.mem_map]
  exact ⟨c, Finset.mem_toList.2 (Finset.mem_univ c), rfl⟩

/-- The label slot is nonempty (the `none`-label coordinate is always present). -/
theorem labelSlot_ne_nil (t : Fin (T + 1)) : labelSlot (tm := tm) (S := S) t ≠ [] :=
  List.ne_nil_of_mem (mem_labelSlot t none)

/-- The state slot is nonempty (`tm.σ` is inhabited by `tm.initialState`). -/
theorem stateSlot_ne_nil (t : Fin (T + 1)) : stateSlot (tm := tm) (S := S) t ≠ [] :=
  List.ne_nil_of_mem (mem_stateSlot t tm.initialState)

/-- The cell slot is nonempty (the `none`-cell coordinate is always present). -/
theorem cellSlot_ne_nil (t : Fin (T + 1)) (k : tm.K) (i : Fin S) :
    cellSlot (tm := tm) t k i ≠ [] :=
  List.ne_nil_of_mem (mem_cellSlot t k i none)

/-! ## (5) Size characterization -/

variable (tm T S)

/-- **Exact variable count.** `numVars` splits as the label part, the state part, and the
cell part summed over stacks.  Uses `Fintype.card` of the components. -/
theorem numVars_eq :
    numVars tm T S =
      (T + 1) * (Fintype.card tm.Λ + 1)
        + (T + 1) * Fintype.card tm.σ
        + (T + 1) * S * ∑ k : tm.K, (Fintype.card (tm.Γ k) + 1) := by
  -- the cell part summed over the time axis equals `(T+1) * S * ∑ₖ (card (Γ k) + 1)`
  have hcell : (∑ _t : Fin (T + 1), Fintype.card (Σ k : tm.K, Fin S × Option (tm.Γ k)))
      = (T + 1) * S * ∑ k : tm.K, (Fintype.card (tm.Γ k) + 1) := by
    simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, Fintype.card_option,
      Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [← Finset.mul_sum, ← mul_assoc]
  show Fintype.card ((Fin (T + 1) × Option tm.Λ) ⊕ (Fin (T + 1) × tm.σ) ⊕
      (Σ _ : Fin (T + 1), Σ k : tm.K, Fin S × Option (tm.Γ k))) = _
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_sigma, Fintype.card_fin, Fintype.card_option, hcell]
  ring

/-- **Polynomial-shaped upper bound.** With `Fintype.card tm.Λ + Fintype.card tm.σ` the
label+state weight and `∑ₖ (card (Γ k) + 1)` the per-position cell weight, the variable count
is bounded by a degree-2 polynomial in `(T, S)`. -/
theorem numVars_le :
    numVars tm T S ≤
      (T + 1) * (Fintype.card tm.Λ + Fintype.card tm.σ + 1)
        + (T + 1) * S * ∑ k : tm.K, (Fintype.card (tm.Γ k) + 1) := by
  rw [numVars_eq]
  refine Nat.add_le_add_right ?_ _
  rw [← Nat.mul_add]
  exact Nat.mul_le_mul_left _ (by omega)

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

variable {tm : FinTM2} {T S : ℕ} [∀ k, Fintype (tm.Γ k)]

-- `numVars` is exactly the coordinate-type cardinality.
example : numVars tm T S = Fintype.card (TableauCoord tm T S) := rfl

-- `coordVar` reads off the index assigned to a coordinate by `coordEquiv`.
example (c : TableauCoord tm T S) : coordVar c = coordEquiv tm T S c := rfl

-- A label coordinate's variable index lies in that time step's label slot.
example (t : Fin (T + 1)) (l : Option tm.Λ) :
    coordVar (labelCoord t l : TableauCoord tm T S) ∈ labelSlot (tm := tm) (S := S) t :=
  mem_labelSlot t l

-- Distinct coordinates always get distinct variable indices.
example {c c' : TableauCoord tm T S} (h : coordVar c = coordVar c') : c = c' :=
  coordVar_injective h

end Examples

end TableauSchema

end DeepWiki
