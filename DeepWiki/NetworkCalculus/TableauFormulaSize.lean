import DeepWiki.NetworkCalculus.TableauFormula
import DeepWiki.NetworkCalculus.CookLevin

/-!
# Polynomial size bound for the Cook- and Levin-style tableau formula

Layer 3e: a **polynomial upper bound** on `CnfFormula.size (tableauFormula …)` — the
"the reduction output is small" half of the Cook–Levin theorem. The bound is a polynomial
in `T`, `S`, `input.length`, `acceptOutput.length` whose coefficients are machine
cardinalities (`Fintype.card tm.Λ`, `Fintype.card tm.σ`, `Fintype.card tm.K`,
`(relevantStmts tm).card`, `∑ k, Fintype.card (tm.Γ k)`).

The whole argument is *generous counting*: the total literal count of a clause list `cs`
is `cs.flatten.length` (`totalLits`), which splits over `++`/`flatMap`/`map`, and is bounded
by `(clause count) * (max clause width)`. Each family — consistency, init, accept, the
per-time transition — is bounded by such a product; the four are combined through
`List.map_append`/`List.sum_append`.

* `consistencyClauses_size_le` / `fullConsistencyClauses_size_le`, `initClausesC_size_le`,
  `transClauses_size_le`, `acceptClausesC_size_le` — the per-family total-literal-count bounds.
* `tableauFormula_size_le` — the headline
  `CnfFormula.size (tableauFormula …) ≤ (T+1) * (S+1) * machineConst³ * 30`, where `machineConst`
  packs every machine cardinality (`card Λ`, `card σ`, `card K`, `(relevantStmts).card`,
  `∑ₖ card (Γ k)`); `input`/`acceptOutput` enter only through `≤ S` (the formula fixes them in
  the space bound), so the bound is uniform in their lengths.
* `cnfEncode_length_eq` / `cnfEncode_length_le` — the serialized `cnfEncode` length is
  `2 + numClauses + 2·totalLits ≤ 2·size + 2 + numClauses`; combined with the all-clauses-nonempty
  fact (`tableauFormula_clauses_ne_nil`), `cnfEncode_tableauFormula_length_le` gives
  `(cnfEncode (tableauFormula …)).length ≤ (T+1)*(S+1)*machineConst³*90 + 2` (the SAT
  `KarpReduction` measure).

## Deferred

ONLY the size bound. The `AcceptsWithin` encode bridge, the verifier/certificate encoding,
and the final `cookLevin` discharge are later layers (see `TableauFormula`/`CookLevin`).
-/

open Turing

namespace DeepWiki

namespace CombinedTableau

open TableauSchema OneHotRegister BooleanConstraints ReachableCont CnfFormula

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

/-! ## (0) `totalLits`: the total literal count of a clause list -/

/-- The **total literal count** of a clause list: the length of the flattened literal list,
equivalently `(cs.map List.length).sum`. The summand of `CnfFormula.size`. -/
def totalLits {n : ℕ} (cs : List (Clause n)) : ℕ := cs.flatten.length

/-- `totalLits cs = (cs.map length).sum` — the `CnfFormula.size` summand. -/
theorem totalLits_eq_sum {n : ℕ} (cs : List (Clause n)) :
    totalLits cs = (cs.map List.length).sum := by
  rw [totalLits, List.length_flatten]

/-- `CnfFormula.size φ = φ.numVars + totalLits φ.clauses`. -/
theorem size_eq_numVars_add_totalLits (φ : CnfFormula) :
    φ.size = φ.numVars + totalLits φ.clauses := by
  rw [CnfFormula.size, totalLits_eq_sum]

/-- `totalLits` is additive over `++`. -/
@[simp] theorem totalLits_append {n : ℕ} (c₁ c₂ : List (Clause n)) :
    totalLits (c₁ ++ c₂) = totalLits c₁ + totalLits c₂ := by
  rw [totalLits, totalLits, totalLits, List.flatten_append, List.length_append]

/-- `totalLits` of `nil` is `0`. -/
@[simp] theorem totalLits_nil {n : ℕ} : totalLits ([] : List (Clause n)) = 0 := rfl

/-- `totalLits` of a singleton clause list is that clause's length. -/
@[simp] theorem totalLits_singleton {n : ℕ} (c : Clause n) : totalLits [c] = c.length := by
  simp [totalLits]

/-- `totalLits` of a `cons` is the head clause's length plus the tail's total. -/
@[simp] theorem totalLits_cons {n : ℕ} (c : Clause n) (cs : List (Clause n)) :
    totalLits (c :: cs) = c.length + totalLits cs := by
  rw [totalLits, totalLits, List.flatten_cons, List.length_append]

/-- `totalLits` of `cs ++ [c]` (a single trailing clause) is `totalLits cs + c.length`. -/
theorem totalLits_append_singleton {n : ℕ} (cs : List (Clause n)) (c : Clause n) :
    totalLits (cs ++ [c]) = totalLits cs + c.length := by
  rw [totalLits, totalLits, List.flatten_concat, List.length_append]

/-- **Width bound.** If every clause of `cs` has length `≤ w`, then
`totalLits cs ≤ cs.length * w`. -/
theorem totalLits_le_of_width {n : ℕ} (cs : List (Clause n)) (w : ℕ)
    (hw : ∀ c ∈ cs, c.length ≤ w) : totalLits cs ≤ cs.length * w := by
  rw [totalLits_eq_sum]
  refine le_trans (List.sum_le_card_nsmul (cs.map List.length) w ?_) ?_
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    exact hw c hc
  · rw [List.length_map, smul_eq_mul]

/-- `totalLits` of a `flatMap` over a list: the sum of the groups' totals (via `length_flatMap`
on the flattened literal stream). -/
theorem totalLits_flatMap {n : ℕ} {α : Type*} (l : List α) (g : α → List (Clause n)) :
    totalLits (l.flatMap g) = (l.map (fun a => totalLits (g a))).sum := by
  rw [totalLits, List.flatMap_def, List.flatten_flatten, List.length_flatten, List.map_map,
    List.map_map]
  rfl

/-- **`flatMap` per-group bound.** If `l` has length `≤ N` and each group `g a` has
`totalLits (g a) ≤ B`, then `totalLits (l.flatMap g) ≤ N * B`. -/
theorem totalLits_flatMap_le_of_group {n : ℕ} {α : Type*} (l : List α) (g : α → List (Clause n))
    (N B : ℕ) (hN : l.length ≤ N) (hg : ∀ a ∈ l, totalLits (g a) ≤ B) :
    totalLits (l.flatMap g) ≤ N * B := by
  rw [totalLits_flatMap]
  refine le_trans (List.sum_le_card_nsmul (l.map (fun a => totalLits (g a))) B ?_) ?_
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact hg a ha
  · rw [List.length_map, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hN

/-- **`flatMap` width-and-count bound.** If `l` has length `≤ N` and each group `g a`
has `≤ C` clauses each of width `≤ w`, then `totalLits (l.flatMap g) ≤ N * (C * w)`. -/
theorem totalLits_flatMap_le {n : ℕ} {α : Type*} (l : List α) (g : α → List (Clause n))
    (N C w : ℕ) (hN : l.length ≤ N)
    (hg : ∀ a ∈ l, (g a).length ≤ C ∧ ∀ c ∈ g a, c.length ≤ w) :
    totalLits (l.flatMap g) ≤ N * (C * w) := by
  rw [totalLits_flatMap]
  refine le_trans (List.sum_le_card_nsmul (l.map (fun a => totalLits (g a))) (C * w) ?_) ?_
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨hcount, hwidth⟩ := hg a ha
    exact le_trans (totalLits_le_of_width (g a) w hwidth) (Nat.mul_le_mul_right _ hcount)
  · rw [List.length_map, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hN

/-! ## (1) Counting `exactlyOne` / `atMostOne` / `atLeastOneTrue` -/

open BooleanConstraints in
/-- Every clause of `atMostOne vars` is a 2-literal exclusion. -/
theorem length_mem_atMostOne {n : ℕ} (vars : List (Fin n)) (c : Clause n)
    (hc : c ∈ atMostOne vars) : c.length = 2 := by
  induction vars with
  | nil => simp [atMostOne] at hc
  | cons x xs ih =>
    rw [atMostOne, List.mem_append] at hc
    rcases hc with hc | hc
    · rw [List.mem_map] at hc
      obtain ⟨p, _, rfl⟩ := hc
      rfl
    · exact ih hc

open BooleanConstraints in
/-- `atMostOne vars` has at most `vars.length ^ 2` clauses (an exclusion per ordered pair). -/
theorem length_atMostOne_le {n : ℕ} (vars : List (Fin n)) :
    (atMostOne vars).length ≤ vars.length ^ 2 := by
  induction vars with
  | nil => simp [atMostOne]
  | cons x xs ih =>
    rw [atMostOne, List.length_append, List.length_map]
    -- the head contributes `xs.length` exclusions; the tail `≤ xs.length^2`
    show (xs.map (x, ·)).length + (atMostOne xs).length ≤ (xs.length + 1) ^ 2
    rw [List.length_map]
    have : (xs.length + 1) ^ 2 = xs.length ^ 2 + (2 * xs.length + 1) := by ring
    rw [this]
    omega

open BooleanConstraints in
/-- **`atMostOne` total literals.** Each of the `≤ vars.length ^ 2` clauses is 2-wide, so
`totalLits (atMostOne vars) ≤ 2 * vars.length ^ 2`. -/
theorem totalLits_atMostOne_le {n : ℕ} (vars : List (Fin n)) :
    totalLits (atMostOne vars) ≤ vars.length ^ 2 * 2 := by
  refine le_trans (totalLits_le_of_width (atMostOne vars) 2
    (fun c hc => le_of_eq (length_mem_atMostOne vars c hc))) ?_
  exact Nat.mul_le_mul_right 2 (length_atMostOne_le vars)

open BooleanConstraints in
/-- `atLeastOneTrue vars` is one clause of `vars.length` literals. -/
@[simp] theorem totalLits_atLeastOneTrue {n : ℕ} (vars : List (Fin n)) :
    totalLits [atLeastOneTrue vars] = vars.length := by
  rw [totalLits_singleton, atLeastOneTrue, List.length_map]

open BooleanConstraints in
/-- **`exactlyOne` total literals.** The disjunction (`vars.length`) plus the exclusions
(`≤ 2 * vars.length ^ 2`): `totalLits (exactlyOne vars) ≤ vars.length + 2 * vars.length ^ 2`. -/
theorem totalLits_exactlyOne_le {n : ℕ} (vars : List (Fin n)) :
    totalLits (exactlyOne vars) ≤ vars.length + vars.length ^ 2 * 2 := by
  rw [exactlyOne]
  show totalLits (atLeastOneTrue vars :: atMostOne vars) ≤ _
  rw [show (atLeastOneTrue vars :: atMostOne vars)
        = [atLeastOneTrue vars] ++ atMostOne vars from rfl, totalLits_append,
    totalLits_atLeastOneTrue]
  exact Nat.add_le_add_left (totalLits_atMostOne_le vars) _

/-- **`exactlyOne` total literals, slot form.** If `vars.length ≤ m`, then
`totalLits (exactlyOne vars) ≤ m + m ^ 2 * 2`. -/
theorem totalLits_exactlyOne_le_of_length {n : ℕ} (vars : List (Fin n)) (m : ℕ)
    (hm : vars.length ≤ m) :
    totalLits (BooleanConstraints.exactlyOne vars) ≤ m + m ^ 2 * 2 := by
  refine le_trans (totalLits_exactlyOne_le vars) ?_
  exact Nat.add_le_add (le_trans hm (le_refl m)) (Nat.mul_le_mul_right 2 (Nat.pow_le_pow_left hm 2))

/-! ## (1b) Lifting preserves total literal count -/

/-- `liftClauseL` preserves a clause's length (it maps each literal individually). -/
@[simp] theorem length_liftClauseL {n m : ℕ} (c : Clause n) :
    (BooleanConstraints.liftClauseL (m := m) c).length = c.length := by
  rw [BooleanConstraints.liftClauseL, List.length_map]

/-- `liftClauseR` preserves a clause's length. -/
@[simp] theorem length_liftClauseR {n m : ℕ} (c : Clause m) :
    (BooleanConstraints.liftClauseR (n := n) c).length = c.length := by
  rw [BooleanConstraints.liftClauseR, List.length_map]

/-- `liftClausesL` preserves the clause count. -/
@[simp] theorem length_liftClausesL {n m : ℕ} (cs : List (Clause n)) :
    (BooleanConstraints.liftClausesL (m := m) cs).length = cs.length := by
  rw [BooleanConstraints.liftClausesL, List.length_map]

/-- `liftClausesL` preserves the total literal count. -/
@[simp] theorem totalLits_liftClausesL {n m : ℕ} (cs : List (Clause n)) :
    totalLits (BooleanConstraints.liftClausesL (m := m) cs) = totalLits cs := by
  rw [totalLits_eq_sum, totalLits_eq_sum, BooleanConstraints.liftClausesL, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp [Function.comp_apply]

/-- `liftClausesR` preserves the total literal count. -/
@[simp] theorem totalLits_liftClausesR {n m : ℕ} (cs : List (Clause m)) :
    totalLits (BooleanConstraints.liftClausesR (n := n) cs) = totalLits cs := by
  rw [totalLits_eq_sum, totalLits_eq_sum, BooleanConstraints.liftClausesR, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp [Function.comp_apply]

/-! ## (2) Slot lengths -/

variable {tm : FinTM2} {T S : ℕ} [∀ k, Fintype (tm.Γ k)]

/-- The label slot has `Fintype.card tm.Λ + 1` entries (one per `Option tm.Λ` value). -/
theorem length_labelSlot (t : Fin (T + 1)) :
    (labelSlot (tm := tm) (S := S) t).length = Fintype.card tm.Λ + 1 := by
  rw [labelSlot, List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_option]

/-- The state slot has `Fintype.card tm.σ` entries (one per internal state). -/
theorem length_stateSlot (t : Fin (T + 1)) :
    (stateSlot (tm := tm) (S := S) t).length = Fintype.card tm.σ := by
  rw [stateSlot, List.length_map, Finset.length_toList, Finset.card_univ]

/-- The cell slot has `Fintype.card (tm.Γ k) + 1` entries (one per `Option (tm.Γ k)` value). -/
theorem length_cellSlot (t : Fin (T + 1)) (k : tm.K) (i : Fin S) :
    (cellSlot (tm := tm) t k i).length = Fintype.card (tm.Γ k) + 1 := by
  rw [cellSlot, List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_option]

/-! ## (3) The single machine constant `machineConst` -/

variable (tm) in
/-- The **machine constant**: a single number dominating every per-position cardinality of the
tableau (label, state, control-token, stack-symbol counts), used as the uniform coefficient of
the polynomial size bound. -/
noncomputable def machineConst : ℕ :=
  Fintype.card tm.Λ + Fintype.card tm.σ + Fintype.card tm.K
    + (relevantStmts tm).card + (∑ k : tm.K, Fintype.card (tm.Γ k)) + 2

omit [∀ k, Fintype (tm.Γ k)] in
/-- `Fintype.card (ContTok tm) = (relevantStmts tm).card + 1`. -/
theorem card_contTok : Fintype.card (ContTok tm) = (relevantStmts tm).card + 1 := by
  classical
  show Fintype.card (Option {q // q ∈ relevantStmts tm}) = _
  rw [Fintype.card_option, Fintype.card_coe]

/-- The control-token count is `≤ machineConst`. -/
theorem card_contTok_le_machineConst : Fintype.card (ContTok tm) ≤ machineConst tm := by
  rw [card_contTok, machineConst]; omega

/-- The label-slot width `card Λ + 1` is `≤ machineConst`. -/
theorem labelWidth_le_machineConst : Fintype.card tm.Λ + 1 ≤ machineConst tm := by
  rw [machineConst]; omega

/-- The state-slot width `card σ` is `≤ machineConst`. -/
theorem stateWidth_le_machineConst : Fintype.card tm.σ ≤ machineConst tm := by
  rw [machineConst]; omega

/-- Each cell-slot width `card (Γ k) + 1` is `≤ machineConst` (its summand bounds the sum). -/
theorem cellWidth_le_machineConst (k : tm.K) :
    Fintype.card (tm.Γ k) + 1 ≤ machineConst tm := by
  classical
  have hk : Fintype.card (tm.Γ k) ≤ ∑ k : tm.K, Fintype.card (tm.Γ k) :=
    Finset.single_le_sum (f := fun k => Fintype.card (tm.Γ k)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
  rw [machineConst]; omega

/-- `Fintype.card tm.K ≤ machineConst`. -/
theorem cardK_le_machineConst : Fintype.card tm.K ≤ machineConst tm := by
  rw [machineConst]; omega

variable (tm) in
/-- The **per-slot `exactlyOne` weight**: `machineConst + machineConst² · 2`, the uniform upper
bound on `totalLits (exactlyOne slot)` for any tableau slot (whose width is `≤ machineConst`). -/
noncomputable def slotWeight : ℕ := machineConst tm + (machineConst tm) ^ 2 * 2

/-- `exactlyOne (labelSlot t)` contributes `≤ slotWeight` literals. -/
theorem totalLits_exactlyOne_labelSlot_le (t : Fin (T + 1)) :
    totalLits (BooleanConstraints.exactlyOne (labelSlot (tm := tm) (S := S) t)) ≤ slotWeight tm := by
  rw [slotWeight]
  exact totalLits_exactlyOne_le_of_length _ _
    (by rw [length_labelSlot]; exact labelWidth_le_machineConst)

/-- `exactlyOne (stateSlot t)` contributes `≤ slotWeight` literals. -/
theorem totalLits_exactlyOne_stateSlot_le (t : Fin (T + 1)) :
    totalLits (BooleanConstraints.exactlyOne (stateSlot (tm := tm) (S := S) t)) ≤ slotWeight tm := by
  rw [slotWeight]
  exact totalLits_exactlyOne_le_of_length _ _
    (by rw [length_stateSlot]; exact stateWidth_le_machineConst)

/-- `exactlyOne (cellSlot t k i)` contributes `≤ slotWeight` literals. -/
theorem totalLits_exactlyOne_cellSlot_le (t : Fin (T + 1)) (k : tm.K) (i : Fin S) :
    totalLits (BooleanConstraints.exactlyOne (cellSlot (tm := tm) t k i)) ≤ slotWeight tm := by
  rw [slotWeight]
  exact totalLits_exactlyOne_le_of_length _ _
    (by rw [length_cellSlot]; exact cellWidth_le_machineConst k)

/-! ## (4) The consistency family bound -/

/-- **Consistency clauses size.** `totalLits (consistencyClauses tm T S) ≤
(T + 1) * (slotWeight * 2) + (T + 1) * (card K * (S * slotWeight))` — the label/state half is
`2` slots over `T+1` times, the cell half a triple `flatMap` over time × stacks × positions. -/
theorem consistencyClauses_size_le :
    totalLits (consistencyClauses tm T S) ≤
      (T + 1) * (slotWeight tm * 2)
        + (T + 1) * (Fintype.card tm.K * (S * slotWeight tm)) := by
  rw [consistencyClauses, totalLits_append]
  refine Nat.add_le_add ?_ ?_
  · -- label/state half: per `t`, two slots each `≤ slotWeight`
    refine totalLits_flatMap_le_of_group _ _ (T + 1) (slotWeight tm * 2)
      (by rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]) ?_
    intro t _
    rw [totalLits_append, Nat.mul_two]
    exact Nat.add_le_add (totalLits_exactlyOne_labelSlot_le t)
      (totalLits_exactlyOne_stateSlot_le t)
  · -- cell half: time × stacks × positions, each leaf slot `≤ slotWeight`
    refine totalLits_flatMap_le_of_group _ _ (T + 1)
      (Fintype.card tm.K * (S * slotWeight tm))
      (by rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]) ?_
    intro t _
    refine totalLits_flatMap_le_of_group _ _ (Fintype.card tm.K) (S * slotWeight tm)
      (by rw [Finset.length_toList, Finset.card_univ]) ?_
    intro k _
    refine totalLits_flatMap_le_of_group _ _ S (slotWeight tm)
      (by rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]) ?_
    intro i _
    exact totalLits_exactlyOne_cellSlot_le t k i

/-- **Register consistency size.** Over the continuation token block `V = ContTok tm`,
`totalLits (regConsistencyClauses T (ContTok tm)) ≤ (T + 1) * slotWeight`: one `exactlyOne`
per time step, each over `card (ContTok tm) ≤ machineConst` values. -/
theorem regConsistencyClauses_contTok_size_le :
    totalLits (regConsistencyClauses T (ContTok tm)) ≤ (T + 1) * slotWeight tm := by
  classical
  rw [regConsistencyClauses]
  refine totalLits_flatMap_le_of_group _ _ (T + 1) (slotWeight tm)
    (by rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]) ?_
  intro t _
  rw [slotWeight]
  refine totalLits_exactlyOne_le_of_length _ _ ?_
  rw [regSlot, List.length_map, Finset.length_toList, Finset.card_univ]
  exact card_contTok_le_machineConst

/-- **Full consistency size.** The combined consistency clauses (left-lifted main + right-lifted
register) preserve literal counts under lifting, so the bound is the sum of the two family
bounds — a degree-`3` polynomial in `(T, S)` with `slotWeight` (a `machineConst²`-scale constant)
coefficients. -/
theorem fullConsistencyClauses_size_le :
    totalLits (fullConsistencyClauses tm T S (ContTok tm)) ≤
      ((T + 1) * (slotWeight tm * 2)
        + (T + 1) * (Fintype.card tm.K * (S * slotWeight tm)))
      + (T + 1) * slotWeight tm := by
  rw [fullConsistencyClauses, totalLits_append, totalLits_liftClausesL, totalLits_liftClausesR]
  exact Nat.add_le_add consistencyClauses_size_le regConsistencyClauses_contTok_size_le

/-! ## (5) The init / accept family bounds (unit clauses) -/

/-- `totalLits` of a `map` producing one unit clause per element is the element count: each
cell clause is `[(coordVar …, true)]`, a single literal. -/
theorem totalLits_map_unit {n : ℕ} {α : Type*} (l : List α) (h : α → Fin n) :
    totalLits (l.map (fun a => [(h a, true)])) = l.length := by
  rw [totalLits_eq_sum, List.map_map]
  simp only [Function.comp_def, List.length_singleton, List.map_const', List.sum_replicate,
    smul_eq_mul, mul_one]

/-- **Init main clauses size.** `totalLits (initClauses tm T S input) = 2 + card K * S`: the
label/state unit clauses plus one unit clause per `(k, i)` cell. -/
theorem totalLits_initClauses :
    ∀ input : List (tm.Γ tm.k₀),
      totalLits (initClauses tm T S input) = 2 + Fintype.card tm.K * S := by
  classical
  intro input
  rw [initClauses]
  -- two leading unit clauses, then the cell flatMap
  rw [totalLits_cons, totalLits_cons]
  -- the cell flatMap: per stack `k`, `S` unit clauses
  rw [totalLits_flatMap]
  have hgroup : ∀ k : tm.K,
      totalLits ((Finset.univ : Finset (Fin S)).toList.map
        (fun i => [(coordVar (cellCoord (0 : Fin (T + 1)) k i
          (((initList tm input).stk k)[(i : ℕ)]?)), true)])) = S := by
    intro k
    rw [totalLits_map_unit, Finset.length_toList, Finset.card_univ, Fintype.card_fin]
  rw [List.map_congr_left (fun k _ => hgroup k)]
  rw [List.map_const', List.sum_replicate, Finset.length_toList, Finset.card_univ, smul_eq_mul]
  simp only [List.length_singleton]
  ring

/-- **Combined init clauses size.** `totalLits (initClausesC tm T S input) = 3 + card K * S`:
the lifted main init clauses plus one continuation unit clause. -/
theorem initClausesC_size_le (input : List (tm.Γ tm.k₀)) :
    totalLits (initClausesC tm T S input) ≤ 3 + Fintype.card tm.K * S := by
  -- re-elaborate the defining append with the homogeneous `++` instance so `totalLits_append`
  -- applies (the stored `initClausesC` append displays heterogeneously)
  set L := BooleanConstraints.liftClausesL (m := regNumVars T (ContTok tm))
    (initClauses tm T S input) with hL
  set c : Clause (numVars tm T S + regNumVars T (ContTok tm)) :=
    [(contVar (tm := tm) (S := S) (0 : Fin (T + 1))
      (some ⟨tm.m tm.main, program_mem_relevant tm tm.main⟩ : ContTok tm), true)] with hc
  have h : totalLits (initClausesC tm T S input) = totalLits (L ++ [c]) :=
    congrArg totalLits rfl
  rw [h, totalLits_append, totalLits_singleton, hL, totalLits_liftClausesL, totalLits_initClauses,
    hc, List.length_singleton]
  omega

/-- **Halt main clauses size.** `totalLits (haltClauses tm T S acceptOutput) = 2 + card K * S`
(mirror of `initClauses`). -/
theorem totalLits_haltClauses :
    ∀ acceptOutput : List (tm.Γ tm.k₁),
      totalLits (haltClauses tm T S acceptOutput) = 2 + Fintype.card tm.K * S := by
  classical
  intro acceptOutput
  rw [haltClauses]
  rw [totalLits_cons, totalLits_cons]
  rw [totalLits_flatMap]
  have hgroup : ∀ k : tm.K,
      totalLits ((Finset.univ : Finset (Fin S)).toList.map
        (fun i => [(coordVar (cellCoord (Fin.last T) k i
          (((haltList tm acceptOutput).stk k)[(i : ℕ)]?)), true)])) = S := by
    intro k
    rw [totalLits_map_unit, Finset.length_toList, Finset.card_univ, Fintype.card_fin]
  rw [List.map_congr_left (fun k _ => hgroup k)]
  rw [List.map_const', List.sum_replicate, Finset.length_toList, Finset.card_univ, smul_eq_mul]
  simp only [List.length_singleton]
  ring

/-- **Combined accept clauses size.** `totalLits (acceptClausesC tm T S acceptOutput) ≤
3 + card K * S` (mirror of `initClausesC`). -/
theorem acceptClausesC_size_le (acceptOutput : List (tm.Γ tm.k₁)) :
    totalLits (acceptClausesC tm T S acceptOutput) ≤ 3 + Fintype.card tm.K * S := by
  set L := BooleanConstraints.liftClausesL (m := regNumVars T (ContTok tm))
    (haltClauses tm T S acceptOutput) with hL
  set c : Clause (numVars tm T S + regNumVars T (ContTok tm)) :=
    [(contVar (tm := tm) (S := S) (Fin.last T) (none : ContTok tm), true)] with hc
  have h : totalLits (acceptClausesC tm T S acceptOutput) = totalLits (L ++ [c]) :=
    congrArg totalLits rfl
  rw [h, totalLits_append, totalLits_singleton, hL, totalLits_liftClausesL, totalLits_haltClauses,
    hc, List.length_singleton]
  omega

/-! ## (6) Transition gadget primitives: `funClauses` / `funClauses₂` / `conditionOn` -/

/-- `funClauses` has `Fintype.card A` clauses (one implication per input value). -/
theorem length_funClauses {n : ℕ} {A B : Type} [Fintype A] (inVar : A → Fin n)
    (outVar : B → Fin n) (f : A → B) :
    (BooleanConstraints.funClauses inVar outVar f).length = Fintype.card A := by
  rw [BooleanConstraints.funClauses, List.length_map, Finset.length_toList, Finset.card_univ]

/-- `funClauses` clauses are 2-wide (each is an `implies`), so `totalLits ≤ 2 * card A`. -/
theorem totalLits_funClauses_le {n : ℕ} {A B : Type} [Fintype A] (inVar : A → Fin n)
    (outVar : B → Fin n) (f : A → B) :
    totalLits (BooleanConstraints.funClauses inVar outVar f) ≤ Fintype.card A * 2 := by
  refine le_trans (totalLits_le_of_width _ 2 ?_) ?_
  · intro c hc
    obtain ⟨a, rfl⟩ := (BooleanConstraints.mem_funClauses inVar outVar f c).1 hc
    rfl
  · rw [length_funClauses]

/-- `funClauses₂` has `card A * card B` clauses (one implication per input pair). -/
theorem length_funClauses₂ {n : ℕ} {A B C : Type} [Fintype A] [Fintype B] (inA : A → Fin n)
    (inB : B → Fin n) (outVar : C → Fin n) (g : A → B → C) :
    (BooleanConstraints.funClauses₂ inA inB outVar g).length = Fintype.card A * Fintype.card B := by
  rw [BooleanConstraints.funClauses₂, List.length_map, Finset.length_toList, Finset.card_univ,
    Fintype.card_prod]

/-- `funClauses₂` clauses are 3-wide (each is an `implies₂`), so `totalLits ≤ 3 * card A * card B`. -/
theorem totalLits_funClauses₂_le {n : ℕ} {A B C : Type} [Fintype A] [Fintype B] (inA : A → Fin n)
    (inB : B → Fin n) (outVar : C → Fin n) (g : A → B → C) :
    totalLits (BooleanConstraints.funClauses₂ inA inB outVar g)
      ≤ Fintype.card A * Fintype.card B * 3 := by
  refine le_trans (totalLits_le_of_width _ 3 ?_) ?_
  · intro c hc
    obtain ⟨a, b, rfl⟩ := (BooleanConstraints.mem_funClauses₂ inA inB outVar g c).1 hc
    rfl
  · rw [length_funClauses₂]

/-- `conditionOn` preserves the clause count (it guards each clause in place). -/
@[simp] theorem length_conditionOn {n : ℕ} (v : Fin n) (cs : List (Clause n)) :
    (BooleanConstraints.conditionOn v cs).length = cs.length := by
  rw [BooleanConstraints.conditionOn, List.length_map]

/-- `conditionOn` adds one literal (the guard) to each clause: `totalLits` grows by `cs.length`. -/
theorem totalLits_conditionOn {n : ℕ} (v : Fin n) (cs : List (Clause n)) :
    totalLits (BooleanConstraints.conditionOn v cs) = totalLits cs + cs.length := by
  induction cs with
  | nil => simp [BooleanConstraints.conditionOn]
  | cons c cs ih =>
    rw [BooleanConstraints.conditionOn, List.map_cons, totalLits_cons, ← BooleanConstraints.conditionOn,
      ih, totalLits_cons, List.length_cons, List.length_cons]
    omega

/-- **`flatMap` clause-count bound.** If `l` has length `≤ N` and each group `g a` has
`≤ C` clauses, then `(l.flatMap g).length ≤ N * C`. -/
theorem length_flatMap_le {n : ℕ} {α : Type*} (l : List α) (g : α → List (Clause n))
    (N C : ℕ) (hN : l.length ≤ N) (hg : ∀ a ∈ l, (g a).length ≤ C) :
    (l.flatMap g).length ≤ N * C := by
  rw [List.length_flatMap]
  refine le_trans (List.sum_le_card_nsmul (l.map (fun a => (g a).length)) C ?_) ?_
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact hg a ha
  · rw [List.length_map, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hN

/-! ## (7) State-gadget bounds (uniform over the head statement) -/

open Turing.TM2.Stmt

/-- `card σ ≤ machineConst ^ 2`. -/
private theorem stateWidth_le_machineConst_sq : Fintype.card tm.σ ≤ machineConst tm ^ 2 :=
  stateWidth_le_machineConst.trans (Nat.le_self_pow (by norm_num) _)

/-- `2 ≤ machineConst` (the `+ 2` summand), so `machineConst` is positive. -/
theorem two_le_machineConst : 2 ≤ machineConst tm := by rw [machineConst]; omega

/-- **State-gadget uniform bound.** Over every continuation token, `stateGadgetFor cont t hS0` has
`≤ machineConst²` clauses and `≤ machineConst² * 3` literals: `funClauses` over `σ`
(`keep`/`load`) or `funClauses₂` over `σ × Option (Γ k)` (`peek`/`pop`). -/
theorem stateGadgetFor_bounds (cont : ContTok tm) (t : Fin T) (hS0 : 0 < S) :
    (stateGadgetFor cont t hS0).length ≤ machineConst tm ^ 2
      ∧ totalLits (stateGadgetFor cont t hS0) ≤ machineConst tm ^ 2 * 3 := by
  -- a single bound for the `funClauses` (state-only) `keep`/`load` gadgets
  have hkeep : (keepStateClauses (tm := tm) (S := S) t).length ≤ machineConst tm ^ 2
      ∧ totalLits (keepStateClauses (tm := tm) (S := S) t) ≤ machineConst tm ^ 2 * 3 := by
    rw [keepStateClauses]
    refine ⟨?_, ?_⟩
    · rw [length_funClauses]; exact stateWidth_le_machineConst_sq
    · refine le_trans (totalLits_funClauses_le _ _ _) ?_
      calc Fintype.card tm.σ * 2 ≤ machineConst tm ^ 2 * 2 :=
            Nat.mul_le_mul_right 2 stateWidth_le_machineConst_sq
        _ ≤ machineConst tm ^ 2 * 3 := Nat.mul_le_mul_left _ (by omega)
  have hload : ∀ a : tm.σ → tm.σ,
      (loadStateClauses (tm := tm) (S := S) t a).length ≤ machineConst tm ^ 2
      ∧ totalLits (loadStateClauses (tm := tm) (S := S) t a) ≤ machineConst tm ^ 2 * 3 := by
    intro a
    rw [loadStateClauses]
    refine ⟨?_, ?_⟩
    · rw [length_funClauses]; exact stateWidth_le_machineConst_sq
    · refine le_trans (totalLits_funClauses_le _ _ _) ?_
      calc Fintype.card tm.σ * 2 ≤ machineConst tm ^ 2 * 2 :=
            Nat.mul_le_mul_right 2 stateWidth_le_machineConst_sq
        _ ≤ machineConst tm ^ 2 * 3 := Nat.mul_le_mul_left _ (by omega)
  -- the `funClauses₂` (peek/pop) gadget: `card σ * card (Option (Γ k))` clauses
  have hpeek : ∀ (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ),
      (peekStateClauses (tm := tm) (S := S) t k f hS0).length ≤ machineConst tm ^ 2
      ∧ totalLits (peekStateClauses (tm := tm) (S := S) t k f hS0) ≤ machineConst tm ^ 2 * 3 := by
    intro k f
    have hcard : Fintype.card tm.σ * Fintype.card (Option (tm.Γ k)) ≤ machineConst tm ^ 2 := by
      rw [Fintype.card_option, sq]
      exact Nat.mul_le_mul stateWidth_le_machineConst (cellWidth_le_machineConst k)
    rw [peekStateClauses]
    refine ⟨?_, ?_⟩
    · rw [length_funClauses₂]; exact hcard
    · refine le_trans (totalLits_funClauses₂_le _ _ _ _) ?_
      exact Nat.mul_le_mul_right 3 hcard
  -- dispatch on the head statement
  cases cont with
  | none => exact hkeep
  | some w =>
    obtain ⟨q, hq⟩ := w
    cases q with
    | push k f q => exact hkeep
    | branch f q₁ q₂ => exact hkeep
    | goto f => exact hkeep
    | halt => exact hkeep
    | load a q => exact hload a
    | peek k f q => exact hpeek k f
    | pop k f q => exact hpeek k f

/-! ## (8) Cell-gadget bounds (uniform over the head statement) -/

/-- `card (Option (tm.Γ k)) ≤ machineConst`. -/
private theorem cardOptionΓ_le_machineConst (k : tm.K) :
    Fintype.card (Option (tm.Γ k)) ≤ machineConst tm := by
  rw [Fintype.card_option]; exact cellWidth_le_machineConst k

/-- **`keepCellClauses` bound.** Per position a `funClauses` over `Option (Γ k)`
(`≤ machineConst` clauses, 2-wide): `≤ S * machineConst` clauses, `≤ S * machineConst * 2`
literals — both `≤ (S+1) * machineConst [* 2]`. -/
theorem keepCellClauses_bounds (t : Fin T) (k : tm.K) :
    (keepCellClauses (tm := tm) (S := S) t k).length ≤ (S + 1) * machineConst tm
      ∧ totalLits (keepCellClauses (tm := tm) (S := S) t k) ≤ (S + 1) * machineConst tm * 2 := by
  rw [keepCellClauses]
  refine ⟨?_, ?_⟩
  · refine le_trans (length_flatMap_le _ _ S (machineConst tm)
      (by rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]) ?_) ?_
    · intro i _; rw [length_funClauses]; exact cardOptionΓ_le_machineConst k
    · exact Nat.mul_le_mul_right _ (by omega)
  · refine le_trans (totalLits_flatMap_le_of_group _ _ S (machineConst tm * 2)
      (by rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]) ?_) ?_
    · intro i _
      refine le_trans (totalLits_funClauses_le _ _ _) ?_
      exact Nat.mul_le_mul_right 2 (cardOptionΓ_le_machineConst k)
    · rw [mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)

/-- **`popCellClauses` bound.** Per position a `funClauses` shift (`≤ machineConst`, 2-wide) or a
unit clause: `≤ S * machineConst` clauses, `≤ S * machineConst * 2` literals. -/
theorem popCellClauses_bounds (t : Fin T) (k : tm.K) :
    (popCellClauses (tm := tm) (S := S) t k).length ≤ (S + 1) * machineConst tm
      ∧ totalLits (popCellClauses (tm := tm) (S := S) t k) ≤ (S + 1) * machineConst tm * 2 := by
  rw [popCellClauses]
  refine ⟨?_, ?_⟩
  · refine le_trans (length_flatMap_le _ _ S (machineConst tm)
      (by rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]) ?_) ?_
    · intro i _
      split
      · simp only [popShiftClauses, length_funClauses]; exact cardOptionΓ_le_machineConst k
      · rw [machineConst]; simp only [List.length_singleton]; omega
    · exact Nat.mul_le_mul_right _ (by omega)
  · refine le_trans (totalLits_flatMap_le_of_group _ _ S (machineConst tm * 2)
      (by rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]) ?_) ?_
    · intro i _
      split
      · simp only [popShiftClauses]
        refine le_trans (totalLits_funClauses_le _ _ _) ?_
        exact Nat.mul_le_mul_right 2 (cardOptionΓ_le_machineConst k)
      · rw [totalLits_singleton, List.length_singleton, machineConst]; omega
    · rw [mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)

/-- **`pushCellClauses` bound.** A bottom `funClauses` over `σ` (`≤ machineConst`) plus per-position
shift `funClauses` (`≤ machineConst`): `≤ (S+1) * machineConst` clauses, `≤ (S+1) * machineConst * 2`
literals. -/
theorem pushCellClauses_bounds (t : Fin T) (k : tm.K) (f : tm.σ → tm.Γ k) :
    (pushCellClauses (tm := tm) (S := S) t k f).length ≤ (S + 1) * machineConst tm
      ∧ totalLits (pushCellClauses (tm := tm) (S := S) t k f) ≤ (S + 1) * machineConst tm * 2 := by
  rw [pushCellClauses]
  -- the shift `flatMap` part bounds
  have hshiftLen : ((Finset.univ : Finset (Fin S)).toList.flatMap
      (fun i : Fin S => if h : (i : ℕ) + 1 < S then pushShiftClauses t k i h
        else ([] : List (Clause (numVars tm T S))))).length ≤ S * machineConst tm := by
    refine length_flatMap_le _ _ S (machineConst tm)
      (by rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]) ?_
    intro i _
    split
    · simp only [pushShiftClauses, length_funClauses]; exact cardOptionΓ_le_machineConst k
    · simp
  have hshiftLits : totalLits ((Finset.univ : Finset (Fin S)).toList.flatMap
      (fun i : Fin S => if h : (i : ℕ) + 1 < S then pushShiftClauses t k i h
        else ([] : List (Clause (numVars tm T S))))) ≤ S * (machineConst tm * 2) := by
    refine totalLits_flatMap_le_of_group _ _ S (machineConst tm * 2)
      (by rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]) ?_
    intro i _
    split
    · simp only [pushShiftClauses]
      refine le_trans (totalLits_funClauses_le _ _ _) ?_
      exact Nat.mul_le_mul_right 2 (cardOptionΓ_le_machineConst k)
    · simp
  refine ⟨?_, ?_⟩
  · rw [List.length_append]
    have hbot : (if h0 : 0 < S then pushBottomClauses t k f h0
        else ([] : List (Clause (numVars tm T S)))).length ≤ machineConst tm := by
      split
      · simp only [pushBottomClauses, length_funClauses]; exact stateWidth_le_machineConst
      · simp
    calc _ ≤ machineConst tm + S * machineConst tm := Nat.add_le_add hbot hshiftLen
      _ ≤ (S + 1) * machineConst tm := by ring_nf; omega
  · rw [totalLits_append]
    have hbot : totalLits (if h0 : 0 < S then pushBottomClauses t k f h0
        else ([] : List (Clause (numVars tm T S)))) ≤ machineConst tm * 2 := by
      split
      · simp only [pushBottomClauses]
        refine le_trans (totalLits_funClauses_le _ _ _) ?_
        exact Nat.mul_le_mul_right 2 stateWidth_le_machineConst
      · simp
    calc _ ≤ machineConst tm * 2 + S * (machineConst tm * 2) :=
          Nat.add_le_add hbot hshiftLits
      _ ≤ (S + 1) * machineConst tm * 2 := by ring_nf; omega

/-- A `flatMap` of `keepCellClauses` over a stack-list of length `≤ N`: `≤ N * (S+1) * machineConst`
clauses and `≤ N * (2 * (S+1) * machineConst)` literals. -/
theorem keepCellClauses_flatMap_bounds (t : Fin T) (ks : List tm.K) (N : ℕ) (hN : ks.length ≤ N) :
    (ks.flatMap (fun k' => keepCellClauses (tm := tm) (S := S) t k')).length
        ≤ N * ((S + 1) * machineConst tm)
      ∧ totalLits (ks.flatMap (fun k' => keepCellClauses (tm := tm) (S := S) t k'))
        ≤ N * ((S + 1) * machineConst tm * 2) := by
  refine ⟨?_, ?_⟩
  · exact length_flatMap_le _ _ N ((S + 1) * machineConst tm) hN
      (fun k' _ => (keepCellClauses_bounds t k').1)
  · exact totalLits_flatMap_le_of_group _ _ N ((S + 1) * machineConst tm * 2) hN
      (fun k' _ => (keepCellClauses_bounds t k').2)

/-- **Cell-gadget uniform bound.** Over every continuation token, `cellGadgetFor cont t` has
`≤ (S+1) * machineConst²` clauses and `≤ (S+1) * machineConst² * 2` literals: `keepCellClauses`
over all (or all-but-one) stacks, plus one `pushCellClauses`/`popCellClauses` on the active stack. -/
theorem cellGadgetFor_bounds (cont : ContTok tm) (t : Fin T) :
    (cellGadgetFor (S := S) cont t).length ≤ (S + 1) * machineConst tm ^ 2
      ∧ totalLits (cellGadgetFor (S := S) cont t) ≤ (S + 1) * machineConst tm ^ 2 * 2 := by
  classical
  set MC := machineConst tm with hMC
  have hMC2 : 2 ≤ MC := two_le_machineConst
  -- a keep-`flatMap` over a `card ≤ machineConst` stack-list: `≤ machineConst*(S+1)*MC` etc.
  have hkeepK : ∀ (ks : List tm.K), ks.length ≤ Fintype.card tm.K →
      (ks.flatMap (fun k' => keepCellClauses (tm := tm) (S := S) t k')).length
          ≤ MC * ((S + 1) * MC)
      ∧ totalLits (ks.flatMap (fun k' => keepCellClauses (tm := tm) (S := S) t k'))
          ≤ MC * ((S + 1) * MC * 2) := by
    intro ks hks
    exact keepCellClauses_flatMap_bounds t ks MC (hks.trans cardK_le_machineConst)
  -- the all-keep case (over all `K`)
  have hallkeep : ((Finset.univ : Finset tm.K).toList.flatMap
        (fun k' => keepCellClauses (tm := tm) (S := S) t k')).length
          ≤ (S + 1) * MC ^ 2
      ∧ totalLits ((Finset.univ : Finset tm.K).toList.flatMap
        (fun k' => keepCellClauses (tm := tm) (S := S) t k'))
          ≤ (S + 1) * MC ^ 2 * 2 := by
    obtain ⟨h1, h2⟩ := hkeepK _ (by rw [Finset.length_toList, Finset.card_univ])
    have e1 : MC * ((S + 1) * MC) = (S + 1) * MC ^ 2 := by rw [sq]; ring
    have e2 : MC * ((S + 1) * MC * 2) = (S + 1) * MC ^ 2 * 2 := by rw [sq]; ring
    exact ⟨e1 ▸ h1, e2 ▸ h2⟩
  -- the active (push/pop) case: leaf on stack `k` + keep on the `K.erase k` stacks
  have hactive : ∀ (k : tm.K) (leafLen leafLits : ℕ),
      leafLen ≤ (S + 1) * MC → leafLits ≤ (S + 1) * MC * 2 →
      leafLen + (((Finset.univ : Finset tm.K).erase k).toList.flatMap
          (fun k' => keepCellClauses (tm := tm) (S := S) t k')).length ≤ (S + 1) * MC ^ 2
      ∧ leafLits + totalLits (((Finset.univ : Finset tm.K).erase k).toList.flatMap
          (fun k' => keepCellClauses (tm := tm) (S := S) t k')) ≤ (S + 1) * MC ^ 2 * 2 := by
    intro k leafLen leafLits hLen hLits
    have hcardK : (((Finset.univ : Finset tm.K).erase k).card + 1) ≤ MC := by
      have : ((Finset.univ : Finset tm.K).erase k).card + 1 ≤ Fintype.card tm.K := by
        have := Finset.card_erase_add_one (Finset.mem_univ k)
        rw [Finset.card_univ] at this; omega
      exact this.trans cardK_le_machineConst
    obtain ⟨h1, h2⟩ := keepCellClauses_flatMap_bounds t
      (((Finset.univ : Finset tm.K).erase k).toList) (((Finset.univ : Finset tm.K).erase k).card)
      (by rw [Finset.length_toList])
    set e := ((Finset.univ : Finset tm.K).erase k).card with he
    refine ⟨?_, ?_⟩
    · refine (Nat.add_le_add hLen h1).trans ?_
      -- `(S+1)*MC + e*(S+1)*MC = (e+1)*(S+1)*MC ≤ MC*(S+1)*MC = (S+1)*MC²`
      have : (S + 1) * MC + e * ((S + 1) * MC) = (e + 1) * ((S + 1) * MC) := by ring
      rw [this, sq]
      calc (e + 1) * ((S + 1) * MC) ≤ MC * ((S + 1) * MC) :=
            Nat.mul_le_mul_right _ hcardK
        _ = (S + 1) * (MC * MC) := by ring
    · refine (Nat.add_le_add hLits h2).trans ?_
      have : (S + 1) * MC * 2 + e * ((S + 1) * MC * 2) = (e + 1) * ((S + 1) * MC * 2) := by ring
      rw [this, sq]
      calc (e + 1) * ((S + 1) * MC * 2) ≤ MC * ((S + 1) * MC * 2) :=
            Nat.mul_le_mul_right _ hcardK
        _ = (S + 1) * (MC * MC) * 2 := by ring
  cases cont with
  | none => exact hallkeep
  | some w =>
    obtain ⟨q, hq⟩ := w
    cases q with
    | push k f q =>
      rw [cellGadgetFor]
      rw [List.length_append, totalLits_append]
      exact ⟨(hactive k _ _ (pushCellClauses_bounds t k f).1 (pushCellClauses_bounds t k f).2).1,
        (hactive k _ _ (pushCellClauses_bounds t k f).1 (pushCellClauses_bounds t k f).2).2⟩
    | branch f q₁ q₂ => exact hallkeep
    | goto f => exact hallkeep
    | halt => exact hallkeep
    | load a q => exact hallkeep
    | peek k f q => exact hallkeep
    | pop k f q =>
      rw [cellGadgetFor]
      rw [List.length_append, totalLits_append]
      exact ⟨(hactive k _ _ (popCellClauses_bounds t k).1 (popCellClauses_bounds t k).2).1,
        (hactive k _ _ (popCellClauses_bounds t k).1 (popCellClauses_bounds t k).2).2⟩

/-! ## (9) The transition family bound -/

section Transition

open scoped Classical

/-- **`contTransClauses` bound.** A single `funClauses₂` over `ContTok × σ`: `≤ machineConst²`
clauses (3-wide), so `totalLits ≤ machineConst² * 3`. -/
theorem contTransClauses_size_le (t : Fin T) :
    totalLits (contTransClauses tm T S t) ≤ machineConst tm ^ 2 * 3 := by
  rw [contTransClauses]
  refine le_trans (totalLits_funClauses₂_le _ _ _ _) ?_
  rw [sq]
  exact Nat.mul_le_mul_right 3
    (Nat.mul_le_mul card_contTok_le_machineConst stateWidth_le_machineConst)

/-- A guarded, lifted gadget over the continuation token block: its `totalLits` is the gadget's
`totalLits` plus its clause count (the guards). -/
theorem totalLits_conditionOn_liftClausesL {n m : ℕ} (v : Fin (n + m)) (cs : List (Clause n)) :
    totalLits (BooleanConstraints.conditionOn v (BooleanConstraints.liftClausesL (m := m) cs))
      = totalLits cs + cs.length := by
  rw [totalLits_conditionOn, totalLits_liftClausesL, length_liftClausesL]

/-- **`stateTransClauses` bound.** `flatMap` over `≤ machineConst` continuation tokens of a guarded,
lifted state gadget (`≤ machineConst²` clauses, `≤ 3·machineConst²` literals; the guard adds the
clause count): `totalLits ≤ machineConst * (machineConst² * 4)`. -/
theorem stateTransClauses_size_le (t : Fin T) (hS0 : 0 < S) :
    totalLits (stateTransClauses tm S t hS0) ≤ machineConst tm * (machineConst tm ^ 2 * 4) := by
  rw [stateTransClauses]
  refine totalLits_flatMap_le_of_group _ _ (machineConst tm) (machineConst tm ^ 2 * 4)
    (by rw [Finset.length_toList, Finset.card_univ]; exact card_contTok_le_machineConst) ?_
  intro cont _
  rw [totalLits_conditionOn_liftClausesL]
  obtain ⟨hlen, hlits⟩ := stateGadgetFor_bounds cont t hS0
  -- gadget lits + gadget count ≤ 3·MC² + MC² = 4·MC²
  calc totalLits (stateGadgetFor cont t hS0) + (stateGadgetFor cont t hS0).length
      ≤ machineConst tm ^ 2 * 3 + machineConst tm ^ 2 := Nat.add_le_add hlits hlen
    _ ≤ machineConst tm ^ 2 * 4 := by ring_nf; omega

/-- **`cellTransClauses` bound.** `flatMap` over `≤ machineConst` continuation tokens of a guarded,
lifted cell gadget (`≤ (S+1)·machineConst²` clauses, `≤ 2(S+1)·machineConst²` literals; the guard
adds the clause count): `totalLits ≤ machineConst * ((S+1) · machineConst² * 3)`. -/
theorem cellTransClauses_size_le (t : Fin T) :
    totalLits (cellTransClauses tm S t)
      ≤ machineConst tm * ((S + 1) * machineConst tm ^ 2 * 3) := by
  rw [cellTransClauses]
  refine totalLits_flatMap_le_of_group _ _ (machineConst tm) ((S + 1) * machineConst tm ^ 2 * 3)
    (by rw [Finset.length_toList, Finset.card_univ]; exact card_contTok_le_machineConst) ?_
  intro cont _
  rw [totalLits_conditionOn_liftClausesL]
  obtain ⟨hlen, hlits⟩ := cellGadgetFor_bounds (S := S) cont t
  calc totalLits (cellGadgetFor (S := S) cont t) + (cellGadgetFor (S := S) cont t).length
      ≤ (S + 1) * machineConst tm ^ 2 * 2 + (S + 1) * machineConst tm ^ 2 :=
        Nat.add_le_add hlits hlen
    _ ≤ (S + 1) * machineConst tm ^ 2 * 3 := by ring_nf; omega

/-- **Per-time transition bound.** `unifTransClauses tm S t hS0` is the append of the continuation,
state, and cell transition clauses: `totalLits ≤ (S+1) * machineConst³ * 10` (a single generous
machine-and-`S` bound dominating all three: `3 + 4 + 3` units of `(S+1)·machineConst³`). -/
theorem unifTransClauses_size_le (t : Fin T) (hS0 : 0 < S) :
    totalLits (unifTransClauses tm S t hS0) ≤ (S + 1) * machineConst tm ^ 3 * 10 := by
  rw [unifTransClauses, totalLits_append, totalLits_append]
  have hcont := contTransClauses_size_le (tm := tm) (S := S) t
  have hstate := stateTransClauses_size_le (tm := tm) t hS0
  have hcell := cellTransClauses_size_le (tm := tm) (S := S) t
  set MC := machineConst tm with hMC
  set P := (S + 1) * MC ^ 3 with hP
  -- bound each of the three pieces by a multiple of `P = (S+1)·MC³`
  have h3 : MC * MC ^ 2 = MC ^ 3 := by ring
  have hSpos : MC ^ 3 ≤ (S + 1) * MC ^ 3 := Nat.le_mul_of_pos_left (MC ^ 3) (by omega)
  have hcontle : MC ^ 2 * 3 ≤ P * 3 := by
    rw [hP]
    have hMCpos : 1 ≤ MC := by rw [hMC]; have := two_le_machineConst (tm := tm); omega
    have : MC ^ 2 ≤ (S + 1) * MC ^ 3 :=
      (Nat.pow_le_pow_right hMCpos (by omega)).trans hSpos
    exact Nat.mul_le_mul_right 3 this
  have hstatele : MC * (MC ^ 2 * 4) ≤ P * 4 := by
    rw [hP, show MC * (MC ^ 2 * 4) = MC * MC ^ 2 * 4 by ring, h3]
    exact Nat.mul_le_mul_right 4 hSpos
  have hcelle : MC * ((S + 1) * MC ^ 2 * 3) = P * 3 := by
    rw [hP, show MC * ((S + 1) * MC ^ 2 * 3) = (S + 1) * (MC * MC ^ 2) * 3 by ring, h3]
  refine le_trans (Nat.add_le_add (Nat.add_le_add hcont hstate) hcell) ?_
  rw [hcelle]
  calc MC ^ 2 * 3 + MC * (MC ^ 2 * 4) + P * 3 ≤ P * 3 + P * 4 + P * 3 :=
        Nat.add_le_add (Nat.add_le_add hcontle hstatele) (le_refl _)
    _ = P * 10 := by ring

/-- **Transition family size.** The flat-map over `Fin T` of the per-time transition clauses:
`totalLits ≤ T * ((S+1) * machineConst³ * 10)` — `T` time steps, each `≤ (S+1) * machineConst³ * 10`. -/
theorem transClauses_size_le (hS0 : 0 < S) :
    totalLits ((Finset.univ : Finset (Fin T)).toList.flatMap
        (fun t => unifTransClauses tm S t hS0))
      ≤ T * ((S + 1) * machineConst tm ^ 3 * 10) := by
  refine totalLits_flatMap_le_of_group _ _ T ((S + 1) * machineConst tm ^ 3 * 10)
    (by rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]) ?_
  intro t _
  exact unifTransClauses_size_le t hS0

end Transition

/-! ## (10) The variable-count bound -/

/-- `∑ₖ (card (Γ k) + 1) ≤ machineConst * 2`: the stack-symbol sum plus the stack count, both
`≤ machineConst`. -/
theorem sum_cellWidth_le : (∑ k : tm.K, (Fintype.card (tm.Γ k) + 1)) ≤ machineConst tm * 2 := by
  classical
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  have h1 : (∑ k : tm.K, Fintype.card (tm.Γ k)) ≤ machineConst tm := by rw [machineConst]; omega
  have h2 : Fintype.card tm.K ≤ machineConst tm := cardK_le_machineConst
  omega

/-- **Combined variable-count bound.** `fullNumVars tm T S (ContTok tm) ≤
(T+1) * (S+1) * machineConst² * 4` — a generous degree-2-in-`(T,S)` machine polynomial. -/
theorem fullNumVars_le :
    fullNumVars tm T S (ContTok tm) ≤ (T + 1) * (S + 1) * machineConst tm ^ 2 * 4 := by
  classical
  rw [fullNumVars, regNumVars_eq]
  set MC := machineConst tm with hMC
  -- bound `numVars` via `TableauSchema.numVars_le`
  have hnv : numVars tm T S
      ≤ (T + 1) * (Fintype.card tm.Λ + Fintype.card tm.σ + 1)
        + (T + 1) * S * ∑ k : tm.K, (Fintype.card (tm.Γ k) + 1) := numVars_le tm T S
  -- the label/state weight ≤ MC, the cell weight ≤ 2·MC
  have hls : Fintype.card tm.Λ + Fintype.card tm.σ + 1 ≤ MC := by rw [hMC, machineConst]; omega
  have hcw : (∑ k : tm.K, (Fintype.card (tm.Γ k) + 1)) ≤ MC * 2 := sum_cellWidth_le
  have hreg : Fintype.card (ContTok tm) ≤ MC := card_contTok_le_machineConst
  -- assemble
  have hbound : numVars tm T S + (T + 1) * Fintype.card (ContTok tm)
      ≤ (T + 1) * MC + (T + 1) * S * (MC * 2) + (T + 1) * MC := by
    refine Nat.add_le_add (le_trans hnv (Nat.add_le_add ?_ ?_)) ?_
    · exact Nat.mul_le_mul_left _ hls
    · exact Nat.mul_le_mul_left _ hcw
    · exact Nat.mul_le_mul_left _ hreg
  refine le_trans hbound ?_
  -- (T+1)·MC + (T+1)·S·2·MC + (T+1)·MC ≤ (T+1)(S+1)·MC²·4
  have hsq : MC ≤ MC ^ 2 := Nat.le_self_pow (by omega) MC
  set Q := (T + 1) * (S + 1) * MC ^ 2 with hQ
  -- each of the three terms is `≤ Q` (the middle one `≤ 2Q`); total `≤ 4Q`
  have t1 : (T + 1) * MC ≤ Q := by
    rw [hQ]
    calc (T + 1) * MC ≤ (T + 1) * MC ^ 2 := Nat.mul_le_mul_left _ hsq
      _ ≤ (T + 1) * (S + 1) * MC ^ 2 := by
          rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  have t2 : (T + 1) * S * (MC * 2) ≤ Q * 2 := by
    rw [hQ]
    calc (T + 1) * S * (MC * 2) = (T + 1) * S * MC * 2 := by ring
      _ ≤ (T + 1) * (S + 1) * MC ^ 2 * 2 := by
          refine Nat.mul_le_mul_right 2 ?_
          calc (T + 1) * S * MC ≤ (T + 1) * (S + 1) * MC := by
                exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
            _ ≤ (T + 1) * (S + 1) * MC ^ 2 := Nat.mul_le_mul_left _ hsq
  calc (T + 1) * MC + (T + 1) * S * (MC * 2) + (T + 1) * MC ≤ Q + Q * 2 + Q :=
        Nat.add_le_add (Nat.add_le_add t1 t2) t1
    _ = Q * 4 := by ring

/-! ## (11) The headline size bound -/

section Headline

open scoped Classical

/-- `slotWeight ≤ machineConst² * 3` (since `machineConst ≤ machineConst²`). -/
theorem slotWeight_le : slotWeight tm ≤ machineConst tm ^ 2 * 3 := by
  rw [slotWeight]
  have hsq : machineConst tm ≤ machineConst tm ^ 2 := Nat.le_self_pow (by omega) _
  calc machineConst tm + machineConst tm ^ 2 * 2 ≤ machineConst tm ^ 2 + machineConst tm ^ 2 * 2 :=
        Nat.add_le_add_right hsq _
    _ = machineConst tm ^ 2 * 3 := by ring

/-- **Full consistency size, in `machineConst` powers.** `totalLits (fullConsistencyClauses …) ≤
(T+1) * (S+1) * machineConst³ * 12` (a generous machine-cube bound). -/
theorem fullConsistencyClauses_size_le' :
    totalLits (fullConsistencyClauses tm T S (ContTok tm))
      ≤ (T + 1) * (S + 1) * machineConst tm ^ 3 * 12 := by
  refine le_trans fullConsistencyClauses_size_le ?_
  set MC := machineConst tm with hMC
  have hsw : slotWeight tm ≤ MC ^ 2 * 3 := slotWeight_le
  have hcardK : Fintype.card tm.K ≤ MC := cardK_le_machineConst
  set Q := (T + 1) * (S + 1) * MC ^ 3 with hQ
  -- term1 = (T+1)·slotWeight·2 ≤ Q·6 ; term2 = (T+1)·cardK·(S·slotWeight) ≤ Q·3 ; term3 ≤ Q·3
  have hT1 : (T + 1) * (slotWeight tm * 2) ≤ Q * 6 := by
    rw [hQ]
    calc (T + 1) * (slotWeight tm * 2) ≤ (T + 1) * (MC ^ 2 * 3 * 2) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right 2 hsw)
      _ ≤ (T + 1) * (S + 1) * MC ^ 3 * 6 := by
          rw [show (T + 1) * (MC ^ 2 * 3 * 2) = (T + 1) * MC ^ 2 * 6 by ring]
          refine Nat.mul_le_mul_right 6 ?_
          calc (T + 1) * MC ^ 2 ≤ (T + 1) * (S + 1) * MC ^ 2 := by
                rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
            _ ≤ (T + 1) * (S + 1) * MC ^ 3 := Nat.mul_le_mul_left _
                (Nat.pow_le_pow_right (by rw [hMC]; have := two_le_machineConst (tm := tm); omega)
                  (by omega))
  have hT3 : (T + 1) * slotWeight tm ≤ Q * 3 := by
    rw [hQ]
    calc (T + 1) * slotWeight tm ≤ (T + 1) * (MC ^ 2 * 3) := Nat.mul_le_mul_left _ hsw
      _ ≤ (T + 1) * (S + 1) * MC ^ 3 * 3 := by
          rw [show (T + 1) * (MC ^ 2 * 3) = (T + 1) * MC ^ 2 * 3 by ring]
          refine Nat.mul_le_mul_right 3 ?_
          calc (T + 1) * MC ^ 2 ≤ (T + 1) * (S + 1) * MC ^ 2 := by
                rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
            _ ≤ (T + 1) * (S + 1) * MC ^ 3 := Nat.mul_le_mul_left _
                (Nat.pow_le_pow_right (by rw [hMC]; have := two_le_machineConst (tm := tm); omega)
                  (by omega))
  have hT2 : (T + 1) * (Fintype.card tm.K * (S * slotWeight tm)) ≤ Q * 3 := by
    rw [hQ]
    -- ≤ (T+1)·MC·(S·(MC²·3)) = (T+1)·S·MC³·3 ≤ (T+1)·(S+1)·MC³·3
    calc (T + 1) * (Fintype.card tm.K * (S * slotWeight tm))
        ≤ (T + 1) * (MC * (S * (MC ^ 2 * 3))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hcardK (Nat.mul_le_mul_left _ hsw))
      _ = (T + 1) * S * MC ^ 3 * 3 := by ring
      _ ≤ (T + 1) * (S + 1) * MC ^ 3 * 3 := by
          refine Nat.mul_le_mul_right 3 (Nat.mul_le_mul_right _ ?_)
          exact Nat.mul_le_mul_left _ (by omega)
  calc (T + 1) * (slotWeight tm * 2) + (T + 1) * (Fintype.card tm.K * (S * slotWeight tm))
          + (T + 1) * slotWeight tm
      ≤ Q * 6 + Q * 3 + Q * 3 := Nat.add_le_add (Nat.add_le_add hT1 hT2) hT3
    _ = (T + 1) * (S + 1) * MC ^ 3 * 12 := by rw [hQ]; ring

/-- The init / accept families' bound, in the common `machineConst`-cube shape:
`totalLits ≤ (T+1)*(S+1)*machineConst³ + (input/output length factor) ...`; here we use the
generous `≤ (S + 1) * machineConst³ + machineConst²` (their `3 + card K · S` is dominated). -/
private theorem initOrAccept_size_le (cnt : ℕ) (hcnt : cnt ≤ 3 + Fintype.card tm.K * S) :
    cnt ≤ (S + 1) * machineConst tm ^ 3 * 2 := by
  have hk : Fintype.card tm.K ≤ machineConst tm := cardK_le_machineConst
  set MC := machineConst tm with hMC
  have hMC2 : 2 ≤ MC := by rw [hMC]; exact two_le_machineConst
  have hcube : MC ≤ MC ^ 3 := Nat.le_self_pow (by omega) MC
  have h8 : 8 ≤ MC ^ 3 := by
    have : (2 : ℕ) ^ 3 ≤ MC ^ 3 := Nat.pow_le_pow_left hMC2 3
    simpa using this
  -- `3 ≤ (S+1)·MC³` and `cardK·S ≤ MC·S ≤ MC³·(S+1)`, so the sum `≤ 2·(S+1)·MC³`
  have ha : (3 : ℕ) ≤ (S + 1) * MC ^ 3 :=
    le_trans (by omega) (Nat.le_mul_of_pos_left (MC ^ 3) (by omega))
  have hb : Fintype.card tm.K * S ≤ (S + 1) * MC ^ 3 := by
    calc Fintype.card tm.K * S ≤ MC * S := Nat.mul_le_mul_right _ hk
      _ ≤ MC ^ 3 * (S + 1) := Nat.mul_le_mul hcube (by omega)
      _ = (S + 1) * MC ^ 3 := by ring
  calc cnt ≤ 3 + Fintype.card tm.K * S := hcnt
    _ ≤ (S + 1) * MC ^ 3 + (S + 1) * MC ^ 3 := Nat.add_le_add ha hb
    _ = (S + 1) * MC ^ 3 * 2 := by ring

/-- **Headline: polynomial size bound.** The full tableau formula's `CnfFormula.size` is bounded
by a single machine-cube coefficient times a degree-`2` polynomial in `(T, S)`:
`size ≤ (T+1) * (S+1) * machineConst³ * 30`. (`machineConst` packs every machine cardinality;
`input`/`acceptOutput` enter only through `≤ S`, since the formula fixes them within the space
bound — the bound is uniform in their lengths.) -/
theorem tableauFormula_size_le (input : List (tm.Γ tm.k₀))
    (acceptOutput : List (tm.Γ tm.k₁)) (hS0 : 0 < S) :
    CnfFormula.size (tableauFormula tm T S input acceptOutput hS0)
      ≤ (T + 1) * (S + 1) * machineConst tm ^ 3 * 30 := by
  rw [size_eq_numVars_add_totalLits]
  -- the formula's data
  show fullNumVars tm T S (ContTok tm) + totalLits _ ≤ _
  set MC := machineConst tm with hMC
  set Q := (T + 1) * (S + 1) * MC ^ 3 with hQ
  -- split the four-family `(map length).sum` total via `totalLits`; re-elaborate the
  -- four-way append homogeneously (the stored `tableauFormula` append displays heterogeneously)
  set cCons := fullConsistencyClauses tm T S (ContTok tm) with hcCons
  set cInit := initClausesC tm T S input with hcInit
  set cTrans := (Finset.univ : Finset (Fin T)).toList.flatMap
    (fun t => unifTransClauses tm S t hS0) with hcTrans
  set cAcc := acceptClausesC tm T S acceptOutput with hcAcc
  have hsplit : totalLits (tableauFormula tm T S input acceptOutput hS0).clauses
      = totalLits cCons + totalLits cInit + totalLits cTrans + totalLits cAcc := by
    have h : totalLits (tableauFormula tm T S input acceptOutput hS0).clauses
        = totalLits (((cCons ++ cInit) ++ cTrans) ++ cAcc) := congrArg totalLits rfl
    rw [h, totalLits_append, totalLits_append, totalLits_append]
  rw [hsplit]
  -- bound `numVars` and each family by a multiple of `Q`
  have hnv : fullNumVars tm T S (ContTok tm) ≤ Q * 4 := by
    refine le_trans fullNumVars_le ?_
    rw [hQ]
    -- (T+1)·(S+1)·MC²·4 ≤ (T+1)·(S+1)·MC³·4 (since MC² ≤ MC³)
    refine Nat.mul_le_mul_right 4 (Nat.mul_le_mul_left _ ?_)
    have : 0 < MC := by rw [hMC]; have := two_le_machineConst (tm := tm); omega
    exact Nat.pow_le_pow_right this (by omega)
  have hcons : totalLits cCons ≤ Q * 12 := by
    rw [hcCons, hQ]; exact fullConsistencyClauses_size_le'
  have htrans : totalLits cTrans ≤ Q * 10 := by
    rw [hcTrans, hQ]
    refine le_trans (transClauses_size_le hS0) ?_
    rw [show T * ((S + 1) * MC ^ 3 * 10) = T * (S + 1) * MC ^ 3 * 10 by ring]
    exact Nat.mul_le_mul_right 10 (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (by omega)))
  have hQT : (S + 1) * MC ^ 3 * 2 ≤ Q * 2 := by
    rw [hQ]
    refine Nat.mul_le_mul_right 2 ?_
    calc (S + 1) * MC ^ 3 ≤ (T + 1) * ((S + 1) * MC ^ 3) :=
          Nat.le_mul_of_pos_left _ (by omega)
      _ = (T + 1) * (S + 1) * MC ^ 3 := by ring
  have hinit : totalLits cInit ≤ Q * 2 := by
    rw [hcInit]
    exact le_trans (initOrAccept_size_le _ (initClausesC_size_le input)) hQT
  have hacc : totalLits cAcc ≤ Q * 2 := by
    rw [hcAcc]
    exact le_trans (initOrAccept_size_le _ (acceptClausesC_size_le acceptOutput)) hQT
  -- assemble: 4 + 12 + 2 + 10 + 2 = 30
  calc fullNumVars tm T S (ContTok tm)
        + (totalLits cCons + totalLits cInit + totalLits cTrans + totalLits cAcc)
      ≤ Q * 4 + (Q * 12 + Q * 2 + Q * 10 + Q * 2) :=
        Nat.add_le_add hnv (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hcons hinit) htrans) hacc)
    _ = Q * 30 := by ring

/-! ## (12) The serialized `cnfEncode` length -/

/-- **`cnfEncode` length, exact.** `(cnfEncode φ).length = 2 + numClauses + 2 · totalLits`:
two header entries, then `1 + 2·(clause length)` per clause (`clauseEncode`, with `litEncode`
contributing `2` per literal). -/
theorem cnfEncode_length_eq (φ : CnfFormula) :
    (cnfEncode φ).length = 2 + φ.clauses.length + 2 * totalLits φ.clauses := by
  rw [cnfEncode, List.length_cons, List.length_cons, List.length_flatMap, totalLits_eq_sum]
  -- each clause's encode length is `1 + 2·(clause length)`
  have hmap : φ.clauses.map (fun c => (clauseEncode c).length)
      = φ.clauses.map (fun c => 1 + 2 * c.length) := by
    apply List.map_congr_left
    intro c _
    rw [clauseEncode, List.length_cons, List.length_flatMap]
    have hlit : c.map (fun l => (litEncode l).length) = c.map (fun _ => 2) := by
      apply List.map_congr_left; intro l _; rfl
    rw [hlit, List.map_const', List.sum_replicate, smul_eq_mul]
    omega
  rw [hmap]
  -- `Σ (1 + 2·len) = numClauses + 2·Σ len`
  rw [List.sum_map_add]
  have hone : (φ.clauses.map (fun _ => 1)).sum = φ.clauses.length := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul, mul_one]
  have htwo : (φ.clauses.map (fun c => 2 * c.length)).sum
      = 2 * (φ.clauses.map List.length).sum := by
    rw [← List.sum_map_mul_left]
  rw [hone, htwo]
  omega

/-- **`cnfEncode` length bound (size form).** `(cnfEncode φ).length ≤ 2 · size φ + 2 + numClauses`
— two header entries, two literal-bytes per literal (`2·totalLits ≤ 2·size`), one length-prefix per
clause. This is the measure the SAT `CookLevin.KarpReduction` consumes; it stays polynomial whenever
`size` and the clause count are. -/
theorem cnfEncode_length_le (φ : CnfFormula) :
    (cnfEncode φ).length ≤ 2 * φ.size + 2 + φ.clauses.length := by
  rw [cnfEncode_length_eq, size_eq_numVars_add_totalLits]
  -- 2 + numClauses + 2·totalLits ≤ 2·(numVars + totalLits) + 2 + numClauses
  omega

/-- If every clause of `cs` is nonempty (`≥ 1` literal), the clause count is `≤ totalLits`. -/
theorem length_le_totalLits_of_ne_nil {n : ℕ} (cs : List (Clause n))
    (h : ∀ c ∈ cs, c ≠ []) : cs.length ≤ totalLits cs := by
  rw [totalLits_eq_sum]
  calc cs.length = (cs.map (fun _ => 1)).sum := by
        rw [List.map_const', List.sum_replicate, smul_eq_mul, mul_one]
    _ ≤ (cs.map List.length).sum := by
        refine List.sum_le_sum ?_
        intro c hc
        exact Nat.one_le_iff_ne_zero.2 (by simpa [List.length_eq_zero_iff] using h c hc)

/-! ## (13) Tableau clauses are nonempty, and the `cnfEncode` tableau length bound -/

section Nonempty

open scoped Classical

/-- Clauses produced by `exactlyOne` over a nonempty slot are nonempty (`atLeastOneTrue` of a
nonempty list, or a 2-literal `atMostOne` exclusion). -/
theorem exactlyOne_clause_ne_nil {n : ℕ} (vars : List (Fin n)) (hvars : vars ≠ [])
    (c : Clause n) (hc : c ∈ BooleanConstraints.exactlyOne vars) : c ≠ [] := by
  rw [BooleanConstraints.exactlyOne, List.mem_cons] at hc
  rcases hc with rfl | hc
  · -- `atLeastOneTrue vars` is `vars.map _`, nonempty since `vars ≠ []`
    rw [BooleanConstraints.atLeastOneTrue]
    simpa [List.map_eq_nil_iff] using hvars
  · -- exclusion clause has length 2
    have := length_mem_atMostOne vars c hc
    intro hnil; rw [hnil] at this; simp at this

/-- A lifted clause is nonempty iff the original is. -/
theorem liftClauseL_ne_nil {n m : ℕ} (c : Clause n) (hc : c ≠ []) :
    BooleanConstraints.liftClauseL (m := m) c ≠ [] := by
  intro hnil
  rw [BooleanConstraints.liftClauseL, List.map_eq_nil_iff] at hnil
  exact hc hnil

/-- Clauses of `liftClausesL cs` are nonempty when those of `cs` are. -/
theorem mem_liftClausesL_ne_nil {n m : ℕ} (cs : List (Clause n))
    (h : ∀ c ∈ cs, c ≠ []) (d : Clause (n + m)) (hd : d ∈ BooleanConstraints.liftClausesL cs) :
    d ≠ [] := by
  rw [BooleanConstraints.liftClausesL, List.mem_map] at hd
  obtain ⟨c, hc, rfl⟩ := hd
  exact liftClauseL_ne_nil c (h c hc)

/-- Clauses of `conditionOn v cs` are nonempty (the guard literal makes them `≥ 1`-wide). -/
theorem mem_conditionOn_ne_nil {n : ℕ} (v : Fin n) (cs : List (Clause n))
    (d : Clause n) (hd : d ∈ BooleanConstraints.conditionOn v cs) : d ≠ [] := by
  rw [BooleanConstraints.conditionOn, List.mem_map] at hd
  obtain ⟨c, _, rfl⟩ := hd
  simp

/-- Clauses of `funClauses` are nonempty (each is a 2-literal `implies`). -/
theorem mem_funClauses_ne_nil {n : ℕ} {A B : Type} [Fintype A] (inVar : A → Fin n)
    (outVar : B → Fin n) (f : A → B) (c : Clause n)
    (hc : c ∈ BooleanConstraints.funClauses inVar outVar f) : c ≠ [] := by
  obtain ⟨a, rfl⟩ := (BooleanConstraints.mem_funClauses inVar outVar f c).1 hc
  simp [BooleanConstraints.implies]

/-- Clauses of `funClauses₂` are nonempty (each is a 3-literal `implies₂`). -/
theorem mem_funClauses₂_ne_nil {n : ℕ} {A B C : Type} [Fintype A] [Fintype B] (inA : A → Fin n)
    (inB : B → Fin n) (outVar : C → Fin n) (g : A → B → C) (c : Clause n)
    (hc : c ∈ BooleanConstraints.funClauses₂ inA inB outVar g) : c ≠ [] := by
  obtain ⟨a, b, rfl⟩ := (BooleanConstraints.mem_funClauses₂ inA inB outVar g c).1 hc
  simp [BooleanConstraints.implies₂]

/-! ### Per-family nonemptiness -/

open Turing.TM2.Stmt

/-- Every consistency clause is nonempty (`exactlyOne` over a nonempty label/state/cell slot). -/
theorem consistencyClauses_ne_nil (c : Clause (numVars tm T S))
    (hc : c ∈ consistencyClauses tm T S) : c ≠ [] := by
  rw [consistencyClauses, List.mem_append] at hc
  rcases hc with hc | hc
  · -- label/state half
    rw [List.mem_flatMap] at hc
    obtain ⟨t, _, hc⟩ := hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact exactlyOne_clause_ne_nil _ (labelSlot_ne_nil t) c hc
    · exact exactlyOne_clause_ne_nil _ (stateSlot_ne_nil t) c hc
  · -- cell half
    rw [List.mem_flatMap] at hc
    obtain ⟨t, _, hc⟩ := hc
    rw [List.mem_flatMap] at hc
    obtain ⟨k, _, hc⟩ := hc
    rw [List.mem_flatMap] at hc
    obtain ⟨i, _, hc⟩ := hc
    exact exactlyOne_clause_ne_nil _ (cellSlot_ne_nil t k i) c hc

omit [∀ k, Fintype (tm.Γ k)] in
/-- Every register consistency clause is nonempty (`exactlyOne` over a nonempty register slot). -/
theorem regConsistencyClauses_ne_nil (c : Clause (regNumVars T (ContTok tm)))
    (hc : c ∈ regConsistencyClauses T (ContTok tm)) : c ≠ [] := by
  rw [regConsistencyClauses, List.mem_flatMap] at hc
  obtain ⟨t, _, hc⟩ := hc
  exact exactlyOne_clause_ne_nil _ (regSlot_ne_nil t) c hc

/-- Every full-consistency clause is nonempty. -/
theorem fullConsistencyClauses_ne_nil (c : Clause (numVars tm T S + regNumVars T (ContTok tm)))
    (hc : c ∈ fullConsistencyClauses tm T S (ContTok tm)) : c ≠ [] := by
  rw [fullConsistencyClauses, List.mem_append] at hc
  rcases hc with hc | hc
  · exact mem_liftClausesL_ne_nil _ (consistencyClauses_ne_nil) c hc
  · rw [BooleanConstraints.liftClausesR, List.mem_map] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    intro hnil
    rw [BooleanConstraints.liftClauseR, List.map_eq_nil_iff] at hnil
    exact regConsistencyClauses_ne_nil d hd hnil

/-- Every state-gadget clause is nonempty (funClauses / funClauses₂ over any head). -/
theorem stateGadgetFor_ne_nil (cont : ContTok tm) (t : Fin T) (hS0 : 0 < S)
    (c : Clause (numVars tm T S)) (hc : c ∈ stateGadgetFor cont t hS0) : c ≠ [] := by
  cases cont with
  | none => exact mem_funClauses_ne_nil _ _ _ c hc
  | some w =>
    obtain ⟨q, hq⟩ := w
    cases q with
    | push k f q => exact mem_funClauses_ne_nil _ _ _ c hc
    | branch f q₁ q₂ => exact mem_funClauses_ne_nil _ _ _ c hc
    | goto f => exact mem_funClauses_ne_nil _ _ _ c hc
    | halt => exact mem_funClauses_ne_nil _ _ _ c hc
    | load a q => exact mem_funClauses_ne_nil _ _ _ c hc
    | peek k f q =>
      rw [stateGadgetFor, peekStateClauses] at hc
      exact mem_funClauses₂_ne_nil _ _ _ _ c hc
    | pop k f q =>
      rw [stateGadgetFor, peekStateClauses] at hc
      exact mem_funClauses₂_ne_nil _ _ _ _ c hc

/-- Every `keepCellClauses` clause is nonempty (per-position funClauses). -/
theorem keepCellClauses_ne_nil (t : Fin T) (k : tm.K) (c : Clause (numVars tm T S))
    (hc : c ∈ keepCellClauses (S := S) t k) : c ≠ [] := by
  rw [keepCellClauses, List.mem_flatMap] at hc
  obtain ⟨i, _, hc⟩ := hc
  exact mem_funClauses_ne_nil _ _ _ c hc

/-- Every cell-gadget clause is nonempty (keep / pop / push leaves, all funClauses or units). -/
theorem cellGadgetFor_ne_nil (cont : ContTok tm) (t : Fin T) (c : Clause (numVars tm T S))
    (hc : c ∈ cellGadgetFor (S := S) cont t) : c ≠ [] := by
  -- the all-keep case (over a stack list)
  have hkeepflat : ∀ (ks : List tm.K),
      c ∈ ks.flatMap (fun k' => keepCellClauses (S := S) t k') → c ≠ [] := by
    intro ks hc'
    rw [List.mem_flatMap] at hc'
    obtain ⟨k', _, hc'⟩ := hc'
    exact keepCellClauses_ne_nil t k' c hc'
  cases cont with
  | none => exact hkeepflat _ hc
  | some w =>
    obtain ⟨q, hq⟩ := w
    cases q with
    | push k f q =>
      rw [cellGadgetFor, List.mem_append] at hc
      rcases hc with hc | hc
      · -- pushCellClauses: bottom funClauses + shift funClauses
        rw [pushCellClauses, List.mem_append] at hc
        rcases hc with hc | hc
        · split at hc
          · exact mem_funClauses_ne_nil _ _ _ c hc
          · simp at hc
        · rw [List.mem_flatMap] at hc
          obtain ⟨i, _, hc⟩ := hc
          split at hc
          · exact mem_funClauses_ne_nil _ _ _ c hc
          · simp at hc
      · exact hkeepflat _ hc
    | pop k f q =>
      rw [cellGadgetFor, List.mem_append] at hc
      rcases hc with hc | hc
      · -- popCellClauses: per-position shift funClauses or unit clause
        rw [popCellClauses, List.mem_flatMap] at hc
        obtain ⟨i, _, hc⟩ := hc
        split at hc
        · exact mem_funClauses_ne_nil _ _ _ c hc
        · rw [List.mem_singleton] at hc; subst hc; simp
      · exact hkeepflat _ hc
    | branch f q₁ q₂ => exact hkeepflat _ hc
    | goto f => exact hkeepflat _ hc
    | halt => exact hkeepflat _ hc
    | load a q => exact hkeepflat _ hc
    | peek k f q => exact hkeepflat _ hc

/-- Every per-time transition clause is nonempty (`funClauses₂` for cont, `conditionOn`-guarded
gadgets for state/cell). -/
theorem unifTransClauses_ne_nil (t : Fin T) (hS0 : 0 < S)
    (c : Clause (fullNumVars tm T S (ContTok tm))) (hc : c ∈ unifTransClauses tm S t hS0) :
    c ≠ [] := by
  rw [unifTransClauses, List.mem_append, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · -- contTransClauses = funClauses₂
    rw [contTransClauses] at hc
    exact mem_funClauses₂_ne_nil _ _ _ _ c hc
  · -- stateTransClauses: flatMap of conditionOn-guarded gadgets
    rw [stateTransClauses, List.mem_flatMap] at hc
    obtain ⟨cont, _, hc⟩ := hc
    exact mem_conditionOn_ne_nil _ _ c hc
  · -- cellTransClauses: flatMap of conditionOn-guarded gadgets
    rw [cellTransClauses, List.mem_flatMap] at hc
    obtain ⟨cont, _, hc⟩ := hc
    exact mem_conditionOn_ne_nil _ _ c hc

/-- Every clause of the transition flat-map is nonempty. -/
theorem transClauses_ne_nil (hS0 : 0 < S)
    (c : Clause (fullNumVars tm T S (ContTok tm)))
    (hc : c ∈ (Finset.univ : Finset (Fin T)).toList.flatMap
        (fun t => unifTransClauses tm S t hS0)) : c ≠ [] := by
  rw [List.mem_flatMap] at hc
  obtain ⟨t, _, hc⟩ := hc
  exact unifTransClauses_ne_nil t hS0 c hc

/-- Every `initClauses` clause is nonempty (unit clauses, one per slot/cell). -/
theorem initClauses_ne_nil (input : List (tm.Γ tm.k₀)) (c : Clause (numVars tm T S))
    (hc : c ∈ initClauses tm T S input) : c ≠ [] := by
  rw [initClauses, List.mem_cons, List.mem_cons] at hc
  rcases hc with rfl | rfl | hc
  · simp
  · simp
  · rw [List.mem_flatMap] at hc
    obtain ⟨k, _, hc⟩ := hc
    rw [List.mem_map] at hc
    obtain ⟨i, _, rfl⟩ := hc
    simp

/-- Every `haltClauses` clause is nonempty. -/
theorem haltClauses_ne_nil (acceptOutput : List (tm.Γ tm.k₁)) (c : Clause (numVars tm T S))
    (hc : c ∈ haltClauses tm T S acceptOutput) : c ≠ [] := by
  rw [haltClauses, List.mem_cons, List.mem_cons] at hc
  rcases hc with rfl | rfl | hc
  · simp
  · simp
  · rw [List.mem_flatMap] at hc
    obtain ⟨k, _, hc⟩ := hc
    rw [List.mem_map] at hc
    obtain ⟨i, _, rfl⟩ := hc
    simp

/-- Every combined init clause is nonempty (lifted units + the cont unit clause). -/
theorem initClausesC_ne_nil (input : List (tm.Γ tm.k₀))
    (c : Clause (fullNumVars tm T S (ContTok tm))) (hc : c ∈ initClausesC tm T S input) :
    c ≠ [] := by
  -- re-elaborate the defining append homogeneously
  set L := BooleanConstraints.liftClausesL (m := regNumVars T (ContTok tm)) (initClauses tm T S input)
  set d : Clause (numVars tm T S + regNumVars T (ContTok tm)) :=
    [(contVar (tm := tm) (S := S) (0 : Fin (T + 1))
      (some ⟨tm.m tm.main, program_mem_relevant tm tm.main⟩ : ContTok tm), true)]
  have hmem : c ∈ L ++ [d] := hc
  rw [List.mem_append] at hmem
  rcases hmem with hc' | hc'
  · exact mem_liftClausesL_ne_nil _ (initClauses_ne_nil input) c hc'
  · rw [List.mem_singleton] at hc'; subst hc'; simp

/-- Every combined accept clause is nonempty (lifted units + the cont unit clause). -/
theorem acceptClausesC_ne_nil (acceptOutput : List (tm.Γ tm.k₁))
    (c : Clause (fullNumVars tm T S (ContTok tm))) (hc : c ∈ acceptClausesC tm T S acceptOutput) :
    c ≠ [] := by
  set L := BooleanConstraints.liftClausesL (m := regNumVars T (ContTok tm))
    (haltClauses tm T S acceptOutput)
  set d : Clause (numVars tm T S + regNumVars T (ContTok tm)) :=
    [(contVar (tm := tm) (S := S) (Fin.last T) (none : ContTok tm), true)]
  have hmem : c ∈ L ++ [d] := hc
  rw [List.mem_append] at hmem
  rcases hmem with hc' | hc'
  · exact mem_liftClausesL_ne_nil _ (haltClauses_ne_nil acceptOutput) c hc'
  · rw [List.mem_singleton] at hc'; subst hc'; simp

/-- **Every clause of the tableau formula is nonempty.** Hence its clause count is `≤ totalLits`. -/
theorem tableauFormula_clauses_ne_nil (input : List (tm.Γ tm.k₀))
    (acceptOutput : List (tm.Γ tm.k₁)) (hS0 : 0 < S)
    (c : Clause (fullNumVars tm T S (ContTok tm)))
    (hc : c ∈ (tableauFormula tm T S input acceptOutput hS0).clauses) : c ≠ [] := by
  -- re-elaborate the four-way append homogeneously
  set cCons := fullConsistencyClauses tm T S (ContTok tm)
  set cInit := initClausesC tm T S input
  set cTrans := (Finset.univ : Finset (Fin T)).toList.flatMap
    (fun t => unifTransClauses tm S t hS0)
  set cAcc := acceptClausesC tm T S acceptOutput
  have hmem : c ∈ ((cCons ++ cInit) ++ cTrans) ++ cAcc := hc
  rcases List.mem_append.mp hmem with hc' | hc'
  · rcases List.mem_append.mp hc' with hc'' | hc''
    · rcases List.mem_append.mp hc'' with hc₃ | hc₃
      · exact fullConsistencyClauses_ne_nil c hc₃
      · exact initClausesC_ne_nil input c hc₃
    · exact transClauses_ne_nil hS0 c hc''
  · exact acceptClausesC_ne_nil acceptOutput c hc'

/-- **`cnfEncode (tableauFormula …)` length bound.** Composing `cnfEncode_length_le` with the
headline `size` bound and the all-clauses-nonempty fact (so `numClauses ≤ totalLits ≤ size`):
`(cnfEncode (tableauFormula …)).length ≤ 3 · size + 2 ≤ (T+1)*(S+1)*machineConst³*90 + 2`. This is
the measure `CookLevin`'s SAT `KarpReduction` consumes. -/
theorem cnfEncode_tableauFormula_length_le (input : List (tm.Γ tm.k₀))
    (acceptOutput : List (tm.Γ tm.k₁)) (hS0 : 0 < S) :
    (cnfEncode (tableauFormula tm T S input acceptOutput hS0)).length
      ≤ (T + 1) * (S + 1) * machineConst tm ^ 3 * 90 + 2 := by
  set φ := tableauFormula tm T S input acceptOutput hS0 with hφ
  -- clause count ≤ totalLits ≤ size (all clauses nonempty)
  have hcount : φ.clauses.length ≤ φ.size := by
    rw [size_eq_numVars_add_totalLits]
    refine le_trans (length_le_totalLits_of_ne_nil φ.clauses ?_) (Nat.le_add_left _ _)
    rw [hφ]; exact tableauFormula_clauses_ne_nil input acceptOutput hS0
  refine le_trans (cnfEncode_length_le φ) ?_
  have hsize : φ.size ≤ (T + 1) * (S + 1) * machineConst tm ^ 3 * 30 := by
    rw [hφ]; exact tableauFormula_size_le input acceptOutput hS0
  calc 2 * φ.size + 2 + φ.clauses.length ≤ 2 * φ.size + 2 + φ.size :=
        Nat.add_le_add_left hcount _
    _ = 3 * φ.size + 2 := by ring
    _ ≤ 3 * ((T + 1) * (S + 1) * machineConst tm ^ 3 * 30) + 2 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hsize) _
    _ = (T + 1) * (S + 1) * machineConst tm ^ 3 * 90 + 2 := by ring

end Nonempty

end Headline

/-! ## Sanity restatement -/

section Examples

variable {n : ℕ}

-- `totalLits` is the `CnfFormula.size` summand.
example (φ : CnfFormula) : φ.size = φ.numVars + totalLits φ.clauses :=
  size_eq_numVars_add_totalLits φ

-- `totalLits` splits over append.
example (c₁ c₂ : List (Clause n)) :
    totalLits (c₁ ++ c₂) = totalLits c₁ + totalLits c₂ :=
  totalLits_append c₁ c₂

-- An `exactlyOne` over `≤ m` variables contributes `≤ m + 2m²` literals.
example (vars : List (Fin n)) (m : ℕ) (hm : vars.length ≤ m) :
    totalLits (BooleanConstraints.exactlyOne vars) ≤ m + m ^ 2 * 2 :=
  totalLits_exactlyOne_le_of_length vars m hm

variable {tm : FinTM2} {T S : ℕ} [∀ k, Fintype (tm.Γ k)]
  [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- HEADLINE: the full tableau formula's `size` is a degree-2-in-`(T,S)` machine polynomial.
example (input : List (tm.Γ tm.k₀)) (acceptOutput : List (tm.Γ tm.k₁)) (hS0 : 0 < S) :
    CnfFormula.size (tableauFormula tm T S input acceptOutput hS0)
      ≤ (T + 1) * (S + 1) * machineConst tm ^ 3 * 30 :=
  tableauFormula_size_le input acceptOutput hS0

-- The serialized `cnfEncode` length (the SAT `KarpReduction` measure) is also polynomial.
example (input : List (tm.Γ tm.k₀)) (acceptOutput : List (tm.Γ tm.k₁)) (hS0 : 0 < S) :
    (cnfEncode (tableauFormula tm T S input acceptOutput hS0)).length
      ≤ (T + 1) * (S + 1) * machineConst tm ^ 3 * 90 + 2 :=
  cnfEncode_tableauFormula_length_le input acceptOutput hS0

end Examples

end CombinedTableau

end DeepWiki
