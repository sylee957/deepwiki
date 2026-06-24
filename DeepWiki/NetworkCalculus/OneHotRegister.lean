import Mathlib.Data.Fintype.Prod
import DeepWiki.NetworkCalculus.BooleanSatisfiability
import DeepWiki.NetworkCalculus.BooleanConstraints

/-!
# A generic one-hot register variable block

A self-contained CNF variable block that carries one value from a `Fintype V` at every
time step `t ∈ Fin (T+1)`.  This is the reusable **register** building block for a
Cook- and Levin-style tableau: a coordinate type `RegCoord T V`, the `Fin (regNumVars …)`
variable indices, the per-step `exactlyOne` consistency clauses, the assignment readback
`readReg`, the encoding `encodeReg` of a value sequence, and the round-trip lemmas.

The block is fully generic over `(T : ℕ) (V : Type) [Fintype V] [DecidableEq V] [Inhabited V]`,
with no Turing-machine or tableau types — it is meant to be instantiated (e.g. `V` = a
continuation type) and combined with other variable blocks through an offset lift.
-/

namespace DeepWiki

namespace OneHotRegister

variable (T : ℕ) (V : Type) [Fintype V] [DecidableEq V] [Inhabited V]

/-! ## (1) Coordinate type and variable indexing -/

/-- A **register coordinate**: the atomic fact "at time `t` the register holds value `val`". -/
def RegCoord : Type := Fin (T + 1) × V

instance : Fintype (RegCoord T V) := inferInstanceAs (Fintype (Fin (T + 1) × V))

instance : DecidableEq (RegCoord T V) := inferInstanceAs (DecidableEq (Fin (T + 1) × V))

instance : Inhabited (RegCoord T V) := ⟨(⟨0, Nat.succ_pos T⟩, default)⟩

/-- The **number of Boolean variables** of the register: the cardinality of `RegCoord T V`. -/
def regNumVars : ℕ := Fintype.card (RegCoord T V)

omit [DecidableEq V] [Inhabited V] in
/-- **Exact variable count.** `(T+1)` time steps times `Fintype.card V` values. -/
theorem regNumVars_eq : regNumVars T V = (T + 1) * Fintype.card V := by
  show Fintype.card (Fin (T + 1) × V) = _
  rw [Fintype.card_prod, Fintype.card_fin]

/-- The coordinate-to-index equivalence `RegCoord T V ≃ Fin (regNumVars T V)`. -/
noncomputable def regEquiv : RegCoord T V ≃ Fin (regNumVars T V) :=
  Fintype.equivFin _

variable {T V}

/-- The `Fin (regNumVars …)` variable **index** of the coordinate "at time `t`, value `val`". -/
noncomputable def regVar (t : Fin (T + 1)) (val : V) : Fin (regNumVars T V) :=
  regEquiv T V (t, val)

omit [DecidableEq V] [Inhabited V] in
/-- The variable index map is injective (distinct coordinates get distinct indices). -/
theorem regVar_injective :
    Function.Injective (fun p : RegCoord T V => regEquiv T V p) :=
  (regEquiv T V).injective

omit [DecidableEq V] [Inhabited V] in
/-- `regVar t val = regVar t' val'` iff `(t, val) = (t', val')`. -/
@[simp] theorem regVar_inj {t t' : Fin (T + 1)} {val val' : V} :
    regVar t val = regVar t' val' ↔ t = t' ∧ val = val' := by
  unfold regVar
  rw [(regEquiv T V).injective.eq_iff]
  exact Prod.mk.injEq .. ▸ Iff.rfl

/-! ## (2) Slots and consistency clauses

A *slot* is the list of variable indices that the consistency clauses force to "exactly one
true": all values of the register at a single time step. -/

open BooleanConstraints

/-- The **register slot** at time `t`: the variable indices for every possible value. -/
noncomputable def regSlot (t : Fin (T + 1)) : List (Fin (regNumVars T V)) :=
  (Finset.univ : Finset V).toList.map (fun val => regVar t val)

omit [DecidableEq V] [Inhabited V] in
/-- Every register coordinate at time `t` appears in `regSlot t`. -/
theorem mem_regSlot (t : Fin (T + 1)) (val : V) :
    regVar t val ∈ regSlot t := by
  simp only [regSlot, List.mem_map]
  exact ⟨val, Finset.mem_toList.2 (Finset.mem_univ val), rfl⟩

omit [DecidableEq V] in
/-- The register slot is nonempty (`V` is inhabited). -/
theorem regSlot_ne_nil (t : Fin (T + 1)) : regSlot (V := V) t ≠ [] :=
  List.ne_nil_of_mem (mem_regSlot t default)

variable (T V) in
/-- The **register consistency clauses**: for each time step, the `exactlyOne` constraint
forcing precisely one of that step's value variables true. -/
noncomputable def regConsistencyClauses : List (Clause (regNumVars T V)) :=
  (Finset.univ : Finset (Fin (T + 1))).toList.flatMap (fun t => exactlyOne (regSlot t))

/-- An assignment is **register-consistent** iff it satisfies every register consistency clause. -/
def RegConsistent (assign : Fin (regNumVars T V) → Bool) : Prop :=
  satisfiesAll assign (regConsistencyClauses T V)

omit [DecidableEq V] [Inhabited V] in
/-- `RegConsistent` decomposes step-by-step: every register slot has exactly one true variable. -/
theorem regConsistent_iff (assign : Fin (regNumVars T V) → Bool) :
    RegConsistent assign ↔
      ∀ t : Fin (T + 1), ((regSlot t).filter (fun v => assign v)).length = 1 := by
  rw [RegConsistent, regConsistencyClauses, List.flatMap_def, satisfiesAll_flatten]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index]
  constructor
  · intro h t
    have := h _ t rfl
    rwa [exactlyOne_sat_iff_length] at this
  · rintro h g t rfl
    rw [exactlyOne_sat_iff_length]
    exact h t

/-! ## (3) Readback and its correctness under consistency -/

/-- In a slot list with exactly one `true`-assigned entry, any two `true`-assigned members are
equal: a length-1 list is a singleton, so all its members coincide. -/
theorem eq_of_filter_length_one {n : ℕ} {assign : Fin n → Bool} {vars : List (Fin n)}
    (hlen : (vars.filter (fun v => assign v)).length = 1)
    {a b : Fin n} (ha : a ∈ vars) (hat : assign a = true) (hb : b ∈ vars)
    (hbt : assign b = true) : a = b := by
  have hmemA : a ∈ vars.filter (fun v => assign v) := by
    rw [List.mem_filter]; exact ⟨ha, by simpa using hat⟩
  have hmemB : b ∈ vars.filter (fun v => assign v) := by
    rw [List.mem_filter]; exact ⟨hb, by simpa using hbt⟩
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hlen
  rw [hx] at hmemA hmemB
  rw [List.mem_singleton] at hmemA hmemB
  rw [hmemA, hmemB]

omit [DecidableEq V] [Inhabited V] in
/-- **Value uniqueness.** Under consistency, two values true at the same time coincide. -/
theorem reg_unique {assign : Fin (regNumVars T V) → Bool} (hcons : RegConsistent assign)
    {t : Fin (T + 1)} {val val' : V}
    (hv : assign (regVar t val) = true) (hv' : assign (regVar t val') = true) : val = val' := by
  have := eq_of_filter_length_one ((regConsistent_iff assign).1 hcons t)
    (mem_regSlot t val) hv (mem_regSlot t val') hv'
  exact (regVar_inj.1 this).2

/-- The **register read** of an assignment at time `t`: the value some true coordinate certifies,
or `default` by default. -/
noncomputable def readReg (assign : Fin (regNumVars T V) → Bool) (t : Fin (T + 1)) : V :=
  if h : ∃ val, assign (regVar t val) = true then Classical.choose h else default

omit [DecidableEq V] in
/-- **Readback correctness.** Under consistency, a true register coordinate is read back. -/
theorem readReg_eq {assign : Fin (regNumVars T V) → Bool} (hcons : RegConsistent assign)
    {t : Fin (T + 1)} {val : V} (hv : assign (regVar t val) = true) :
    readReg assign t = val := by
  have hex : ∃ val, assign (regVar t val) = true := ⟨val, hv⟩
  rw [readReg, dif_pos hex]
  exact reg_unique hcons (Classical.choose_spec hex) hv

omit [DecidableEq V] in
/-- **The read value's own coordinate is true.** Consistency gives each slot a true entry, so the
read picks a genuinely-true value coordinate. -/
theorem readReg_self_true {assign : Fin (regNumVars T V) → Bool} (hcons : RegConsistent assign)
    (t : Fin (T + 1)) : assign (regVar t (readReg assign t)) = true := by
  -- consistency: the slot has filter-length 1, so some value's coordinate is true
  have hlen := (regConsistent_iff assign).1 hcons t
  have hpos : 0 < ((regSlot t).filter (fun v => assign v)).length := by omega
  rw [List.length_pos_iff_exists_mem] at hpos
  obtain ⟨w, hw⟩ := hpos
  rw [List.mem_filter] at hw
  obtain ⟨hwmem, hwt⟩ := hw
  -- `w` is `regVar t val` for some value `val`
  simp only [regSlot, List.mem_map] at hwmem
  obtain ⟨val, _, rfl⟩ := hwmem
  rw [readReg_eq hcons (by simpa using hwt)]
  simpa using hwt

/-! ## (4) Encoding a value sequence and the round-trip -/

/-- **Slot-counting helper.** A slot `univ.toList.map g` whose assignment sends each `g x` to
`target == x` has exactly one true variable (the one at `target`). -/
theorem filter_map_univ_beq_length_one {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    {assign : Fin n → Bool} {g : α → Fin n} (target : α)
    (hval : ∀ x, assign (g x) = decide (target = x)) :
    (((Finset.univ : Finset α).toList.map g).filter (fun v => assign v)).length = 1 := by
  rw [List.filter_map, List.length_map]
  have hnd : (Finset.univ : Finset α).toList.Nodup := Finset.nodup_toList _
  have hpred : ((fun v => assign v) ∘ g) = (fun x => x == target) := by
    funext x
    simp only [Function.comp_apply, hval x]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, eq_comm]
  rw [hpred, ← List.countP_eq_length_filter, ← List.count_eq_countP]
  exact List.count_eq_one_of_mem hnd (Finset.mem_toList.2 (Finset.mem_univ target))

/-- The **assignment encoding** a value sequence `vals`: each variable's truth is whether the
coordinate's value matches `vals` at the coordinate's time. -/
noncomputable def encodeReg (vals : Fin (T + 1) → V) : Fin (regNumVars T V) → Bool :=
  fun w => let c := (regEquiv T V).symm w; decide (c.2 = vals c.1)

omit [Inhabited V] in
/-- `encodeReg` at a register variable evaluates to the value equality test. -/
theorem encodeReg_regVar (vals : Fin (T + 1) → V) (t : Fin (T + 1)) (val : V) :
    encodeReg vals (regVar t val) = decide (val = vals t) := by
  rw [encodeReg, regVar, Equiv.symm_apply_apply]

omit [Inhabited V] in
/-- **Encoding is consistent.** Encoding a value sequence satisfies every consistency clause: each
slot has exactly the one matching value true. -/
theorem encodeReg_regConsistent (vals : Fin (T + 1) → V) :
    RegConsistent (encodeReg vals) := by
  rw [regConsistent_iff]
  intro t
  refine filter_map_univ_beq_length_one (vals t) (fun val => ?_)
  rw [encodeReg_regVar]
  exact decide_eq_decide.2 eq_comm

/-- **Round-trip.** Reading back an encoded value sequence recovers the value at each time. -/
theorem readReg_encodeReg (vals : Fin (T + 1) → V) (t : Fin (T + 1)) :
    readReg (encodeReg vals) t = vals t :=
  readReg_eq (encodeReg_regConsistent vals) (by rw [encodeReg_regVar]; simp)

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

variable {T : ℕ} {V : Type} [Fintype V] [DecidableEq V] [Inhabited V]

-- `regNumVars` is exactly the coordinate-type cardinality.
example : regNumVars T V = Fintype.card (RegCoord T V) := rfl

-- A register coordinate's variable index lies in that time step's slot.
example (t : Fin (T + 1)) (val : V) : regVar t val ∈ regSlot t := mem_regSlot t val

-- Under consistency, a true register coordinate is read back to its value.
example {assign : Fin (regNumVars T V) → Bool} (hcons : RegConsistent assign)
    {t : Fin (T + 1)} {val : V} (hv : assign (regVar t val) = true) :
    readReg assign t = val :=
  readReg_eq hcons hv

-- The encode-then-read round-trip recovers the value at each time.
example (vals : Fin (T + 1) → V) (t : Fin (T + 1)) :
    readReg (encodeReg vals) t = vals t :=
  readReg_encodeReg vals t

end Examples

end OneHotRegister

end DeepWiki
