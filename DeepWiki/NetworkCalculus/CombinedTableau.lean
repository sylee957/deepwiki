import DeepWiki.NetworkCalculus.TableauInit
import DeepWiki.NetworkCalculus.OneHotRegister
import DeepWiki.NetworkCalculus.ClauseDispatch

/-!
# Combined tableau variable space: machine tableau ⊕ continuation register

Layer 3c of a Cook- and Levin-style formalization: the **unified variable space** that the
per-`stmtStep` dispatch will use.  It glues two already-built variable blocks into one
`Fin (fullNumVars …)` space via the offset lift of `ClauseDispatch`:

* the **main tableau** block (`TableauSchema`, over `numVars tm T S` — label/state/cell
  coordinates of the machine configuration), embedded on the left via `Fin.castAdd`;
* the **continuation register** block (`OneHotRegister`, over `regNumVars T V` — a one-hot
  value of a `Fintype V` at each time step), embedded on the right via `Fin.natAdd`.

The two blocks live side by side: `mainVar (coordVar …)` for the machine config and
`contVar t val` for the continuation.  Consistency is the append of the two lifted clause
sets (`fullConsistencyClauses`), and bridges to the conjunction of the underlying
consistencies (`fullConsistent_iff`).  Readback (`readConfigC`/`readContC`) and encoding
(`encodeC` via `Fin.addCases`) are thin wrappers whose correctness composes the underlying
round-trips.

Everything here is pure **composition** of the underlying gadget lemmas — no gadget fact is
reproved.  `noncomputable` throughout (the indexings of both blocks are noncomputable).
-/

open Turing

namespace DeepWiki

namespace CombinedTableau

open TableauSchema OneHotRegister BooleanConstraints

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

variable {tm : FinTM2} {T S : ℕ} {V : Type}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]
variable [Fintype V] [DecidableEq V] [Inhabited V]

/-! ## (1) Combined size and the two variable blocks -/

variable (tm T S V) in
/-- The **combined variable count**: the main tableau block plus the continuation register.
A reducible `abbrev` so `Fin (fullNumVars …)` unfolds to `Fin (numVars … + regNumVars …)` and the
offset-lift lemmas (`Fin.castAdd`/`Fin.natAdd`, `satisfiesAll_append_lift`) apply directly. -/
abbrev fullNumVars : ℕ := numVars tm T S + regNumVars T V

/-- A **main-block variable**: a tableau coordinate embedded on the left via `Fin.castAdd`. -/
noncomputable def mainVar (c : TableauCoord tm T S) : Fin (fullNumVars tm T S V) :=
  Fin.castAdd (regNumVars T V) (coordVar c)

/-- A **continuation-block variable**: a register coordinate embedded on the right via
`Fin.natAdd`. -/
noncomputable def contVar (t : Fin (T + 1)) (val : V) : Fin (fullNumVars tm T S V) :=
  Fin.natAdd (numVars tm T S) (regVar t val)

/-! ## (2) Assignment restrictions to the two blocks -/

/-- Restrict a combined assignment to the **main block** (the left `castAdd` factor). -/
def mainAssign (assign : Fin (fullNumVars tm T S V) → Bool) : Fin (numVars tm T S) → Bool :=
  fun i => assign (Fin.castAdd (regNumVars T V) i)

/-- Restrict a combined assignment to the **continuation block** (the right `natAdd` factor). -/
def contAssign (assign : Fin (fullNumVars tm T S V) → Bool) : Fin (regNumVars T V) → Bool :=
  fun i => assign (Fin.natAdd (numVars tm T S) i)

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] [DecidableEq V]
  [Inhabited V] in
/-- `mainAssign` at a tableau coordinate is the combined assignment at its `mainVar`. -/
@[simp] theorem mainAssign_mainVar (assign : Fin (fullNumVars tm T S V) → Bool)
    (c : TableauCoord tm T S) :
    mainAssign assign (coordVar c) = assign (mainVar (V := V) c) := rfl

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] [DecidableEq V]
  [Inhabited V] in
/-- `contAssign` at a register coordinate is the combined assignment at its `contVar`. -/
@[simp] theorem contAssign_contVar (assign : Fin (fullNumVars tm T S V) → Bool)
    (t : Fin (T + 1)) (val : V) :
    contAssign assign (regVar t val) = assign (contVar (tm := tm) (S := S) t val) := rfl

/-! ## (3) Combined consistency and the bridge to the two blocks -/

variable (tm T S V) in
/-- The **combined consistency clauses**: the left-lifted main consistency clauses appended to the
right-lifted register consistency clauses. -/
noncomputable def fullConsistencyClauses :
    List (Clause (numVars tm T S + regNumVars T V)) :=
  liftClausesL (consistencyClauses tm T S) ++ liftClausesR (regConsistencyClauses T V)

/-- An assignment is **fully consistent** iff it satisfies every combined consistency clause. -/
def FullConsistent (assign : Fin (fullNumVars tm T S V) → Bool) : Prop :=
  satisfiesAll assign (fullConsistencyClauses tm T S V)

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] [DecidableEq V]
  [Inhabited V] in
/-- **Consistency bridge.** Full consistency decomposes as the main block's `Consistent` of the
main restriction and the register block's `RegConsistent` of the continuation restriction. -/
theorem fullConsistent_iff (assign : Fin (fullNumVars tm T S V) → Bool) :
    FullConsistent assign ↔
      Consistent (mainAssign assign) ∧ RegConsistent (contAssign assign) := by
  rw [FullConsistent, fullConsistencyClauses, satisfiesAll_append_lift]
  rfl

/-! ## (4) Combined readback -/

/-- The **combined configuration read** at time `t`: the main block's `readConfig` of the main
restriction. -/
noncomputable def readConfigC (assign : Fin (fullNumVars tm T S V) → Bool) (t : Fin (T + 1)) :
    tm.Cfg :=
  readConfig (mainAssign assign) t

/-- The **combined continuation read** at time `t`: the register block's `readReg` of the
continuation restriction. -/
noncomputable def readContC (assign : Fin (fullNumVars tm T S V) → Bool) (t : Fin (T + 1)) : V :=
  readReg (contAssign assign) t

/-! ## (5) Combined encoding and the round-trips -/

/-- The **combined encoding** of a configuration sequence and a continuation sequence: the main
block uses `encodeSeq cfgs`, the continuation block uses `encodeReg conts`, glued by
`Fin.addCases`. -/
noncomputable def encodeC (cfgs : Fin (T + 1) → tm.Cfg) (conts : Fin (T + 1) → V) :
    Fin (fullNumVars tm T S V) → Bool :=
  Fin.addCases (motive := fun _ => Bool) (encodeSeq cfgs) (encodeReg conts)

omit [Inhabited V] in
/-- The main restriction of `encodeC` is exactly `encodeSeq cfgs`. -/
@[simp] theorem mainAssign_encodeC (cfgs : Fin (T + 1) → tm.Cfg) (conts : Fin (T + 1) → V) :
    mainAssign (encodeC (S := S) (V := V) cfgs conts) = encodeSeq cfgs := by
  funext i
  exact Fin.addCases_left (motive := fun _ => Bool) i

omit [Inhabited V] in
/-- The continuation restriction of `encodeC` is exactly `encodeReg conts`. -/
@[simp] theorem contAssign_encodeC (cfgs : Fin (T + 1) → tm.Cfg) (conts : Fin (T + 1) → V) :
    contAssign (encodeC (S := S) (V := V) cfgs conts) = encodeReg conts := by
  funext i
  exact Fin.addCases_right (motive := fun _ => Bool) i

omit [Inhabited V] in
/-- **Combined encoding is consistent.** `encodeC` of a real configuration/continuation pair
satisfies every combined consistency clause. -/
theorem encodeC_fullConsistent (cfgs : Fin (T + 1) → tm.Cfg) (conts : Fin (T + 1) → V) :
    FullConsistent (encodeC (S := S) (V := V) cfgs conts) := by
  rw [fullConsistent_iff, mainAssign_encodeC, contAssign_encodeC]
  exact ⟨encodeSeq_consistent cfgs, encodeReg_regConsistent conts⟩

/-- **Continuation round-trip.** Reading back the combined encoding recovers the continuation at
each time. -/
theorem readContC_encodeC (cfgs : Fin (T + 1) → tm.Cfg) (conts : Fin (T + 1) → V)
    (t : Fin (T + 1)) :
    readContC (encodeC (S := S) cfgs conts) t = conts t := by
  rw [readContC, contAssign_encodeC, readReg_encodeReg]

omit [Inhabited V] in
/-- **Configuration round-trip.** With every stack of `cfgs t` fitting in `S`, reading back the
combined encoding recovers the whole configuration at time `t`. -/
theorem readConfigC_encodeC (cfgs : Fin (T + 1) → tm.Cfg) (conts : Fin (T + 1) → V)
    (t : Fin (T + 1)) (hS : ∀ k, ((cfgs t).stk k).length ≤ S) :
    readConfigC (V := V) (encodeC (S := S) cfgs conts) t = cfgs t := by
  rw [readConfigC, mainAssign_encodeC, readConfig_encodeSeq cfgs t hS]

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

variable {tm : FinTM2} {T S : ℕ} {V : Type}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]
variable [Fintype V] [DecidableEq V] [Inhabited V]

-- Full consistency is the conjunction of the two block consistencies on their restrictions.
example (assign : Fin (fullNumVars tm T S V) → Bool) :
    FullConsistent assign ↔
      Consistent (mainAssign assign) ∧ RegConsistent (contAssign assign) :=
  fullConsistent_iff assign

-- The combined encode-then-read round-trip recovers the continuation at each time.
example (cfgs : Fin (T + 1) → tm.Cfg) (conts : Fin (T + 1) → V) (t : Fin (T + 1)) :
    readContC (encodeC (S := S) cfgs conts) t = conts t :=
  readContC_encodeC cfgs conts t

end Examples

end CombinedTableau

end DeepWiki
