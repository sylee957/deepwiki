import DeepWiki.NetworkCalculus.CombinedInit
import DeepWiki.NetworkCalculus.CombinedAccept
import DeepWiki.NetworkCalculus.TransitionEncode

/-!
# Encode direction for the Cook- and Levin-style boundary clauses

Layer 3c-v (encode side): the **converse** of the boundary decode lemmas — encoding a trace
whose endpoints sit at `initList`/`haltList` *satisfies* the combined init/accept clauses.

* `TableauSchema.encodeSeq_satisfies_haltClauses` — the halt analog of
  `encodeSeq_satisfies_initClauses`: a sequence with `cfgs (Fin.last T) = haltList tm acceptOutput`
  satisfies the main halt clauses (label `none`, state `tm.initialState`, cells over `haltList`).
* `initClausesC_satisfies` — the combined init clauses are satisfied by `encodeC cfgs conts` when
  `cfgs 0 = initList tm input` and `conts 0 = some ⟨tm.m tm.main, _⟩`.
* `acceptClausesC_satisfies` — the combined accept clauses are satisfied by `encodeC cfgs conts`
  when `cfgs (Fin.last T) = haltList tm acceptOutput` and `conts (Fin.last T) = none`.

Pure mirroring: `encodeSeq_satisfies_initClauses` for the halt main block, then
`satisfiesAll_append` + `satisfiesAll_liftClausesL` + `mainAssign_encodeC` (lifted main block) and
`encodeC_contVarFin` (the cont unit clause) for the combined assemblies — exactly the structure of
`initClausesC`/`acceptClausesC`.

## Deferred

Only init/accept (and the halt main sub-lemma) encode-satisfies. The full per-time formula
assembly, `Satisfiable ⟺ accepts`, the witness-trace construction, the polynomial-size bound, and
the final `cookLevin` reduction discharge are **later** layers.
-/

open Turing

namespace DeepWiki

namespace TableauSchema

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

open BooleanConstraints

variable {tm : FinTM2} {T S : ℕ} [∀ k, Fintype (tm.Γ k)]

/-! ## (1) Halt-clause encode (main block) -/

section Encode

variable [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

/-- **Halt-clause converse.** Encoding a sequence whose time-`last` configuration is
`haltList tm acceptOutput` satisfies the halt clauses. Mirror of `encodeSeq_satisfies_initClauses`
at `Fin.last T` (label `none`, state `tm.initialState`, cells over `haltList`). -/
theorem encodeSeq_satisfies_haltClauses (cfgs : Fin (T + 1) → tm.Cfg)
    (acceptOutput : List (tm.Γ tm.k₁)) (hlast : cfgs (Fin.last T) = haltList tm acceptOutput) :
    satisfiesAll (encodeSeq (S := S) cfgs) (haltClauses tm T S acceptOutput) := by
  rw [haltClauses, satisfiesAll_cons, satisfiesAll_cons]
  refine ⟨?_, ?_, ?_⟩
  · -- the label unit clause
    simp only [CnfFormula.clauseSat, List.any_cons, List.any_nil, CnfFormula.litSat, Bool.or_false,
      beq_iff_eq, encodeSeq_labelCoord, hlast]
    simp [haltList]
  · -- the state unit clause
    simp only [CnfFormula.clauseSat, List.any_cons, List.any_nil, CnfFormula.litSat, Bool.or_false,
      beq_iff_eq, encodeSeq_stateCoord, hlast]
    simp [haltList]
  · -- the cell unit clauses
    rw [List.flatMap_def, satisfiesAll_flatten]
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index]
    rintro g k rfl
    intro c hc
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hc
    obtain ⟨i, rfl⟩ := hc
    simp only [CnfFormula.clauseSat, List.any_cons, List.any_nil, CnfFormula.litSat, Bool.or_false,
      beq_iff_eq, encodeSeq_cellCoord, hlast]

end Encode

end TableauSchema

namespace CombinedTableau

open TableauSchema OneHotRegister BooleanConstraints ReachableCont UnifSmallStep

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

/-! ## (2) Cont unit-clause evaluation over `Fin (T + 1)` -/

/-- **One-hot `contVar` evaluation (full time range).** `encodeC cfgs conts` at `contVar t cont` is
`decide (cont = conts t)`: it is `true` exactly on the real continuation. The `Fin (T + 1)`
companion of `encodeC_contVar` (which is stated through `Fin.castSucc` on `Fin T`). -/
theorem encodeC_contVarFin (cfgs : Fin (T + 1) → tm.Cfg) (conts : Fin (T + 1) → ContTok tm)
    (t : Fin (T + 1)) (cont : ContTok tm) :
    encodeC (S := S) cfgs conts (contVar (V := ContTok tm) t cont)
      = decide (cont = conts t) := by
  simp only [← contAssign_contVar, contAssign_encodeC, encodeReg_regVar]

/-! ## (3) Combined init-clause encode -/

/-- **Combined init converse.** Encoding a `(cfgs, conts)` trace starting at `initList tm input`
on the main block and at `some ⟨tm.m tm.main, _⟩` on the continuation register satisfies the
combined init clauses. -/
theorem initClausesC_satisfies (cfgs : Fin (T + 1) → tm.Cfg) (conts : Fin (T + 1) → ContTok tm)
    (input : List (tm.Γ tm.k₀)) (h0cfg : cfgs (0 : Fin (T + 1)) = initList tm input)
    (h0cont : conts (0 : Fin (T + 1)) =
      (some ⟨tm.m tm.main, program_mem_relevant tm tm.main⟩ : ContTok tm)) :
    satisfiesAll (encodeC (S := S) cfgs conts) (initClausesC tm T S input) := by
  refine (satisfiesAll_append (encodeC (S := S) cfgs conts) (liftClausesL (initClauses tm T S input))
    [[(contVar (tm := tm) (S := S) (0 : Fin (T + 1))
        (some ⟨tm.m tm.main, program_mem_relevant tm tm.main⟩ : ContTok tm), true)]]).mpr ⟨?_, ?_⟩
  · -- the lifted main init clauses, dropped to the main block (= `encodeSeq cfgs`)
    rw [satisfiesAll_liftClausesL]
    show satisfiesAll (mainAssign (encodeC (S := S) cfgs conts)) (initClauses tm T S input)
    rw [mainAssign_encodeC]
    exact encodeSeq_satisfies_initClauses cfgs input h0cfg
  · -- the cont unit clause: `decide (some ⟨…⟩ = conts 0) = true` from `h0cont`
    intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    simp only [CnfFormula.clauseSat, List.any_cons, List.any_nil, CnfFormula.litSat, Bool.or_false,
      beq_iff_eq, encodeC_contVarFin, decide_eq_true_eq]
    exact h0cont.symm

/-! ## (4) Combined accept-clause encode -/

/-- **Combined accept converse.** Encoding a `(cfgs, conts)` trace ending at
`haltList tm acceptOutput` on the main block and at the halted token `none` on the continuation
register satisfies the combined accept clauses. -/
theorem acceptClausesC_satisfies (cfgs : Fin (T + 1) → tm.Cfg) (conts : Fin (T + 1) → ContTok tm)
    (acceptOutput : List (tm.Γ tm.k₁)) (hlcfg : cfgs (Fin.last T) = haltList tm acceptOutput)
    (hlcont : conts (Fin.last T) = (none : ContTok tm)) :
    satisfiesAll (encodeC (S := S) cfgs conts) (acceptClausesC tm T S acceptOutput) := by
  refine (satisfiesAll_append (encodeC (S := S) cfgs conts) (liftClausesL (haltClauses tm T S acceptOutput))
    [[(contVar (tm := tm) (S := S) (Fin.last T) (none : ContTok tm), true)]]).mpr ⟨?_, ?_⟩
  · -- the lifted main halt clauses, dropped to the main block (= `encodeSeq cfgs`)
    rw [satisfiesAll_liftClausesL]
    show satisfiesAll (mainAssign (encodeC (S := S) cfgs conts)) (haltClauses tm T S acceptOutput)
    rw [mainAssign_encodeC]
    exact encodeSeq_satisfies_haltClauses cfgs acceptOutput hlcfg
  · -- the cont unit clause: `decide (none = conts last) = true` from `hlcont`
    intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    simp only [CnfFormula.clauseSat, List.any_cons, List.any_nil, CnfFormula.litSat, Bool.or_false,
      beq_iff_eq, encodeC_contVarFin, decide_eq_true_eq]
    exact hlcont.symm

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- The combined init clauses are satisfied by the encoding of a trace starting at `initList`.
example (cfgs : Fin (T + 1) → tm.Cfg) (conts : Fin (T + 1) → ContTok tm)
    (input : List (tm.Γ tm.k₀)) (h0cfg : cfgs (0 : Fin (T + 1)) = initList tm input)
    (h0cont : conts (0 : Fin (T + 1)) =
      (some ⟨tm.m tm.main, program_mem_relevant tm tm.main⟩ : ContTok tm)) :
    satisfiesAll (encodeC (S := S) cfgs conts) (initClausesC tm T S input) :=
  initClausesC_satisfies cfgs conts input h0cfg h0cont

-- The combined accept clauses are satisfied by the encoding of a trace ending at `haltList`.
example (cfgs : Fin (T + 1) → tm.Cfg) (conts : Fin (T + 1) → ContTok tm)
    (acceptOutput : List (tm.Γ tm.k₁)) (hlcfg : cfgs (Fin.last T) = haltList tm acceptOutput)
    (hlcont : conts (Fin.last T) = (none : ContTok tm)) :
    satisfiesAll (encodeC (S := S) cfgs conts) (acceptClausesC tm T S acceptOutput) :=
  acceptClausesC_satisfies cfgs conts acceptOutput hlcfg hlcont

end Examples

end CombinedTableau

end DeepWiki
