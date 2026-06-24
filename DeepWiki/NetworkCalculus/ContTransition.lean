import DeepWiki.NetworkCalculus.CombinedTableau
import DeepWiki.NetworkCalculus.ReachableCont
import DeepWiki.NetworkCalculus.TableauCellTransition

/-!
# Continuation-transition clauses for the combined Cook- and Levin-style tableau

Layer 3c-i: the **continuation update** of the unified tableau.  Specializing the combined
variable space (`CombinedTableau`) to register-value type `V := ReachableCont.ContTok tm`, this
file encodes the single uniform continuation step `ReachableCont.unifNextCont` as one binary
finite-function gadget (`BooleanConstraints.funClauses₂`) directly over the combined
`Fin (fullNumVars …)` space:

* `contTransClauses` — the clause list whose two `funClauses₂` inputs are the continuation
  variable at `t.castSucc` and the *state* tableau variable at `t.castSucc`, and whose output is
  the continuation variable at `t.succ`;
* `contTransClauses_spec` — its `readContC`-level correctness: under full consistency, a satisfying
  assignment reads back `readContC … t.succ = unifNextCont tm (readContC … t.castSucc)
  (readState … t.castSucc)`;
* `contTransClauses_satisfies` — the encode direction: the combined encoding of a continuation
  sequence that follows `unifNextCont` satisfies the clauses.

This is pure **composition**: `funClauses₂_spec` plus the two self-true facts
(`OneHotRegister.readReg_self_true` on the continuation block, `TableauSchema.readState_self_true`
on the main block), bridged through the defeq `contAssign_contVar` and `mainAssign_mainVar`, then
`readReg_eq` to land at `readContC`.  No gadget fact is reproved.

Deferred to later layers: the state-transition assembly (lifting the state-update gadgets into the
combined space, conditioned per continuation for the load- and peek- and pop- distinction); the
cell-transition assembly (push and pop per continuation); the full per-time
`readUnif (t+1) = unifStep (readUnif t)` correctness; `IsStackShape` propagation; init and accept;
and reduction correctness.
-/

open Turing

namespace DeepWiki

namespace CombinedTableau

open TableauSchema OneHotRegister BooleanConstraints ReachableCont

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

/-! ## (1) The continuation-transition clauses -/

/-- The **continuation-transition clauses** at step `t`: the binary finite-function gadget that
forces the continuation register at `t.succ` to `unifNextCont tm` of the continuation register at
`t.castSucc` and the machine state at `t.castSucc`.  All three index functions land in the combined
`Fin (fullNumVars … (ContTok tm))` space, so no offset lift is needed. -/
noncomputable def contTransClauses (tm : FinTM2) (T S : ℕ)
    [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]
    (t : Fin T) : List (Clause (fullNumVars tm T S (ContTok tm))) :=
  funClauses₂
    (fun c => contVar (S := S) (V := ContTok tm) t.castSucc c)
    (fun s => mainVar (V := ContTok tm) (stateCoord t.castSucc s))
    (fun c => contVar (S := S) (V := ContTok tm) t.succ c)
    (unifNextCont tm)

/-! ## (2) Readback-level correctness (forward / decode) -/

/-- **Forward spec.** Under full consistency, a satisfying assignment reads back the continuation
register at `t.succ` as `unifNextCont tm` of the continuation register at `t.castSucc` and the state
at `t.castSucc`. -/
theorem contTransClauses_spec {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hfull : FullConsistent assign) {t : Fin T}
    (hsat : satisfiesAll assign (contTransClauses tm T S t)) :
    readContC assign t.succ =
      unifNextCont tm (readContC assign t.castSucc) (readState (mainAssign assign) t.castSucc) := by
  obtain ⟨hmain, hreg⟩ := (fullConsistent_iff assign).1 hfull
  -- the continuation input variable is true at the actual read continuation
  have hinA : assign (contVar (S := S) (V := ContTok tm) t.castSucc (readContC assign t.castSucc))
      = true := by
    have := readReg_self_true hreg t.castSucc
    rwa [contAssign_contVar] at this
  -- the state input variable is true at the actual read state
  have hinB : assign (mainVar (V := ContTok tm)
      (stateCoord t.castSucc (readState (mainAssign assign) t.castSucc))) = true := by
    have := readState_self_true hmain t.castSucc
    rwa [mainAssign_mainVar] at this
  -- the gadget forces the output continuation variable true
  have hout := funClauses₂_spec
    (fun c => contVar (S := S) (V := ContTok tm) t.castSucc c)
    (fun s => mainVar (V := ContTok tm) (stateCoord t.castSucc s))
    (fun c => contVar (S := S) (V := ContTok tm) t.succ c)
    (unifNextCont tm) assign hsat
    (readContC assign t.castSucc) (readState (mainAssign assign) t.castSucc) hinA hinB
  -- read it back through the register block
  apply readReg_eq hreg
  rwa [contAssign_contVar]

/-! ## (3) Encode direction (forward step of the reduction) -/

/-- **Encode direction.** The combined encoding of a configuration sequence and a continuation
sequence that follows `unifNextCont` (`conts t.succ = unifNextCont tm (conts t.castSucc)
(cfgs t.castSucc).var`) satisfies the continuation-transition clauses. -/
theorem contTransClauses_satisfies (cfgs : Fin (T + 1) → tm.Cfg)
    (conts : Fin (T + 1) → ContTok tm) (t : Fin T)
    (hstep : conts t.succ = unifNextCont tm (conts t.castSucc) (cfgs t.castSucc).var) :
    satisfiesAll (encodeC (S := S) cfgs conts) (contTransClauses tm T S t) := by
  refine funClauses₂_satisfies _ _ _ _ _ (fun c s hc hs => ?_)
  -- a true continuation input pins `c = conts t.castSucc`
  simp only [← contAssign_contVar, contAssign_encodeC] at hc
  have hcval : c = conts t.castSucc := by
    have := (readReg_eq (encodeReg_regConsistent conts) hc).symm
    rwa [readReg_encodeReg] at this
  -- a true state input pins `s = (cfgs t.castSucc).var`
  simp only [← mainAssign_mainVar, mainAssign_encodeC] at hs
  have hsval : s = (cfgs t.castSucc).var := by
    have := (readState_eq (encodeSeq_consistent cfgs) hs).symm
    rwa [readState_encodeSeq] at this
  subst hcval hsval
  -- the output continuation variable is true because `conts t.succ` follows the step
  simp only [← contAssign_contVar, contAssign_encodeC, encodeReg_regVar, decide_eq_true_iff, hstep]

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- A satisfying, fully consistent assignment reads back the next continuation as `unifNextCont`.
example {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hfull : FullConsistent assign) {t : Fin T}
    (hsat : satisfiesAll assign (contTransClauses tm T S t)) :
    readContC assign t.succ =
      unifNextCont tm (readContC assign t.castSucc) (readState (mainAssign assign) t.castSucc) :=
  contTransClauses_spec hfull hsat

-- The combined encoding of a `unifNextCont`-following continuation sequence satisfies the clauses.
example (cfgs : Fin (T + 1) → tm.Cfg) (conts : Fin (T + 1) → ContTok tm) (t : Fin T)
    (hstep : conts t.succ = unifNextCont tm (conts t.castSucc) (cfgs t.castSucc).var) :
    satisfiesAll (encodeC (S := S) cfgs conts) (contTransClauses tm T S t) :=
  contTransClauses_satisfies cfgs conts t hstep

end Examples

end CombinedTableau

end DeepWiki
