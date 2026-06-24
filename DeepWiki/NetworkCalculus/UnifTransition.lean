import DeepWiki.NetworkCalculus.ContTransition
import DeepWiki.NetworkCalculus.StateTransitionAssembly
import DeepWiki.NetworkCalculus.CellTransitionAssembly

/-!
# Full per-time-step transition correctness for the Cook- and Levin-style tableau

Layer 3c-iii: the **unified transition** of the combined tableau, assembling the three
clause families — `ContTransition.contTransClauses` (continuation), `StateTransitionAssembly.
stateTransClauses` (state), `CellTransitionAssembly.cellTransClauses` (stacks) — into one
family `unifTransClauses` whose satisfaction forces a single uniform small step:
`readUnif (t+1) = unifStep (readUnif t)` on the unified `UnifSmallStep.UnifState` reading.

* `readUnif` — the unified readback at a time: the `UnifState` triple
  `(contToUnif (readContC …), readState …, stacks)`, with `readUnif_fst`/`readUnif_snd_fst`/
  `readUnif_snd_snd` exposing its components by `rfl`.
* `contToUnif_unifNextCont` — the both-cases continuation bridge:
  `contToUnif (unifNextCont tm cont v) = (unifStep tm.m (contToUnif cont, v, S')).1`, for any
  stack argument `S'` (the continuation component of `unifStep` ignores the stacks).
* `unifTransClauses` — the concatenation `contTransClauses ++ stateTransClauses ++ cellTransClauses`.
* `unifTransClauses_spec` — pure **composition**: `satisfiesAll_append` splits off the three
  families, each `_spec` lemma supplies one component of the `UnifState` triple, and
  `Prod.ext`/`funext` reassembles `readUnif (t+1) = unifStep (readUnif t)`.

## Deferred

This chunk is the per-time correctness only, with `IsStackShape@t.castSucc` and
`length < S` as hypotheses (mirroring the state- and cell- assemblies' hypothesis style).
The `IsStackShape` invariant *propagation* across time (`@t.castSucc ⟹ @t.succ`, a cell-level
argument), the multi-step `readUnif@N = unifStep^[N] (readUnif@0)` induction, init- and accept-
clauses, and reduction correctness are **later** layers.
-/

open Turing

namespace DeepWiki

namespace CombinedTableau

open TableauSchema OneHotRegister BooleanConstraints ReachableCont UnifSmallStep
open Turing.TM2 Turing.TM2.Stmt

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.decidableEqK

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

/-! ## (1) The unified readback -/

/-- The **unified readback** at time `t`: the `UnifState` triple of the read continuation (with
its membership proof forgotten by `contToUnif`), the read state, and the read stacks. -/
noncomputable def readUnif (assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool)
    (t : Fin (T + 1)) : UnifState tm.Γ tm.Λ tm.σ :=
  (contToUnif (readContC assign t), readState (mainAssign assign) t,
    fun k => readStack (mainAssign assign) t k)

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- The continuation component of `readUnif`. -/
@[simp] theorem readUnif_fst (assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool)
    (t : Fin (T + 1)) : (readUnif assign t).1 = contToUnif (readContC assign t) := rfl

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- The state component of `readUnif`. -/
@[simp] theorem readUnif_snd_fst (assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool)
    (t : Fin (T + 1)) : (readUnif assign t).2.1 = readState (mainAssign assign) t := rfl

omit [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- The stacks component of `readUnif`. -/
@[simp] theorem readUnif_snd_snd (assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool)
    (t : Fin (T + 1)) :
    (readUnif assign t).2.2 = fun k => readStack (mainAssign assign) t k := rfl

/-! ## (2) The both-cases continuation bridge -/

omit [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ] in
/-- **Continuation bridge (both cases).** `contToUnif` of the next continuation equals the
continuation component of one `unifStep` from the forgotten continuation, state, and *any* stacks
`S'`: at `none`, `unifNextCont_none`/`unifStep_none` (and `contToUnif none = none`); at
`some ⟨q, hq⟩`, `unifNextCont_eq_unifStep` (with `contToUnif (some ⟨q, hq⟩) = some q`).  The RHS
does not depend on `S'`. -/
theorem contToUnif_unifNextCont (cont : ContTok tm) (v : tm.σ) (S' : ∀ k, List (tm.Γ k)) :
    contToUnif (unifNextCont tm cont v) = (unifStep tm.m (contToUnif cont, v, S')).1 := by
  cases cont with
  | none =>
    show contToUnif (unifNextCont tm none v) = (unifStep tm.m ((none : Option _), v, S')).1
    rw [unifNextCont_none, contToUnif_none, unifStep_none]
  | some w =>
    obtain ⟨q, hq⟩ := w
    rw [contToUnif_some]
    show (unifNextCont tm (some ⟨q, hq⟩) v).map Subtype.val = (unifStep tm.m (some q, v, S')).1
    exact unifNextCont_eq_unifStep q hq v S'

/-! ## (3) The combined transition clauses -/

variable (tm S) in
/-- The **unified transition clauses** over `t → t+1`: the concatenation of the continuation-,
state-, and cell- transition clause families. -/
noncomputable def unifTransClauses (t : Fin T) (hS0 : 0 < S) :
    List (Clause (fullNumVars tm T S (ContTok tm))) :=
  contTransClauses tm T S t ++ stateTransClauses tm S t hS0 ++ cellTransClauses tm S t

/-! ## (4) Full per-time-step correctness -/

/-- **Full per-time correctness.** Under full consistency, the per-stack stack-shape hypothesis,
and the per-stack room hypothesis (`length < S`) at the time-`t` cells, a satisfying assignment to
the unified transition clauses forces one uniform small step: `readUnif (t+1) = unifStep
(readUnif t)`.  Pure composition of the three `_spec` lemmas through `satisfiesAll_append` and the
continuation bridge `contToUnif_unifNextCont`, reassembled componentwise by `Prod.ext`/`funext`. -/
theorem unifTransClauses_spec {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {t : Fin T} {hS0 : 0 < S}
    (hsat : satisfiesAll assign (unifTransClauses tm S t hS0))
    (hshape : ∀ k, IsStackShape (fun i : Fin S => readCell (mainAssign assign) t.castSucc k i)
      (readStack (mainAssign assign) t.castSucc k))
    (hlen : ∀ k, (readStack (mainAssign assign) t.castSucc k).length < S) :
    readUnif assign t.succ = unifStep tm.m (readUnif assign t.castSucc) := by
  -- split the satisfaction of the concatenation into the three clause families
  rw [unifTransClauses, satisfiesAll_append, satisfiesAll_append] at hsat
  obtain ⟨⟨hcont, hstate⟩, hcell⟩ := hsat
  -- reassemble the `UnifState` triple componentwise
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · -- continuation: contTransClauses_spec, then the both-cases bridge
    rw [readUnif_fst, contTransClauses_spec hcons hcont,
      contToUnif_unifNextCont (readContC assign t.castSucc)
        (readState (mainAssign assign) t.castSucc)
        (fun k => readStack (mainAssign assign) t.castSucc k)]
    rfl
  · -- state: stateTransClauses_spec directly
    rw [readUnif_snd_fst, stateTransClauses_spec hcons hstate hshape]
    rfl
  · -- stacks: cellTransClauses_spec pointwise
    rw [readUnif_snd_snd]
    funext k'
    rw [cellTransClauses_spec hcons hcell hshape hlen k']
    rfl

/-! ## Sanity restatements (intent checks against the design) -/

section Examples

variable {tm : FinTM2} {T S : ℕ}
variable [∀ k, Fintype (tm.Γ k)] [∀ k, DecidableEq (tm.Γ k)] [DecidableEq tm.Λ] [DecidableEq tm.σ]

-- The unified transition clauses force one uniform small step on the unified readback.
example {assign : Fin (fullNumVars tm T S (ContTok tm)) → Bool}
    (hcons : FullConsistent assign) {t : Fin T} {hS0 : 0 < S}
    (hsat : satisfiesAll assign (unifTransClauses tm S t hS0))
    (hshape : ∀ k, IsStackShape (fun i : Fin S => readCell (mainAssign assign) t.castSucc k i)
      (readStack (mainAssign assign) t.castSucc k))
    (hlen : ∀ k, (readStack (mainAssign assign) t.castSucc k).length < S) :
    readUnif assign t.succ = unifStep tm.m (readUnif assign t.castSucc) :=
  unifTransClauses_spec hcons hsat hshape hlen

end Examples

end CombinedTableau

end DeepWiki
