import DeepWiki.NetworkCalculus.StmtSmallStep

/-!
# Uniform continuous small-step semantics for `Turing.TM2`

Layer 3b-iii(c) of a Cook- and Levin-style formalization: a *uniform* small-step
function `unifStep` over `(continuation, state, stacks)` that, unlike
`TM2SmallStep.stmtStep`, is total and never "terminal" — at a `goto f` it loads
the *next* label's program `M (f v)`, and at `halt` it moves to the halted
continuation `none` (a fixed point). Thus the same one-step function applies at
every time step, which is what the tableau needs.

The headline bridge `exists_unifStep_iterate_step` relates iterated `unifStep`
to one big-step `Turing.TM2.stepAux`/`step`: from `(some (M l), v, S)`,
iterating `unifStep` reaches `contOfLabel (stepAux (M l) v S).l` with the
big-step `var`/`stk`, for some fuel `n`.

Deferred to later layers: the multi-big-step trace concatenation (iterating this
bridge across the whole computation), the tableau clause encoding of `unifStep`,
and reduction correctness.
-/

open Function (update)

namespace DeepWiki

namespace UnifSmallStep

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}

open Turing.TM2 Turing.TM2.Stmt

/-- A uniform small-step configuration: a *continuation* (an optional statement,
`none` = halted, `some q` = about to execute `q`), the local state, and stacks. -/
def UnifState (Γ : K → Type*) (Λ σ : Type*) : Type _ :=
  Option (Turing.TM2.Stmt Γ Λ σ) × σ × (∀ k, List (Γ k))

/-- Read a TM2 label into a continuation: `none ↦ none` (halted), `some l ↦
some (M l)` (load the label's program). The big-step `Cfg.l` lives here. -/
def contOfLabel (M : Λ → Turing.TM2.Stmt Γ Λ σ) : Option Λ → Option (Turing.TM2.Stmt Γ Λ σ)
  | none => none
  | some l => some (M l)

omit [DecidableEq K] in
@[simp] theorem contOfLabel_none (M : Λ → Turing.TM2.Stmt Γ Λ σ) :
    contOfLabel M none = none := rfl

omit [DecidableEq K] in
@[simp] theorem contOfLabel_some (M : Λ → Turing.TM2.Stmt Γ Λ σ) (l : Λ) :
    contOfLabel M (some l) = some (M l) := rfl

/-- The uniform step: peels one statement constructor like `stmtStep`, but at a
`goto f` loads the target program `some (M (f v))` (NON-terminal) and at `halt`
moves to the halted continuation `none`; the halted state `none` is a fixed point. -/
def unifStep (M : Λ → Turing.TM2.Stmt Γ Λ σ) : UnifState Γ Λ σ → UnifState Γ Λ σ
  | (some (push k f q'), v, S) => (some q', v, update S k (f v :: S k))
  | (some (peek k f q'), v, S) => (some q', f v (S k).head?, S)
  | (some (pop k f q'), v, S) => (some q', f v (S k).head?, update S k (S k).tail)
  | (some (load a q'), v, S) => (some q', a v, S)
  | (some (branch f q₁ q₂), v, S) => (some (cond (f v) q₁ q₂), v, S)
  | (some (goto f), v, S) => (some (M (f v)), v, S)
  | (some Turing.TM2.Stmt.halt, v, S) => (none, v, S)
  | (none, v, S) => (none, v, S)

variable (M : Λ → Turing.TM2.Stmt Γ Λ σ)

@[simp] theorem unifStep_push (k : K) (f : σ → Γ k) (q' : Turing.TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) :
    unifStep M (some (push k f q'), v, S) = (some q', v, update S k (f v :: S k)) := rfl

@[simp] theorem unifStep_peek (k : K) (f : σ → Option (Γ k) → σ) (q' : Turing.TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) :
    unifStep M (some (peek k f q'), v, S) = (some q', f v (S k).head?, S) := rfl

@[simp] theorem unifStep_pop (k : K) (f : σ → Option (Γ k) → σ) (q' : Turing.TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) :
    unifStep M (some (pop k f q'), v, S) = (some q', f v (S k).head?, update S k (S k).tail) := rfl

@[simp] theorem unifStep_load (a : σ → σ) (q' : Turing.TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) :
    unifStep M (some (load a q'), v, S) = (some q', a v, S) := rfl

@[simp] theorem unifStep_branch (f : σ → Bool) (q₁ q₂ : Turing.TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) :
    unifStep M (some (branch f q₁ q₂), v, S) = (some (cond (f v) q₁ q₂), v, S) := rfl

@[simp] theorem unifStep_goto (f : σ → Λ) (v : σ) (S : ∀ k, List (Γ k)) :
    unifStep M (some (goto f), v, S) = (some (M (f v)), v, S) := rfl

@[simp] theorem unifStep_halt (v : σ) (S : ∀ k, List (Γ k)) :
    unifStep M (some Turing.TM2.Stmt.halt, v, S) = (none, v, S) := rfl

/-- The halted continuation `none` is a fixed point of `unifStep`. -/
@[simp] theorem unifStep_none (v : σ) (S : ∀ k, List (Γ k)) :
    unifStep M (none, v, S) = (none, v, S) := rfl

/-- Iterating `unifStep` from the halted state stays halted. -/
theorem unifStep_halted_iterate (n : ℕ) (v : σ) (S : ∀ k, List (Γ k)) :
    (unifStep M)^[n] (none, v, S) = (none, v, S) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, unifStep_none, ih]

/-- INDUCTIVE CORE: from `(some q, v, S)`, *some* number of `unifStep` moves
reach the continuation/state/stacks read off the big-step `stepAux q v S` via
`contOfLabel`. The within-statement moves agree with `stmtStep`; the terminal
`goto f`/`halt` take ONE move (to `some (M (f v))` / `none`) where `stmtStep`
would have returned the `Cfg`. Proof: structural induction on `q` — `push`/
`peek`/`pop`/`load` prepend one move and recurse; `branch` takes the chosen
arm's witness; `goto`/`halt` are the one-move base cases. -/
theorem exists_unifStep_iterate_stmt (q : Turing.TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    ∃ n, (unifStep M)^[n] (some q, v, S) =
      (contOfLabel M (Turing.TM2.stepAux q v S).l, (Turing.TM2.stepAux q v S).var,
        (Turing.TM2.stepAux q v S).stk) := by
  induction q generalizing v S with
  | push k f q ih =>
    obtain ⟨n, hn⟩ := ih v (update S k (f v :: S k))
    exact ⟨n + 1, by rw [Function.iterate_succ_apply, unifStep_push]; simpa using hn⟩
  | peek k f q ih =>
    obtain ⟨n, hn⟩ := ih (f v (S k).head?) S
    exact ⟨n + 1, by rw [Function.iterate_succ_apply, unifStep_peek]; simpa using hn⟩
  | pop k f q ih =>
    obtain ⟨n, hn⟩ := ih (f v (S k).head?) (update S k (S k).tail)
    exact ⟨n + 1, by rw [Function.iterate_succ_apply, unifStep_pop]; simpa using hn⟩
  | load a q ih =>
    obtain ⟨n, hn⟩ := ih (a v) S
    exact ⟨n + 1, by rw [Function.iterate_succ_apply, unifStep_load]; simpa using hn⟩
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases hb : f v with
    | false =>
      obtain ⟨n, hn⟩ := ih₂ v S
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply, unifStep_branch]
      simp only [Turing.TM2.stepAux, hb, Bool.cond_false]
      exact hn
    | true =>
      obtain ⟨n, hn⟩ := ih₁ v S
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ_apply, unifStep_branch]
      simp only [Turing.TM2.stepAux, hb, Bool.cond_true]
      exact hn
  | goto f => exact ⟨1, by rw [Function.iterate_one, unifStep_goto]; rfl⟩
  | halt => exact ⟨1, by rw [Function.iterate_one, unifStep_halt]; rfl⟩

/-- HEADLINE BRIDGE: from `(some (M l), v, S)`, iterating `unifStep` reaches the
state encoding the next big-step config `stepAux (M l) v S`, i.e. its label read
through `contOfLabel`, with the big-step `var`/`stk`. Since
`Turing.TM2.step M ⟨some l, v, S⟩ = some (stepAux (M l) v S)`, the reached
uniform state encodes exactly the next `step`. -/
theorem exists_unifStep_iterate_step (l : Λ) (v : σ) (S : ∀ k, List (Γ k)) :
    ∃ n, (unifStep M)^[n] (some (M l), v, S) =
      (contOfLabel M (Turing.TM2.stepAux (M l) v S).l, (Turing.TM2.stepAux (M l) v S).var,
        (Turing.TM2.stepAux (M l) v S).stk) :=
  exists_unifStep_iterate_stmt M (M l) v S

/-- `Turing.TM2.step` on a labelled config is `some` of the big-step `stepAux`
(the config the headline bridge's reached uniform state encodes). -/
theorem step_eq_some_stepAux (l : Λ) (v : σ) (S : ∀ k, List (Γ k)) :
    Turing.TM2.step M ⟨some l, v, S⟩ = some (Turing.TM2.stepAux (M l) v S) := rfl

/-- The halted state is a fixed point of `unifStep`. -/
example (v : σ) (S : ∀ k, List (Γ k)) : unifStep M (none, v, S) = (none, v, S) :=
  unifStep_none M v S

/-- Iterating `unifStep` from the halted state stays halted. -/
example (n : ℕ) (v : σ) (S : ∀ k, List (Γ k)) :
    (unifStep M)^[n] (none, v, S) = (none, v, S) :=
  unifStep_halted_iterate M n v S

/-- The bridge: iterating `unifStep` from `(some (M l), v, S)` reaches the
uniform state encoding `step M ⟨some l, v, S⟩`. -/
example (l : Λ) (v : σ) (S : ∀ k, List (Γ k)) :
    ∃ n, (unifStep M)^[n] (some (M l), v, S) =
      (contOfLabel M (Turing.TM2.stepAux (M l) v S).l, (Turing.TM2.stepAux (M l) v S).var,
        (Turing.TM2.stepAux (M l) v S).stk) :=
  exists_unifStep_iterate_step M l v S

end UnifSmallStep

end DeepWiki
