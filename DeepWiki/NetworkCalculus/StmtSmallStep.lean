import Mathlib.Computability.TuringMachine.StackTuringMachine

/-!
# Small-step semantics for `Turing.TM2.Stmt`

Layer 3b-iii(b) of a Cook- and Levin-style formalization: a small-step
semantics for `Turing.TM2.Stmt` decomposing one big-step `Turing.TM2.stepAux`
into O(1)-local moves (`stmtStep`), each peeling off ONE statement constructor,
plus the proof that iterating `stmtStep` (the runner `runStmt`) equals `stepAux`.
A statement size `stmtSize` (strictly decreasing along `stmtStep`, lemma
`stmtStep_size_lt`) makes the runner terminate; `runFuel` gives a bounded
small-step count (`runFuel_stmtSize_succ`), the time axis the tableau will use.

Deferred to later layers (consumers of this file): the tableau encoding of
`stmtStep` as clauses (continuation one-hot variables, `funClauses` for the
state and stack functions, cell updates for `push` and `pop`), the
halt-padding of the big-step trace, and reduction correctness.
-/

open Function (update)

namespace DeepWiki

namespace TM2SmallStep

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}

open Turing.TM2 Turing.TM2.Stmt

/-- `stmtSize q`: a strictly-decreasing-along-`stmtStep` measure; `1` for the
terminal `goto`/`halt`, `+1` per peeled constructor (`branch` adds both arms).
The `≥ 1` leaf size keeps the `branch` fuel bound `runFuel_stmtSize_succ` clean. -/
def stmtSize : Turing.TM2.Stmt Γ Λ σ → ℕ
  | push _ _ q => stmtSize q + 1
  | peek _ _ q => stmtSize q + 1
  | pop _ _ q => stmtSize q + 1
  | load _ q => stmtSize q + 1
  | branch _ q₁ q₂ => stmtSize q₁ + stmtSize q₂ + 1
  | goto _ => 1
  | halt => 1

omit [DecidableEq K] in
/-- Every statement has at least one small step (`1 ≤ stmtSize q`). -/
theorem one_le_stmtSize (q : Turing.TM2.Stmt Γ Λ σ) : 1 ≤ stmtSize q := by
  cases q <;> simp [stmtSize]

/-- A small-step configuration: a continuation statement, the local state, and the stacks. -/
def StmtState (Γ : K → Type*) (Λ σ : Type*) : Type _ :=
  Turing.TM2.Stmt Γ Λ σ × σ × (∀ k, List (Γ k))

/-- One small step of `Turing.TM2.Stmt`: peel off a single constructor, either
producing a new `StmtState` continuation (`Sum.inl`) or a final `Cfg` (`Sum.inr`).
Mirrors `Turing.TM2.stepAux` one constructor at a time. -/
def stmtStep : Turing.TM2.Stmt Γ Λ σ → σ → (∀ k, List (Γ k)) →
    StmtState Γ Λ σ ⊕ Turing.TM2.Cfg Γ Λ σ
  | push k f q, v, S => Sum.inl (q, v, update S k (f v :: S k))
  | peek k f q, v, S => Sum.inl (q, f v (S k).head?, S)
  | pop k f q, v, S => Sum.inl (q, f v (S k).head?, update S k (S k).tail)
  | load a q, v, S => Sum.inl (q, a v, S)
  | branch f q₁ q₂, v, S => Sum.inl (cond (f v) q₁ q₂, v, S)
  | goto f, v, S => Sum.inr ⟨some (f v), v, S⟩
  | halt, v, S => Sum.inr ⟨none, v, S⟩

omit [DecidableEq K] in
/-- `stmtSize (cond b q₁ q₂) < stmtSize q₁ + stmtSize q₂ + 1` for either choice of `b`. -/
theorem stmtSize_cond_lt (b : Bool) (q₁ q₂ : Turing.TM2.Stmt Γ Λ σ) :
    stmtSize (cond b q₁ q₂) < stmtSize q₁ + stmtSize q₂ + 1 := by
  cases b <;> simp <;> omega

/-- A small step to a continuation strictly decreases `stmtSize`. -/
theorem stmtStep_size_lt {q : Turing.TM2.Stmt Γ Λ σ} {v : σ} {S : ∀ k, List (Γ k)}
    {st : StmtState Γ Λ σ} (h : stmtStep q v S = Sum.inl st) :
    stmtSize st.1 < stmtSize q := by
  cases q with
  | push k f q => cases h; simp [stmtSize]
  | peek k f q => cases h; simp [stmtSize]
  | pop k f q => cases h; simp [stmtSize]
  | load a q => cases h; simp [stmtSize]
  | branch f q₁ q₂ =>
    cases h; simpa [stmtSize] using stmtSize_cond_lt (f v) q₁ q₂
  | goto f => simp [stmtStep] at h
  | halt => simp [stmtStep] at h

/-- The iterated runner: apply `stmtStep` until it produces a final `Cfg`.
Terminates by well-founded recursion on `stmtSize` via `stmtStep_size_lt`. -/
def runStmt : Turing.TM2.Stmt Γ Λ σ → σ → (∀ k, List (Γ k)) → Turing.TM2.Cfg Γ Λ σ
  | q, v, S =>
    match _h : stmtStep q v S with
    | Sum.inl (q', v', S') => runStmt q' v' S'
    | Sum.inr c => c
  termination_by q => stmtSize q
  decreasing_by exact stmtStep_size_lt ‹_›

/-- KEY LEMMA: iterating `stmtStep` (the `runStmt` runner) computes the big-step
`Turing.TM2.stepAux`. -/
theorem runStmt_eq_stepAux (q : Turing.TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    runStmt q v S = Turing.TM2.stepAux q v S := by
  induction q generalizing v S with
  | push k f q ih => rw [runStmt]; simp only [stmtStep]; exact ih _ _
  | peek k f q ih => rw [runStmt]; simp only [stmtStep]; exact ih _ _
  | pop k f q ih => rw [runStmt]; simp only [stmtStep]; exact ih _ _
  | load a q ih => rw [runStmt]; simp only [stmtStep]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    rw [runStmt]; simp only [stmtStep, Turing.TM2.stepAux]
    cases f v with
    | false => simpa using ih₂ v S
    | true => simpa using ih₁ v S
  | goto f => rw [runStmt]; rfl
  | halt => rw [runStmt]; rfl

/-- `Turing.TM2.step` on a labelled config is `some` of the small-step runner. -/
theorem step_eq_runStmt (M : Λ → Turing.TM2.Stmt Γ Λ σ) (l : Λ) (v : σ)
    (S : ∀ k, List (Γ k)) :
    Turing.TM2.step M ⟨some l, v, S⟩ = some (runStmt (M l) v S) := by
  rw [runStmt_eq_stepAux]; rfl

/-- Fuel-indexed runner: at most `n` small steps, `none` if fuel runs out. -/
def runFuel : ℕ → StmtState Γ Λ σ → Option (Turing.TM2.Cfg Γ Λ σ)
  | 0, _ => none
  | n + 1, (q, v, S) =>
    match stmtStep q v S with
    | Sum.inl st => runFuel n st
    | Sum.inr c => some c

/-- Fuel monotonicity: once `runFuel m` succeeds, any larger fuel `n` gives the same `Cfg`. -/
theorem runFuel_le_of_le {m n : ℕ} (hmn : m ≤ n) {st : StmtState Γ Λ σ}
    {c : Turing.TM2.Cfg Γ Λ σ} (h : runFuel m st = some c) : runFuel n st = some c := by
  induction m generalizing n st with
  | zero => simp [runFuel] at h
  | succ m ih =>
    obtain ⟨q, v, S⟩ := st
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [runFuel] at h ⊢
    cases hstep : stmtStep q v S with
    | inl st' => rw [hstep] at h; exact ih (by omega) h
    | inr c' => rw [hstep] at h; exact h

/-- One fuel-step on a continuation move: `runFuel (n+1)` peels the `stmtStep` and recurses. -/
theorem runFuel_succ_inl {n : ℕ} {q : Turing.TM2.Stmt Γ Λ σ} {v : σ} {S : ∀ k, List (Γ k)}
    {st : StmtState Γ Λ σ} (h : stmtStep q v S = Sum.inl st) :
    runFuel (n + 1) (q, v, S) = runFuel n st := by
  simp only [runFuel, h]

/-- `stmtSize q + 1` fuel suffices to reach the big-step `stepAux` config. -/
theorem runFuel_stmtSize_succ (q : Turing.TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    runFuel (stmtSize q + 1) (q, v, S) = some (Turing.TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    rw [runFuel_succ_inl (by rfl : stmtStep (push k f q) v S = Sum.inl _)]; exact ih _ _
  | peek k f q ih =>
    rw [runFuel_succ_inl (by rfl : stmtStep (peek k f q) v S = Sum.inl _)]; exact ih _ _
  | pop k f q ih =>
    rw [runFuel_succ_inl (by rfl : stmtStep (pop k f q) v S = Sum.inl _)]; exact ih _ _
  | load a q ih =>
    rw [runFuel_succ_inl (by rfl : stmtStep (load a q) v S = Sum.inl _)]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    rw [show stmtSize (branch f q₁ q₂) = stmtSize q₁ + stmtSize q₂ + 1 from rfl,
        runFuel_succ_inl (q := branch f q₁ q₂) (by rfl)]
    simp only [Turing.TM2.stepAux]
    cases f v with
    | false =>
      simp only [Bool.cond_false]
      have h₁ := one_le_stmtSize q₁
      exact runFuel_le_of_le (by omega) (ih₂ v S)
    | true =>
      simp only [Bool.cond_true]
      have h₂ := one_le_stmtSize q₂
      exact runFuel_le_of_le (by omega) (ih₁ v S)
  | goto f => simp [runFuel, stmtStep, Turing.TM2.stepAux]
  | halt => simp [runFuel, stmtStep, Turing.TM2.stepAux]

/-- The small-step runner agrees with Mathlib's big-step `stepAux`. -/
example (q : Turing.TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    runStmt q v S = Turing.TM2.stepAux q v S :=
  runStmt_eq_stepAux q v S

/-- `Turing.TM2.step` on a labelled config is `some` of the small-step runner. -/
example (M : Λ → Turing.TM2.Stmt Γ Λ σ) (l : Λ) (v : σ) (S : ∀ k, List (Γ k)) :
    Turing.TM2.step M ⟨some l, v, S⟩ = some (runStmt (M l) v S) :=
  step_eq_runStmt M l v S

/-- `stmtSize q + 1` small steps reach the big-step config (the tableau's time bound). -/
example (q : Turing.TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    runFuel (stmtSize q + 1) (q, v, S) = some (Turing.TM2.stepAux q v S) :=
  runFuel_stmtSize_succ q v S

end TM2SmallStep

end DeepWiki
