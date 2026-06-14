import Book.ServersDrr

/-! # An operational semantics for the scheduler pseudocode
The book's scheduling algorithms (DRR, WRR, …) are imperative programs:
mutable per-flow packet queues and deficit counters, `while`/`for` loops,
and `send`/`removeHead` statements. This file gives them a formal
operational semantics — a machine `SchedState`, an arithmetic/boolean
expression language (`AExp`/`BExp`), a statement language (`Stmt`), and a
big-step evaluation relation `BigStep`. A statement diverges exactly when
it has no `BigStep` derivation, so the non-terminating outer `while True`
needs no special treatment: one round (a pass of the per-flow `for` loop)
is a statement, and inner-loop termination is a theorem, not a definitional
side condition. The concrete algorithms and their soundness against the
functional models (`drrServe`/`wrrServe`) live in the `*Semantics`
chapters that import this one. -/

namespace DeepWiki

open scoped Classical NNReal

/-- Scheduler machine state over `n` flows: per-flow packet queue
`queue i` (head = front), per-flow deficit counter `dc i`, the cumulative
output trace `out` (served sizes, in order), and the scalar loop variable
`kvar` (the weighted-round-robin counter `k`). -/
structure SchedState (n : ℕ) where
  queue : Fin n → List ℝ≥0
  dc : Fin n → ℝ≥0
  out : List ℝ≥0
  kvar : ℕ

namespace SchedState
variable {n : ℕ}

/-- Functional update of one flow's queue. -/
def setQueue (σ : SchedState n) (i : Fin n) (q : List ℝ≥0) : SchedState n :=
  { σ with queue := Function.update σ.queue i q }

/-- Functional update of one flow's deficit counter `DC[i]`. -/
def setDc (σ : SchedState n) (i : Fin n) (d : ℝ≥0) : SchedState n :=
  { σ with dc := Function.update σ.dc i d }

/-- `send(x)`: append a served size to the output trace. -/
def emit (σ : SchedState n) (x : ℝ≥0) : SchedState n :=
  { σ with out := σ.out ++ [x] }

/-- Set the scalar loop counter `k`. -/
def setK (σ : SchedState n) (k : ℕ) : SchedState n := { σ with kvar := k }

end SchedState

/-- `size(head(i))`: the head packet's size (`0` on the empty queue). -/
def headSize {n : ℕ} (σ : SchedState n) (i : Fin n) : ℝ≥0 :=
  (σ.queue i).headI

/-- Arithmetic expressions: the deficit-counter RHS forms of the
pseudocode — constants, `DC[i]`, `size(head(i))`, sums and truncated
differences. -/
inductive AExp (n : ℕ) where
  | lit (c : ℝ≥0)
  | dc (i : Fin n)
  | headSize (i : Fin n)
  | add (a b : AExp n)
  | sub (a b : AExp n)

/-- Value of an arithmetic expression in a state. -/
def AExp.eval {n : ℕ} (σ : SchedState n) : AExp n → ℝ≥0
  | lit c => c
  | dc i => σ.dc i
  | headSize i => _root_.DeepWiki.headSize σ i
  | add a b => a.eval σ + b.eval σ
  | sub a b => a.eval σ - b.eval σ

/-- Boolean guards: queue non-emptiness, a `≤` test between arithmetic
expressions, the weight test `k ≤ w`, and conjunction. -/
inductive BExp (n : ℕ) where
  | notEmpty (i : Fin n)
  | le (a b : AExp n)
  | kLe (w : ℕ)
  | and (a b : BExp n)

/-- Value of a boolean guard in a state. -/
noncomputable def BExp.eval {n : ℕ} (σ : SchedState n) : BExp n → Bool
  | notEmpty i => !(σ.queue i).isEmpty
  | le a b => decide (a.eval σ ≤ b.eval σ)
  | kLe w => decide (σ.kvar ≤ w)
  | and a b => a.eval σ && b.eval σ

/-- Statements: structural forms (`skip`, sequencing, `if`, `while`) plus
the domain primitives — counter assignment `DC[i] ← e`, the loop-counter
updates `k ← c` and `k ← k + 1`, and `serveHead i` fusing
`send(head(i)); removeHead(i)`. -/
inductive Stmt (n : ℕ) where
  | skip
  | seq (s t : Stmt n)
  | ifte (b : BExp n) (s t : Stmt n)
  | whileB (b : BExp n) (body : Stmt n)
  | assignDc (i : Fin n) (a : AExp n)
  | setK (c : ℕ)
  | incK
  | serveHead (i : Fin n)

/-- **Big-step operational semantics**: `BigStep s σ σ'` holds when
running statement `s` from `σ` terminates in `σ'`. A divergent statement
(e.g. the outer `while True`) simply has no derivation. -/
inductive BigStep {n : ℕ} : Stmt n → SchedState n → SchedState n → Prop where
  | skip (σ) : BigStep .skip σ σ
  | seq {s t σ σ' σ''} :
      BigStep s σ σ' → BigStep t σ' σ'' → BigStep (.seq s t) σ σ''
  | ifTrue {b s t σ σ'} :
      b.eval σ = true → BigStep s σ σ' → BigStep (.ifte b s t) σ σ'
  | ifFalse {b s t σ σ'} :
      b.eval σ = false → BigStep t σ σ' → BigStep (.ifte b s t) σ σ'
  | whileFalse {b body σ} :
      b.eval σ = false → BigStep (.whileB b body) σ σ
  | whileTrue {b body σ σ' σ''} :
      b.eval σ = true → BigStep body σ σ' →
      BigStep (.whileB b body) σ' σ'' → BigStep (.whileB b body) σ σ''
  | assignDc {i a σ} :
      BigStep (.assignDc i a) σ (σ.setDc i (a.eval σ))
  | setK {c σ} : BigStep (.setK c) σ (σ.setK c)
  | incK {σ} : BigStep .incK σ (σ.setK (σ.kvar + 1))
  | serveHead {i σ} :
      BigStep (.serveHead i) σ
        ((σ.emit (headSize σ i)).setQueue i (σ.queue i).tail)

/-- One scheduling round: run `body i` for each flow `i` in turn,
`for i = 1 to n do body i`, desugared to a chain of `seq`. -/
def roundStmt {n : ℕ} (body : Fin n → Stmt n) : Stmt n :=
  (List.finRange n).foldr (fun i s => .seq (body i) s) .skip

/-! ## State-update field lemmas -/

namespace SchedState
variable {n : ℕ}

@[simp] theorem setDc_dc (σ : SchedState n) (i : Fin n) (d : ℝ≥0) :
    (σ.setDc i d).dc = Function.update σ.dc i d := rfl

@[simp] theorem setDc_queue (σ : SchedState n) (i : Fin n) (d : ℝ≥0) :
    (σ.setDc i d).queue = σ.queue := rfl

@[simp] theorem setDc_kvar (σ : SchedState n) (i : Fin n) (d : ℝ≥0) :
    (σ.setDc i d).kvar = σ.kvar := rfl

@[simp] theorem setQueue_queue (σ : SchedState n) (i : Fin n)
    (q : List ℝ≥0) : (σ.setQueue i q).queue = Function.update σ.queue i q :=
  rfl

@[simp] theorem setQueue_dc (σ : SchedState n) (i : Fin n) (q : List ℝ≥0) :
    (σ.setQueue i q).dc = σ.dc := rfl

@[simp] theorem setQueue_kvar (σ : SchedState n) (i : Fin n)
    (q : List ℝ≥0) : (σ.setQueue i q).kvar = σ.kvar := rfl

@[simp] theorem emit_queue (σ : SchedState n) (x : ℝ≥0) :
    (σ.emit x).queue = σ.queue := rfl

@[simp] theorem emit_dc (σ : SchedState n) (x : ℝ≥0) :
    (σ.emit x).dc = σ.dc := rfl

@[simp] theorem emit_kvar (σ : SchedState n) (x : ℝ≥0) :
    (σ.emit x).kvar = σ.kvar := rfl

@[simp] theorem setK_dc (σ : SchedState n) (k : ℕ) :
    (σ.setK k).dc = σ.dc := rfl

@[simp] theorem setK_queue (σ : SchedState n) (k : ℕ) :
    (σ.setK k).queue = σ.queue := rfl

@[simp] theorem setK_kvar (σ : SchedState n) (k : ℕ) :
    (σ.setK k).kvar = k := rfl

@[simp] theorem emit_out (σ : SchedState n) (x : ℝ≥0) :
    (σ.emit x).out = σ.out ++ [x] := rfl

@[simp] theorem setQueue_out (σ : SchedState n) (i : Fin n) (q : List ℝ≥0) :
    (σ.setQueue i q).out = σ.out := rfl

@[simp] theorem setDc_out (σ : SchedState n) (i : Fin n) (d : ℝ≥0) :
    (σ.setDc i d).out = σ.out := rfl

@[simp] theorem setK_out (σ : SchedState n) (k : ℕ) :
    (σ.setK k).out = σ.out := rfl

end SchedState

/-! ## Inversion of the big-step relation -/

variable {n : ℕ}

/-- `skip` leaves the state unchanged. -/
@[simp] theorem bigStep_skip_iff {σ σ' : SchedState n} :
    BigStep .skip σ σ' ↔ σ' = σ :=
  ⟨fun h => by cases h; rfl, fun h => by subst h; exact .skip _⟩

/-- A sequence splits at an intermediate state. -/
theorem bigStep_seq_iff {s t : Stmt n} {σ σ'' : SchedState n} :
    BigStep (.seq s t) σ σ'' ↔ ∃ σ', BigStep s σ σ' ∧ BigStep t σ' σ'' :=
  ⟨fun h => by cases h with | seq h1 h2 => exact ⟨_, h1, h2⟩,
   fun ⟨_, h1, h2⟩ => .seq h1 h2⟩

/-- Counter assignment sets `DC[i]` to the expression's value. -/
@[simp] theorem bigStep_assignDc_iff {i : Fin n} {a : AExp n}
    {σ σ' : SchedState n} :
    BigStep (.assignDc i a) σ σ' ↔ σ' = σ.setDc i (a.eval σ) :=
  ⟨fun h => by cases h; rfl, fun h => by subst h; exact .assignDc⟩

/-- `serveHead i` emits the head size and drops the head of queue `i`. -/
@[simp] theorem bigStep_serveHead_iff {i : Fin n} {σ σ' : SchedState n} :
    BigStep (.serveHead i) σ σ'
      ↔ σ' = (σ.emit (headSize σ i)).setQueue i (σ.queue i).tail :=
  ⟨fun h => by cases h; rfl, fun h => by subst h; exact .serveHead⟩

/-- `k ← c`. -/
@[simp] theorem bigStep_setK_iff {c : ℕ} {σ σ' : SchedState n} :
    BigStep (.setK c) σ σ' ↔ σ' = σ.setK c :=
  ⟨fun h => by cases h; rfl, fun h => by subst h; exact .setK⟩

/-- `k ← k + 1`. -/
@[simp] theorem bigStep_incK_iff {σ σ' : SchedState n} :
    BigStep .incK σ σ' ↔ σ' = σ.setK (σ.kvar + 1) :=
  ⟨fun h => by cases h; rfl, fun h => by subst h; exact .incK⟩

/-- An `if` branches on its guard. -/
theorem bigStep_ifte_iff {b : BExp n} {s t : Stmt n} {σ σ' : SchedState n} :
    BigStep (.ifte b s t) σ σ'
      ↔ (b.eval σ = true ∧ BigStep s σ σ')
        ∨ (b.eval σ = false ∧ BigStep t σ σ') :=
  ⟨fun h => by
      cases h with
      | ifTrue hc h => exact Or.inl ⟨hc, h⟩
      | ifFalse hc h => exact Or.inr ⟨hc, h⟩,
   fun h => h.elim (fun ⟨hc, h⟩ => .ifTrue hc h) (fun ⟨hc, h⟩ => .ifFalse hc h)⟩

/-- One unfolding of a `while`: either the guard is false and the state is
unchanged, or it is true and the body runs once before the loop repeats. -/
theorem bigStep_whileB_iff {b : BExp n} {body : Stmt n} {σ σ' : SchedState n} :
    BigStep (.whileB b body) σ σ'
      ↔ (b.eval σ = false ∧ σ' = σ)
        ∨ (b.eval σ = true ∧ ∃ σm, BigStep body σ σm
            ∧ BigStep (.whileB b body) σm σ') := by
  constructor
  · intro h
    cases h with
    | whileFalse hc => exact Or.inl ⟨hc, rfl⟩
    | whileTrue hc hbody hrest => exact Or.inr ⟨hc, _, hbody, hrest⟩
  · rintro (⟨hc, rfl⟩ | ⟨hc, σm, hbody, hrest⟩)
    · exact .whileFalse hc
    · exact .whileTrue hc hbody hrest

end DeepWiki
