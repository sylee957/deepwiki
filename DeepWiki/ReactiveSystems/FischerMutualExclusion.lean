import DeepWiki.ReactiveSystems.TimedAutomata

/-! # Fischer's mutual-exclusion algorithm (§13.2)
Fischer's algorithm achieves mutual exclusion for `n` processes through *timing*
rather than atomic test-and-set: each process writes its index into a shared
register `id`, waits long enough for any competing write to settle, and enters
its critical section only if it still owns `id`. The book models it as a network
of timed automata, one per process (Figure 13.1, the automaton `Aᵢ` with control
locations `L → 1 → 2 → CS`, a clock `xᵢ`, and the bound `c`).

Here the network is a single `TimedAutomaton` over a *global* location that folds
the shared register `id` (so the register guards `id = 0` / `id = i` / `id ≠ i`
and assignments `id := i` / `id := 0` become conditions on the location) together
with one clock per process. Mutual exclusion is the safety property that no two
processes occupy their critical sections simultaneously. Its correctness
(Lynch–Shavit, Theorem 4.6) rests on the timing assumptions and is verified
externally (UPPAAL); we formalize the model and the specification. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- The four control locations of Fischer's process automaton `Aᵢ` (Figure 13.1):
the waiting loop `L`, the write location `1` (invariant `xᵢ ≤ c`), the post-write
test location `2`, and the critical section `CS`. -/
inductive FischerCtrl
  | wait
  | setting
  | testing
  | critical
  deriving DecidableEq

/-- A global location of the Fischer network of `n` processes: each process's
control location together with the shared register `id` (`none` ≙ `0`, free;
`some i` ≙ process `i`'s value). -/
structure FischerLoc (n : ℕ) where
  /-- The control location of each process. -/
  ctrl : Fin n → FischerCtrl
  /-- The shared register: `none` is free (`0`); `some i` is process `i`. -/
  id : Option (Fin n)

namespace FischerLoc

variable {n : ℕ}

/-- **Mutual exclusion** (the safety specification): no two distinct processes are
in their critical sections at the same time. -/
def MutualExclusion (ℓ : FischerLoc n) : Prop :=
  ∀ i j, ℓ.ctrl i = .critical → ℓ.ctrl j = .critical → i = j

end FischerLoc

/-- The location invariant of the Fischer network: every process currently
writing (at location `1`, `setting`) must act within `c` time units (`xᵢ ≤ c`). -/
def fischerInv (c : ℕ) {n : ℕ} (ℓ : FischerLoc n) : ClockConstraint (Fin n) :=
  (List.finRange n).foldr
    (fun i g => if ℓ.ctrl i = .setting then .and (.atom i .le c) g else g) .true_

/-- The invariant holds exactly when every writing process's clock is at most
`c`. -/
theorem satisfies_fischerInv {n c : ℕ} (ℓ : FischerLoc n) (v : Valuation (Fin n)) :
    satisfies v (fischerInv c ℓ) ↔ ∀ i, ℓ.ctrl i = .setting → v i ≤ c := by
  have aux : ∀ l : List (Fin n),
      satisfies v (l.foldr
        (fun i g => if ℓ.ctrl i = .setting then .and (.atom i .le c) g else g) .true_)
        ↔ ∀ i ∈ l, ℓ.ctrl i = .setting → v i ≤ c := by
    intro l
    induction l with
    | nil => simp [satisfies]
    | cons a t ih =>
        rw [List.foldr_cons]
        by_cases h : ℓ.ctrl a = .setting
        · rw [if_pos h]
          simp only [satisfies, Cmp.holds, List.mem_cons, ih]
          constructor
          · rintro ⟨ha, ht⟩ i (rfl | hi) hset
            · exact ha
            · exact ht i hi hset
          · intro hall
            exact ⟨hall a (Or.inl rfl) h, fun i hi hset => hall i (Or.inr hi) hset⟩
        · rw [if_neg h, ih]
          simp only [List.mem_cons]
          constructor
          · rintro ht i (rfl | hi) hset
            · exact absurd hset h
            · exact ht i hi hset
          · intro hall i hi hset; exact hall i (Or.inr hi) hset
  rw [fischerInv, aux]
  simp

/-- The edge relation of the Fischer network (Figure 13.1): some process `i`
takes one of its five steps. With `id` folded into the location, the register
guards and assignments become conditions on the global location; the clock guard
`g` and reset set `r` carry the timing (`xᵢ ≥ c` before re-checking, `xᵢ := 0` on
the two writing steps). -/
def fischerEdge (c : ℕ) {n : ℕ} (ℓ : FischerLoc n)
    (g : ClockConstraint (Fin n)) (_a : Unit) (r : Set (Fin n)) (ℓ' : FischerLoc n) : Prop :=
  ∃ i : Fin n,
    -- L → 1 : id = 0, reset xᵢ
    (ℓ.ctrl i = .wait ∧ ℓ.id = none ∧ g = .true_ ∧ r = {i} ∧
        ℓ' = ⟨Function.update ℓ.ctrl i .setting, ℓ.id⟩) ∨
    -- 1 → 2 : id := i, reset xᵢ
    (ℓ.ctrl i = .setting ∧ g = .true_ ∧ r = {i} ∧
        ℓ' = ⟨Function.update ℓ.ctrl i .testing, some i⟩) ∨
    -- 2 → CS : id = i ∧ xᵢ ≥ c
    (ℓ.ctrl i = .testing ∧ ℓ.id = some i ∧ g = .atom i .ge c ∧ r = ∅ ∧
        ℓ' = ⟨Function.update ℓ.ctrl i .critical, ℓ.id⟩) ∨
    -- 2 → L : id ≠ i ∧ xᵢ ≥ c
    (ℓ.ctrl i = .testing ∧ ℓ.id ≠ some i ∧ g = .atom i .ge c ∧ r = ∅ ∧
        ℓ' = ⟨Function.update ℓ.ctrl i .wait, ℓ.id⟩) ∨
    -- CS → L : id := 0 (release)
    (ℓ.ctrl i = .critical ∧ g = .true_ ∧ r = ∅ ∧
        ℓ' = ⟨Function.update ℓ.ctrl i .wait, none⟩)

/-- **§13.2.** Fischer's mutual-exclusion algorithm modelled as a network of `n`
timed automata (Figure 13.1): the shared register `id` is folded into the global
location, with one clock `xᵢ` per process and bound `c`. The initial location has
every process waiting and the register free. -/
def fischer (n c : ℕ) : TimedAutomaton (FischerLoc n) Unit (Fin n) where
  initial := ⟨fun _ => .wait, none⟩
  edge := fischerEdge c
  inv := fischerInv c

/-- The Fischer network is **safe** when mutual exclusion holds at every reachable
global location. (Theorem 4.6 of Lynch–Shavit: this holds under the timing
assumptions; the proof is delegated to external verification.) -/
def FischerSafe (n c : ℕ) : Prop :=
  ∀ s, (fischer n c).tlts.Reachable ((fischer n c).initial, fun _ => 0) s →
    s.1.MutualExclusion

/-- Sanity check: the initial global location satisfies mutual exclusion (no
process is in its critical section). -/
theorem fischer_initial_mutualExclusion (n c : ℕ) :
    (fischer n c).initial.MutualExclusion := by
  intro i _ hi _
  simp [fischer] at hi

end DeepWiki.ReactiveSystems
