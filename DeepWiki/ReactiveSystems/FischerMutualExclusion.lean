import DeepWiki.ReactiveSystems.TimedAutomata
import Mathlib.Tactic.FinCases

/-! # Fischer's mutual-exclusion algorithm
Fischer's algorithm achieves mutual exclusion for `n` processes through *timing*
rather than atomic test-and-set: each process writes its index into a shared
register `id`, waits long enough for any competing write to settle, and enters
its critical section only if it still owns `id`. The book models it as a network
of timed automata, one per process (the automaton `Aᵢ` with control
locations `L → 1 → 2 → CS`, a clock `xᵢ`, and the bound `c`).

Here the network is a single `TimedAutomaton` over a *global* location that folds
the shared register `id` (so the register guards `id = 0` / `id = i` / `id ≠ i`
and assignments `id := i` / `id := 0` become conditions on the location) together
with one clock per process. Mutual exclusion is the safety property that no two
processes occupy their critical sections simultaneously. Its correctness
(Lynch–Shavit) rests on the timing assumptions; we formalize the model, the
specification, and a direct proof of safety for *every* `n` (`fischer_safe`), via an
inductive invariant on reachable configurations (`FischerInv`). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- The four control locations of Fischer's process automaton `Aᵢ`:
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

/-- The edge relation of the Fischer network: some process `i` takes one of its
five steps, with the node-`2` re-check guard `xᵢ ⋈ c` using comparison `cmp`.
With `id` folded into the location, the register guards and assignments become
conditions on the global location; the clock guard `g` and reset set `r` carry
the timing. The correct version uses `cmp = >` (strictly more than `c`);
the erroneous version uses `cmp = ≥` (exactly `c` suffices). -/
def fischerEdgeWith (cmp : Cmp) (c : ℕ) {n : ℕ} (ℓ : FischerLoc n)
    (g : ClockConstraint (Fin n)) (_a : Unit) (r : Set (Fin n)) (ℓ' : FischerLoc n) : Prop :=
  ∃ i : Fin n,
    -- L → 1 : id = 0, reset xᵢ
    (ℓ.ctrl i = .wait ∧ ℓ.id = none ∧ g = .true_ ∧ r = {i} ∧
        ℓ' = ⟨Function.update ℓ.ctrl i .setting, ℓ.id⟩) ∨
    -- 1 → 2 : id := i, reset xᵢ
    (ℓ.ctrl i = .setting ∧ g = .true_ ∧ r = {i} ∧
        ℓ' = ⟨Function.update ℓ.ctrl i .testing, some i⟩) ∨
    -- 2 → CS : id = i ∧ xᵢ ⋈ c
    (ℓ.ctrl i = .testing ∧ ℓ.id = some i ∧ g = .atom i cmp c ∧ r = ∅ ∧
        ℓ' = ⟨Function.update ℓ.ctrl i .critical, ℓ.id⟩) ∨
    -- 2 → L : id ≠ i ∧ xᵢ ⋈ c
    (ℓ.ctrl i = .testing ∧ ℓ.id ≠ some i ∧ g = .atom i cmp c ∧ r = ∅ ∧
        ℓ' = ⟨Function.update ℓ.ctrl i .wait, ℓ.id⟩) ∨
    -- CS → L : id := 0 (release)
    (ℓ.ctrl i = .critical ∧ g = .true_ ∧ r = ∅ ∧
        ℓ' = ⟨Function.update ℓ.ctrl i .wait, none⟩)

/-- Fischer's mutual-exclusion algorithm modelled as a network of `n`
timed automata: the shared register `id` is folded into the global
location, with one clock `xᵢ` per process and bound `c`; the node-`2` re-check
requires `xᵢ > c` (strictly more than `c` time elapsed). The initial location has
every process waiting and the register free. -/
def fischer (n c : ℕ) : TimedAutomaton (FischerLoc n) Unit (Fin n) where
  initial := ⟨fun _ => .wait, none⟩
  edge := fischerEdgeWith .gt c
  inv := fischerInv c

/-- The *erroneous* version of Fischer's algorithm: the
node-`2` re-check guard is weakened to `xᵢ ≥ c`, allowing a process to proceed
after a delay of *exactly* `c`. This version does not preserve mutual exclusion
(`not_fischerErroneous_mutualExclusion`). -/
def fischerErroneous (n c : ℕ) : TimedAutomaton (FischerLoc n) Unit (Fin n) where
  initial := ⟨fun _ => .wait, none⟩
  edge := fischerEdgeWith .ge c
  inv := fischerInv c

/-- The Fischer network is **safe** when mutual exclusion holds at every reachable
global location. (Lynch–Shavit: this holds under the timing assumptions; proved
directly for every `n` in `fischer_safe`.) -/
def FischerSafe (n c : ℕ) : Prop :=
  ∀ s, (fischer n c).tlts.Reachable ((fischer n c).initial, fun _ => 0) s →
    s.1.MutualExclusion

/-- Sanity check: the initial global location satisfies mutual exclusion (no
process is in its critical section). -/
theorem fischer_initial_mutualExclusion (n c : ℕ) :
    (fischer n c).initial.MutualExclusion := by
  intro i _ hi _
  simp [fischer] at hi

/-! ## Safety: Fischer preserves mutual exclusion for every `n`

We verify the model directly rather than delegating to UPPAAL, by exhibiting an inductive
invariant on the reachable configurations from which mutual exclusion follows. The
load-bearing clause is `crit_id` — *a process in its critical section owns `id`* — which
already forces mutual exclusion (two owners of `id` are equal, so two critical processes
coincide). Keeping `crit_id` inductive is where the **timing** enters: a writer `k` about
to overwrite `id` (`setting → testing`) cannot do so while another process `i` is critical,
because a critical `i` has clock `> c` (clause `crit_clock`, from the strict guard `xᵢ > c`)
yet `i`'s clock is `≤` every concurrent writer's clock (clause `owner_le`), while a writer's
clock is `≤ c` (the location invariant, clause `setting_le`) — an impossible
`c < vᵢ ≤ v_k ≤ c`. -/

/-- The inductive safety invariant for the (correct, strict-guard) Fischer network. -/
structure FischerInv (c : ℕ) {n : ℕ} (ℓ : FischerLoc n) (v : Valuation (Fin n)) : Prop where
  /-- A process in its critical section owns the register (forces mutual exclusion). -/
  crit_id : ∀ i, ℓ.ctrl i = .critical → ℓ.id = some i
  /-- A critical process's clock exceeds `c` (it passed the strict re-check `xᵢ > c`). -/
  crit_clock : ∀ i, ℓ.ctrl i = .critical → (c : ℝ≥0) < v i
  /-- A register-owning post-writer's clock is `≤` every concurrent writer's clock. -/
  owner_le : ∀ i j, (ℓ.ctrl i = .testing ∨ ℓ.ctrl i = .critical) → ℓ.id = some i →
      ℓ.ctrl j = .setting → v i ≤ v j
  /-- A writing process must act within `c` (the location invariant). -/
  setting_le : ∀ i, ℓ.ctrl i = .setting → v i ≤ (c : ℝ≥0)

/-- The initial configuration satisfies the invariant (every process waits, vacuously). -/
theorem fischerInv_initial (n c : ℕ) :
    FischerInv c (fischer n c).initial (fun _ => 0) where
  crit_id i h := by simp [fischer] at h
  crit_clock i h := by simp [fischer] at h
  owner_le i j h _ _ := by rcases h with h | h <;> simp [fischer] at h
  setting_le i h := by simp [fischer] at h

/-- Delay steps preserve the invariant: clocks advance uniformly, the location
invariant of the post-state is enforced by the semantics. -/
theorem fischerInv_delay {n c : ℕ} {ℓ ℓ' : FischerLoc n} {v v' : Valuation (Fin n)} {d : ℝ≥0}
    (hpre : FischerInv c ℓ v) (hstep : (fischer n c).tlts.delay (ℓ, v) d (ℓ', v')) :
    FischerInv c ℓ' v' := by
  rw [TimedAutomaton.tlts_delay_iff] at hstep
  obtain ⟨hℓ, hv, _, hpost⟩ := hstep
  rw [hℓ, hv]
  refine ⟨fun i hi => hpre.crit_id i hi, fun i hi => ?_, fun i j hi hid hj => ?_,
    (satisfies_fischerInv ℓ (v.add d)).mp hpost⟩
  · have hle : v i ≤ (v.add d) i := by rw [Valuation.add_apply]; exact le_self_add
    exact lt_of_lt_of_le (hpre.crit_clock i hi) hle
  · have := hpre.owner_le i j hi hid hj
    simp only [Valuation.add_apply]; gcongr

/-- Action steps preserve the invariant. The only clause needing the timing argument is
`crit_id` on the `setting → testing` edge: a write cannot occur while another process is
critical (`c < vᵢ ≤ v_k ≤ c`). -/
theorem fischerInv_act {n c : ℕ} {ℓ ℓ' : FischerLoc n} {v v' : Valuation (Fin n)}
    (hpre : FischerInv c ℓ v) (hstep : (fischer n c).tlts.act (ℓ, v) () (ℓ', v')) :
    FischerInv c ℓ' v' := by
  rw [TimedAutomaton.tlts_act_iff] at hstep
  obtain ⟨g, r, ⟨k, hk⟩, hg, hv', hpost⟩ := hstep
  rcases hk with ⟨hck, hidk, rfl, rfl, rfl⟩ | ⟨hck, rfl, rfl, rfl⟩ |
    ⟨hck, hidk, rfl, rfl, rfl⟩ | ⟨hck, hidk, rfl, rfl, rfl⟩ | ⟨hck, rfl, rfl, rfl⟩
  · -- wait → setting: id unchanged (= none), no new critical/owner facts
    subst hv'
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hi hid hj => ?_,
      (satisfies_fischerInv _ _).mp hpost⟩
    · simp only [Function.update_apply] at hi
      by_cases h : i = k
      · rw [if_pos h] at hi; exact absurd hi (by decide)
      · rw [if_neg h] at hi; exact hpre.crit_id i hi
    · simp only [Function.update_apply] at hi
      by_cases h : i = k
      · rw [if_pos h] at hi; exact absurd hi (by decide)
      · rw [if_neg h] at hi
        rw [Valuation.reset_not_mem (by simpa using h)]; exact hpre.crit_clock i hi
    · change ℓ.id = some i at hid; rw [hidk] at hid; exact absurd hid (by simp)
  · -- setting → testing: id := k. The timing argument lives in `crit_id` here.
    subst hv'
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hi hid hj => ?_,
      (satisfies_fischerInv _ _).mp hpost⟩
    · simp only [Function.update_apply] at hi
      by_cases h : i = k
      · rw [if_pos h] at hi; exact absurd hi (by decide)
      · rw [if_neg h] at hi
        -- i ≠ k critical while k writes: impossible by timing
        exfalso
        have h1 := hpre.crit_clock i hi
        have h2 := hpre.owner_le i k (Or.inr hi) (hpre.crit_id i hi) hck
        have h3 := hpre.setting_le k hck
        exact absurd (lt_of_lt_of_le (lt_of_lt_of_le h1 h2) h3) (lt_irrefl _)
    · simp only [Function.update_apply] at hi
      by_cases h : i = k
      · rw [if_pos h] at hi; exact absurd hi (by decide)
      · rw [if_neg h] at hi
        rw [Valuation.reset_not_mem (by simpa using h)]; exact hpre.crit_clock i hi
    · -- owner is k (id = some k); its reset clock 0 ≤ everything
      change some k = some i at hid
      have hik : i = k := (Option.some.inj hid).symm
      rw [hik, Valuation.reset_mem (show k ∈ ({k} : Set (Fin n)) by simp)]
      exact zero_le
  · -- testing → critical: guard xₖ > c, id = some k unchanged
    subst hv'
    simp only [satisfies, Cmp.holds] at hg
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hi hid hj => ?_,
      (satisfies_fischerInv _ _).mp hpost⟩
    · simp only [Function.update_apply] at hi
      by_cases h : i = k
      · subst h; exact hidk
      · rw [if_neg h] at hi; exact hpre.crit_id i hi
    · simp only [Function.update_apply] at hi
      by_cases h : i = k
      · subst h; rw [Valuation.reset_not_mem (by simp)]; exact hg
      · rw [if_neg h] at hi
        rw [Valuation.reset_not_mem (by simp)]; exact hpre.crit_clock i hi
    · change ℓ.id = some i at hid; rw [hidk] at hid
      have hik : i = k := (Option.some.inj hid).symm
      simp only [Function.update_apply] at hj
      by_cases hjk : j = k
      · rw [if_pos hjk] at hj; exact absurd hj (by decide)
      · rw [if_neg hjk] at hj
        rw [hik, Valuation.reset_not_mem (by simp), Valuation.reset_not_mem (by simp)]
        exact hpre.owner_le k j (Or.inl hck) hidk hj
  · -- testing → wait: id unchanged
    subst hv'
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hi hid hj => ?_,
      (satisfies_fischerInv _ _).mp hpost⟩
    · simp only [Function.update_apply] at hi
      by_cases h : i = k
      · rw [if_pos h] at hi; exact absurd hi (by decide)
      · rw [if_neg h] at hi; exact hpre.crit_id i hi
    · simp only [Function.update_apply] at hi
      by_cases h : i = k
      · rw [if_pos h] at hi; exact absurd hi (by decide)
      · rw [if_neg h] at hi
        rw [Valuation.reset_not_mem (by simp)]; exact hpre.crit_clock i hi
    · have hjk : j ≠ k := by
        rintro rfl; simp [Function.update] at hj
      have hik : i ≠ k := by
        rintro rfl
        rcases hi with hi | hi <;> simp [Function.update] at hi
      simp only [Function.update_apply] at hj; rw [if_neg hjk] at hj
      change ℓ.id = some i at hid
      rw [Valuation.reset_not_mem (by simp), Valuation.reset_not_mem (by simp)]
      refine hpre.owner_le i j ?_ hid hj
      rcases hi with hi | hi <;>
        (simp only [Function.update_apply] at hi; rw [if_neg hik] at hi)
      · exact Or.inl hi
      · exact Or.inr hi
  · -- critical → wait: id := none
    subst hv'
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hi hid hj => ?_,
      (satisfies_fischerInv _ _).mp hpost⟩
    · simp only [Function.update_apply] at hi
      by_cases h : i = k
      · rw [if_pos h] at hi; exact absurd hi (by decide)
      · rw [if_neg h] at hi
        exfalso
        have hki := hpre.crit_id k hck
        have hii := hpre.crit_id i hi
        exact h (Option.some.inj (hki.symm.trans hii)).symm
    · simp only [Function.update_apply] at hi
      by_cases h : i = k
      · rw [if_pos h] at hi; exact absurd hi (by decide)
      · rw [if_neg h] at hi
        rw [Valuation.reset_not_mem (by simp)]; exact hpre.crit_clock i hi
    · change (none : Option (Fin n)) = some i at hid; exact absurd hid (by simp)

/-- Every reachable configuration satisfies the invariant. -/
theorem fischer_reachable_inv (n c : ℕ) {s : FischerLoc n × Valuation (Fin n)}
    (h : (fischer n c).tlts.Reachable ((fischer n c).initial, fun _ => 0) s) :
    FischerInv c s.1 s.2 := by
  induction h with
  | refl => exact fischerInv_initial n c
  | tail _ hstep ih =>
      obtain ⟨l, hl⟩ := hstep
      cases l with
      | inl _ => exact fischerInv_act ih hl
      | inr d => exact fischerInv_delay ih hl

/-- **Theorem 4.6 (Lynch–Shavit): Fischer's algorithm is safe for every `n` and bound `c`.**
Mutual exclusion holds at every reachable global location — proved directly via the
inductive invariant `FischerInv`, whose `crit_id` clause forces two critical processes to
own the same `id`, hence to coincide. -/
theorem fischer_safe (n c : ℕ) : FischerSafe n c := by
  intro s hreach i j hi hj
  have inv := fischer_reachable_inv n c hreach
  have := (inv.crit_id i hi).symm.trans (inv.crit_id j hj)
  exact Option.some.inj this

/-! ## The erroneous version violates mutual exclusion

A concrete run of the erroneous two-process network reaches a global location with
both processes in their critical sections. The run lets process `0` write `id`,
delay exactly `c`, and enter; then process `1` (still writing) overwrites `id`,
delays exactly `c`, and also enters — the erroneous `xᵢ ≥ c` guard admits both
entries at exactly `c`, which the correct strict `xᵢ > c` guard would forbid. -/

/-- One action step of the erroneous two-process network. -/
private theorem err_act (c : ℕ) {ℓ ℓ' : FischerLoc 2} {v v' : Valuation (Fin 2)}
    {g : ClockConstraint (Fin 2)} {r : Set (Fin 2)}
    (hedge : fischerEdgeWith .ge c ℓ g () r ℓ') (hg : satisfies v g)
    (hv : v' = Valuation.reset r v) (hinv : ∀ i, ℓ'.ctrl i = .setting → v' i ≤ c) :
    (fischerErroneous 2 c).tlts.step (ℓ, v) (Sum.inl ()) (ℓ', v') := by
  show (fischerErroneous 2 c).tlts.act (ℓ, v) () (ℓ', v')
  rw [TimedAutomaton.tlts_act_iff]
  exact ⟨g, r, hedge, hg, hv, (satisfies_fischerInv ℓ' v').mpr hinv⟩

/-- One delay step of the erroneous two-process network. -/
private theorem err_delay (c : ℕ) {ℓ : FischerLoc 2} {v : Valuation (Fin 2)} (d : ℝ≥0)
    (hb : ∀ i, ℓ.ctrl i = .setting → v i ≤ c)
    (ha : ∀ i, ℓ.ctrl i = .setting → (v.add d) i ≤ c) :
    (fischerErroneous 2 c).tlts.step (ℓ, v) (Sum.inr d) (ℓ, v.add d) := by
  show (fischerErroneous 2 c).tlts.delay (ℓ, v) d (ℓ, v.add d)
  rw [TimedAutomaton.tlts_delay_iff]
  exact ⟨rfl, rfl, (satisfies_fischerInv ℓ v).mpr hb, (satisfies_fischerInv ℓ (v.add d)).mpr ha⟩

/-- The *erroneous* version of Fischer's algorithm (guard `xᵢ ≥ c`)
does **not** preserve mutual exclusion: the two-process
network reaches a global location in which both processes are in their critical
sections. (With the correct strict guard `xᵢ > c` this run is
blocked — neither process can enter after a delay of *exactly* `c`.) -/
theorem not_fischerErroneous_mutualExclusion (c : ℕ) :
    ∃ s, (fischerErroneous 2 c).tlts.Reachable
        ((fischerErroneous 2 c).initial, fun _ => 0) s ∧ ¬ s.1.MutualExclusion := by
  -- uniform discharge of an invariant condition `∀ i, ctrl i = setting → v i ≤ c`
  -- (and likewise guards): evaluate the concrete control and clock values
  have h0 := LTS.reachable_tail _
    (LTS.reachable_refl (fischerErroneous 2 c).tlts
      ((fischerErroneous 2 c).initial, (fun _ => 0 : Valuation (Fin 2))))
    (err_act c ⟨0, .inl ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ trivial rfl
      (by intro i hi; fin_cases i <;>
        simp_all [fischerErroneous, Function.update, Valuation.reset]))
  have h1 := LTS.reachable_tail _ h0
    (err_act c ⟨1, .inl ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ trivial rfl
      (by intro i hi; fin_cases i <;>
        simp_all [fischerErroneous, Function.update, Valuation.reset, Set.mem_singleton_iff]))
  have h2 := LTS.reachable_tail _ h1
    (err_act c ⟨0, .inr (.inl ⟨rfl, rfl, rfl, rfl⟩)⟩ trivial rfl
      (by intro i hi; fin_cases i <;>
        simp_all [fischerErroneous, Function.update, Valuation.reset, Set.mem_singleton_iff]))
  have h3 := LTS.reachable_tail _ h2
    (err_delay c (c : ℝ≥0)
      (by intro i hi; fin_cases i <;>
        simp_all [Function.update, Valuation.reset, Set.mem_singleton_iff])
      (by intro i hi; fin_cases i <;>
        simp_all [Function.update, Valuation.reset, Valuation.add, Set.mem_singleton_iff]))
  have h4 := LTS.reachable_tail _ h3
    (err_act c ⟨0, .inr (.inr (.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))⟩
      (by simp [satisfies, Cmp.holds, Valuation.add, Valuation.reset, Set.mem_singleton_iff]) rfl
      (by intro i hi; fin_cases i <;>
        simp_all [Function.update, Valuation.reset, Valuation.add, Set.mem_singleton_iff]))
  have h5 := LTS.reachable_tail _ h4
    (err_act c ⟨1, .inr (.inl ⟨rfl, rfl, rfl, rfl⟩)⟩ trivial rfl
      (by intro i hi; fin_cases i <;> simp_all [Function.update]))
  have h6 := LTS.reachable_tail _ h5
    (err_delay c (c : ℝ≥0)
      (by intro i hi; fin_cases i <;> simp_all [Function.update])
      (by intro i hi; fin_cases i <;> simp_all [Function.update]))
  have h7 := LTS.reachable_tail _ h6
    (err_act c ⟨1, .inr (.inr (.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))⟩
      (by simp [satisfies, Cmp.holds, Valuation.add, Valuation.reset, Set.mem_singleton_iff]) rfl
      (by intro i hi; fin_cases i <;> simp_all [Function.update]))
  refine ⟨_, h7, ?_⟩
  intro hme
  exact absurd (hme 0 1 (by simp [Function.update]) (by simp [Function.update])) (by decide)

end DeepWiki.ReactiveSystems
