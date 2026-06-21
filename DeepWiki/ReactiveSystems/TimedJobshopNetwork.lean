import DeepWiki.ReactiveSystems.NetworkTimedAutomata
import DeepWiki.ReactiveSystems.TimedAutomatonBisimilarity

/-! # The lazy-worker / demanding-employer network and a single two-clock Jobshop
A *worker* and his *employer*, modelled as two timed automata synchronising on the
channels `start` and `done`, with `hit` the only ordinary action. The worker uses
clocks `x` (mode timer) and `y` (hit timer); the employer uses `z` (the employer's
own mode timer) — and, sharing the network clock set, imposes the upper hit bound
`y ≤ 4` from its working location. Because `x` and `z` are reset together at every
`start` and every `done` and never apart, they stay equal on all reachable states,
so the three-clock network `Worker ∣ Employer` is timed bisimilar to a single
`SimpleJobshop` automaton with only **two** clocks (`x`, `y`) — the conjoined
working invariant `x ≤ 60 ∧ y ≤ 4` being exactly the small Jobshop's. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- The synchronisation channels of the worker/employer network. -/
inductive JobChan | start | done
  deriving DecidableEq

/-- The ordinary (non-synchronising) actions: only `hit`. -/
inductive JobOrd | hit
  deriving DecidableEq

/-- The three network clocks: the worker's mode timer `x`, the shared hit timer
`y`, and the employer's mode timer `z`. -/
inductive Clock3 | x | y | z
  deriving DecidableEq

/-- The two clocks of the single Jobshop automaton: mode timer `x`, hit timer `y`. -/
inductive Clock2 | x | y
  deriving DecidableEq

/-- Worker locations: resting (`Rw`) and working (`Ww`). -/
inductive LocW | Rw | Ww
  deriving DecidableEq

/-- Employer locations: idle (`Re`) and working (`We`). -/
inductive LocE | Re | We
  deriving DecidableEq

/-- Jobshop locations: resting (`Rest`) and working (`Work`). -/
inductive LocSJ | Rest | Work
  deriving DecidableEq

/-- The network action alphabet `{c! ∣ c?} ∪ {hit} ∪ {τ}`. -/
abbrev JobAct := NetAct JobChan JobOrd

/-! ## The worker automaton -/

/-- The worker's edges: `start?` from rest to work (guard `x ≥ 5`, reset `x, y`),
`done!` back to rest (reset `x`), and the `hit` self-loop while working (guard
`y ≥ 1`, reset `y`). -/
def Worker.edge : LocW → ClockConstraint Clock3 → JobAct → Set Clock3 → LocW → Prop
  | .Rw, g, a, r, .Ww => g = .atom .x .ge 5 ∧ a = .inp .start ∧ r = {.x, .y}
  | .Ww, g, a, r, .Rw => g = .true_ ∧ a = .out .done ∧ r = {.x}
  | .Ww, g, a, r, .Ww => g = .atom .y .ge 1 ∧ a = .ord .hit ∧ r = {.y}
  | _, _, _, _, _ => False

/-- The worker's invariants: none while resting, `x ≤ 60` while working. -/
def Worker.inv : LocW → ClockConstraint Clock3
  | .Rw => .true_
  | .Ww => .atom .x .le 60

/-- The lazy worker as a timed automaton over the network clock set. -/
def Worker : TimedAutomaton LocW JobAct Clock3 where
  initial := .Rw
  edge := Worker.edge
  inv := Worker.inv

/-! ## The employer automaton -/

/-- The employer's edges: `start!` from idle to working (reset `z`) and `done?`
back to idle (guard `z ≥ 40`, reset `z`). -/
def Employer.edge : LocE → ClockConstraint Clock3 → JobAct → Set Clock3 → LocE → Prop
  | .Re, g, a, r, .We => g = .true_ ∧ a = .out .start ∧ r = {.z}
  | .We, g, a, r, .Re => g = .atom .z .ge 40 ∧ a = .inp .done ∧ r = {.z}
  | _, _, _, _, _ => False

/-- The employer's invariants: `z ≤ 10` while idle, `y ≤ 4` while working (the
demanding upper bound on the worker's hit timer). -/
def Employer.inv : LocE → ClockConstraint Clock3
  | .Re => .atom .z .le 10
  | .We => .atom .y .le 4

/-- The demanding employer as a timed automaton over the network clock set. -/
def Employer : TimedAutomaton LocE JobAct Clock3 where
  initial := .Re
  edge := Employer.edge
  inv := Employer.inv

/-- The network `Worker ∣ Employer` (a timed automaton over `LocW × LocE` and the
three clocks). -/
def networkWorkerEmployer : TimedAutomaton (LocW × LocE) JobAct Clock3 :=
  networkAutomaton Worker Employer

/-! ## The single two-clock Jobshop -/

/-- The Jobshop's edges: an internal `start` (`τ`, guard `x ≥ 5`, reset `x, y`), an
internal `done` (`τ`, guard `x ≥ 40`, reset `x`), and the `hit` self-loop (guard
`y ≥ 1`, reset `y`). -/
def SimpleJobshop.edge : LocSJ → ClockConstraint Clock2 → JobAct → Set Clock2 → LocSJ → Prop
  | .Rest, g, a, r, .Work => g = .atom .x .ge 5 ∧ a = .tau ∧ r = {.x, .y}
  | .Work, g, a, r, .Rest => g = .atom .x .ge 40 ∧ a = .tau ∧ r = {.x}
  | .Work, g, a, r, .Work => g = .atom .y .ge 1 ∧ a = .ord .hit ∧ r = {.y}
  | _, _, _, _, _ => False

/-- The Jobshop's invariants: `x ≤ 10` while resting, `x ≤ 60 ∧ y ≤ 4` while
working (exactly the conjoined network invariant of `(Ww, We)`). -/
def SimpleJobshop.inv : LocSJ → ClockConstraint Clock2
  | .Rest => .atom .x .le 10
  | .Work => .and (.atom .x .le 60) (.atom .y .le 4)

/-- The single Jobshop automaton with only two clocks. -/
def SimpleJobshop : TimedAutomaton LocSJ JobAct Clock2 where
  initial := .Rest
  edge := SimpleJobshop.edge
  inv := SimpleJobshop.inv

/-- The Jobshop really uses only two clocks: a clock valuation is determined by its
values at `x` and `y`. -/
theorem simpleJobshop_two_clocks (c : Clock2) : c = Clock2.x ∨ c = Clock2.y := by
  cases c <;> simp

/-! ## Network action transitions, characterized -/

/-- From the resting network state `(Rw, Re)` the only action is the internal
`start` synchronisation (a `τ`), enabled by the worker's `x ≥ 5` guard, resetting
`x, y` (worker) and `z` (employer). -/
theorem act_RwRe (v : Valuation Clock3) (a : JobAct) (q : (LocW × LocE) × Valuation Clock3) :
    networkWorkerEmployer.tlts.act ((.Rw, .Re), v) a q ↔
      a = .tau ∧ 5 ≤ v .x ∧
        q = ((.Ww, .We), Valuation.reset ({Clock3.x, Clock3.y} ∪ {Clock3.z}) v) := by
  constructor
  · intro h
    rw [networkWorkerEmployer, TimedAutomaton.tlts_act_iff] at h
    obtain ⟨g, r, hedge, hg, hq, hinv⟩ := h
    obtain ⟨⟨ql, qr⟩, vq⟩ := q
    simp only [networkAutomaton, Worker, Employer] at hedge
    rcases hedge with ⟨hIsN, hwe, _⟩ | ⟨hIsN, hee, _⟩ | ⟨ha, c, g₁, r₁, g₂, r₂, hpair, hgeq, hreq⟩
    · cases ql <;> simp only [Worker.edge] at hwe
      · obtain ⟨_, harw, _⟩ := hwe; rw [harw] at hIsN; simp [NetAct.IsN] at hIsN
    · cases qr <;> simp only [Employer.edge] at hee
      · obtain ⟨_, hare, _⟩ := hee; rw [hare] at hIsN; simp [NetAct.IsN] at hIsN
    · rcases hpair with ⟨hwout, _⟩ | ⟨hwin, hein⟩
      · cases ql <;> simp only [Worker.edge] at hwout
        · obtain ⟨_, h, _⟩ := hwout; exact absurd h (by simp)
      · cases ql <;> simp only [Worker.edge] at hwin
        cases qr <;> simp only [Employer.edge] at hein
        obtain ⟨hg₁, _hcin, hr₁⟩ := hwin
        obtain ⟨hg₂, _, hr₂⟩ := hein
        subst ha hg₁ hg₂ hr₁ hr₂ hgeq hreq
        exact ⟨rfl, hg.1, Prod.ext rfl hq⟩
  · rintro ⟨rfl, hge, rfl⟩
    rw [networkWorkerEmployer, TimedAutomaton.tlts_act_iff]
    refine ⟨(ClockConstraint.atom Clock3.x Cmp.ge 5).and ClockConstraint.true_,
            {Clock3.x, Clock3.y} ∪ {Clock3.z}, ?_, ⟨hge, trivial⟩, rfl, ?_⟩
    · refine Or.inr (Or.inr ⟨rfl, JobChan.start, _, _, _, _, Or.inr ⟨?_, ?_⟩, rfl, rfl⟩)
      · exact ⟨rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl⟩
    · simp only [networkAutomaton, Worker, Employer, Worker.inv, Employer.inv, satisfies,
        Cmp.holds]
      refine ⟨?_, ?_⟩
      · rw [Valuation.reset_mem (show Clock3.x ∈ _ by simp)]; exact zero_le
      · rw [Valuation.reset_mem (show Clock3.y ∈ _ by simp)]; exact zero_le

/-- From the working network state `(Ww, We)` exactly two actions are possible: the
worker's `hit` (guard `y ≥ 1`, also needing `x ≤ 60` to stay within the working
invariant, resetting `y`), and the internal `done` synchronisation (a `τ`, enabled
by the employer's `z ≥ 40`, resetting `x` and `z`). -/
theorem act_WwWe (v : Valuation Clock3) (a : JobAct) (q : (LocW × LocE) × Valuation Clock3) :
    networkWorkerEmployer.tlts.act ((.Ww, .We), v) a q ↔
      (a = .ord .hit ∧ 1 ≤ v .y ∧ v .x ≤ 60 ∧
        q = ((.Ww, .We), Valuation.reset {Clock3.y} v)) ∨
      (a = .tau ∧ 40 ≤ v .z ∧
        q = ((.Rw, .Re), Valuation.reset ({Clock3.x} ∪ {Clock3.z}) v)) := by
  constructor
  · intro h
    rw [networkWorkerEmployer, TimedAutomaton.tlts_act_iff] at h
    obtain ⟨g, r, hedge, hg, hq, hinv⟩ := h
    obtain ⟨⟨ql, qr⟩, vq⟩ := q
    simp only [networkAutomaton, Worker, Employer] at hedge
    rcases hedge with ⟨hIsN, hwe, hqr⟩ | ⟨hIsN, hee, _⟩ | ⟨ha, c, g₁, r₁, g₂, r₂, hpair, hgeq, hreq⟩
    · cases ql
      · simp only [Worker.edge] at hwe
        obtain ⟨_, ha, _⟩ := hwe; rw [ha] at hIsN; simp [NetAct.IsN] at hIsN
      · simp only [Worker.edge] at hwe
        obtain ⟨hg', ha, hr'⟩ := hwe
        subst ha hg' hr' hqr
        left
        rw [hq] at hinv
        simp only [networkAutomaton, Worker, Employer, Worker.inv, Employer.inv, satisfies,
          Cmp.holds] at hinv
        rw [Valuation.reset_not_mem (show Clock3.x ∉ ({Clock3.y} : Set Clock3) by simp)] at hinv
        refine ⟨rfl, ?_, ?_, Prod.ext rfl hq⟩
        · simpa [satisfies, Cmp.holds] using hg
        · exact_mod_cast hinv.1
    · cases qr <;> simp only [Employer.edge] at hee
      · obtain ⟨_, ha, _⟩ := hee; rw [ha] at hIsN; simp [NetAct.IsN] at hIsN
    · rcases hpair with ⟨hwout, hein⟩ | ⟨hwin, _⟩
      · cases ql
        · simp only [Worker.edge] at hwout
          obtain ⟨hg₁, _, hr₁⟩ := hwout
          cases qr <;> simp only [Employer.edge] at hein
          · obtain ⟨hg₂, _, hr₂⟩ := hein
            subst ha hg₁ hg₂ hr₁ hr₂ hgeq hreq
            right
            refine ⟨rfl, ?_, Prod.ext rfl hq⟩
            simpa [satisfies, Cmp.holds] using hg.2
        · simp only [Worker.edge] at hwout
          obtain ⟨_, hc, _⟩ := hwout; exact absurd hc (by simp)
      · cases ql <;> simp only [Worker.edge] at hwin
        · obtain ⟨_, hc, _⟩ := hwin; exact absurd hc (by simp)
        · obtain ⟨_, hc, _⟩ := hwin; exact absurd hc (by simp)
  · rintro (⟨rfl, hy, hx, rfl⟩ | ⟨rfl, hz, rfl⟩)
    · rw [networkWorkerEmployer, TimedAutomaton.tlts_act_iff]
      refine ⟨ClockConstraint.atom Clock3.y Cmp.ge 1, {Clock3.y}, ?_, ?_, rfl, ?_⟩
      · exact Or.inl ⟨trivial, ⟨rfl, rfl, rfl⟩, rfl⟩
      · simpa [satisfies, Cmp.holds] using hy
      · simp only [networkAutomaton, Worker, Employer, Worker.inv, Employer.inv, satisfies,
          Cmp.holds]
        refine ⟨?_, ?_⟩
        · rw [Valuation.reset_not_mem (show Clock3.x ∉ ({Clock3.y} : Set Clock3) by simp)]
          exact_mod_cast hx
        · rw [Valuation.reset_mem (show Clock3.y ∈ ({Clock3.y} : Set Clock3) by simp)]; exact zero_le
    · rw [networkWorkerEmployer, TimedAutomaton.tlts_act_iff]
      refine ⟨ClockConstraint.true_.and (ClockConstraint.atom Clock3.z Cmp.ge 40),
              {Clock3.x} ∪ {Clock3.z}, ?_, ?_, rfl, ?_⟩
      · refine Or.inr (Or.inr ⟨rfl, JobChan.done, _, _, _, _, Or.inl ⟨?_, ?_⟩, rfl, rfl⟩)
        · exact ⟨rfl, rfl, rfl⟩
        · exact ⟨rfl, rfl, rfl⟩
      · refine ⟨trivial, ?_⟩
        simpa [satisfies, Cmp.holds] using hz
      · simp only [networkAutomaton, Worker, Employer, Worker.inv, Employer.inv, satisfies,
          Cmp.holds, true_and]
        rw [Valuation.reset_mem (show Clock3.z ∈ _ by simp)]; exact zero_le

/-! ## Jobshop action transitions, characterized -/

/-- From the Jobshop's `Rest` the only action is the internal `start` (`τ`, guard
`x ≥ 5`, reset `x, y`). -/
theorem sj_act_Rest (w : Valuation Clock2) (a : JobAct) (q : LocSJ × Valuation Clock2) :
    SimpleJobshop.tlts.act (.Rest, w) a q ↔
      a = .tau ∧ 5 ≤ w .x ∧ q = (.Work, Valuation.reset {Clock2.x, Clock2.y} w) := by
  constructor
  · intro h
    rw [TimedAutomaton.tlts_act_iff] at h
    obtain ⟨g, r, hedge, hg, hq, _⟩ := h
    obtain ⟨ql, wq⟩ := q
    simp only [SimpleJobshop] at hedge
    cases ql <;> simp only [SimpleJobshop.edge] at hedge
    · obtain ⟨hg', ha, hr'⟩ := hedge
      subst ha hg' hr'
      refine ⟨rfl, ?_, Prod.ext rfl hq⟩
      simpa [satisfies, Cmp.holds] using hg
  · rintro ⟨rfl, hx, rfl⟩
    rw [TimedAutomaton.tlts_act_iff]
    refine ⟨ClockConstraint.atom Clock2.x Cmp.ge 5, {Clock2.x, Clock2.y}, ?_, ?_, rfl, ?_⟩
    · exact ⟨rfl, rfl, rfl⟩
    · simpa [satisfies, Cmp.holds] using hx
    · simp only [SimpleJobshop, SimpleJobshop.inv, satisfies, Cmp.holds]
      refine ⟨?_, ?_⟩
      · rw [Valuation.reset_mem (show Clock2.x ∈ _ by simp)]; exact zero_le
      · rw [Valuation.reset_mem (show Clock2.y ∈ _ by simp)]; exact zero_le

/-- From the Jobshop's `Work` exactly two actions are possible: the `hit` (guard
`y ≥ 1`, needing `x ≤ 60`, reset `y`) and the internal `done` (`τ`, guard `x ≥ 40`,
reset `x`). -/
theorem sj_act_Work (w : Valuation Clock2) (a : JobAct) (q : LocSJ × Valuation Clock2) :
    SimpleJobshop.tlts.act (.Work, w) a q ↔
      (a = .ord .hit ∧ 1 ≤ w .y ∧ w .x ≤ 60 ∧ q = (.Work, Valuation.reset {Clock2.y} w)) ∨
      (a = .tau ∧ 40 ≤ w .x ∧ q = (.Rest, Valuation.reset {Clock2.x} w)) := by
  constructor
  · intro h
    rw [TimedAutomaton.tlts_act_iff] at h
    obtain ⟨g, r, hedge, hg, hq, hinv⟩ := h
    obtain ⟨ql, wq⟩ := q
    simp only [SimpleJobshop] at hedge
    cases ql <;> simp only [SimpleJobshop.edge] at hedge
    · obtain ⟨hg', ha, hr'⟩ := hedge
      subst ha hg' hr'
      right
      refine ⟨rfl, ?_, Prod.ext rfl hq⟩
      simpa [satisfies, Cmp.holds] using hg
    · obtain ⟨hg', ha, hr'⟩ := hedge
      subst ha hg' hr'
      left
      rw [hq] at hinv
      simp only [SimpleJobshop, SimpleJobshop.inv, satisfies, Cmp.holds] at hinv
      rw [Valuation.reset_not_mem (show Clock2.x ∉ ({Clock2.y} : Set Clock2) by simp)] at hinv
      refine ⟨rfl, ?_, ?_, Prod.ext rfl hq⟩
      · simpa [satisfies, Cmp.holds] using hg
      · exact_mod_cast hinv.1
  · rintro (⟨rfl, hy, hx, rfl⟩ | ⟨rfl, hx, rfl⟩)
    · rw [TimedAutomaton.tlts_act_iff]
      refine ⟨ClockConstraint.atom Clock2.y Cmp.ge 1, {Clock2.y}, ?_, ?_, rfl, ?_⟩
      · exact ⟨rfl, rfl, rfl⟩
      · simpa [satisfies, Cmp.holds] using hy
      · simp only [SimpleJobshop, SimpleJobshop.inv, satisfies, Cmp.holds]
        refine ⟨?_, ?_⟩
        · rw [Valuation.reset_not_mem (show Clock2.x ∉ ({Clock2.y} : Set Clock2) by simp)]
          exact_mod_cast hx
        · rw [Valuation.reset_mem (show Clock2.y ∈ ({Clock2.y} : Set Clock2) by simp)]; exact zero_le
    · rw [TimedAutomaton.tlts_act_iff]
      refine ⟨ClockConstraint.atom Clock2.x Cmp.ge 40, {Clock2.x}, ?_, ?_, rfl, ?_⟩
      · exact ⟨rfl, rfl, rfl⟩
      · simpa [satisfies, Cmp.holds] using hx
      · simp only [SimpleJobshop, SimpleJobshop.inv, satisfies, Cmp.holds]
        rw [Valuation.reset_mem (show Clock2.x ∈ ({Clock2.x} : Set Clock2) by simp)]; exact zero_le

/-! ## The timed bisimulation `Worker ∣ Employer ≈ SimpleJobshop` -/

/-- The bisimulation relating each reachable network state to the Jobshop state
with the same `x` (= `z`) and `y`. The hypothesis `v z = v x` records the invariant
that the worker's and employer's mode timers stay synchronised. -/
inductive JobshopRel :
    ((LocW × LocE) × Valuation Clock3) ⊕ (LocSJ × Valuation Clock2) →
    ((LocW × LocE) × Valuation Clock3) ⊕ (LocSJ × Valuation Clock2) → Prop
  /-- Resting: `((Rw, Re), v)` relates to `(Rest, w)` when `w x = v x`, `w y = v y`
  and `v z = v x`. -/
  | rest (v : Valuation Clock3) (w : Valuation Clock2)
      (hx : w .x = v .x) (hy : w .y = v .y) (hz : v .z = v .x) :
      JobshopRel (.inl ((.Rw, .Re), v)) (.inr (.Rest, w))
  /-- Working: `((Ww, We), v)` relates to `(Work, w)` under the same clock
  correspondence. -/
  | work (v : Valuation Clock3) (w : Valuation Clock2)
      (hx : w .x = v .x) (hy : w .y = v .y) (hz : v .z = v .x) :
      JobshopRel (.inl ((.Ww, .We), v)) (.inr (.Work, w))

/-- `JobshopRel` is a (timed) bisimulation on the disjoint union of the network's
and the Jobshop's timed transition systems. -/
theorem isBisimulation_jobshopRel :
    LTS.IsBisimulation (LTS.sum networkWorkerEmployer.tlts SimpleJobshop.tlts) JobshopRel := by
  intro p q hR
  cases hR with
  | rest v w hx hy hz =>
    refine ⟨fun lbl t hstep => ?_, fun lbl t hstep => ?_⟩
    · rw [LTS.sum_step_inl_iff] at hstep
      obtain ⟨t', rfl, hstep⟩ := hstep
      cases lbl with
      | inl a =>
        obtain ⟨rfl, h5, rfl⟩ := (act_RwRe v a t').mp hstep
        refine ⟨.inr (.Work, Valuation.reset {Clock2.x, Clock2.y} w), ?_, ?_⟩
        · rw [LTS.sum_step_inr_iff]
          exact ⟨_, rfl, (sj_act_Rest w .tau _).mpr ⟨rfl, by rw [hx]; exact h5, rfl⟩⟩
        · refine JobshopRel.work _ _ ?_ ?_ ?_ <;>
            simp [Valuation.reset, Set.mem_insert_iff, Set.mem_singleton_iff]
      | inr d =>
        obtain ⟨rfl, _, hRe, _, hRe'⟩ :=
          (networkTLTS_delay_iff Worker Employer .Rw .Re v d t').mp hstep
        refine ⟨.inr (.Rest, w.add d), ?_, ?_⟩
        · rw [LTS.sum_step_inr_iff]
          refine ⟨_, rfl, ?_⟩
          refine (TimedAutomaton.tlts_delay_iff SimpleJobshop .Rest w d .Rest (w.add d)).mpr
            ⟨rfl, rfl, ?_, ?_⟩
          · simp only [SimpleJobshop, SimpleJobshop.inv, satisfies, Cmp.holds]
            simp only [Employer, Employer.inv, satisfies, Cmp.holds] at hRe
            rw [hx, ← hz]; exact hRe
          · simp only [SimpleJobshop, SimpleJobshop.inv, satisfies, Cmp.holds, Valuation.add_apply]
            simp only [Employer, Employer.inv, satisfies, Cmp.holds, Valuation.add_apply] at hRe'
            rw [hx, ← hz]; exact hRe'
        · refine JobshopRel.rest _ _ ?_ ?_ ?_ <;> simp [Valuation.add_apply, hx, hy, hz]
    · rw [LTS.sum_step_inr_iff] at hstep
      obtain ⟨t', rfl, hstep⟩ := hstep
      cases lbl with
      | inl a =>
        obtain ⟨rfl, h5, rfl⟩ := (sj_act_Rest w a t').mp hstep
        refine ⟨.inl ((.Ww, .We), Valuation.reset ({Clock3.x, Clock3.y} ∪ {Clock3.z}) v), ?_, ?_⟩
        · rw [LTS.sum_step_inl_iff]
          exact ⟨_, rfl, (act_RwRe v .tau _).mpr ⟨rfl, by rw [← hx]; exact h5, rfl⟩⟩
        · refine JobshopRel.work _ _ ?_ ?_ ?_ <;>
            simp [Valuation.reset, Set.mem_insert_iff, Set.mem_singleton_iff]
      | inr d =>
        obtain ⟨tl, tv⟩ := t'
        obtain ⟨rfl, rfl, hw, hw'⟩ :=
          (TimedAutomaton.tlts_delay_iff SimpleJobshop .Rest w d tl tv).mp hstep
        refine ⟨.inl ((.Rw, .Re), v.add d), ?_, ?_⟩
        · rw [LTS.sum_step_inl_iff]
          refine ⟨_, rfl, ?_⟩
          refine (networkTLTS_delay_iff Worker Employer .Rw .Re v d _).mpr
            ⟨rfl, trivial, ?_, trivial, ?_⟩
          · simp only [Employer, Employer.inv, satisfies, Cmp.holds]
            simp only [SimpleJobshop, SimpleJobshop.inv, satisfies, Cmp.holds] at hw
            rw [hz, ← hx]; exact hw
          · simp only [Employer, Employer.inv, satisfies, Cmp.holds, Valuation.add_apply]
            simp only [SimpleJobshop, SimpleJobshop.inv, satisfies, Cmp.holds,
              Valuation.add_apply] at hw'
            rw [hz, ← hx]; exact hw'
        · refine JobshopRel.rest _ _ ?_ ?_ ?_ <;> simp [Valuation.add_apply, hx, hy, hz]
  | work v w hx hy hz =>
    refine ⟨fun lbl t hstep => ?_, fun lbl t hstep => ?_⟩
    · rw [LTS.sum_step_inl_iff] at hstep
      obtain ⟨t', rfl, hstep⟩ := hstep
      cases lbl with
      | inl a =>
        rcases (act_WwWe v a t').mp hstep with ⟨rfl, hy1, hx60, rfl⟩ | ⟨rfl, hz40, rfl⟩
        · refine ⟨.inr (.Work, Valuation.reset {Clock2.y} w), ?_, ?_⟩
          · rw [LTS.sum_step_inr_iff]
            exact ⟨_, rfl, (sj_act_Work w (.ord .hit) _).mpr
              (Or.inl ⟨rfl, by rw [hy]; exact hy1, by rw [hx]; exact hx60, rfl⟩)⟩
          · refine JobshopRel.work _ _ ?_ ?_ ?_ <;>
              simp [Valuation.reset, Set.mem_singleton_iff, hx, hz]
        · refine ⟨.inr (.Rest, Valuation.reset {Clock2.x} w), ?_, ?_⟩
          · rw [LTS.sum_step_inr_iff]
            exact ⟨_, rfl, (sj_act_Work w .tau _).mpr
              (Or.inr ⟨rfl, by rw [hx, ← hz]; exact hz40, rfl⟩)⟩
          · refine JobshopRel.rest _ _ ?_ ?_ ?_ <;>
              simp [Valuation.reset, Set.mem_insert_iff, Set.mem_singleton_iff, hy]
      | inr d =>
        obtain ⟨rfl, hWw, hWe, hWw', hWe'⟩ :=
          (networkTLTS_delay_iff Worker Employer .Ww .We v d t').mp hstep
        refine ⟨.inr (.Work, w.add d), ?_, ?_⟩
        · rw [LTS.sum_step_inr_iff]
          refine ⟨_, rfl, ?_⟩
          refine (TimedAutomaton.tlts_delay_iff SimpleJobshop .Work w d .Work (w.add d)).mpr
            ⟨rfl, rfl, ?_, ?_⟩
          · simp only [SimpleJobshop, SimpleJobshop.inv, satisfies, Cmp.holds]
            simp only [Worker, Worker.inv, Employer, Employer.inv, satisfies, Cmp.holds]
              at hWw hWe
            exact ⟨by rw [hx]; exact hWw, by rw [hy]; exact hWe⟩
          · simp only [SimpleJobshop, SimpleJobshop.inv, satisfies, Cmp.holds, Valuation.add_apply]
            simp only [Worker, Worker.inv, Employer, Employer.inv, satisfies, Cmp.holds,
              Valuation.add_apply] at hWw' hWe'
            exact ⟨by rw [hx]; exact hWw', by rw [hy]; exact hWe'⟩
        · refine JobshopRel.work _ _ ?_ ?_ ?_ <;> simp [Valuation.add_apply, hx, hy, hz]
    · rw [LTS.sum_step_inr_iff] at hstep
      obtain ⟨t', rfl, hstep⟩ := hstep
      cases lbl with
      | inl a =>
        rcases (sj_act_Work w a t').mp hstep with ⟨rfl, hy1, hx60, rfl⟩ | ⟨rfl, hx40, rfl⟩
        · refine ⟨.inl ((.Ww, .We), Valuation.reset {Clock3.y} v), ?_, ?_⟩
          · rw [LTS.sum_step_inl_iff]
            exact ⟨_, rfl, (act_WwWe v (.ord .hit) _).mpr
              (Or.inl ⟨rfl, by rw [← hy]; exact hy1, by rw [← hx]; exact hx60, rfl⟩)⟩
          · refine JobshopRel.work _ _ ?_ ?_ ?_ <;>
              simp [Valuation.reset, Set.mem_singleton_iff, hx, hz]
        · refine ⟨.inl ((.Rw, .Re), Valuation.reset ({Clock3.x} ∪ {Clock3.z}) v), ?_, ?_⟩
          · rw [LTS.sum_step_inl_iff]
            exact ⟨_, rfl, (act_WwWe v .tau _).mpr
              (Or.inr ⟨rfl, by rw [hz, ← hx]; exact hx40, rfl⟩)⟩
          · refine JobshopRel.rest _ _ ?_ ?_ ?_ <;>
              simp [Valuation.reset, Set.mem_insert_iff, Set.mem_singleton_iff, hy]
      | inr d =>
        obtain ⟨tl, tv⟩ := t'
        obtain ⟨rfl, rfl, hw, hw'⟩ :=
          (TimedAutomaton.tlts_delay_iff SimpleJobshop .Work w d tl tv).mp hstep
        refine ⟨.inl ((.Ww, .We), v.add d), ?_, ?_⟩
        · rw [LTS.sum_step_inl_iff]
          refine ⟨_, rfl, ?_⟩
          refine (networkTLTS_delay_iff Worker Employer .Ww .We v d _).mpr ?_
          simp only [SimpleJobshop, SimpleJobshop.inv, satisfies, Cmp.holds,
            Valuation.add_apply] at hw hw'
          refine ⟨rfl, ?_, ?_, ?_, ?_⟩
          · simp only [Worker, Worker.inv, satisfies, Cmp.holds]; rw [← hx]; exact hw.1
          · simp only [Employer, Employer.inv, satisfies, Cmp.holds]; rw [← hy]; exact hw.2
          · simp only [Worker, Worker.inv, satisfies, Cmp.holds, Valuation.add_apply]
            rw [← hx]; exact hw'.1
          · simp only [Employer, Employer.inv, satisfies, Cmp.holds, Valuation.add_apply]
            rw [← hy]; exact hw'.2
        · refine JobshopRel.work _ _ ?_ ?_ ?_ <;> simp [Valuation.add_apply, hx, hy, hz]

/-- **Exercise 11.3.** The lazy-worker / demanding-employer network is timed
bisimilar to the single two-clock `SimpleJobshop`. -/
theorem networkWorkerEmployer_timedBisimilar_simpleJobshop :
    networkWorkerEmployer.TimedBisimilar SimpleJobshop :=
  isBisimulation_jobshopRel.le_bisimilar (JobshopRel.rest _ _ rfl rfl rfl)

end DeepWiki.ReactiveSystems
