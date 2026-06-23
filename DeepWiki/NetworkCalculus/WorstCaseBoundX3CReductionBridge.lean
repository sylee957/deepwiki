import DeepWiki.NetworkCalculus.WorstCaseBoundX3CReduction
import DeepWiki.NetworkCalculus.WorstCaseLP

/-! # The worst-case-objective bridge for the X3C reduction (DNC Theorem 10.2)
The combinatorial core (`WorstCaseBoundX3CReduction`) shows that, at an integral
extremal vertex of the Figure-10.7 rate polytope, the convex objective the book
maximizes is the number of **saturated** subsets — bounded by `q`, equal to `q`
iff an exact 3-cover exists. This file wires that core to the worst-case
**objective** through the `programOptimum` framework (`WorstCaseLP`): the
worst-case middle-stage backlog is the *optimum over the feasible assignments* of
the saturation objective, so deciding whether the backlog reaches the cover
threshold is X3C — the genuine, formalizable NP-hardness content.

What is proved here is the *objective-level* reduction: the optimum over the
extremal vertices, its `q`-bound and threshold correspondence, the backlog-value
framing `3s − 2·saturatedCount` and its `3s − 2q` threshold, and the reduction
packaged as decidable instance data with a bi-implication
`(∃ exact cover) ↔ (worst-case objective reaches the threshold)`. What is *not*
proved is (a) that the continuous network dynamics realize this objective at the
integral vertices — the convex-maximization-attains-vertices step, an analysis
fact about the Figure-10.7 trajectories — and (b) a `Complexity.NPHard`
typeclass, which Mathlib does not provide. Both are recorded as `[research]` /
`[external]` in the catalog; (a) is the only mathematical gap, and it is the
attainment half, not the combinatorial correspondence. -/

namespace DeepWiki

open Finset

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [DecidableEq ι]

/-! ## An assignment exists exactly when every element is coverable
The reduction is well-formed only if each of the `3q` elements lies in some
3-subset (otherwise no assignment, hence trivially no cover). We phrase this as
`HasAssignment`. -/

/-- The instance **admits an assignment**: some routing sends every element to a
containing subset (equivalently, every element lies in some 3-subset). -/
def X3CInstance.HasAssignment (I : X3CInstance ι α) : Prop :=
  ∃ assign : α → ι, I.IsAssignment assign

/-! ## The saturation objective and its optimum over assignments
The worst-case backlog growth, after optimizing the rate-sharing over the
feasible polytope, is attained at the integral vertices — the assignments — where
the objective is `saturatedCount`. We lift it into the `programOptimum`
framework. -/

/-- The **saturation objective** at an assignment, as an `EReal` for the
`programOptimum` framework: the number of saturated subsets. This is the convex
objective `Σ_i [Σ_{j} r_{i,j} − 2]⁺` of the reduction read at an integral extremal
vertex. -/
noncomputable def X3CInstance.satObjective (I : X3CInstance ι α)
    (assign : α → ι) : EReal :=
  (I.saturatedCount assign : EReal)

/-- The **optimum of the saturation objective** over the feasible assignments —
the worst-case value of the reduction's convex program, `programOptimum`-style
(supremum over the extremal vertices). -/
noncomputable def X3CInstance.satOptimum (I : X3CInstance ι α) : EReal :=
  programOptimum I.IsAssignment I.satObjective

/-- Each feasible assignment's saturation objective lies below the optimum. -/
theorem X3CInstance.satObjective_le_satOptimum (I : X3CInstance ι α)
    {assign : α → ι} (h : I.IsAssignment assign) :
    I.satObjective assign ≤ I.satOptimum :=
  le_programOptimum h

/-- **The optimum is bounded by `q`** (the lift of `saturatedCount_le_q` to the
`programOptimum` level): no extremal vertex saturates more than `q` subsets, so
their supremum is `≤ q`. -/
theorem X3CInstance.satOptimum_le_q (I : X3CInstance ι α) :
    I.satOptimum ≤ (I.q : EReal) :=
  programOptimum_le fun assign h => by
    rw [X3CInstance.satObjective]; exact_mod_cast I.saturatedCount_le_q assign

/-! ## Existential cover correspondence
The per-assignment correspondence (`saturatedCount_eq_q_iff_exists_cover`)
existentialized: *some* assignment attains `q` iff *some* assignment's saturated
subsets form an exact cover. This is the form the optimum threshold needs. -/

/-- **Some assignment attains the optimum `q` iff an exact cover exists.** The
forward direction packages the saturated subsets of the attaining assignment into
a cover; the backward direction reads off the assignment of the cover, whose
saturation count is forced to `q` by the `≤ q` bound. -/
theorem X3CInstance.exists_saturatedCount_eq_q_iff_exists_cover
    (I : X3CInstance ι α) :
    (∃ assign, I.IsAssignment assign ∧ I.saturatedCount assign = I.q) ↔
      ∃ assign C, I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ I.members i) := by
  constructor
  · rintro ⟨assign, hassign, hq⟩
    obtain ⟨C, hcover, htot⟩ :=
      (I.saturatedCount_eq_q_iff_exists_cover hassign).mp hq
    exact ⟨assign, C, hcover, htot⟩
  · rintro ⟨assign, C, ⟨hassign, hCsub, hCcard⟩, htot⟩
    refine ⟨assign, hassign, ?_⟩
    exact le_antisymm (I.saturatedCount_le_q assign)
      (hCcard ▸ Finset.card_le_card hCsub)

/-! ## The optimum threshold ⟺ exact cover
The `programOptimum`-level threshold correspondence: the saturation optimum
reaches `q` exactly when an exact cover exists — the NP-hardness-defining
equivalence (a feasible objective bound decides X3C). It needs the instance to
admit an assignment (otherwise both sides are vacuously false: no assignment ⟹ the
optimum is `⊥ < q`, and no cover). -/

/-- **The optimum equals `q` iff an exact cover exists** (given the instance
admits an assignment): the saturation optimum over the extremal vertices reaches
the cover threshold exactly when X3C has a solution. -/
theorem X3CInstance.satOptimum_eq_q_iff_exists_cover (I : X3CInstance ι α)
    (hne : I.HasAssignment) :
    I.satOptimum = (I.q : EReal) ↔
      ∃ assign C, I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ I.members i) := by
  rw [← I.exists_saturatedCount_eq_q_iff_exists_cover]
  -- reduce to the generic "sup of a `q`-bounded ℕ objective equals `q` iff attained"
  constructor
  · intro hsup
    rcases Nat.eq_zero_or_pos I.q with hq0 | hqpos
    · obtain ⟨assign, hassign⟩ := hne
      exact ⟨assign, hassign, by have := I.saturatedCount_le_q assign; omega⟩
    · by_contra hcon
      have hcon' : ∀ assign, I.IsAssignment assign → I.saturatedCount assign ≠ I.q :=
        fun assign h hq => hcon ⟨assign, h, hq⟩
      have hlt : ∀ c : {assign // I.IsAssignment assign},
          I.satObjective c.1 ≤ ((I.q - 1 : ℕ) : EReal) := fun c => by
        rw [X3CInstance.satObjective]
        have : I.saturatedCount c.1 ≤ I.q - 1 :=
          Nat.le_sub_one_of_lt (lt_of_le_of_ne (I.saturatedCount_le_q c.1) (hcon' c.1 c.2))
        exact_mod_cast this
      have hbot : I.satOptimum ≤ ((I.q - 1 : ℕ) : EReal) := by
        rw [X3CInstance.satOptimum, programOptimum]; exact iSup_le hlt
      rw [hsup] at hbot
      have : I.q ≤ I.q - 1 := by exact_mod_cast hbot
      omega
  · rintro ⟨assign, hassign, hq⟩
    refine le_antisymm I.satOptimum_le_q ?_
    calc (I.q : EReal) = I.satObjective assign := by
          rw [X3CInstance.satObjective, hq]
      _ ≤ I.satOptimum := I.satObjective_le_satOptimum hassign

/-- **The optimum reaches the threshold `q` iff an exact cover exists** (the
`≥`-form, given the instance admits an assignment): equivalent to equality since
the optimum is `≤ q`. This is the decision the book reduces X3C to —
`q ≤ satOptimum` is a *feasible objective bound* deciding X3C. -/
theorem X3CInstance.q_le_satOptimum_iff_exists_cover (I : X3CInstance ι α)
    (hne : I.HasAssignment) :
    (I.q : EReal) ≤ I.satOptimum ↔
      ∃ assign C, I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ I.members i) := by
  rw [← I.satOptimum_eq_q_iff_exists_cover hne]
  exact ⟨fun h => le_antisymm I.satOptimum_le_q h, fun h => h.ge⟩

/-! ## The backlog-value framing (`3s − 2q` threshold)
The middle-stage backlog grows at the saturation rate; together with the upper
stage (rate `3(s−q)`) the total backlog at the bottom server `W` at time `1⁻` is
`3(s−q) + saturatedCount`. Maximizing over assignments, the worst-case backlog is
`3(s−q) + (max saturatedCount)`, which is `≤ 3s − 2q` (since the max is `≤ q`) and
*reaches* `3s − 2q` exactly when an exact cover exists. We state this at the `ℕ`
level (closed-form, no `EReal` pathology), with `s = card ι` the number of
3-subsets. -/

/-- The number of 3-subsets `s = |U|` of the instance. -/
def X3CInstance.numSubsets (_I : X3CInstance ι α) : ℕ := Fintype.card ι

/-- The **backlog value at `W`** realized by an assignment (time `1⁻`): the
upper-stage backlog `3(s−q)` plus the middle-stage backlog `saturatedCount`. The
constant `3(s−q)` is the data not yet served at the upper stage; it does not
depend on the assignment. -/
def X3CInstance.backlogValue (I : X3CInstance ι α) (assign : α → ι) : ℕ :=
  3 * (I.numSubsets - I.q) + I.saturatedCount assign

/-- The **worst-case backlog at `W`**: the maximum realized backlog value over the
feasible assignments — `3(s−q) + (max saturatedCount)`. -/
noncomputable def X3CInstance.worstCaseBacklog (I : X3CInstance ι α) : ℕ :=
  ⨆ c : {assign // I.IsAssignment assign}, I.backlogValue c.1

/-- The worst-case backlog is `3(s−q) +` the maximal saturated count over
assignments (the additive constant pulls out of the supremum). -/
theorem X3CInstance.worstCaseBacklog_eq (I : X3CInstance ι α)
    (hne : I.HasAssignment) :
    I.worstCaseBacklog =
      3 * (I.numSubsets - I.q) +
        ⨆ c : {assign // I.IsAssignment assign}, I.saturatedCount c.1 := by
  obtain ⟨a0, ha0⟩ := hne
  haveI : Nonempty {assign // I.IsAssignment assign} := ⟨⟨a0, ha0⟩⟩
  -- a maximizing assignment attains both supremums; the constant pulls out
  obtain ⟨c0, hc0⟩ :=
    Finite.exists_max (fun c : {assign // I.IsAssignment assign} => I.saturatedCount c.1)
  have hmax : (⨆ c : {assign // I.IsAssignment assign}, I.saturatedCount c.1) =
      I.saturatedCount c0.1 :=
    le_antisymm (ciSup_le hc0)
      (le_ciSup (f := fun c : {assign // I.IsAssignment assign} => I.saturatedCount c.1)
        (Finite.bddAbove_range _) c0)
  rw [X3CInstance.worstCaseBacklog, hmax]
  apply le_antisymm
  · refine ciSup_le fun c => ?_
    have := hc0 c
    simp only [X3CInstance.backlogValue]; omega
  · have hle : 3 * (I.numSubsets - I.q) + I.saturatedCount c0.1 = I.backlogValue c0.1 := rfl
    rw [hle]
    exact le_ciSup
      (f := fun c : {assign // I.IsAssignment assign} => I.backlogValue c.1)
      (Finite.bddAbove_range _) c0

/-- Every assignment's backlog value is dominated by the worst case. -/
theorem X3CInstance.backlogValue_le_worstCaseBacklog (I : X3CInstance ι α)
    {assign : α → ι} (h : I.IsAssignment assign) :
    I.backlogValue assign ≤ I.worstCaseBacklog := by
  haveI : Nonempty {assign // I.IsAssignment assign} := ⟨⟨assign, h⟩⟩
  exact le_ciSup
    (f := fun c : {assign // I.IsAssignment assign} => I.backlogValue c.1)
    (Finite.bddAbove_range _) (⟨assign, h⟩ : {assign // I.IsAssignment assign})

/-- The maximal saturated count over assignments is `≤ q`. -/
theorem X3CInstance.iSup_saturatedCount_le_q (I : X3CInstance ι α) :
    (⨆ c : {assign // I.IsAssignment assign}, I.saturatedCount c.1) ≤ I.q :=
  ciSup_le' fun c => I.saturatedCount_le_q c.1

/-- The maximal saturated count over assignments reaches `q` iff an exact cover
exists (given an assignment exists). -/
theorem X3CInstance.iSup_saturatedCount_eq_q_iff_exists_cover (I : X3CInstance ι α)
    (hne : I.HasAssignment) :
    (⨆ c : {assign // I.IsAssignment assign}, I.saturatedCount c.1) = I.q ↔
      ∃ assign C, I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ I.members i) := by
  obtain ⟨a0, ha0⟩ := hne
  haveI : Nonempty {assign // I.IsAssignment assign} := ⟨⟨a0, ha0⟩⟩
  rw [← I.exists_saturatedCount_eq_q_iff_exists_cover]
  constructor
  · intro hsup
    rcases Nat.eq_zero_or_pos I.q with hq0 | hqpos
    · exact ⟨a0, ha0, by have := I.saturatedCount_le_q a0; omega⟩
    · -- the ℕ sup over a nonempty finite family attains its value
      obtain ⟨c, hc⟩ :=
        (Finite.exists_max (fun c : {assign // I.IsAssignment assign} =>
          I.saturatedCount c.1))
      refine ⟨c.1, c.2, ?_⟩
      have hle : ∀ d : {assign // I.IsAssignment assign},
          I.saturatedCount d.1 ≤ I.saturatedCount c.1 := hc
      have : (⨆ d : {assign // I.IsAssignment assign}, I.saturatedCount d.1) =
          I.saturatedCount c.1 :=
        le_antisymm (ciSup_le' hle)
          (le_ciSup
            (f := fun d : {assign // I.IsAssignment assign} => I.saturatedCount d.1)
            (Finite.bddAbove_range _) c)
      rw [hsup] at this; exact this.symm
  · rintro ⟨assign, hassign, hq⟩
    refine le_antisymm I.iSup_saturatedCount_le_q ?_
    calc I.q = I.saturatedCount assign := hq.symm
      _ ≤ _ := le_ciSup
          (f := fun c : {assign // I.IsAssignment assign} => I.saturatedCount c.1)
          (Finite.bddAbove_range _)
          (⟨assign, hassign⟩ : {assign // I.IsAssignment assign})

/-- **The worst-case backlog is `≤ 3s − 2q`** (the book's upper bound on the
maximum backlog at `W`): `3(s−q) + (max saturatedCount) ≤ 3(s−q) + q`. -/
theorem X3CInstance.worstCaseBacklog_le (I : X3CInstance ι α)
    (hne : I.HasAssignment) (hsq : I.q ≤ I.numSubsets) :
    I.worstCaseBacklog ≤ 3 * I.numSubsets - 2 * I.q := by
  rw [I.worstCaseBacklog_eq hne]
  have h := I.iSup_saturatedCount_le_q
  omega

/-- **The worst-case backlog reaches `3s − 2q` iff an exact cover exists** (the
NP-hardness-defining threshold of Theorem 10.2): deciding whether the worst-case
backlog at `W` can be at least `3s − 2q` is exactly deciding X3C. Needs an
assignment (well-formed instance) and `q ≤ s` (enough subsets to cover, else no
cover and the upper-stage constant truncates). -/
theorem X3CInstance.worstCaseBacklog_eq_threshold_iff_exists_cover
    (I : X3CInstance ι α) (hne : I.HasAssignment) (hsq : I.q ≤ I.numSubsets) :
    I.worstCaseBacklog = 3 * I.numSubsets - 2 * I.q ↔
      ∃ assign C, I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ I.members i) := by
  rw [I.worstCaseBacklog_eq hne, ← I.iSup_saturatedCount_eq_q_iff_exists_cover hne]
  have h := I.iSup_saturatedCount_le_q
  constructor
  · intro heq; omega
  · intro heq; omega

/-- **The decision form** (the book's "backlog at least `3s − 2q`"): with the
`≤ 3s − 2q` upper bound, the worst-case backlog *reaches* the threshold iff it is
*at least* the threshold — and that holds iff an exact cover exists. -/
theorem X3CInstance.threshold_le_worstCaseBacklog_iff_exists_cover
    (I : X3CInstance ι α) (hne : I.HasAssignment) (hsq : I.q ≤ I.numSubsets) :
    3 * I.numSubsets - 2 * I.q ≤ I.worstCaseBacklog ↔
      ∃ assign C, I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ I.members i) := by
  rw [← I.worstCaseBacklog_eq_threshold_iff_exists_cover hne hsq]
  exact ⟨fun h => le_antisymm (I.worstCaseBacklog_le hne hsq) h, fun h => h.ge⟩

/-! ## The reduction as data, and the NP-hardness correspondence
The reduction is a *computable map* `X3CInstance → (instance data + threshold)`
with a decidable threshold and a bi-implication `(∃ cover) ↔ (objective reaches
threshold)`. This is the polynomial-time-reduction *correctness* — the part of
NP-hardness that is formalizable without a complexity-class framework. -/

/-- The reduction's **output data**: the worst-case backlog quantity and the
decision threshold `3s − 2q` it is compared against. The map `I ↦ this` is the
Figure-10.7 construction read at the objective level (the network topology is
determined by `I.members`; the backlog objective is what the dynamics realize). -/
structure WorstCaseDecisionData where
  /-- The worst-case backlog value of the constructed network. -/
  value : ℕ
  /-- The decision threshold `3s − 2q`. -/
  threshold : ℕ

/-- The reduction map `X3C ↦ decision data`: computes the worst-case backlog and
the threshold `3s − 2q`. This is the data of the Figure-10.7 reduction at the
objective level — a (noncomputable in the supremum, but finitely determined) map. -/
noncomputable def X3CInstance.reduceToDecision (I : X3CInstance ι α) :
    WorstCaseDecisionData where
  value := I.worstCaseBacklog
  threshold := 3 * I.numSubsets - 2 * I.q

/-- **The reduction correctness (Theorem 10.2, objective level)**: the constructed
network's worst-case backlog reaches its threshold *iff* the X3C instance has an
exact cover. This is the bi-implication that makes "X3C ≤ₚ worst-case-backlog
decision" a theorem — the genuine NP-hardness content (the polynomial-time map is
`reduceToDecision`; what a full `NPHard` claim additionally needs is a
complexity-class framework Mathlib lacks, and that the network *dynamics* realize
`worstCaseBacklog`). -/
theorem X3CInstance.reduceToDecision_correct (I : X3CInstance ι α)
    (hne : I.HasAssignment) (hsq : I.q ≤ I.numSubsets) :
    I.reduceToDecision.threshold ≤ I.reduceToDecision.value ↔
      ∃ assign C, I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ I.members i) :=
  I.threshold_le_worstCaseBacklog_iff_exists_cover hne hsq

/-! ## Book restatement (Theorem 10.2, NP-hardness reduction — objective level)
The Figure-10.7 reduction sends an X3C instance to a network whose worst-case
backlog at the bottom server `W` (time `1⁻`) is `3(s−q) +` the count of saturated
subsets at an integral extremal vertex. This optimum is `≤ q`, so the backlog is
`≤ 3s − 2q`, reaching `3s − 2q` *iff* there is an X3C cover. Hence deciding
whether the worst-case backlog is at least `3s − 2q` is equivalent to X3C, which
is the polynomial reduction underlying the NP-hardness of computing exact
worst-case bounds. The objective optimum is exhibited both as the `programOptimum`
of the saturation objective (`satOptimum`, the convex program over the extremal
vertices) and as the closed-form backlog value. -/
example (I : X3CInstance ι α) (hne : I.HasAssignment) (hsq : I.q ≤ I.numSubsets) :
    -- the optimum of the saturation objective is bounded by `q` and reaches it iff a cover
    I.satOptimum ≤ (I.q : EReal) ∧
    ((I.q : EReal) ≤ I.satOptimum ↔
      ∃ assign C, I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ I.members i)) ∧
    -- the worst-case backlog is bounded by `3s − 2q` and reaches it iff a cover
    I.worstCaseBacklog ≤ 3 * I.numSubsets - 2 * I.q ∧
    (3 * I.numSubsets - 2 * I.q ≤ I.worstCaseBacklog ↔
      ∃ assign C, I.IsExactCover C assign ∧ (∀ e, ∃ i ∈ C, e ∈ I.members i)) :=
  ⟨I.satOptimum_le_q, I.q_le_satOptimum_iff_exists_cover hne,
   I.worstCaseBacklog_le hne hsq, I.threshold_le_worstCaseBacklog_iff_exists_cover hne hsq⟩

end DeepWiki
