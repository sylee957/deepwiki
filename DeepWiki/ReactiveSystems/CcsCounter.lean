import DeepWiki.ReactiveSystems.Bisimulation
import DeepWiki.ReactiveSystems.Ccs

/-! # The unbounded counter `C ~ Counter₀` (Proposition 3.1)
The book's headline infinite-state example: the recursively-defined process
`C = up.(C ∣ down.0)` is strongly bisimilar to the counter specification
`Counter₀ = up.Counter₁`, `Counterₙ = up.Counterₙ₊₁ + down.Counterₙ₋₁` (`n > 0`).
The reachable states of `C` are parallel products `C ∣ Π Pᵢ` with each `Pᵢ` either
`0` or `down.0`; we represent such a product faithfully as a left-nested comb
`comb bs` over a bit-list `bs : List Bool` (`true ↦ down.0`, `false ↦ 0`), the
head being the outermost component and `C` at the deep end. An `up` appends a
fresh `down.0` next to `C`; a `down` flips one `down.0` to `0`; the number of
`down.0` components (`bs.count true`) is the counter's value. The relating
relation `counterRel` is the book's `R`; it is a strong bisimulation
(Proposition 3.1), whence `C ~ Counter₀`. -/

namespace DeepWiki.ReactiveSystems

open LTS

/-- The two visible actions of the counter: `up` and `down`. -/
inductive CtrChan | up | down
  deriving DecidableEq

/-- Process constants: the implementation `C` and the specification family
`Counterₙ` (one constant per natural number). -/
inductive CtrK | impl | counter (n : ℕ)
  deriving DecidableEq

open CtrChan CtrK

/-- The defining environment (§3.3, p.49): `C = up.(C ∣ down.0)`,
`Counter₀ = up.Counter₁`, `Counterₙ₊₁ = up.Counterₙ₊₂ + down.Counterₙ`. -/
def ctrDefn : CtrK → CCS CtrChan CtrK
  | impl => .pre (.name up) (.par (.const impl) (.pre (.name down) .nil))
  | counter 0 => .pre (.name up) (.const (counter 1))
  | counter (n + 1) =>
      .choice (.pre (.name up) (.const (counter (n + 2))))
        (.pre (.name down) (.const (counter n)))

/-- A bag component: `item true = down.0`, `item false = 0`. -/
def item : Bool → CCS CtrChan CtrK
  | true => .pre (.name down) .nil
  | false => .nil

/-- The parallel product `C ∣ Π Pᵢ` as a left-nested comb over a bit-list: the
head is the outermost component and `C` sits at the deep (empty-list) end. So
`comb [] = C` and `comb (b :: bs) = comb bs ∣ item b`. -/
def comb : List Bool → CCS CtrChan CtrK
  | [] => .const impl
  | b :: bs => .par (comb bs) (item b)

/-- A bag component steps only when it is a `down.0`, on `down`, to `0`. -/
theorem item_step_iff {b : Bool} {α : Act CtrChan} {Q : CCS CtrChan CtrK} :
    Step ctrDefn (item b) α Q ↔ (b = true ∧ α = Act.name down ∧ Q = .nil) := by
  cases b with
  | true => simp [item, step_pre_iff]
  | false => simp [item]

/-- The comb never performs a co-name: its only actions are the names `up`/`down`,
so a parallel synchronisation (which would need complementary labels) is
impossible. -/
theorem comb_no_co {bs : List Bool} {x : CtrChan} {P : CCS CtrChan CtrK} :
    ¬ Step ctrDefn (comb bs) (Act.coname x) P := by
  induction bs generalizing P with
  | nil =>
    rw [comb, step_const_iff, ctrDefn]
    simp [step_pre_iff]
  | cons b bs ih =>
    rw [comb, step_par_iff]
    rintro (⟨P', hP, rfl⟩ | ⟨Q', hQ, rfl⟩ | ⟨ℓ, P', Q', hτ, -, -, -, rfl⟩)
    · exact ih hP
    · obtain ⟨-, hco, -⟩ := item_step_iff.1 hQ; simp at hco
    · simp at hτ

/-- **Reachable-state transitions of the comb.** `comb bs` performs exactly:
`up`, appending a fresh `down.0` (`comb (bs ++ [true])`); or `down`, flipping some
one `down.0` to `0` (some split `bs = pre ++ true :: suf ↦ pre ++ false :: suf`). -/
theorem comb_step_iff {bs : List Bool} {α : Act CtrChan} {Q : CCS CtrChan CtrK} :
    Step ctrDefn (comb bs) α Q ↔
      (α = Act.name up ∧ Q = comb (bs ++ [true])) ∨
      (α = Act.name down ∧
        ∃ pre suf, bs = pre ++ true :: suf ∧ Q = comb (pre ++ false :: suf)) := by
  induction bs generalizing Q with
  | nil =>
    rw [comb, step_const_iff, ctrDefn, step_pre_iff]
    constructor
    · rintro ⟨rfl, rfl⟩; exact Or.inl ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, _, _, h, -⟩)
      · exact ⟨rfl, rfl⟩
      · simp at h
  | cons b bs ih =>
    rw [comb, step_par_iff]
    constructor
    · rintro (⟨P', hP, rfl⟩ | ⟨Q', hQ, rfl⟩ | ⟨ℓ, P', Q', rfl, -, hP, hQ, rfl⟩)
      · -- COM1: the inner comb moves
        rcases ih.1 hP with ⟨rfl, rfl⟩ | ⟨rfl, pre, suf, rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, b :: pre, suf, rfl, rfl⟩
      · -- COM2: the head component moves
        obtain ⟨rfl, rfl, rfl⟩ := item_step_iff.1 hQ
        exact Or.inr ⟨rfl, [], bs, rfl, rfl⟩
      · -- COM3: synchronisation is impossible (the bag offers no co-name)
        obtain ⟨-, hℓco, rfl⟩ := item_step_iff.1 hQ
        cases ℓ with
        | tau => simp at hℓco
        | name a => simp at hℓco
        | coname a =>
          obtain rfl : a = down := by simpa using hℓco
          exact absurd hP comb_no_co
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, pre, suf, hbs, rfl⟩)
      · -- up appends a `down.0`, fired from the deep `C` (COM1)
        exact Or.inl ⟨comb (bs ++ [true]), ih.2 (Or.inl ⟨rfl, rfl⟩), rfl⟩
      · -- down flips one `down.0`: head (COM2) or deeper (COM1)
        cases pre with
        | nil =>
          obtain ⟨rfl, rfl⟩ : b = true ∧ bs = suf := by simpa using hbs
          exact Or.inr (Or.inl ⟨.nil, item_step_iff.2 ⟨rfl, rfl, rfl⟩, rfl⟩)
        | cons c pre =>
          obtain ⟨rfl, rfl⟩ : b = c ∧ bs = pre ++ true :: suf := by simpa using hbs
          exact Or.inl ⟨comb (pre ++ false :: suf),
            ih.2 (Or.inr ⟨rfl, pre, suf, rfl, rfl⟩), rfl⟩

/-- **Transitions of the counter specification.** `Counterₙ` performs `up` to
`Counterₙ₊₁`, and (only when `n > 0`) `down` to `Counterₙ₋₁`. -/
theorem counter_step_iff {n : ℕ} {α : Act CtrChan} {Q : CCS CtrChan CtrK} :
    Step ctrDefn (.const (counter n)) α Q ↔
      (α = Act.name up ∧ Q = .const (counter (n + 1))) ∨
      (0 < n ∧ α = Act.name down ∧ Q = .const (counter (n - 1))) := by
  rw [step_const_iff]
  cases n with
  | zero => simp [ctrDefn, step_pre_iff]
  | succ m =>
    simp only [ctrDefn, step_choice_iff, step_pre_iff, Nat.succ_sub_one]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨Nat.succ_pos m, rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨-, rfl, rfl⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩

/-- A `down`-flip drops the `down.0` count by exactly one. -/
theorem count_flip (pre suf : List Bool) :
    (pre ++ false :: suf).count true + 1 = (pre ++ true :: suf).count true := by
  have h1 : (false :: suf).count true = suf.count true := by simp
  have h2 : (true :: suf).count true = suf.count true + 1 := by simp
  rw [List.count_append, List.count_append, h1, h2]; omega

/-- **The book's relation `R`** (§3.3, p.49): a comb (a `C`-with-bag product) is
related to the counter holding as many units as the bag has `down.0` components. -/
def counterRel : CCS CtrChan CtrK → CCS CtrChan CtrK → Prop := fun p q =>
  ∃ bs : List Bool, p = comb bs ∧ q = .const (counter (bs.count true))

/-- **Proposition 3.1** (§3.3, p.50). The relation `counterRel` (the book's `R`)
is a strong bisimulation. -/
theorem isBisimulation_counterRel : IsBisimulation (ccsLTS ctrDefn) counterRel := by
  rintro p q ⟨bs, rfl, rfl⟩
  refine ⟨fun α p' hp => ?_, fun α q' hq => ?_⟩
  · -- a move of `comb bs` is matched by `Counter (count bs)`
    rw [ccsLTS_step, comb_step_iff] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, pre, suf, rfl, rfl⟩
    · refine ⟨.const (counter (bs.count true + 1)), ?_, ⟨_, rfl, ?_⟩⟩
      · rw [ccsLTS_step, counter_step_iff]; exact Or.inl ⟨rfl, rfl⟩
      · rw [List.count_append]; simp
    · refine ⟨.const (counter ((pre ++ true :: suf).count true - 1)), ?_, ⟨_, rfl, ?_⟩⟩
      · rw [ccsLTS_step, counter_step_iff]
        exact Or.inr ⟨by rw [← count_flip]; omega, rfl, rfl⟩
      · rw [← count_flip]; simp
  · -- a move of `Counter (count bs)` is matched by `comb bs`
    rw [ccsLTS_step, counter_step_iff] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨hpos, rfl, rfl⟩
    · refine ⟨comb (bs ++ [true]), ?_, ⟨_, rfl, ?_⟩⟩
      · rw [ccsLTS_step, comb_step_iff]; exact Or.inl ⟨rfl, rfl⟩
      · rw [List.count_append]; simp
    · -- count > 0 ⟹ a `down.0` exists to flip
      have hmem : true ∈ bs := List.count_pos_iff.1 hpos
      obtain ⟨pre, suf, rfl⟩ := List.append_of_mem hmem
      refine ⟨comb (pre ++ false :: suf), ?_, ⟨_, rfl, ?_⟩⟩
      · rw [ccsLTS_step, comb_step_iff]
        exact Or.inr ⟨rfl, pre, suf, rfl, rfl⟩
      · rw [← count_flip]; simp

/-- **Proposition 3.1 / §3.3** (p.49). The unbounded counter implementation is
strongly bisimilar to its specification: `C ~ Counter₀`. -/
theorem counter_bisim : (CCS.const impl) ~[ccsLTS ctrDefn] (CCS.const (counter 0)) :=
  isBisimulation_counterRel.le_bisimilar ⟨[], rfl, rfl⟩

/-- Faithfulness: `C` does exactly an `up` to `C ∣ down.0`, matching `Counter₀`'s
`up` to `Counter₁`; and `Counterₙ₊₁` additionally does `down` to `Counterₙ`. -/
example :
    Step ctrDefn (.const impl) (Act.name up) (.par (.const impl) (item true)) ∧
    Step ctrDefn (.const (counter 0)) (Act.name up) (.const (counter 1)) ∧
    Step ctrDefn (.const (counter 1)) (Act.name down) (.const (counter 0)) :=
  ⟨Step.con (Step.act _ _), Step.con (Step.act _ _),
   Step.con (Step.sumr (Step.act _ _))⟩

end DeepWiki.ReactiveSystems
