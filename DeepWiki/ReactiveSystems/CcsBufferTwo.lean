import DeepWiki.ReactiveSystems.Bisimulation
import DeepWiki.ReactiveSystems.Ccs

/-! # A two-place buffer equals two one-place buffers
A capacity-two buffer is strongly bisimilar to two capacity-one buffers in
parallel, `B²₀ ~ B¹₀ ∣ B¹₀`. The one-place buffer is `B¹₀ = in.B¹₁`,
`B¹₁ = out.B¹₀`; the two-place buffer is `B²₀ = in.B²₁`,
`B²₁ = in.B²₂ + out.B²₀`, `B²₂ = out.B²₁`. The bisimulation relates `B²ᵢ` to a
parallel pair of one-place buffers exactly `i` of which are full. (The general
`n`-buffer statement is a parallel-bag bisimulation over `n` components.) -/

namespace DeepWiki.ReactiveSystems

open LTS

/-- The two channels of the buffer: `in` and `out`. -/
inductive BufChan | bin | bout
  deriving DecidableEq

/-- Process constants: the one-place buffer states `B¹₀`/`B¹₁` (empty/full) and
the two-place buffer states `B²₀`/`B²₁`/`B²₂` (holding 0/1/2 items). -/
inductive BufK | One0 | One1 | Two0 | Two1 | Two2
  deriving DecidableEq

open BufChan BufK

/-- Defining environment: `B¹₀ = in.B¹₁`, `B¹₁ = out.B¹₀`; `B²₀ = in.B²₁`,
`B²₁ = in.B²₂ + out.B²₀`, `B²₂ = out.B²₁`. -/
def bufDefn : BufK → CCS BufChan BufK
  | One0 => .pre (.name bin) (.const One1)
  | One1 => .pre (.name bout) (.const One0)
  | Two0 => .pre (.name bin) (.const Two1)
  | Two1 => .choice (.pre (.name bin) (.const Two2)) (.pre (.name bout) (.const Two0))
  | Two2 => .pre (.name bout) (.const Two1)

/-- The bisimulation: `B²ᵢ` is related to a parallel pair of one-place buffers
exactly `i` of which are full. -/
def bufRel : CCS BufChan BufK → CCS BufChan BufK → Prop := fun p q =>
  (p = .const Two0 ∧ q = .par (.const One0) (.const One0)) ∨
  (p = .const Two1 ∧ q = .par (.const One1) (.const One0)) ∨
  (p = .const Two1 ∧ q = .par (.const One0) (.const One1)) ∨
  (p = .const Two2 ∧ q = .par (.const One1) (.const One1))

/-- A two-place buffer is strongly bisimilar to two one-place buffers in
parallel: `B²₀ ~ B¹₀ ∣ B¹₀`. -/
theorem buffer_two : (CCS.const Two0) ~[ccsLTS bufDefn]
    (CCS.par (CCS.const One0) (CCS.const One0)) := by
  refine ⟨bufRel, ?_, Or.inl ⟨rfl, rfl⟩⟩
  rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · -- (B²₀, B¹₀ ∣ B¹₀): only `in` is possible
    refine ⟨fun α p' hp => ?_, fun α q' hq => ?_⟩
    · simp only [ccsLTS_step, step_const_iff, bufDefn, step_pre_iff] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨_, Step.com1 (Step.con (Step.act _ _)), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · rw [ccsLTS_step, step_par_iff] at hq
      rcases hq with ⟨l', hl, rfl⟩ | ⟨r', hr, rfl⟩ | ⟨ℓ, l', r', _, _, hl, hr, rfl⟩
      · simp only [step_const_iff, bufDefn, step_pre_iff] at hl; obtain ⟨rfl, rfl⟩ := hl
        exact ⟨_, Step.con (Step.act _ _), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · simp only [step_const_iff, bufDefn, step_pre_iff] at hr; obtain ⟨rfl, rfl⟩ := hr
        exact ⟨_, Step.con (Step.act _ _), Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · simp only [step_const_iff, bufDefn, step_pre_iff] at hl; obtain ⟨rfl, _⟩ := hl
        simp [step_const_iff, bufDefn, step_pre_iff, Act.co] at hr
  · -- (B²₁, B¹₁ ∣ B¹₀): `in` (right fills) or `out` (left empties)
    refine ⟨fun α p' hp => ?_, fun α q' hq => ?_⟩
    · simp only [ccsLTS_step, step_const_iff, bufDefn, step_choice_iff, step_pre_iff] at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, Step.com2 (Step.con (Step.act _ _)), Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
      · exact ⟨_, Step.com1 (Step.con (Step.act _ _)), Or.inl ⟨rfl, rfl⟩⟩
    · rw [ccsLTS_step, step_par_iff] at hq
      rcases hq with ⟨l', hl, rfl⟩ | ⟨r', hr, rfl⟩ | ⟨ℓ, l', r', _, _, hl, hr, rfl⟩
      · simp only [step_const_iff, bufDefn, step_pre_iff] at hl; obtain ⟨rfl, rfl⟩ := hl
        exact ⟨_, Step.con (Step.sumr (Step.act _ _)), Or.inl ⟨rfl, rfl⟩⟩
      · simp only [step_const_iff, bufDefn, step_pre_iff] at hr; obtain ⟨rfl, rfl⟩ := hr
        exact ⟨_, Step.con (Step.suml (Step.act _ _)), Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
      · simp only [step_const_iff, bufDefn, step_pre_iff] at hl; obtain ⟨rfl, _⟩ := hl
        simp [step_const_iff, bufDefn, step_pre_iff, Act.co] at hr
  · -- (B²₁, B¹₀ ∣ B¹₁): symmetric to the previous
    refine ⟨fun α p' hp => ?_, fun α q' hq => ?_⟩
    · simp only [ccsLTS_step, step_const_iff, bufDefn, step_choice_iff, step_pre_iff] at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, Step.com1 (Step.con (Step.act _ _)), Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
      · exact ⟨_, Step.com2 (Step.con (Step.act _ _)), Or.inl ⟨rfl, rfl⟩⟩
    · rw [ccsLTS_step, step_par_iff] at hq
      rcases hq with ⟨l', hl, rfl⟩ | ⟨r', hr, rfl⟩ | ⟨ℓ, l', r', _, _, hl, hr, rfl⟩
      · simp only [step_const_iff, bufDefn, step_pre_iff] at hl; obtain ⟨rfl, rfl⟩ := hl
        exact ⟨_, Step.con (Step.suml (Step.act _ _)), Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
      · simp only [step_const_iff, bufDefn, step_pre_iff] at hr; obtain ⟨rfl, rfl⟩ := hr
        exact ⟨_, Step.con (Step.sumr (Step.act _ _)), Or.inl ⟨rfl, rfl⟩⟩
      · simp only [step_const_iff, bufDefn, step_pre_iff] at hl; obtain ⟨rfl, _⟩ := hl
        simp [step_const_iff, bufDefn, step_pre_iff, Act.co] at hr
  · -- (B²₂, B¹₁ ∣ B¹₁): only `out` is possible
    refine ⟨fun α p' hp => ?_, fun α q' hq => ?_⟩
    · simp only [ccsLTS_step, step_const_iff, bufDefn, step_pre_iff] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨_, Step.com1 (Step.con (Step.act _ _)), Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · rw [ccsLTS_step, step_par_iff] at hq
      rcases hq with ⟨l', hl, rfl⟩ | ⟨r', hr, rfl⟩ | ⟨ℓ, l', r', _, _, hl, hr, rfl⟩
      · simp only [step_const_iff, bufDefn, step_pre_iff] at hl; obtain ⟨rfl, rfl⟩ := hl
        exact ⟨_, Step.con (Step.act _ _), Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · simp only [step_const_iff, bufDefn, step_pre_iff] at hr; obtain ⟨rfl, rfl⟩ := hr
        exact ⟨_, Step.con (Step.act _ _), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · simp only [step_const_iff, bufDefn, step_pre_iff] at hl; obtain ⟨rfl, _⟩ := hl
        simp [step_const_iff, bufDefn, step_pre_iff, Act.co] at hr

end DeepWiki.ReactiveSystems
