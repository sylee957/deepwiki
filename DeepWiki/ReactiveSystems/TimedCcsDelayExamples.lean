import DeepWiki.ReactiveSystems.TimedCCS

/-! # Which timed-CCS agents can delay by 4
Four recursive TCCS agents (`a, b` visible, `τ` silent):
`M₁ ≝ ε(3).(ε(2).a.M₁ + b.M₁)`, `M₂ ≝ ε(5).a.M₂ + ε(3).b.M₂`,
`M₃ ≝ ε(3).(ε(2).a.M₃ + τ.M₃)`, `M₄ ≝ ε(5).a.M₄ + ε(3).τ.M₄`.
`M₁` and `M₂` can delay by `4` (the `b`-prefix idles patiently); `M₃` and `M₄`
cannot — after `3` time units a `τ` becomes enabled and maximal progress halts
time. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- Visible channels `a`, `b` of Exercise 9.6. -/
inductive Name96 | a | b
  deriving DecidableEq

/-- The four process constants `M₁..M₄`. -/
inductive K96 | M1 | M2 | M3 | M4
  deriving DecidableEq

/-- The definition environment for `M₁..M₄`. -/
def defn96 : K96 → TCCS Name96 K96
  | .M1 => .eps 3 (.choice (.eps 2 (.pre (.name .a) (.const .M1))) (.pre (.name .b) (.const .M1)))
  | .M2 => .choice (.eps 5 (.pre (.name .a) (.const .M2))) (.eps 3 (.pre (.name .b) (.const .M2)))
  | .M3 => .eps 3 (.choice (.eps 2 (.pre (.name .a) (.const .M3))) (.pre Act.tau (.const .M3)))
  | .M4 => .choice (.eps 5 (.pre (.name .a) (.const .M4))) (.eps 3 (.pre Act.tau (.const .M4)))

private theorem sub_two_one : (2 : ℝ≥0) - 1 = 1 := by
  rw [← NNReal.coe_inj, NNReal.coe_sub (by norm_num)]; norm_num

private theorem sub_five_four : (5 : ℝ≥0) - 4 = 1 := by
  rw [← NNReal.coe_inj, NNReal.coe_sub (by norm_num)]; norm_num

/-- `M₁ —4→ ε(1).a.M₁ + b.M₁`: wait out `ε(3)`, then let the body delay `1` more
(the `ε(2)`-prefix counts down to `ε(1)`, the `b`-prefix idles). -/
theorem M1_delay4 :
    TDelay defn96 (.const .M1) 4
      (.choice (.eps 1 (.pre (.name .a) (.const .M1))) (.pre (.name .b) (.const .M1))) := by
  rw [tDelay_const_iff]
  show TDelay defn96 (.eps 3 _) 4 _
  rw [tDelay_eps_iff]
  refine Or.inr ⟨1, by norm_num, ?_⟩
  rw [tDelay_choice_iff]
  refine ⟨_, _, ?_, ?_, rfl⟩
  · rw [tDelay_eps_iff]; exact Or.inl ⟨by norm_num, by rw [sub_two_one]⟩
  · rw [tDelay_pre_iff]; exact ⟨by decide, rfl⟩

/-- `M₂ —4→ ε(1).a.M₂ + b.M₂`: `ε(5)` counts down to `ε(1)`, while `ε(3).b.M₂` waits
out its prefix and the `b`-prefix idles for the remaining unit. -/
theorem M2_delay4 :
    TDelay defn96 (.const .M2) 4
      (.choice (.eps 1 (.pre (.name .a) (.const .M2))) (.pre (.name .b) (.const .M2))) := by
  rw [tDelay_const_iff]
  show TDelay defn96 (.choice _ _) 4 _
  rw [tDelay_choice_iff]
  refine ⟨_, _, ?_, ?_, rfl⟩
  · rw [tDelay_eps_iff]; exact Or.inl ⟨by norm_num, by rw [sub_five_four]⟩
  · rw [tDelay_eps_iff]; refine Or.inr ⟨1, by norm_num, ?_⟩
    rw [tDelay_pre_iff]; exact ⟨by decide, rfl⟩

/-- `M₃` cannot delay by `4`: after waiting out `ε(3)` the body `ε(2).a.M₃ + τ.M₃`
has an enabled `τ` (in the `τ.M₃` summand), so maximal progress forbids any further
delay. -/
theorem M3_not_delay4 : ¬ ∃ Q, TDelay defn96 (.const .M3) 4 Q := by
  rintro ⟨Q, hQ⟩
  rw [tDelay_const_iff] at hQ
  simp only [defn96] at hQ
  rw [tDelay_eps_iff] at hQ
  rcases hQ with ⟨hle, _⟩ | ⟨_, _, hbody⟩
  · exact absurd hle (by norm_num)
  · rw [tDelay_choice_iff] at hbody
    obtain ⟨_, _, _, hτ, _⟩ := hbody
    rw [tDelay_pre_iff] at hτ
    exact hτ.1 rfl

/-- `M₄` cannot delay by `4`: its `ε(3).τ.M₄` summand can only delay `3` before the
`τ` becomes urgent, so the choice (which delays componentwise) cannot reach `4`. -/
theorem M4_not_delay4 : ¬ ∃ Q, TDelay defn96 (.const .M4) 4 Q := by
  rintro ⟨Q, hQ⟩
  rw [tDelay_const_iff] at hQ
  simp only [defn96] at hQ
  rw [tDelay_choice_iff] at hQ
  obtain ⟨_, _, _, hτ, _⟩ := hQ
  rw [tDelay_eps_iff] at hτ
  rcases hτ with ⟨hle, _⟩ | ⟨_, _, hbody⟩
  · exact absurd hle (by norm_num)
  · rw [tDelay_pre_iff] at hbody
    exact hbody.1 rfl

/-- **Exercise 9.6** (§9.4, p.171). Of the four agents, exactly `M₁` and `M₂` can
delay by `4` time units (with the indicated targets); `M₃` and `M₄` cannot, because
a `τ` becomes enabled after `3` units and maximal progress halts time. -/
theorem tccsAgents_delay4_characterization :
    TDelay defn96 (.const .M1) 4
        (.choice (.eps 1 (.pre (.name .a) (.const .M1))) (.pre (.name .b) (.const .M1))) ∧
    TDelay defn96 (.const .M2) 4
        (.choice (.eps 1 (.pre (.name .a) (.const .M2))) (.pre (.name .b) (.const .M2))) ∧
    (¬ ∃ Q, TDelay defn96 (.const .M3) 4 Q) ∧
    (¬ ∃ Q, TDelay defn96 (.const .M4) 4 Q) :=
  ⟨M1_delay4, M2_delay4, M3_not_delay4, M4_not_delay4⟩

end DeepWiki.ReactiveSystems
