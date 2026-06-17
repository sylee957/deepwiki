import DeepWiki.ReactiveSystems.TimedCCS

/-! # The timed light switch: guardedness and a delay transition
The timed-CCS light switch: `Off ≝ press.Light`, `Bright ≝ press.Off`,
`Light ≝ ε(1.4).τ.press.Off + press.Bright`. It is guarded, and from the
`Light` state a delay of `d ≤ 1.4` counts the delay-prefix down. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- The single channel `press`. -/
inductive LightChan | press
  deriving DecidableEq

/-- The light-switch constants. -/
inductive LightK | Light | Off | Bright
  deriving DecidableEq

/-- The light-switch definitions: `Off ≝ press.Light`, `Bright ≝ press.Off`,
`Light ≝ ε(1.4).τ.press.Off + press.Bright`. -/
def lightDefn : LightK → TCCS LightChan LightK
  | .Off => .pre (.name .press) (.const .Light)
  | .Bright => .pre (.name .press) (.const .Off)
  | .Light => .choice (.eps 1.4 (.pre Act.tau (.pre (.name .press) (.const .Off))))
      (.pre (.name .press) (.const .Bright))

/-- The light-switch specification is guarded: every
constant occurrence lies under an action prefix or the positive delay `ε(1.4)`. -/
theorem lightDefn_isGuarded : IsGuardedDefn lightDefn := by
  intro K
  cases K with
  | Light => exact ⟨Or.inl (by rw [← NNReal.coe_pos]; push_cast; norm_num), trivial⟩
  | Off => trivial
  | Bright => trivial

/-- From the `Light` state a delay `d ≤ 1.4` counts the
delay-prefix down: `Light —d→ ε(1.4−d).τ.press.Off + press.Bright` (the action-prefixed
summand `press.Bright` idles patiently). -/
theorem lightDefn_light_delayReduces {d : ℝ≥0} (h : d ≤ 1.4) :
    (tccsTLTS lightDefn).delay (.const .Light) d
      (.choice (.eps (1.4 - d) (.pre Act.tau (.pre (.name .press) (.const .Off))))
        (.pre (.name .press) (.const .Bright))) :=
  TDelay.con (TDelay.choice (TDelay.epsPartial h) (TDelay.prePatient (by decide) d))

end DeepWiki.ReactiveSystems
