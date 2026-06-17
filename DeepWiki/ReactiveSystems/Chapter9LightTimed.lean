import DeepWiki.ReactiveSystems.TimedCCS

/-! # Exercises 9.1–9.2 — the timed light switch
The timed-CCS light switch (eq. 9.1): `Off ≝ press.Light`, `Bright ≝ press.Off`,
`Light ≝ ε(1.4).τ.press.Off + press.Bright`. It is guarded (Ex 9.1), and from the
`Light` state a delay of `d ≤ 1.4` counts the delay-prefix down (Ex 9.2). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- The single channel `press`. -/
inductive LightChan | press
  deriving DecidableEq

/-- The light-switch constants. -/
inductive LightK | Light | Off | Bright
  deriving DecidableEq

/-- Equation (9.1): `Off ≝ press.Light`, `Bright ≝ press.Off`,
`Light ≝ ε(1.4).τ.press.Off + press.Bright`. -/
def lightDefn : LightK → TCCS LightChan LightK
  | .Off => .pre (.name .press) (.const .Light)
  | .Bright => .pre (.name .press) (.const .Off)
  | .Light => .choice (.eps 1.4 (.pre Act.tau (.pre (.name .press) (.const .Off))))
      (.pre (.name .press) (.const .Bright))

/-- **Exercise 9.1** (§9.3, p.166). The light-switch specification is guarded: every
constant occurrence lies under an action prefix or the positive delay `ε(1.4)`. -/
theorem ex_9_1 : IsGuardedDefn lightDefn := by
  intro K
  cases K with
  | Light => exact ⟨Or.inl (by rw [← NNReal.coe_pos]; push_cast; norm_num), trivial⟩
  | Off => trivial
  | Bright => trivial

/-- **Exercise 9.2** (§9.3, p.168). From the `Light` state a delay `d ≤ 1.4` counts the
delay-prefix down: `Light —d→ ε(1.4−d).τ.press.Off + press.Bright` (the action-prefixed
summand `press.Bright` idles patiently). -/
theorem ex_9_2 {d : ℝ≥0} (h : d ≤ 1.4) :
    (tccsTLTS lightDefn).delay (.const .Light) d
      (.choice (.eps (1.4 - d) (.pre Act.tau (.pre (.name .press) (.const .Off))))
        (.pre (.name .press) (.const .Bright))) :=
  TDelay.con (TDelay.choice (TDelay.epsPartial h) (TDelay.prePatient (by decide) d))

end DeepWiki.ReactiveSystems
