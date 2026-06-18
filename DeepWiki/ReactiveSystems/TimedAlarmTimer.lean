import DeepWiki.ReactiveSystems.TimedCcs

/-! # A TCCS alarm timer (Exercise 9.4)
An alarm timer that can be *set* to time-out after 5, 10 or 30 minutes (input
actions `set5`, `set10`, `set30`), *signals* the time-out by the output `t̄o`, and
can be *reset* with a new period at any moment — in particular before the running
period has elapsed. Modelled in TCCS: each armed state is a choice of a delay-prefix
`ε(d).t̄o.Idle` (counting the period down to the time-out) with the set menu (so a
new `set` action can re-arm it during the countdown, the set-prefixes idling
patiently while time passes). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- Alarm-timer channels: the set inputs `set5`/`set10`/`set30` and the time-out
output `to`. -/
inductive AlarmChan | set5 | set10 | set30 | to
  deriving DecidableEq

/-- Alarm-timer constants: idle (unset) and armed for each period. -/
inductive AlarmK | Idle | Armed5 | Armed10 | Armed30
  deriving DecidableEq

/-- The *set menu* offered in every state: arm for 5, 10 or 30 by an input action. -/
def alarmSet : TCCS AlarmChan AlarmK :=
  .choice (.pre (.name .set5) (.const .Armed5))
    (.choice (.pre (.name .set10) (.const .Armed10))
      (.pre (.name .set30) (.const .Armed30)))

/-- The alarm timer: `Idle` offers the set menu; each `Armed_d` counts `d` down then
outputs `t̄o` and returns to `Idle`, while *also* offering the set menu (so it can be
reset at any moment during the countdown). -/
def alarmDefn : AlarmK → TCCS AlarmChan AlarmK
  | .Idle => alarmSet
  | .Armed5 => .choice (.eps 5 (.pre (.coname .to) (.const .Idle))) alarmSet
  | .Armed10 => .choice (.eps 10 (.pre (.coname .to) (.const .Idle))) alarmSet
  | .Armed30 => .choice (.eps 30 (.pre (.coname .to) (.const .Idle))) alarmSet

/-- The specification is guarded: every constant occurs under an action prefix or a
positive delay. -/
theorem alarmDefn_isGuarded : IsGuardedDefn alarmDefn := by
  intro K; cases K <;> simp [IsGuarded, alarmDefn, alarmSet]

/-- The set menu idles patiently: it delays any amount, staying put (each set-prefix
is non-`τ`, so time may pass). -/
theorem alarmSet_delay (d : ℝ≥0) : TDelay alarmDefn alarmSet d alarmSet :=
  TDelay.choice (TDelay.prePatient (by decide) d)
    (TDelay.choice (TDelay.prePatient (by decide) d) (TDelay.prePatient (by decide) d))

/-- The set menu arms for 5 on input `set5`. -/
theorem alarmSet_set5 : TAct alarmDefn alarmSet (Act.name .set5) (.const .Armed5) :=
  TAct.suml (TAct.act _ _)

/-- The set menu arms for 10 on input `set10`. -/
theorem alarmSet_set10 : TAct alarmDefn alarmSet (Act.name .set10) (.const .Armed10) :=
  TAct.sumr (TAct.suml (TAct.act _ _))

/-- The set menu arms for 30 on input `set30`. -/
theorem alarmSet_set30 : TAct alarmDefn alarmSet (Act.name .set30) (.const .Armed30) :=
  TAct.sumr (TAct.sumr (TAct.act _ _))

/-- Setting the idle timer arms it: `Idle —set5→ Armed5`. -/
theorem alarm_idle_arms :
    (tccsTLTS alarmDefn).act (.const .Idle) (Act.name .set5) (.const .Armed5) :=
  TAct.con alarmSet_set5

/-- The armed timer counts its period down: `Armed5 —5→ ε(0).t̄o.Idle + set menu`. -/
theorem alarm5_countdown :
    (tccsTLTS alarmDefn).delay (.const .Armed5) 5
      (.choice (.eps 0 (.pre (.coname .to) (.const .Idle))) alarmSet) :=
  TDelay.con (TDelay.choice (TDelay.eps_full _ _ _) (alarmSet_delay 5))

/-- Once the period has elapsed the timer signals the time-out and returns to idle:
the post-countdown state does `t̄o → Idle`. -/
theorem alarm5_timeOut :
    (tccsTLTS alarmDefn).act
      (.choice (.eps 0 (.pre (.coname .to) (.const .Idle))) alarmSet)
      (Act.coname .to) (.const .Idle) :=
  TAct.suml (TAct.eps0 (TAct.act _ _))

/-- The timer can be reset mid-wait: after any delay `d ≤ 5` (before the period
elapses) it can still be re-armed to a new period (`set10 → Armed10`). -/
theorem alarm5_reset {d : ℝ≥0} (h : d ≤ 5) :
    ∃ Y, (tccsTLTS alarmDefn).delay (.const .Armed5) d Y ∧
      (tccsTLTS alarmDefn).act Y (Act.name .set10) (.const .Armed10) :=
  ⟨_, TDelay.con (TDelay.choice (TDelay.epsPartial h) (alarmSet_delay d)),
    TAct.sumr alarmSet_set10⟩

end DeepWiki.ReactiveSystems
