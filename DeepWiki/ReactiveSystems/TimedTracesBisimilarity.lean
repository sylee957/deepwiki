import DeepWiki.ReactiveSystems.TimedTraces
import DeepWiki.ReactiveSystems.TimedBisimulationUntimed

/-! # Untimed bisimilarity preserves the untimed language
Timed bisimilarity already preserves the timed (and hence untimed) language
(`TLTS.timedLang_eq_of_timedBisimilar`). The genuinely *untimed* analogue —
untimed bisimilarity preserves the untimed language — needs its own argument,
because untimed bisimilarity matches a delay by *some* delay of a possibly
different duration. We package an untimed run as a duration-forgetting
`RealizesUntimed` predicate (each action preceded by *some* delay), show it is
exactly the untimed language, and transport it across untimed bisimilarity. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

variable {Proc Act : Type*}

/-- `RealizesUntimed T s u`: the action list `u` is performed from `s` by a
delay/action run that *forgets* delay durations — each action is preceded by some
delay of an unspecified duration. -/
def RealizesUntimed (T : TLTS Proc Act) : Proc → List Act → Prop
  | _, [] => True
  | s, a :: u => ∃ d s1 s2, T.delay s d s1 ∧ T.act s1 a s2 ∧ T.RealizesUntimed s2 u

/-- A timed run realises the untimed projection of its trace (forget the
time-stamps). -/
theorem realizesUntimed_of_timedTraceFrom {T : TLTS Proc Act} :
    ∀ {w : List (ℝ≥0 × Act)} {s : Proc} {now : ℝ≥0},
      T.TimedTraceFrom s now w → T.RealizesUntimed s (w.map Prod.snd) := by
  intro w
  induction w with
  | nil => exact fun _ => trivial
  | cons hd tl ih =>
      obtain ⟨t, a⟩ := hd
      intro s now hw
      obtain ⟨s1, s2, _hle, hdel, hact, hrest⟩ := hw
      exact ⟨t - now, s1, s2, hdel, hact, ih hrest⟩

/-- A duration-forgetting run can be time-stamped into a genuine timed run from
any start time. -/
theorem timedTraceFrom_of_realizesUntimed {T : TLTS Proc Act} :
    ∀ {u : List Act} {s : Proc}, T.RealizesUntimed s u → ∀ now : ℝ≥0,
      ∃ w, T.TimedTraceFrom s now w ∧ w.map Prod.snd = u := by
  intro u
  induction u with
  | nil => exact fun _ now => ⟨[], trivial, rfl⟩
  | cons a u ih =>
      rintro s ⟨d, s1, s2, hdel, hact, hrest⟩ now
      obtain ⟨w, hw, hmap⟩ := ih hrest (now + d)
      refine ⟨(now + d, a) :: w, ⟨s1, s2, le_self_add, ?_, hact, hw⟩, ?_⟩
      · rw [add_tsub_cancel_left]; exact hdel
      · rw [List.map_cons, hmap]

/-- The untimed language is exactly the set of duration-forgetting runs. -/
theorem untimedTrace_iff_realizesUntimed {T : TLTS Proc Act} {s : Proc} {u : List Act} :
    T.UntimedTrace s u ↔ T.RealizesUntimed s u := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact realizesUntimed_of_timedTraceFrom hw
  · intro hu
    obtain ⟨w, hw, hmap⟩ := timedTraceFrom_of_realizesUntimed hu 0
    exact ⟨w, hw, hmap⟩

/-- Untimed bisimilarity transports a duration-forgetting run: actions are matched
exactly, delays by *some* delay. -/
theorem realizesUntimed_of_untimedBisimilar {T : TLTS Proc Act} :
    ∀ {u : List Act} {p q : Proc},
      T.UntimedBisimilar p q → T.RealizesUntimed p u → T.RealizesUntimed q u := by
  intro u
  induction u with
  | nil => exact fun _ _ => trivial
  | cons a u ih =>
      rintro p q h ⟨d, s1, s2, hdel, hact, hrest⟩
      rw [untimedBisimilar_iff] at h
      obtain ⟨d', q1, hq1del, hb1⟩ := h.2.2.1 d s1 hdel
      rw [untimedBisimilar_iff] at hb1
      obtain ⟨q2, hq2act, hb2⟩ := hb1.1 a s2 hact
      exact ⟨d', q1, q2, hq1del, hq2act, ih hb2 hrest⟩

/-- **Untimed bisimilarity implies untimed-trace equivalence**: untimed-bisimilar
states have the same untimed language. -/
theorem untimedLang_eq_of_untimedBisimilar {T : TLTS Proc Act} {p q : Proc}
    (h : T.UntimedBisimilar p q) : T.untimedLang p = T.untimedLang q := by
  ext u
  constructor
  · intro hu
    exact untimedTrace_iff_realizesUntimed.mpr
      (realizesUntimed_of_untimedBisimilar h (untimedTrace_iff_realizesUntimed.mp hu))
  · intro hu
    exact untimedTrace_iff_realizesUntimed.mpr
      (realizesUntimed_of_untimedBisimilar ((untimedBisimilar_equivalence T).symm h)
        (untimedTrace_iff_realizesUntimed.mp hu))

end TLTS

end DeepWiki.ReactiveSystems
