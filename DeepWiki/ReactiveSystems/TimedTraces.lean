import DeepWiki.ReactiveSystems.TimedTransitionSystems

/-! # Timed and untimed trace equivalence
A *timed trace* of a TLTS records, for each visible action, the absolute time at
which it occurs along a run that alternates delays and actions from a start state;
the *timed language* is the set of finite timed traces. Forgetting the time-stamps
gives the *untimed traces* and the *untimed language*. Since the untimed language is
exactly the projection of the timed language onto its action components, timed-language
equivalence implies untimed-language equivalence. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

variable {Proc Act : Type*}

/-- `TimedTraceFrom T s now w`: from state `s` at current time
`now`, the list `w` of `(time-stamp, action)` pairs is realised by a run that, for
each `(t, a)`, delays to absolute time `t` (a delay of `t - now`, with `now ≤ t`)
and then performs `a`. -/
def TimedTraceFrom (T : TLTS Proc Act) : Proc → ℝ≥0 → List (ℝ≥0 × Act) → Prop
  | _, _, [] => True
  | s, now, (t, a) :: w =>
      ∃ s1 s2, now ≤ t ∧ T.delay s (t - now) s1 ∧ T.act s1 a s2 ∧ TimedTraceFrom T s2 t w

/-- A *timed trace* of `T` from `s`: a run starting at time `0`
realising the `(time-stamp, action)` list `w`. -/
def TimedTrace (T : TLTS Proc Act) (s : Proc) (w : List (ℝ≥0 × Act)) : Prop :=
  TimedTraceFrom T s 0 w

/-- The *timed language* of `T` from `s`: its set of finite
timed traces. -/
def timedLang (T : TLTS Proc Act) (s : Proc) : Set (List (ℝ≥0 × Act)) :=
  {w | T.TimedTrace s w}

/-- An *untimed trace* is the action projection of a timed
trace: `u` is untimed iff some timed trace `w` has `w`'s actions equal to `u`. -/
def UntimedTrace (T : TLTS Proc Act) (s : Proc) (u : List Act) : Prop :=
  ∃ w ∈ T.timedLang s, w.map Prod.snd = u

/-- The *untimed language* of `T` from `s`. -/
def untimedLang (T : TLTS Proc Act) (s : Proc) : Set (List Act) :=
  {u | T.UntimedTrace s u}

/-- The untimed language is exactly the projection of the timed language onto its
action components. -/
theorem untimedLang_eq_image (T : TLTS Proc Act) (s : Proc) :
    T.untimedLang s = (List.map Prod.snd) '' T.timedLang s := by
  ext u
  simp only [untimedLang, UntimedTrace, Set.mem_setOf_eq, Set.mem_image]

/-- Timed-language equivalence implies untimed-language
equivalence: forgetting the time-stamps is a function of the timed language. -/
theorem timedLang_eq_untimedLang_eq {T₁ T₂ : TLTS Proc Act} {s₁ s₂ : Proc}
    (h : T₁.timedLang s₁ = T₂.timedLang s₂) : T₁.untimedLang s₁ = T₂.untimedLang s₂ := by
  rw [untimedLang_eq_image, untimedLang_eq_image, h]

/-! ## Timed bisimilarity preserves the timed language -/

/-- Timed bisimilarity transports a timed run: if `p` is timed bisimilar to `q`
and `p` realises `w` from time `now`, then so does `q` (delay-then-action transfer
at each step). -/
theorem timedTraceFrom_of_timedBisimilar {T : TLTS Proc Act} :
    ∀ {w : List (ℝ≥0 × Act)} {p q : Proc} {now : ℝ≥0},
      TimedBisimilar T p q → T.TimedTraceFrom p now w → T.TimedTraceFrom q now w := by
  intro w
  induction w with
  | nil => exact fun _ _ => trivial
  | cons hd tl ih =>
      obtain ⟨t, a⟩ := hd
      intro p q now h hw
      obtain ⟨s1, s2, hle, hdel, hact, hrest⟩ := hw
      rw [timedBisimilar_iff] at h
      obtain ⟨q1, hq1, hb1⟩ := h.2.2.1 _ _ hdel
      rw [timedBisimilar_iff] at hb1
      obtain ⟨q2, hq2, hb2⟩ := hb1.1 _ _ hact
      exact ⟨q1, q2, hle, hq1, hq2, ih hb2 hrest⟩

/-- **Timed bisimilarity implies timed-trace equivalence**: timed bisimilar states
have the same timed language. -/
theorem timedLang_eq_of_timedBisimilar {T : TLTS Proc Act} {p q : Proc}
    (h : TimedBisimilar T p q) : T.timedLang p = T.timedLang q := by
  ext w
  exact ⟨fun hw => timedTraceFrom_of_timedBisimilar h hw,
         fun hw => timedTraceFrom_of_timedBisimilar ((timedBisimilar_equivalence T).symm h) hw⟩

/-- **Timed bisimilarity implies untimed-trace equivalence**: forget the
time-stamps of the equal timed languages. -/
theorem untimedLang_eq_of_timedBisimilar {T : TLTS Proc Act} {p q : Proc}
    (h : TimedBisimilar T p q) : T.untimedLang p = T.untimedLang q :=
  timedLang_eq_untimedLang_eq (timedLang_eq_of_timedBisimilar h)

end TLTS

end DeepWiki.ReactiveSystems
