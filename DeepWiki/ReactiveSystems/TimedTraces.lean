import DeepWiki.ReactiveSystems.TimedTransitionSystems

/-! # Timed and untimed trace equivalence (§11.1)
A *timed trace* of a TLTS records, for each visible action, the absolute time at
which it occurs along a run that alternates delays and actions from a start state
(Definition 11.1); the *timed language* is the set of finite timed traces
(Definition 11.2). Forgetting the time-stamps gives the *untimed traces* and the
*untimed language* (Definitions 11.3–11.4). Since the untimed language is exactly
the projection of the timed language onto its action components, timed-language
equivalence implies untimed-language equivalence (Theorem 11.1). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

variable {Proc Act : Type*}

/-- **Definition 11.1.** `TimedTraceFrom T s now w`: from state `s` at current time
`now`, the list `w` of `(time-stamp, action)` pairs is realised by a run that, for
each `(t, a)`, delays to absolute time `t` (a delay of `t - now`, with `now ≤ t`)
and then performs `a`. -/
def TimedTraceFrom (T : TLTS Proc Act) : Proc → ℝ≥0 → List (ℝ≥0 × Act) → Prop
  | _, _, [] => True
  | s, now, (t, a) :: w =>
      ∃ s1 s2, now ≤ t ∧ T.delay s (t - now) s1 ∧ T.act s1 a s2 ∧ TimedTraceFrom T s2 t w

/-- **Definition 11.1.** A *timed trace* of `T` from `s`: a run starting at time `0`
realising the `(time-stamp, action)` list `w`. -/
def TimedTrace (T : TLTS Proc Act) (s : Proc) (w : List (ℝ≥0 × Act)) : Prop :=
  TimedTraceFrom T s 0 w

/-- **Definition 11.2.** The *timed language* of `T` from `s`: its set of finite
timed traces. -/
def timedLang (T : TLTS Proc Act) (s : Proc) : Set (List (ℝ≥0 × Act)) :=
  {w | T.TimedTrace s w}

/-- **Definition 11.3.** An *untimed trace* is the action projection of a timed
trace: `u` is untimed iff some timed trace `w` has `w`'s actions equal to `u`. -/
def UntimedTrace (T : TLTS Proc Act) (s : Proc) (u : List Act) : Prop :=
  ∃ w ∈ T.timedLang s, w.map Prod.snd = u

/-- **Definition 11.4.** The *untimed language* of `T` from `s`. -/
def untimedLang (T : TLTS Proc Act) (s : Proc) : Set (List Act) :=
  {u | T.UntimedTrace s u}

/-- The untimed language is exactly the projection of the timed language onto its
action components. -/
theorem untimedLang_eq_image (T : TLTS Proc Act) (s : Proc) :
    T.untimedLang s = (List.map Prod.snd) '' T.timedLang s := by
  ext u
  simp only [untimedLang, UntimedTrace, Set.mem_setOf_eq, Set.mem_image]

/-- **Theorem 11.1** (§11.1). Timed-language equivalence implies untimed-language
equivalence: forgetting the time-stamps is a function of the timed language. -/
theorem timedLang_eq_untimedLang_eq {T₁ T₂ : TLTS Proc Act} {s₁ s₂ : Proc}
    (h : T₁.timedLang s₁ = T₂.timedLang s₂) : T₁.untimedLang s₁ = T₂.untimedLang s₂ := by
  rw [untimedLang_eq_image, untimedLang_eq_image, h]

end TLTS

end DeepWiki.ReactiveSystems
