import Mathlib.Data.NNReal.Basic

/-! # Sufficiently-strict service curves (s3c)
The s3c service curve of [SCH 11], introduced to handle non-FIFO flows: a pair
`(A, D)` is sufficiently strict for `β` with a **dwell period** `dw` (the
maximum achievable dwell period, `dw t ≤ t`, refined in the book to
`dw t ≤ t − Start t`) when `D` is causal and the departure dominates the
arrival one dwell earlier plus `β` of the dwell, `A (t − dw t) + β (dw t) ≤ D t`.
The relation here fixes the dwell function `dw`; the book quantifies over a
family of possible dwells. (Theorem 9.8 — the concatenation `s3c(β₂) ∘ s3c(β₁)
⊆ s3c(β₁∗β₂)` via the composed dwell `dw'(t) = dw₂(t) + dw₁(t − dw₂(t))`, and
the blind-multiplexing residual — is the deeper content built on this def.) -/

namespace DeepWiki

open scoped NNReal

/-- **Sufficiently-strict service curve** (s3c): the pair `(A, D)` is s3c for
`β` with dwell period `dw` (with `dw t ≤ t`) when `D` is causal (`D ≤ A`) and at
each time the departure dominates the dwell-shifted arrival plus `β` of the
dwell, `A (t − dw t) + β (dw t) ≤ D t`. -/
def IsSufficientlyStrict (β dw A D : ℝ≥0 → ℝ≥0) : Prop :=
  (∀ t, D t ≤ A t) ∧ (∀ t, dw t ≤ t) ∧ (∀ t, A (t - dw t) + β (dw t) ≤ D t)

/-- The s3c service bound (elimination): the departure dominates the
dwell-shifted arrival plus `β` of the dwell. -/
theorem IsSufficientlyStrict.service_bound {β dw A D : ℝ≥0 → ℝ≥0}
    (h : IsSufficientlyStrict β dw A D) (t : ℝ≥0) :
    A (t - dw t) + β (dw t) ≤ D t := h.2.2 t

/-- The dwell period never exceeds the elapsed time. -/
theorem IsSufficientlyStrict.dwell_le {β dw A D : ℝ≥0 → ℝ≥0}
    (h : IsSufficientlyStrict β dw A D) (t : ℝ≥0) : dw t ≤ t := h.2.1 t

/-- s3c is causal: the departure never exceeds the arrival. -/
theorem IsSufficientlyStrict.causal {β dw A D : ℝ≥0 → ℝ≥0}
    (h : IsSufficientlyStrict β dw A D) (t : ℝ≥0) : D t ≤ A t := h.1 t

/-- s3c is antitone in `β`: a pointwise-smaller service curve is a weaker
requirement, so the same pair satisfies it. -/
theorem IsSufficientlyStrict.mono_beta {β β' dw A D : ℝ≥0 → ℝ≥0}
    (h : IsSufficientlyStrict β dw A D) (hβ : ∀ x, β' x ≤ β x) :
    IsSufficientlyStrict β' dw A D := by
  refine ⟨h.1, h.2.1, fun t => ?_⟩
  calc A (t - dw t) + β' (dw t) ≤ A (t - dw t) + β (dw t) := by gcongr; exact hβ (dw t)
    _ ≤ D t := h.2.2 t

end DeepWiki
