import DeepWiki.NetworkCalculus.FunctionDioids

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

/-- **Blind-multiplexing residual, additive form.** When the aggregate `(A₁+A₂, D₁+D₂)` is s3c
for `β` with dwell `dw`, flow `2` is causal (`D₂ ≤ A₂`) and `α₂`-constrained
(`A₂ t ≤ A₂ s + α₂ (t-s)`), flow `1` satisfies `A₁ (t - dw t) + β (dw t) ≤ D₁ t + α₂ (dw t)` — the
arrival-plus-service of flow `1` over the dwell window is dominated by its departure plus flow `2`'s
burst. (The flow-decomposition core: in `ℝ≥0` this is `(A₁(t-dw)+β(dw)) - α₂(dw) ≤ D₁ t`; turning it
into an s3c bound for `β - α₂` needs `α₂(dw) ≤ β(dw)`, see `residual_flow1_of_dom`.) -/
theorem IsSufficientlyStrict.flow1_add_le {β α₂ A₁ A₂ D₁ D₂ dw : ℝ≥0 → ℝ≥0}
    (hagg : IsSufficientlyStrict β dw (A₁ + A₂) (D₁ + D₂))
    (hcausal2 : ∀ t, D₂ t ≤ A₂ t)
    (harr2 : ∀ s t, s ≤ t → A₂ t ≤ A₂ s + α₂ (t - s)) (t : ℝ≥0) :
    A₁ (t - dw t) + β (dw t) ≤ D₁ t + α₂ (dw t) := by
  have hdw : dw t ≤ t := hagg.dwell_le t
  have hs := hagg.service_bound t
  simp only [Pi.add_apply] at hs
  have ha2 : A₂ t ≤ A₂ (t - dw t) + α₂ (dw t) := by
    have h := harr2 (t - dw t) t tsub_le_self
    rwa [tsub_tsub_cancel_of_le hdw] at h
  have key : (A₁ (t - dw t) + β (dw t)) + A₂ (t - dw t)
      ≤ (D₁ t + α₂ (dw t)) + A₂ (t - dw t) :=
    calc (A₁ (t - dw t) + β (dw t)) + A₂ (t - dw t)
        = A₁ (t - dw t) + A₂ (t - dw t) + β (dw t) := by ring
      _ ≤ D₁ t + D₂ t := hs
      _ ≤ D₁ t + (A₂ (t - dw t) + α₂ (dw t)) := by gcongr; exact (hcausal2 t).trans ha2
      _ = (D₁ t + α₂ (dw t)) + A₂ (t - dw t) := by ring
  exact le_of_add_le_add_right key

/-- **Blind-multiplexing residual for flow 1** (plain difference form). Under the additive bound of
`flow1_add_le` plus `α₂ (dw t) ≤ β (dw t)` (flow `2`'s burst never exceeds the service over the
dwell window), flow `1` is s3c for the residual `β - α₂` with the *same* dwell `dw`. (The book's
result strengthens `β - α₂` to its non-decreasing closure `(β - α₂)↑`, which is *not* obtainable
from a single dwell — that step needs the maximum-achievable-dwell backlog semantics.) -/
theorem IsSufficientlyStrict.residual_flow1_of_dom {β α₂ A₁ A₂ D₁ D₂ dw : ℝ≥0 → ℝ≥0}
    (hagg : IsSufficientlyStrict β dw (A₁ + A₂) (D₁ + D₂))
    (hcausal1 : ∀ t, D₁ t ≤ A₁ t) (hcausal2 : ∀ t, D₂ t ≤ A₂ t)
    (harr2 : ∀ s t, s ≤ t → A₂ t ≤ A₂ s + α₂ (t - s))
    (hdom : ∀ t, α₂ (dw t) ≤ β (dw t)) :
    IsSufficientlyStrict (fun s => β s - α₂ s) dw A₁ D₁ := by
  refine ⟨hcausal1, hagg.dwell_le, fun t => ?_⟩
  show A₁ (t - dw t) + (β (dw t) - α₂ (dw t)) ≤ D₁ t
  rw [← add_tsub_assoc_of_le (hdom t), tsub_le_iff_right]
  exact hagg.flow1_add_le hcausal2 harr2 t

/-- **Theorem 9.8** (s3c concatenation): two s3c servers in tandem — `(A, M)` s3c
for `β₁` with dwell `dw₁`, then `(M, D)` s3c for `β₂` with dwell `dw₂` — compose
to an s3c server `(A, D)` for the convolution `β₁ ∗ β₂` with the **composed dwell**
`dw'(t) = dw₂ t + dw₁ (t − dw₂ t)`. The service part chains the two s3c bounds and
folds the two `β`-increments into the convolution at the split `dw₁(t−dw₂ t) + dw₂ t`. -/
theorem IsSufficientlyStrict.comp {β₁ β₂ dw₁ dw₂ A M D : ℝ≥0 → ℝ≥0}
    (h₁ : IsSufficientlyStrict β₁ dw₁ A M) (h₂ : IsSufficientlyStrict β₂ dw₂ M D) :
    IsSufficientlyStrict (minConv β₁ β₂) (fun t => dw₂ t + dw₁ (t - dw₂ t)) A D := by
  refine ⟨fun t => (h₂.causal t).trans (h₁.causal t), fun t => ?_, fun t => ?_⟩
  · -- the composed dwell never exceeds the elapsed time
    calc dw₂ t + dw₁ (t - dw₂ t) ≤ dw₂ t + (t - dw₂ t) := by gcongr; exact h₁.dwell_le _
      _ = t := add_tsub_cancel_of_le (h₂.dwell_le t)
  · -- the s3c service bound for `β₁ ∗ β₂` at the composed dwell
    have e1 : t - (dw₂ t + dw₁ (t - dw₂ t)) = (t - dw₂ t) - dw₁ (t - dw₂ t) := by
      rw [tsub_tsub]
    have hmc : minConv β₁ β₂ (dw₂ t + dw₁ (t - dw₂ t))
        ≤ β₁ (dw₁ (t - dw₂ t)) + β₂ (dw₂ t) :=
      minConv_le_add β₁ β₂ (add_comm (dw₁ (t - dw₂ t)) (dw₂ t))
    calc A (t - (dw₂ t + dw₁ (t - dw₂ t))) + minConv β₁ β₂ (dw₂ t + dw₁ (t - dw₂ t))
        ≤ A ((t - dw₂ t) - dw₁ (t - dw₂ t)) + (β₁ (dw₁ (t - dw₂ t)) + β₂ (dw₂ t)) := by
          rw [e1]; exact add_le_add le_rfl hmc
      _ = (A ((t - dw₂ t) - dw₁ (t - dw₂ t)) + β₁ (dw₁ (t - dw₂ t))) + β₂ (dw₂ t) := by ring
      _ ≤ M (t - dw₂ t) + β₂ (dw₂ t) := by gcongr; exact h₁.service_bound (t - dw₂ t)
      _ ≤ D t := h₂.service_bound t

-- Restatement (book Thm 9.8): s3c servers concatenate, convolving service curves
-- and composing dwells; the relation-composition `s3c(β₂)∘s3c(β₁) ⊆ s3c(β₁∗β₂)`.
example (β₁ β₂ dw₁ dw₂ A D : ℝ≥0 → ℝ≥0)
    (h : ∃ M, IsSufficientlyStrict β₁ dw₁ A M ∧ IsSufficientlyStrict β₂ dw₂ M D) :
    IsSufficientlyStrict (minConv β₁ β₂) (fun t => dw₂ t + dw₁ (t - dw₂ t)) A D :=
  let ⟨_, h₁, h₂⟩ := h; h₁.comp h₂

/-- The book's s3c service-curve **class** `S_s3c(β, Dw)`: a pair `(A, D)` is s3c for
`β` with *some* dwell drawn from the family `Dw` (the book quantifies over a set of
possible dwell periods, not a single fixed one). -/
def IsSufficientlyStrictFamily (β : ℝ≥0 → ℝ≥0) (Dw : Set (ℝ≥0 → ℝ≥0))
    (A D : ℝ≥0 → ℝ≥0) : Prop :=
  ∃ dw ∈ Dw, IsSufficientlyStrict β dw A D

/-- The composed dwell family for s3c concatenation:
`{t ↦ dw₂ t + dw₁ (t − dw₂ t) | dw₁ ∈ Dw₁, dw₂ ∈ Dw₂}`. -/
def composedDwellFamily (Dw₁ Dw₂ : Set (ℝ≥0 → ℝ≥0)) : Set (ℝ≥0 → ℝ≥0) :=
  {dw | ∃ dw₁ ∈ Dw₁, ∃ dw₂ ∈ Dw₂, dw = fun t => dw₂ t + dw₁ (t - dw₂ t)}

/-- **Theorem 9.8** (s3c concatenation, dwell-family form): the relation composition
`S_s3c(β₂, Dw₂) ∘ S_s3c(β₁, Dw₁) ⊆ S_s3c(β₁ ∗ β₂, Dw')` where `Dw'` is the composed
dwell family — exactly the book's statement over the dwell-period classes. -/
theorem IsSufficientlyStrictFamily.comp {β₁ β₂ : ℝ≥0 → ℝ≥0}
    {Dw₁ Dw₂ : Set (ℝ≥0 → ℝ≥0)} {A M D : ℝ≥0 → ℝ≥0}
    (h₁ : IsSufficientlyStrictFamily β₁ Dw₁ A M)
    (h₂ : IsSufficientlyStrictFamily β₂ Dw₂ M D) :
    IsSufficientlyStrictFamily (minConv β₁ β₂) (composedDwellFamily Dw₁ Dw₂) A D := by
  obtain ⟨dw₁, hdw₁, hs₁⟩ := h₁
  obtain ⟨dw₂, hdw₂, hs₂⟩ := h₂
  exact ⟨_, ⟨dw₁, hdw₁, dw₂, hdw₂, rfl⟩, hs₁.comp hs₂⟩

end DeepWiki
