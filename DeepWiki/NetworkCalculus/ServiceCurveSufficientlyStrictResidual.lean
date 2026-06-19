import DeepWiki.NetworkCalculus.ServiceCurveSufficientlyStrict
import DeepWiki.NetworkCalculus.ClosuresNd

/-! # Blind-multiplexing residual for sufficiently-strict service
When a server offers s3c service `β` to the *aggregate* of two flows and flow 2 is `α₂`-constrained,
flow 1 is guaranteed the residual `(β − α₂)↑` (the non-decreasing closure, `ndClosure`). The closure
form — and dropping the per-window domination hypothesis of `IsSufficientlyStrict.residual_flow1_of_dom`
— needs the *windowed* (continuous-backlog / maximum-achievable-dwell) reading of s3c: across each
dwell window the aggregate provides `β s` at **every** prefix `s ≤ dw t`, not only at `s = dw t`. The
closure is then bounded prefix-by-prefix via `flow1_add_le_at` and `A₁`-monotonicity, taking the
supremum with `ciSup_le`. -/

namespace DeepWiki

open scoped NNReal

/-- **Blind-multiplexing residual** (s3c, non-decreasing-closure form). Suppose across each dwell
window the aggregate `(A₁+A₂, D₁+D₂)` provides `β` at *every* prefix `s ≤ dw t`
(`(A₁+A₂)(t-s) + β s ≤ (D₁+D₂) t`, the continuous-backlog reading of s3c), `A₁` is non-decreasing,
flow 1 is causal, flow 2 is causal and `α₂`-constrained, and `α₂ s ≤ β s` over the windows. Then
flow 1 is sufficiently strict for the residual `(β − α₂)↑` (`ndClosure (β − α₂)`) with the same
dwell `dw`. -/
theorem isSufficientlyStrict_ndClosure_residual_of_windowed
    {β α₂ A₁ A₂ D₁ D₂ dw : ℝ≥0 → ℝ≥0}
    (hA1mono : Monotone A₁) (hdwle : ∀ t, dw t ≤ t)
    (hcausal1 : ∀ t, D₁ t ≤ A₁ t) (hcausal2 : ∀ t, D₂ t ≤ A₂ t)
    (hwin : ∀ t s, s ≤ dw t → (A₁ + A₂) (t - s) + β s ≤ (D₁ + D₂) t)
    (harr2 : ∀ s t, s ≤ t → A₂ t ≤ A₂ s + α₂ (t - s))
    (hdom : ∀ t s, s ≤ dw t → α₂ s ≤ β s) :
    IsSufficientlyStrict (ndClosure (fun s => β s - α₂ s)) dw A₁ D₁ := by
  refine ⟨hcausal1, hdwle, fun t => ?_⟩
  -- per-prefix bound: across the window, flow 1's residual at the *outer* dwell is dominated
  have hper : ∀ s : ℝ≥0, s ≤ dw t → A₁ (t - dw t) + (β s - α₂ s) ≤ D₁ t := by
    intro s hs
    have hst : s ≤ t := hs.trans (hdwle t)
    have hadd : A₁ (t - s) + β s ≤ D₁ t + α₂ s :=
      flow1_add_le_at hcausal2 harr2 hst (hwin t s hs)
    have hfs : A₁ (t - s) + (β s - α₂ s) ≤ D₁ t := by
      rw [← add_tsub_assoc_of_le (hdom t s hs), tsub_le_iff_right]; exact hadd
    calc A₁ (t - dw t) + (β s - α₂ s)
        ≤ A₁ (t - s) + (β s - α₂ s) := by gcongr; exact hA1mono (tsub_le_tsub_left hs t)
      _ ≤ D₁ t := hfs
  have hA1D1 : A₁ (t - dw t) ≤ D₁ t := le_trans le_self_add (hper 0 zero_le)
  have hclose : ndClosure (fun s => β s - α₂ s) (dw t) ≤ D₁ t - A₁ (t - dw t) := by
    apply ciSup_le
    intro s
    exact le_tsub_of_add_le_left (hper s.1 s.2)
  calc A₁ (t - dw t) + ndClosure (fun s => β s - α₂ s) (dw t)
      ≤ A₁ (t - dw t) + (D₁ t - A₁ (t - dw t)) := by gcongr
    _ = D₁ t := add_tsub_cancel_of_le hA1D1

end DeepWiki
