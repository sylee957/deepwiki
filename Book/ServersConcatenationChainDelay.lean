import Book.ServersResidualSfa
import Book.DeviationsCompositionChain

/-! # Delay through a server-concatenation chain (pay bursts only once)
Bridges the two halves of the pay-bursts-only-once tightness picture. The end-to-end
service curve of a server chain (SFA/GFA's `concatConv`, an `EReal`
convolution fold) read in the `ℝ≥0∞` delay world via `toENN` is exactly
the unit-free convolution chain `minConvChain` of the per-server readings
(`toENN_concatConv`). Feeding that into the n-server pay-bursts-only-once
bound (`hDev_minConvChain_le_pbooSum`) shows the horizontal deviation of a
flow through the concatenated service curve is at most the
deconvolution-propagated per-hop deviation sum
(`hDev_toENN_concatConv_le`): convolving the per-server curves and bounding
the delay once never loses to summing the per-hop delays (the TOA route). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The `ℝ≥0∞` reading of a nonempty server-concatenation service curve is
the convolution chain of the per-server readings:
`toENN (β^(h) ∗ β^(h₁) ∗ ⋯) = minConvChain (toENN β^(h)) [toENN β^(h₁), …]`.
-/
theorem toENN_concatConv {κ : Type*} {β : κ → ℝ≥0 → EReal}
    (hnn : ∀ k, IsNonneg (β k)) (h : κ) (hs : List κ) :
    Deviation.toENN (concatConv β (h :: hs))
      = minConvChain (Deviation.toENN (β h))
          (hs.map (fun k => Deviation.toENN (β k))) := by
  induction hs generalizing h with
  | nil =>
    rw [concatConv_singleton β h (hnn h).isBddBelowReal, List.map_nil,
      minConvChain_nil]
  | cons g rest ih =>
    rw [concatConv_cons,
      Deviation.toENN_minConv (hnn h) (isNonneg_concatConv hnn (g :: rest)),
      List.map_cons, minConvChain_cons, ih g]

/-- **Pay bursts only once through a server chain**: a flow with monotone
arrival curve `α` crossing a chain of servers offering nonnegative,
monotone min-plus service curves `β^(h)` has its horizontal deviation
through the end-to-end convolution `concatConv β (h :: hs)` bounded by the
deconvolution-propagated per-hop deviation sum
`pbooSum α ((h :: hs).map (toENN ∘ β))`. The convolved-then-bounded delay
never exceeds the summed per-hop delays — the burst is paid once. -/
theorem hDev_toENN_concatConv_le {κ : Type*} {α : ℝ≥0 → ℝ≥0∞}
    (hαmono : Monotone α) {β : κ → ℝ≥0 → EReal}
    (hnn : ∀ k, IsNonneg (β k)) (hβmono : ∀ k, Monotone (β k))
    (h : κ) (hs : List κ) :
    hDev α (Deviation.toENN (concatConv β (h :: hs)))
      ≤ pbooSum α ((h :: hs).map (fun k => Deviation.toENN (β k))) := by
  rw [toENN_concatConv hnn h hs, List.map_cons]
  refine hDev_minConvChain_le_pbooSum hαmono
    (Deviation.monotone_toENN (hβmono h)) ?_
  intro γ hγ
  rw [List.mem_map] at hγ
  obtain ⟨k, _, rfl⟩ := hγ
  exact Deviation.monotone_toENN (hβmono k)

/-! ## Book restatement (delay of the concatenated service curve)
The end-to-end service curve assembled by SFA/GFA along a path of servers,
`β̃ = ∗_{h∈path} β^(h)` (the `EReal` `concatConv`), read as a delay bound
via `toENN`, obeys the pay-bursts-only-once inequality: for a flow with
arrival curve `α`, the horizontal deviation `hDev(α, β̃)` is bounded by the
sum of the per-hop deviations against the deconvolution-propagated arrival
curve, `hDev(α, β^(h)) + hDev(α ⊘ β^(h), β^(h₁)) + ⋯`. The global
service-curve delay bound is never worse than the per-hop sum. -/
example {κ : Type*} {α : ℝ≥0 → ℝ≥0∞} (hαmono : Monotone α)
    {β : κ → ℝ≥0 → EReal} (hnn : ∀ k, IsNonneg (β k))
    (hβmono : ∀ k, Monotone (β k)) (h : κ) (hs : List κ) :
    hDev α (Deviation.toENN (concatConv β (h :: hs)))
      ≤ pbooSum α ((h :: hs).map (fun k => Deviation.toENN (β k))) :=
  hDev_toENN_concatConv_le hαmono hnn hβmono h hs

end DeepWiki
