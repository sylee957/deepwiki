import Book.DeviationsComposition

/-! # Pay bursts only once along a server chain
The two-server pay-burst-only-once bound
(`hDev_minConv_le_add_hDev_minDeconv`) iterated along a path: the
horizontal deviation of a flow through the *convolved* end-to-end service
curve `β₀ ∗ β₁ ∗ ⋯ ∗ βₙ` is at most the sum of the per-hop deviations
taken against the arrival curve propagated by deconvolution at each hop,
`hDev α₀ β₀ + hDev (α₀ ⊘ β₀) β₁ + ⋯`. This is the curve-level statement
of why computing one delay bound from the global service curve (SFA/GFA's
`concatConv`) beats summing per-hop delays (the TOA route): the burst is
paid only once, so the chain bound is no looser than the per-hop sum. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The end-to-end convolution of a nonempty server chain
`β ∗ γ₁ ∗ ⋯ ∗ γₙ` — head `β` convolved with the downstream list, unit-free
(a singleton chain is its head). -/
noncomputable def minConvChain (β : ℝ≥0 → ℝ≥0∞) :
    List (ℝ≥0 → ℝ≥0∞) → ℝ≥0 → ℝ≥0∞
  | [] => β
  | γ :: rest => minConv β (minConvChain γ rest)

/-- `minConvChain β [] = β`: a singleton chain offers its head. -/
@[simp] theorem minConvChain_nil (β : ℝ≥0 → ℝ≥0∞) :
    minConvChain β [] = β := rfl

/-- `minConvChain β (γ :: rest) = β ∗ minConvChain γ rest`. -/
theorem minConvChain_cons (β γ : ℝ≥0 → ℝ≥0∞) (rest : List (ℝ≥0 → ℝ≥0∞)) :
    minConvChain β (γ :: rest) = minConv β (minConvChain γ rest) := rfl

/-- The chain convolution of monotone service curves is monotone. -/
theorem monotone_minConvChain {β : ℝ≥0 → ℝ≥0∞} (hβmono : Monotone β)
    {βs : List (ℝ≥0 → ℝ≥0∞)} (hγmono : ∀ γ ∈ βs, Monotone γ) :
    Monotone (minConvChain β βs) := by
  induction βs generalizing β with
  | nil => exact hβmono
  | cons γ rest ih =>
    rw [minConvChain_cons]
    exact monotone_minConv hβmono
      (ih (hγmono γ (List.mem_cons_self ..))
        (fun x hx => hγmono x (List.mem_cons_of_mem _ hx)))

/-- The pay-bursts-only-once delay sum along a server chain: the per-hop
horizontal deviations with the arrival curve propagated by deconvolution,
`hDev α β + hDev (α ⊘ β) γ₁ + ⋯`. -/
noncomputable def pbooSum (α : ℝ≥0 → ℝ≥0∞) :
    List (ℝ≥0 → ℝ≥0∞) → ℝ≥0∞
  | [] => 0
  | β :: rest => hDev α β + pbooSum (minDeconv α β) rest

/-- `pbooSum α [] = 0`. -/
@[simp] theorem pbooSum_nil (α : ℝ≥0 → ℝ≥0∞) : pbooSum α [] = 0 := rfl

/-- `pbooSum α (β :: rest) = hDev α β + pbooSum (α ⊘ β) rest`. -/
theorem pbooSum_cons (α β : ℝ≥0 → ℝ≥0∞) (rest : List (ℝ≥0 → ℝ≥0∞)) :
    pbooSum α (β :: rest) = hDev α β + pbooSum (minDeconv α β) rest := rfl

/-- **Pay bursts only once along a chain**: the horizontal deviation of a
monotone arrival curve `α` through the end-to-end convolution
`minConvChain β βs = β ∗ β₁ ∗ ⋯ ∗ βₙ` is at most the propagated per-hop
deviation sum `pbooSum α (β :: βs)`. The convolution bound never exceeds
the per-hop sum — the burst is paid once. -/
theorem hDev_minConvChain_le {α : ℝ≥0 → ℝ≥0∞} (hαmono : Monotone α)
    {β : ℝ≥0 → ℝ≥0∞} (hβmono : Monotone β) {βs : List (ℝ≥0 → ℝ≥0∞)}
    (hγmono : ∀ γ ∈ βs, Monotone γ) :
    hDev α (minConvChain β βs) ≤ hDev α β + pbooSum (minDeconv α β) βs := by
  induction βs generalizing α β with
  | nil =>
    rw [minConvChain_nil]
    exact le_self_add
  | cons γ rest ih =>
    rw [minConvChain_cons, pbooSum_cons]
    have hγ : Monotone γ := hγmono γ (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, Monotone x :=
      fun x hx => hγmono x (List.mem_cons_of_mem _ hx)
    calc hDev α (minConv β (minConvChain γ rest))
        ≤ hDev α β + hDev (minDeconv α β) (minConvChain γ rest) :=
          hDev_minConv_le_add_hDev_minDeconv hαmono hβmono
            (monotone_minConvChain hγ hrest)
      _ ≤ hDev α β + (hDev (minDeconv α β) γ
            + pbooSum (minDeconv (minDeconv α β) γ) rest) :=
          add_le_add le_rfl (ih (monotone_minDeconv α β hαmono) hγ hrest)

/-- `pbooSum α (β :: βs)` is exactly `hDev α β + pbooSum (α ⊘ β) βs`, so
the chain bound reads as a single end-to-end deviation of the convolution
dominated by the head deviation plus the propagated tail sum. -/
theorem hDev_minConvChain_le_pbooSum {α : ℝ≥0 → ℝ≥0∞} (hαmono : Monotone α)
    {β : ℝ≥0 → ℝ≥0∞} (hβmono : Monotone β) {βs : List (ℝ≥0 → ℝ≥0∞)}
    (hγmono : ∀ γ ∈ βs, Monotone γ) :
    hDev α (minConvChain β βs) ≤ pbooSum α (β :: βs) := by
  rw [pbooSum_cons]
  exact hDev_minConvChain_le hαmono hβmono hγmono

/-! ## Book restatement (pay bursts only once, n servers)
For a flow with arrival curve `α` crossing a chain of servers with
service curves `β, β₁, …, βₙ`, the end-to-end deviation through the
convolved service curve `β ∗ β₁ ∗ ⋯ ∗ βₙ` is bounded by the sum of the
per-hop deviations, each against the arrival curve propagated by
deconvolution to that hop:
`hDev(α, β ∗ ⋯ ∗ βₙ) ≤ hDev(α, β) + hDev(α ⊘ β, β₁) + ⋯`. Convolving the
service curves first and bounding the delay once is never worse than
summing the per-hop delay bounds — the burst is paid only once. -/
example {α : ℝ≥0 → ℝ≥0∞} (hαmono : Monotone α)
    {β : ℝ≥0 → ℝ≥0∞} (hβmono : Monotone β) {βs : List (ℝ≥0 → ℝ≥0∞)}
    (hγmono : ∀ γ ∈ βs, Monotone γ) :
    hDev α (minConvChain β βs) ≤ pbooSum α (β :: βs) :=
  hDev_minConvChain_le_pbooSum hαmono hβmono hγmono

end DeepWiki
