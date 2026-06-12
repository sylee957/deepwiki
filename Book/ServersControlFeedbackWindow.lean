import Book.ServersControlFeedback

/-! # Window flow control
The window controller instantiates the feedback design: `βc = ω_w` keeps
the backlog below the window `w` and gives the closed-loop service curve
`β_wfc = β ∗ (ω_w ∗ β)⋆`; a window above `(β ⊘ β²)(0)` preserves the
server curve, `β_wfc = β`. Distinguishing the data flow from the
acknowledgment flow (service `βack`) refines this to
`β_wfc_ack = β ∗ (ω_w ∗ βack ∗ β)⋆`, preserved by a window above
`(β ⊘ (β² ∗ βack))(0)` — the requirement residuates through the
acknowledgment stage. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## The window controller -/

/-- **Window flow control**: with the window controller `βc = ω_w` and a
positive window `0 < w`, the closed-loop network is guaranteed the
service curve `β_wfc = β ∗ (ω_w ∗ β)⋆`. -/
theorem windowFlowControl_minConv_le
    {A A' D D' β : ℝ≥0 → ℝ≥0∞} {w : ℝ≥0∞} (hw : 0 < w)
    (hA' : ∀ t, A t ⊓ D' t ≤ A' t)
    (hD : ∀ t, minConv A' β t ≤ D t)
    (hD' : ∀ t, minConv D (window w) t ≤ D' t) (t : ℝ≥0) :
    minConv (minConv A β)
      (subadditiveClosureENN (minConv (window w) β)) t ≤ D t := by
  have h := feedback_minConv_le hw (le_minConv_window β w) hA' hD hD' t
  rw [minConv_assoc_enn,
    minConv_comm β (subadditiveClosureENN (minConv (window w) β)),
    ← minConv_assoc_enn, minConv_comm (window w) β]
  exact h

/-! ## A large enough window -/

/-- **A large enough window is admissible for the server curve itself**:
`w ≥ (β ⊘ β²) 0` makes the window controller reach the reference `β`,
i.e. `β_wfc = β ∗ (ω_w ∗ β)⋆ ≥ β`. -/
theorem window_mem_feedbackControlSet_self
    {β : ℝ≥0 → ℝ≥0∞} {w : ℝ≥0∞}
    (hw : minDeconv β (minConvPow β 2) 0 ≤ w) :
    window w ∈ feedbackControlSet β β := by
  refine mem_feedbackControlSet_self_of_minDeconv_le fun t => ?_
  by_cases ht : t = 0
  · rw [ht, window_zero_eq]
    exact hw
  · rw [show window w t = ⊤ from if_neg ht]
    exact le_top

/-- **A large enough window preserves the service curve**: for
`w ≥ (β ⊘ β²) 0` the closed-loop curve is exactly the server curve,
`β_wfc = β ∗ (ω_w ∗ β)⋆ = β` — `≥` from the admissibility of `ω_w`, `≤`
always since `(ω_w ∗ β)⋆ 0 = 0`. -/
theorem minConv_subadditiveClosureENN_window_eq
    {β : ℝ≥0 → ℝ≥0∞} {w : ℝ≥0∞}
    (hw : minDeconv β (minConvPow β 2) 0 ≤ w) :
    minConv β (subadditiveClosureENN (minConv (window w) β)) = β :=
  le_antisymm (fun t => minConv_subadditiveClosureENN_le β _ t)
    (window_mem_feedbackControlSet_self hw)

/-! ## Book restatement (window flow control)
Window flow control ensures the backlog never exceeds `w`: when the
feedback filter is exactly the window — `D' ≤ D ∗ ω_w` as well — the
synchronized arrival satisfies `A' t ≤ D t + w`. And replacing `βc` by
`ω_w` in the closed-loop bound, the controlled network has min-plus
service curve `β_wfc = β ∗ (ω_w ∗ β)⋆` (with the positive window as the
loop's well-posedness). -/
example {A' D D' : ℝ≥0 → ℝ≥0∞} {w : ℝ≥0∞}
    (hsync : ∀ t, A' t ≤ D' t)
    (hmax : ∀ t, D' t ≤ minConv D (window w) t) (t : ℝ≥0) :
    A' t ≤ D t + w :=
  le_trans (hsync t)
    (le_trans (hmax t) (congrFun (conv_window D w) t).le)

/-! The window loop curve is the raised service curve of the backlog
requirement: `ω_w ∗ β = β + w`, so `β_wfc = β ∗ (β + w)⋆`. -/
example (β : ℝ≥0 → ℝ≥0∞) (w : ℝ≥0∞) :
    minConv (window w) β = fun s => β s + w := by
  rw [minConv_comm, conv_window]

/-! ## Book restatement (a large enough window)
If `w ≥ (β ⊘ β²)(0)`, then `β_wfc ≥ β` — in which case `β_wfc = β`,
since `(ω_w ∗ β)⋆ 0 = 0` always forces `β_wfc = β ∗ (ω_w ∗ β)⋆ ≤ β`. -/
example {β : ℝ≥0 → ℝ≥0∞} {w : ℝ≥0∞}
    (hw : minDeconv β (minConvPow β 2) 0 ≤ w) :
    β ≤ minConv β (subadditiveClosureENN (minConv (window w) β))
      ∧ minConv β (subadditiveClosureENN (minConv (window w) β)) = β :=
  ⟨window_mem_feedbackControlSet_self hw,
    minConv_subadditiveClosureENN_window_eq hw⟩

/-! ## Window flow control with acknowledgments -/

/-- **Window flow control with acknowledgments**: distinguishing
the data flow (service `β`) from the acknowledgment flow (service `βack`),
the loop equations `A' ≥ A ⊓ (D ∗ βack ∗ ω_w)` and `D ≥ A' ∗ β` give, for
a positive window, the closed-loop bound
`D ≥ (A ∗ β) ∗ (ω_w ∗ βack ∗ β)⋆` — the service curve
`β_wfc_ack = β ∗ (ω_w ∗ βack ∗ β)⋆`. -/
theorem windowAckFlowControl_minConv_le
    {A A' D β βack : ℝ≥0 → ℝ≥0∞} {w : ℝ≥0∞} (hw : 0 < w)
    (hA' : ∀ t, A t ⊓ minConv (minConv D βack) (window w) t ≤ A' t)
    (hD : ∀ t, minConv A' β t ≤ D t) (t : ℝ≥0) :
    minConv (minConv A β)
      (subadditiveClosureENN
        (minConv (minConv (window w) βack) β)) t ≤ D t := by
  -- the two feedback stages compose into the controller `βack ∗ ω_w`
  have hD' : ∀ u, minConv D (minConv βack (window w)) u
      ≤ minConv (minConv D βack) (window w) u := by
    intro u
    rw [← minConv_assoc_enn]
  -- the loop still ends in the window, so each turn costs `w`
  have hlb : ∀ s, w ≤ minConv β (minConv βack (window w)) s := by
    intro s
    rw [← minConv_assoc_enn]
    exact le_minConv_window (minConv β βack) w s
  have h := feedback_minConv_le hw hlb hA' hD hD' t
  rw [minConv_comm (minConv (window w) βack) β, minConv_comm (window w) βack,
    minConv_assoc_enn,
    minConv_comm β (subadditiveClosureENN
      (minConv β (minConv βack (window w)))),
    ← minConv_assoc_enn]
  exact h

/-- **A large enough acknowledged window reaches the server curve**: if
`w ≥ (β ⊘ (β² ∗ βack)) 0`, the two-stage controller `ω_w ∗ βack` dominates
`β ⊘ β²` — the requirement residuates through the acknowledgment stage —
so it is admissible for the reference `β` itself:
`β_wfc_ack = β ∗ (ω_w ∗ βack ∗ β)⋆ ≥ β`. -/
theorem windowAck_mem_feedbackControlSet_self
    {β βack : ℝ≥0 → ℝ≥0∞} {w : ℝ≥0∞}
    (hw : minDeconv β (minConv (minConvPow β 2) βack) 0 ≤ w) :
    minConv (window w) βack ∈ feedbackControlSet β β := by
  refine mem_feedbackControlSet_self_of_minDeconv_le ?_
  rw [← minDeconv_le_iff_le_minConv, minDeconv_minDeconv]
  intro t
  by_cases ht : t = 0
  · rw [ht, window_zero_eq]
    exact hw
  · rw [show window w t = ⊤ from if_neg ht]
    exact le_top

/-- **A large enough acknowledged window preserves the service curve**:
`β_wfc_ack = β ∗ (ω_w ∗ βack ∗ β)⋆ = β` (the `≤` holds always, the
closure vanishing at the origin). -/
theorem minConv_subadditiveClosureENN_windowAck_eq
    {β βack : ℝ≥0 → ℝ≥0∞} {w : ℝ≥0∞}
    (hw : minDeconv β (minConv (minConvPow β 2) βack) 0 ≤ w) :
    minConv β (subadditiveClosureENN
      (minConv (minConv (window w) βack) β)) = β :=
  le_antisymm (fun t => minConv_subadditiveClosureENN_le β _ t)
    (windowAck_mem_feedbackControlSet_self hw)

/-! ## Book restatement (window flow control with acknowledgments)
The acknowledgments require considerably less bandwidth than the data, so
sizing the window against `βack` profits from it: the closed-loop network
of the equations `A' ≥ A ∧ (D ∗ βack ∗ ω_w)`, `D ≥ A' ∗ β` has service
curve `β_wfc_ack = β ∗ (ω_w ∗ βack ∗ β)⋆` ([6.4]); and if
`w ≥ (β ⊘ (β² ∗ βack))(0)`, then the large enough acknowledged window
reaches the server curve, `β_wfc_ack ≥ β`: the
controller `ω_w ∗ βack` must satisfy `ω_w ∗ βack ≥ β ⊘ β²`, which is
equivalent to `ω_w ≥ (β ⊘ β²) ⊘ βack = β ⊘ (β² ∗ βack)`. -/
example {β βack : ℝ≥0 → ℝ≥0∞} {w : ℝ≥0∞}
    (hw : minDeconv β (minConv (minConvPow β 2) βack) 0 ≤ w) :
    β ≤ minConv β (subadditiveClosureENN
      (minConv (minConv (window w) βack) β)) :=
  windowAck_mem_feedbackControlSet_self hw

/-! The two spellings of the window bound agree — the deconvolutions
compose: `(β ⊘ β²) ⊘ βack = β ⊘ (β² ∗ βack)`. -/
example (β βack : ℝ≥0 → ℝ≥0∞) :
    minDeconv (minDeconv β (minConvPow β 2)) βack
      = minDeconv β (minConv (minConvPow β 2) βack) :=
  minDeconv_minDeconv β (minConvPow β 2) βack

/-! The book prints the bound as `(β ⊘ β) ⊘ (βack ∗ β) (0)`: same curve,
since `β ⊘ (β ∗ (βack ∗ β)) = β ⊘ (β² ∗ βack)`. -/
example (β βack : ℝ≥0 → ℝ≥0∞) :
    minDeconv (minDeconv β β) (minConv βack β)
      = minDeconv β (minConv (minConvPow β 2) βack) := by
  rw [minDeconv_minDeconv, minConv_comm βack β, ← minConv_assoc_enn,
    show minConv β β = minConvPow β 2 from by
      rw [show minConvPow β 2 = minConv (minConvPow β 1) β from rfl,
        minConvPow_one]]

/-! ## Minimal and maximal service curves -/

/-- **Window flow control with a maximal service curve**: the upper-side
loop equations `A' ≤ A ⊓ (D ∗ βᴹack ∗ ω_w)` and `D ≤ A' ∗ βᴹ` bound the
output above through the loop star,
`D ≤ (A ∗ βᴹ) ∗ (ω_w ∗ βᴹack ∗ βᴹ)⋆` — unconditionally: the unrolling
induction only discards minimum components. -/
theorem windowAckFlowControl_le_minConv
    {A A' D βM βMack : ℝ≥0 → ℝ≥0∞} {w : ℝ≥0∞}
    (hA' : ∀ t, A' t ≤ A t ⊓ minConv (minConv D βMack) (window w) t)
    (hD : ∀ t, D t ≤ minConv A' βM t) (t : ℝ≥0) :
    D t ≤ minConv (minConv A βM)
      (subadditiveClosureENN
        (minConv (minConv (window w) βMack) βM)) t := by
  have h := feedback_le_minConv
    (D' := fun u => minConv (minConv D βMack) (window w) u)
    hA' hD (fun u => by rw [← minConv_assoc_enn]) t
  rw [minConv_comm (window w) βMack]
  exact h

/-! ## Book restatement (minimal and maximal service curves)
With maximal service curves `βᴹ` for the data and `βᴹack` for the
acknowledgments (`βᴹ ≥ β`, `βᴹack ≥ βack` — not needed for either bound),
the network equations
`A ∧ (D ∗ βack ∗ ω_w) ≤ A' ≤ A ∧ (D ∗ βᴹack ∗ ω_w)` and
`A' ∗ β ≤ D ≤ A' ∗ βᴹ` give the global service curves: at least
`β ∗ (ω_w ∗ βack ∗ β)⋆` as before, and — by the unrolling induction,
with no well-posedness — at most `A ∗ βᴹ ∗ (βᴹ ∗ ω_w ∗ βᴹack)⋆` (the
book's factor order; commutativity gives the statement's
`(ω_w ∗ βᴹack ∗ βᴹ)⋆`). -/
example {A A' D β βM βack βMack : ℝ≥0 → ℝ≥0∞} {w : ℝ≥0∞} (hw : 0 < w)
    (hA'l : ∀ t, A t ⊓ minConv (minConv D βack) (window w) t ≤ A' t)
    (hA'u : ∀ t, A' t ≤ A t ⊓ minConv (minConv D βMack) (window w) t)
    (hDl : ∀ t, minConv A' β t ≤ D t)
    (hDu : ∀ t, D t ≤ minConv A' βM t) (t : ℝ≥0) :
    minConv (minConv A β)
        (subadditiveClosureENN (minConv (minConv (window w) βack) β)) t
        ≤ D t
      ∧ D t ≤ minConv (minConv A βM)
        (subadditiveClosureENN
          (minConv (minConv (window w) βMack) βM)) t :=
  ⟨windowAckFlowControl_minConv_le hw hA'l hDl t,
    windowAckFlowControl_le_minConv hA'u hDu t⟩

/-! The window size that does not damage the service: above both
quadratic-deconvolution bounds,
`w ≥ max((β ⊘ β) ⊘ (βack ∗ β)(0), (βᴹ ⊘ βᴹ) ⊘ (βᴹack ∗ βᴹ)(0))`, both
closed-loop curves collapse — the loop preserves `β` and `βᴹ`
simultaneously (each side an instance of the acknowledged-window
equality). The book prints the preceding "it remains to compute"
sentence with the two inequality directions swapped: the unconditional
side is `β ∗ (loop)⋆ ≤ β`, and the window buys `≥`. -/
example {β βack βM βMack : ℝ≥0 → ℝ≥0∞} {w : ℝ≥0∞}
    (hw : max (minDeconv β (minConv (minConvPow β 2) βack) 0)
        (minDeconv βM (minConv (minConvPow βM 2) βMack) 0) ≤ w) :
    minConv β (subadditiveClosureENN
        (minConv (minConv (window w) βack) β)) = β
      ∧ minConv βM (subadditiveClosureENN
        (minConv (minConv (window w) βMack) βM)) = βM :=
  ⟨minConv_subadditiveClosureENN_windowAck_eq ((le_max_left _ _).trans hw),
    minConv_subadditiveClosureENN_windowAck_eq
      ((le_max_right _ _).trans hw)⟩

end DeepWiki
