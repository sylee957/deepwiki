import Book.ServersControlTandem
import Book.Closures

/-! # Feedback control
A feedback loop around a server: the arrival at the server is synchronized
with the fed-back departures, `A' = A ⊓ D'`, the server gives
`D ≥ A' ∗ β`, and the feedback filter gives `D' ≥ D ∗ βc`. The loop
inequality `A' ≥ A ⊓ A' ∗ (β ∗ βc)` resolves through the star bound to
`A' ≥ A ∗ (β ∗ βc)⋆`, the closed-loop service curve
`D ≥ A ∗ β ∗ (βc ∗ β)⋆` — under the well-posedness hypothesis that one
turn of the loop costs at least `c > 0`: for `(β ∗ βc) 0 = 0` the starved
trajectory `A' = D = D' = 0` meets every loop constraint and defeats the
bound. The feedback design constraint `βref ≤ β ∗ (βc ∗ β)⋆` is
equivalent to the power constraints `∀ n, βref ⊘ βⁿ⁺¹ ≤ βcⁿ`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## The star bound -/

/-- **The star bound for feedback loops**: a curve dominating `a ⊓ (x ∗ w)`
with `w` uniformly positive (`0 < c ≤ w`) dominates `a ∗ w⋆`. Each
unrolling of the loop adds `c` to the discarded branch, which escapes to
`⊤`. -/
theorem minConv_subadditiveClosureENN_le_of_inf_le
    {x a w : ℝ≥0 → ℝ≥0∞} {c : ℝ≥0∞} (hc : 0 < c) (hlb : ∀ s, c ≤ w s)
    (hx : ∀ t, a t ⊓ minConv x w t ≤ x t) (t : ℝ≥0) :
    minConv a (subadditiveClosureENN w) t ≤ x t := by
  -- the bound holds up to the escaping loop cost `n • c`
  have key : ∀ n : ℕ, ∀ u : ℝ≥0,
      minConv a (subadditiveClosureENN w) u ⊓ n • c ≤ x u := by
    intro n
    induction n with
    | zero =>
        intro u
        rw [zero_smul]
        exact inf_le_right.trans zero_le'
    | succ n ih =>
        intro u
        refine le_trans (le_inf ?_ ?_) (hx u)
        · -- the arrival branch: `a ∗ w⋆ ≤ a` since `w⋆ 0 = 0`
          exact inf_le_left.trans (minConv_subadditiveClosureENN_le a w u)
        · -- the loop branch spends one `c` per turn
          refine le_minConv fun p q hpq => ?_
          have hXshift : minConv a (subadditiveClosureENN w) u
              ≤ minConv a (subadditiveClosureENN w) p + w q := by
            rw [← hpq]
            refine le_trans (minConv_apply_add_le_of_isSubadditive
              (subadditiveClosureENN_subadditive w) p q) ?_
            exact add_le_add_right (subadditiveClosureENN_le w q) _
          have hcc : (n + 1) • c ≤ n • c + w q := by
            rw [succ_nsmul]
            exact add_le_add_right (hlb q) _
          rcases le_total (minConv a (subadditiveClosureENN w) p) (n • c)
            with hpc | hpc
          · exact le_trans inf_le_left (hXshift.trans
              (add_le_add_left (le_trans (le_inf le_rfl hpc) (ih p)) _))
          · exact le_trans inf_le_right (hcc.trans
              (add_le_add_left (le_trans (le_inf hpc le_rfl) (ih p)) _))
  -- let the loop cost escape
  rcases eq_or_ne c ⊤ with rfl | hctop
  · have h1 := key 1 t
    rwa [one_nsmul, inf_top_eq] at h1
  rcases eq_or_ne (x t) ⊤ with hxt | hxt
  · rw [hxt]
    exact le_top
  obtain ⟨n, hn⟩ : ∃ n : ℕ, x t < n • c := by
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt
      (ENNReal.div_lt_top hxt hc.ne').ne
    refine ⟨n, ?_⟩
    rw [nsmul_eq_mul]
    rwa [ENNReal.div_lt_iff (Or.inl hc.ne') (Or.inl hctop)] at hn
  have hkey := key n t
  rcases le_total (minConv a (subadditiveClosureENN w) t) (n • c) with hle | hle
  · rwa [inf_eq_left.mpr hle] at hkey
  · rw [inf_eq_right.mpr hle] at hkey
    exact absurd hkey (not_le.mpr hn)

/-! ## The closed-loop service curve -/

/-- **The closed-loop service curve**: with synchronization `A' ≥ A ⊓ D'`,
server `D ≥ A' ∗ β` and feedback filter `D' ≥ D ∗ βc`, a well-posed loop
(`0 < c ≤ β ∗ βc`) guarantees `D ≥ (A ∗ (β ∗ βc)⋆) ∗ β`. -/
theorem feedback_minConv_le {A A' D D' β βc : ℝ≥0 → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : 0 < c) (hlb : ∀ s, c ≤ minConv β βc s)
    (hA' : ∀ t, A t ⊓ D' t ≤ A' t)
    (hD : ∀ t, minConv A' β t ≤ D t)
    (hD' : ∀ t, minConv D βc t ≤ D' t) (t : ℝ≥0) :
    minConv (minConv A (subadditiveClosureENN (minConv β βc))) β t ≤ D t := by
  -- the synchronized arrival absorbs the loop
  have hx : ∀ u, A u ⊓ minConv A' (minConv β βc) u ≤ A' u := by
    intro u
    refine le_trans (inf_le_inf le_rfl ?_) (hA' u)
    calc minConv A' (minConv β βc) u
        = minConv (minConv A' β) βc u := by rw [minConv_assoc_enn]
      _ ≤ minConv D βc u :=
          minConv_le_minConv (fun s => hD s) (fun _ => le_rfl) u
      _ ≤ D' u := hD' u
  calc minConv (minConv A (subadditiveClosureENN (minConv β βc))) β t
      ≤ minConv A' β t :=
        minConv_le_minConv
          (fun s => minConv_subadditiveClosureENN_le_of_inf_le hc hlb hx s)
          (fun _ => le_rfl) t
    _ ≤ D t := hD t

/-! ## The feedback design constraint -/

/-- The admissible feedback controllers for a server curve `β` and a
reference `βref`: those `βc` whose closed-loop guarantee dominates the
reference, `βref ≤ β ∗ (βc ∗ β)⋆`. -/
def feedbackControlSet (β βref : ℝ≥0 → ℝ≥0∞) : Set (ℝ≥0 → ℝ≥0∞) :=
  {βc | βref ≤ minConv β (subadditiveClosureENN (minConv βc β))}

/-- **Feedback control**: `βc` is an admissible feedback controller iff
its convolution powers dominate the shifted deconvolutions,
`∀ n, βref ⊘ βⁿ⁺¹ ≤ βcⁿ` — residuation and the associativity of the
convolution. -/
theorem mem_feedbackControlSet_iff {β βref βc : ℝ≥0 → ℝ≥0∞} :
    βc ∈ feedbackControlSet β βref
      ↔ ∀ n : ℕ, minDeconv βref (minConvPow β (n + 1)) ≤ minConvPow βc n := by
  show βref ≤ minConv β (subadditiveClosureENN (minConv βc β)) ↔ _
  rw [minConv_comm β, ← minDeconv_le_iff_le_minConv,
    le_subadditiveClosureENN_iff]
  refine forall_congr' fun n => ?_
  rw [minConvPow_minConv, ← minDeconv_le_iff_le_minConv,
    minDeconv_minDeconv, minConv_comm β (minConvPow β n), ← minConvPow_succ]

/-! ## Window flow control -/

/-- The loop cost of the window controller is the window itself:
`w ≤ (β ∗ ω_w) s` — one turn around the feedback always pays `w`. -/
theorem le_minConv_window (β : ℝ≥0 → ℝ≥0∞) (w : ℝ≥0∞) (s : ℝ≥0) :
    w ≤ minConv β (window w) s := by
  rw [conv_window]
  exact le_add_self

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

/-- **The quadratic deconvolution controls the loop**: a controller above
`β ⊘ β²` meets every power constraint `βcⁿ ≥ β ⊘ βⁿ⁺¹`, hence is
admissible for the reference `β` itself. Inductively, `β ≤ βcⁿ⁻¹ ∗ βⁿ`
and `β ≤ βc ∗ β²` give `β ≤ βcⁿ ∗ βⁿ⁺¹` by isotony and reshuffling. -/
theorem mem_feedbackControlSet_self_of_minDeconv_le
    {β βc : ℝ≥0 → ℝ≥0∞} (h : minDeconv β (minConvPow β 2) ≤ βc) :
    βc ∈ feedbackControlSet β β := by
  rw [mem_feedbackControlSet_iff]
  have h2 : minConvPow β 2 = minConv β β := by
    have hs : minConvPow β 2 = minConv (minConvPow β 1) β := rfl
    rw [hs, minConvPow_one]
  have hres : β ≤ minConv βc (minConv β β) := by
    have hr := minDeconv_le_iff_le_minConv.mp h
    rwa [h2] at hr
  -- residuated form of the power constraints
  have aux : ∀ n : ℕ, β ≤ minConv (minConvPow βc n) (minConvPow β (n + 1)) := by
    intro n
    induction n with
    | zero =>
        intro t
        rw [minConvPow_one]
        refine le_minConv fun u v huv => ?_
        rw [minConvPow_zero]
        by_cases hu : u = 0
        · rw [if_pos hu, zero_add]
          rw [hu, zero_add] at huv
          rw [huv]
        · rw [if_neg hu, top_add]
          exact le_top
    | succ n ih =>
        calc β ≤ minConv (minConvPow βc n) (minConvPow β (n + 1)) := ih
          _ = minConv (minConvPow βc n)
                (minConv (minConvPow β n) β) := by rw [minConvPow_succ]
          _ ≤ minConv (minConvPow βc n) (minConv (minConvPow β n)
                (minConv βc (minConv β β))) := fun t =>
              minConv_le_minConv (fun _ => le_rfl)
                (fun s => minConv_le_minConv (fun _ => le_rfl)
                  (fun r => hres r) s) t
          _ = minConv (minConv (minConvPow βc n) βc)
                (minConv (minConv (minConvPow β n) β) β) := by
              rw [← minConv_assoc_enn (minConvPow β n) βc (minConv β β),
                minConv_comm (minConvPow β n) βc,
                minConv_assoc_enn βc (minConvPow β n) (minConv β β),
                ← minConv_assoc_enn (minConvPow βc n) βc
                  (minConv (minConvPow β n) (minConv β β)),
                ← minConv_assoc_enn (minConvPow β n) β β]
          _ = minConv (minConvPow βc (n + 1)) (minConvPow β (n + 1 + 1)) := by
              rw [← minConvPow_succ βc n, ← minConvPow_succ β n,
                ← minConvPow_succ β (n + 1)]
  exact fun n => minDeconv_le_iff_le_minConv.mpr (aux n)

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

/-! ## Book restatement (a large enough window)
If `βc ≥ β ⊘ β²` then `∀ n ∈ ℕ, βcⁿ ≥ β ⊘ βⁿ⁺¹`; and if
`w ≥ (β ⊘ β²)(0)`, then `β_wfc ≥ β` — in which case `β_wfc = β`, since
`(ω_w ∗ β)⋆ 0 = 0` always forces `β_wfc = β ∗ (ω_w ∗ β)⋆ ≤ β`. -/
example {β βc : ℝ≥0 → ℝ≥0∞} (h : minDeconv β (minConvPow β 2) ≤ βc) :
    ∀ n : ℕ, minDeconv β (minConvPow β (n + 1)) ≤ minConvPow βc n :=
  mem_feedbackControlSet_iff.mp
    (mem_feedbackControlSet_self_of_minDeconv_le h)

example {β : ℝ≥0 → ℝ≥0∞} {w : ℝ≥0∞}
    (hw : minDeconv β (minConvPow β 2) 0 ≤ w) :
    β ≤ minConv β (subadditiveClosureENN (minConv (window w) β))
      ∧ minConv β (subadditiveClosureENN (minConv (window w) β)) = β :=
  ⟨window_mem_feedbackControlSet_self hw,
    minConv_subadditiveClosureENN_window_eq hw⟩

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

/-! ## Book restatement ([6.3]: the closed-loop service curve)
The closed-loop network obeys `A' = A ∧ D' ≥ A ∧ (D ∗ βc)` and
`D ≥ A' ∗ β`; as a result `A' ≥ A ∧ A' ∗ (β ∗ βc)`, hence
`A' ≥ A ∗ (β ∗ βc)⋆` and `D ≥ A ∗ β ∗ (βc ∗ β)⋆` — the service curve of
the closed-loop network is `β ∗ (βc ∗ β)⋆`. (Stated with the loop cost
`0 < c ≤ β ∗ βc`, which the book leaves implicit: without it the starved
trajectory `A' = D = D' = 0` satisfies every constraint and refutes the
bound.) -/
example {A A' D D' β βc : ℝ≥0 → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : 0 < c) (hlb : ∀ s, c ≤ minConv β βc s)
    (hA' : ∀ t, A t ⊓ D' t ≤ A' t)
    (hD : ∀ t, minConv A' β t ≤ D t)
    (hD' : ∀ t, minConv D βc t ≤ D' t) (t : ℝ≥0) :
    minConv (minConv A β) (subadditiveClosureENN (minConv βc β)) t ≤ D t := by
  have h := feedback_minConv_le hc hlb hA' hD hD' t
  rw [minConv_assoc_enn,
    minConv_comm β (subadditiveClosureENN (minConv βc β)),
    ← minConv_assoc_enn, minConv_comm βc β]
  exact h

/-! ## Book restatement (feedback control design)
Let `βref` be the min-plus service curve that the controlled network has
to reach. The smallest service curve `βc` such that
`β ∗ (βc ∗ β)⋆ ≥ βref` must satisfy `∀ n ∈ ℕ, βcⁿ ≥ βref ⊘ βⁿ⁺¹` — and
conversely, the power constraints already make `βc` admissible. -/
example {β βref βc : ℝ≥0 → ℝ≥0∞}
    (h : βref ≤ minConv β (subadditiveClosureENN (minConv βc β))) :
    ∀ n : ℕ, minDeconv βref (minConvPow β (n + 1)) ≤ minConvPow βc n :=
  mem_feedbackControlSet_iff.mp h

example {β βref βc : ℝ≥0 → ℝ≥0∞}
    (h : ∀ n : ℕ, minDeconv βref (minConvPow β (n + 1)) ≤ minConvPow βc n) :
    βref ≤ minConv β (subadditiveClosureENN (minConv βc β)) :=
  mem_feedbackControlSet_iff.mpr h

end DeepWiki
