import Book.ServersControlTandem
import Book.Closures

/-! # Feedback control
A feedback loop around a server: the arrival at the server is synchronized
with the fed-back departures, `A' = A ⊓ D'`, the server gives
`D ≥ A' ∗ β`, and the feedback filter gives `D' ≥ D ∗ βc`. The loop
inequality `A' ≥ A ⊓ A' ∗ (β ∗ βc)` resolves through the star bound
(`minConv_subadditiveClosureENN_le_of_inf_le`) to `A' ≥ A ∗ (β ∗ βc)⋆`,
the closed-loop service curve `D ≥ A ∗ β ∗ (βc ∗ β)⋆` — under the
well-posedness hypothesis that one turn of the loop costs at least
`c > 0`: for `(β ∗ βc) 0 = 0` the starved trajectory `A' = D = D' = 0`
meets every loop constraint and defeats the bound. The feedback design
constraint `βref ≤ β ∗ (βc ∗ β)⋆` is equivalent to the power constraints
`∀ n, βref ⊘ βⁿ⁺¹ ≤ βcⁿ`, all met by any controller above the quadratic
deconvolution `β ⊘ β²`. The window controller instantiates this design in
`ServersControlFeedbackWindow`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

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
conversely, the power constraints already make `βc` admissible. The
quadratic deconvolution gives them all: if `βc ≥ β ⊘ β²` then
`∀ n ∈ ℕ, βcⁿ ≥ β ⊘ βⁿ⁺¹`. -/
example {β βref βc : ℝ≥0 → ℝ≥0∞}
    (h : βref ≤ minConv β (subadditiveClosureENN (minConv βc β))) :
    ∀ n : ℕ, minDeconv βref (minConvPow β (n + 1)) ≤ minConvPow βc n :=
  mem_feedbackControlSet_iff.mp h

example {β βref βc : ℝ≥0 → ℝ≥0∞}
    (h : ∀ n : ℕ, minDeconv βref (minConvPow β (n + 1)) ≤ minConvPow βc n) :
    βref ≤ minConv β (subadditiveClosureENN (minConv βc β)) :=
  mem_feedbackControlSet_iff.mpr h

example {β βc : ℝ≥0 → ℝ≥0∞} (h : minDeconv β (minConvPow β 2) ≤ βc) :
    ∀ n : ℕ, minDeconv β (minConvPow β (n + 1)) ≤ minConvPow βc n :=
  mem_feedbackControlSet_iff.mp
    (mem_feedbackControlSet_self_of_minDeconv_le h)

end DeepWiki
