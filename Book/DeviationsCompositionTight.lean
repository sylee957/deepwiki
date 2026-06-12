import Book.DeviationsComposition
import Book.ServiceCurveMinimal
import Book.ArrivalCurveShaperGreedy

/-! # The worst-case tandem trajectory
For sub-additive `α` and curves `β₁`, `β₂` in `F₀`, the triple `A = α`,
`B = α ⊓ β₁`, `C = α ⊓ (β₁ ∗ β₂)` is an admissible trajectory of the tandem
of min-plus servers that attains `hDev α C = hDev α (β₁ ∗ β₂)`, while its
per-hop deviations stay below `hDev α β₁ + hDev (α ⊘ β₁) β₂` — re-deriving
the pay-burst-only-once comparison through an explicit trajectory. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- Hop 1 of the worst-case tandem trajectory: the greedy source `α` and the
shaped output `α ⊓ β₁` form a min-plus service pair of `β₁`. -/
theorem minimalServicePair_inf {α β₁ : ℝ≥0 → ℝ≥0∞}
    (hα0 : α 0 = 0) (hβ₁0 : β₁ 0 = 0) :
    minimalServicePair β₁ α (α ⊓ β₁) :=
  ⟨inf_le_left,
    le_inf (fun t => minConv_le_left α hβ₁0 t)
      (fun t => minConv_le_right hα0 β₁ t)⟩

/-- Hop 2 of the worst-case tandem trajectory: the shaped output `α ⊓ β₁` and
the end-to-end output `α ⊓ (β₁ ∗ β₂)` form a min-plus service pair of `β₂`. -/
theorem minimalServicePair_inf_minConv {α β₁ β₂ : ℝ≥0 → ℝ≥0∞}
    (hβ₂0 : β₂ 0 = 0) :
    minimalServicePair β₂ (α ⊓ β₁) (α ⊓ minConv β₁ β₂) :=
  ⟨inf_le_inf le_rfl (fun t => minConv_le_left β₁ hβ₂0 t),
    le_inf
      (fun t => le_trans
        (minConv_le_minConv (fun _ => inf_le_left) (fun _ => le_rfl) t)
        (minConv_le_left α hβ₂0 t))
      (fun t => minConv_le_minConv (fun _ => inf_le_right) (fun _ => le_rfl) t)⟩

/-- **Output arrival bound**, `ℝ≥0∞` function form: a served sandwich
`A ∗ β ≤ D ≤ A` with `A` allowing `α` gives `D` allowing the deconvolution
`α ⊘ β`. -/
theorem IsMaximalArrivalBound.output {A D α β : ℝ≥0 → ℝ≥0∞}
    (harr : IsMaximalArrivalBound A α) (hcaus : D ≤ A)
    (hserv : minConv A β ≤ D) :
    IsMaximalArrivalBound D (minDeconv α β) := by
  rw [isMaximalArrivalBound_iff_increment] at harr ⊢
  intro t d
  refine le_trans (hcaus (t + d))
    (le_trans ?_ (add_le_add (hserv t) le_rfl))
  -- `A (t + d) ≤ (A ∗ β) t + (α ⊘ β) d`, split by split
  rw [← tsub_le_iff_right]
  refine le_minConv fun u s hus => ?_
  rw [tsub_le_iff_right]
  calc A (t + d)
      = A (u + (s + d)) := by rw [← add_assoc, hus]
    _ ≤ A u + α (s + d) := harr u (s + d)
    _ ≤ A u + (β s + minDeconv α β d) := by
        refine add_le_add le_rfl (le_trans le_add_tsub (add_le_add le_rfl ?_))
        rw [add_comm s d]
        exact sub_le_minDeconv α β d s
    _ = A u + β s + minDeconv α β d := (add_assoc _ _ _).symm

/-- **Delay bound at the deviation level**: a pair `(B, C)` with nondecreasing
`B` allowing `α` and `C` dominating the convolution `B ∗ β` has
`hDevAt B C t ≤ hDev α β` for nondecreasing `β`. -/
theorem hDevAt_le_hDev_of_minConv_le {B C α β : ℝ≥0 → ℝ≥0∞}
    (hBmono : Monotone B) (hβmono : Monotone β)
    (harr : IsMaximalArrivalBound B α) (hserv : minConv B β ≤ C) (t : ℝ≥0) :
    (hDevAt B C t : ℝ≥0∞) ≤ hDev α β := by
  rw [isMaximalArrivalBound_iff_increment] at harr
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨d, hd1, hd2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hcon
  have hadm : ∀ x, α x ≤ β (x + d) := le_of_hDev_lt hβmono hd1
  have hBC : B t ≤ C (t + d) := by
    refine le_trans (le_minConv fun u s hus => ?_) (hserv (t + d))
    rcases le_or_gt u t with hut | hut
    · have hs : s = (t - u) + d := by
        have h1 : u + s = u + ((t - u) + d) := by
          rw [hus, ← add_assoc, add_tsub_cancel_of_le hut]
        exact add_left_cancel h1
      have hB : B t ≤ B u + α (t - u) := by
        have h2 := harr u (t - u)
        rwa [add_tsub_cancel_of_le hut] at h2
      calc B t ≤ B u + α (t - u) := hB
        _ ≤ B u + β ((t - u) + d) := add_le_add le_rfl (hadm (t - u))
        _ = B u + β s := by rw [hs]
    · calc B t ≤ B u := hBmono hut.le
        _ ≤ B u + β s := le_self_add
  exact absurd (lt_of_le_of_lt (hDevAt_le hBC) hd2) (lt_irrefl _)

/-- **Delay bound at the deviation level**, sup form: `hDev B C ≤ hDev α β`
for a pair `(B, C)` with nondecreasing `B` allowing `α` and `C` dominating
`B ∗ β`. -/
theorem hDev_le_hDev_of_minConv_le {B C α β : ℝ≥0 → ℝ≥0∞}
    (hBmono : Monotone B) (hβmono : Monotone β)
    (harr : IsMaximalArrivalBound B α) (hserv : minConv B β ≤ C) :
    (hDev B C : ℝ≥0∞) ≤ hDev α β :=
  hDev_le fun t => hDevAt_le_hDev_of_minConv_le hBmono hβmono harr hserv t

/-- Hop 2 of the worst-case trajectory respects the propagated per-hop bound:
`hDev (α ⊓ β₁) (α ⊓ (β₁ ∗ β₂)) ≤ hDev (α ⊘ β₁) β₂`. -/
theorem hDev_inf_le_hDev_minDeconv {α β₁ β₂ : ℝ≥0 → ℝ≥0∞}
    (hαmono : Monotone α) (hα0 : α 0 = 0) (hsub : IsSubadditive α)
    (hβ₁mono : Monotone β₁) (hβ₁0 : β₁ 0 = 0)
    (hβ₂mono : Monotone β₂) (hβ₂0 : β₂ 0 = 0) :
    (hDev (α ⊓ β₁) (α ⊓ minConv β₁ β₂) : ℝ≥0∞)
      ≤ hDev (minDeconv α β₁) β₂ :=
  hDev_le_hDev_of_minConv_le (hαmono.inf hβ₁mono) hβ₂mono
    ((isMaximalArrivalBound_self_of_subadditive hsub).output inf_le_left
      (minimalServicePair_inf hα0 hβ₁0).2)
    (minimalServicePair_inf_minConv hβ₂0).2

/-- **The worst-case tandem trajectory**: for sub-additive `α` and `β₁`, `β₂`
in `F₀`, some trajectory `α → B → C` of the tandem of min-plus servers has an
`α`-constrained source, attains `hDev α C = hDev α (β₁ ∗ β₂)`, and keeps the
per-hop deviation sum below `hDev α β₁ + hDev (α ⊘ β₁) β₂`. The witnesses are
`B = α ⊓ β₁` and `C = α ⊓ (β₁ ∗ β₂)`. -/
theorem exists_tandem_minimalServicePair_hDev_eq {α β₁ β₂ : ℝ≥0 → ℝ≥0∞}
    (hαmono : Monotone α) (hα0 : α 0 = 0) (hsub : IsSubadditive α)
    (hβ₁mono : Monotone β₁) (hβ₁0 : β₁ 0 = 0)
    (hβ₂mono : Monotone β₂) (hβ₂0 : β₂ 0 = 0) :
    ∃ B C : ℝ≥0 → ℝ≥0∞,
      minimalServicePair β₁ α B ∧ minimalServicePair β₂ B C ∧
      IsMaximalArrivalBound α α ∧
      (hDev α C : ℝ≥0∞) = hDev α (minConv β₁ β₂) ∧
      (hDev α B : ℝ≥0∞) + hDev B C
        ≤ (hDev α β₁ : ℝ≥0∞) + hDev (minDeconv α β₁) β₂ :=
  ⟨α ⊓ β₁, α ⊓ minConv β₁ β₂,
    minimalServicePair_inf hα0 hβ₁0,
    minimalServicePair_inf_minConv hβ₂0,
    isMaximalArrivalBound_self_of_subadditive hsub,
    hDev_inf_self hαmono,
    add_le_add (le_of_eq (hDev_inf_self hαmono))
      (hDev_inf_le_hDev_minDeconv hαmono hα0 hsub hβ₁mono hβ₁0
        hβ₂mono hβ₂0)⟩

/-! ## Book restatement (the trajectory route to pay burst only once)
If `A —S₁→ B —S₂→ C` then `hDev(A, C) ≤ hDev(A, B) + hDev(B, C)`. With
`S₁ = S_mp(β₁)`, `S₂ = S_mp(β₂)` and an `α`-constrained flow, the triple
`A = α`, `B = α ⊓ β₁`, `C = α ⊓ (β₁ ∗ β₂)` is an admissible trajectory of
the tandem satisfying `hDev(A, C) = hDev(α, β₁ ∗ β₂)`. But
`hDev(A, B) + hDev(B, C) ≤ hDev(α, β₁) + hDev(α ⊘ β₁, β₂)`, so
`hDev(α, β₁ ∗ β₂) ≤ hDev(α, β₁) + hDev(α ⊘ β₁, β₂)` — `d ≤ d₁ + d₂`. -/

example {α β₁ β₂ : ℝ≥0 → ℝ≥0∞} :
    (hDev α (α ⊓ minConv β₁ β₂) : ℝ≥0∞)
      ≤ (hDev α (α ⊓ β₁) : ℝ≥0∞) + hDev (α ⊓ β₁) (α ⊓ minConv β₁ β₂) :=
  hDev_triangle α (α ⊓ β₁) (α ⊓ minConv β₁ β₂)

example {α β₁ β₂ : ℝ≥0 → ℝ≥0∞} (hα0 : α 0 = 0) (hsub : IsSubadditive α)
    (hβ₁0 : β₁ 0 = 0) (hβ₂0 : β₂ 0 = 0) :
    IsMaximalArrivalBound α α ∧
      minimalServicePair β₁ α (α ⊓ β₁) ∧
      minimalServicePair β₂ (α ⊓ β₁) (α ⊓ minConv β₁ β₂) :=
  ⟨isMaximalArrivalBound_self_of_subadditive hsub,
    minimalServicePair_inf hα0 hβ₁0, minimalServicePair_inf_minConv hβ₂0⟩

example {α β₁ β₂ : ℝ≥0 → ℝ≥0∞} (hαmono : Monotone α) :
    (hDev α (α ⊓ minConv β₁ β₂) : ℝ≥0∞) = hDev α (minConv β₁ β₂) :=
  hDev_inf_self hαmono

example {α β₁ β₂ : ℝ≥0 → ℝ≥0∞}
    (hαmono : Monotone α) (hα0 : α 0 = 0) (hsub : IsSubadditive α)
    (hβ₁mono : Monotone β₁) (hβ₁0 : β₁ 0 = 0)
    (hβ₂mono : Monotone β₂) (hβ₂0 : β₂ 0 = 0) :
    (hDev α (α ⊓ β₁) : ℝ≥0∞) + hDev (α ⊓ β₁) (α ⊓ minConv β₁ β₂)
      ≤ (hDev α β₁ : ℝ≥0∞) + hDev (minDeconv α β₁) β₂ :=
  add_le_add (le_of_eq (hDev_inf_self hαmono))
    (hDev_inf_le_hDev_minDeconv hαmono hα0 hsub hβ₁mono hβ₁0 hβ₂mono hβ₂0)

example {α β₁ β₂ : ℝ≥0 → ℝ≥0∞}
    (hαmono : Monotone α) (hα0 : α 0 = 0) (hsub : IsSubadditive α)
    (hβ₁mono : Monotone β₁) (hβ₁0 : β₁ 0 = 0)
    (hβ₂mono : Monotone β₂) (hβ₂0 : β₂ 0 = 0) :
    (hDev α (minConv β₁ β₂) : ℝ≥0∞)
      ≤ hDev α β₁ + hDev (minDeconv α β₁) β₂ :=
  calc (hDev α (minConv β₁ β₂) : ℝ≥0∞)
      = hDev α (α ⊓ minConv β₁ β₂) := (hDev_inf_self hαmono).symm
    _ ≤ (hDev α (α ⊓ β₁) : ℝ≥0∞) + hDev (α ⊓ β₁) (α ⊓ minConv β₁ β₂) :=
        hDev_triangle _ _ _
    _ ≤ (hDev α β₁ : ℝ≥0∞) + hDev (minDeconv α β₁) β₂ :=
        add_le_add (le_of_eq (hDev_inf_self hαmono))
          (hDev_inf_le_hDev_minDeconv hαmono hα0 hsub hβ₁mono hβ₁0
            hβ₂mono hβ₂0)

end DeepWiki
