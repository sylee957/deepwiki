import DeepWiki.NetworkCalculus.Deviations

/-! # Deviations under server composition
The triangle inequality of the horizontal deviation,
`hDev f h ≤ hDev f g + hDev g h` (admissible shifts compose through the
intermediate function), its delay instance for cumulative processes, and
the pay-burst-only-once inequality
`hDev α (β₁ ∗ β₂) ≤ hDev α β₁ + hDev (α ⊘ β₁) β₂`: bounding the delay of
a tandem through the convolution beats summing per-server delay bounds. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- Pointwise triangle inequality: an admissible shift `d₁` for `(f, g)`
at `t` composes with the deviation of `(g, h)` at `t + d₁`,
`hDevAt f h t ≤ hDevAt f g t + hDev g h`. -/
theorem hDevAt_le_hDevAt_add_hDev {V : Type*} [Preorder V]
    {f g h : ℝ≥0 → V} (t : ℝ≥0) :
    (hDevAt f h t : ℝ≥0∞) ≤ (hDevAt f g t : ℝ≥0∞) + hDev g h :=
  le_hDevAt_add fun d₁ hd₁ =>
    le_trans
      (le_add_hDevAt fun d₂ hd₂ =>
        hDevAt_le (show f t ≤ h (t + (d₁ + d₂)) by
          rw [← add_assoc]
          exact le_trans hd₁ hd₂))
      (add_le_add le_rfl (hDevAt_le_hDev g h (t + d₁)))

/-- **Triangle inequality of the horizontal deviation**:
`hDev f h ≤ hDev f g + hDev g h` (no hypotheses on the functions). -/
theorem hDev_triangle {V : Type*} [Preorder V] (f g h : ℝ≥0 → V) :
    (hDev f h : ℝ≥0∞) ≤ (hDev f g : ℝ≥0∞) + hDev g h :=
  hDev_le fun t => le_trans (hDevAt_le_hDevAt_add_hDev t)
    (add_le_add (hDevAt_le_hDev f g t) le_rfl)

/-- The delay through a tandem of cumulative processes is at most the sum
of the per-hop delays: `d(A, C) ≤ d(A, B) + d(B, C)`. -/
theorem Deviation.delay_triangle (A B C : ℝ≥0 → ℝ≥0) :
    Deviation.delay A C ≤ Deviation.delay A B + Deviation.delay B C :=
  hDev_triangle A B C

/-- **Pay burst only once**: the horizontal deviation from the convolved
curve is at most the per-stage sum through the deconvolved intermediate
arrival, `hDev α (β₁ ∗ β₂) ≤ hDev α β₁ + hDev (α ⊘ β₁) β₂`. Splits of
`t + d₁ + d₂` spending at least `d₂` on the `β₂` side route through the
deconvolution; the others are covered by `β₁ (t + d₁)` alone. -/
theorem hDev_minConv_le_add_hDev_minDeconv {α β₁ β₂ : ℝ≥0 → ℝ≥0∞}
    (hαmono : Monotone α) (hβ₁mono : Monotone β₁)
    (hβ₂mono : Monotone β₂) :
    (hDev α (minConv β₁ β₂) : ℝ≥0∞)
      ≤ hDev α β₁ + hDev (minDeconv α β₁) β₂ := by
  refine hDev_le fun t => ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hb => ?_
  have hε2 : (0 : ℝ≥0∞) < ↑ε / 2 :=
    ENNReal.half_pos (by exact_mod_cast hε.ne')
  have h₁t : (hDev α β₁ : ℝ≥0∞) ≠ ⊤ := (le_self_add.trans_lt hb).ne
  have h₂t : (hDev (minDeconv α β₁) β₂ : ℝ≥0∞) ≠ ⊤ :=
    (le_add_self.trans_lt hb).ne
  obtain ⟨r₁, hr₁l, hr₁u⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp
    (ENNReal.lt_add_right h₁t hε2.ne')
  obtain ⟨r₂, hr₂l, hr₂u⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp
    (ENNReal.lt_add_right h₂t hε2.ne')
  -- `r₁`, `r₂` are uniformly admissible for their pairs
  have hadm₁ : ∀ x, α x ≤ β₁ (x + r₁) := le_of_hDev_lt hβ₁mono hr₁l
  have hadm₂ : ∀ x, minDeconv α β₁ x ≤ β₂ (x + r₂) :=
    le_of_hDev_lt hβ₂mono hr₂l
  refine le_trans (hDevAt_le (d := r₁ + r₂) ?_) ?_
  · -- `α t ≤ (β₁ ∗ β₂) (t + (r₁ + r₂))`, split by split
    refine le_minConv fun u s hus => ?_
    rw [← add_assoc] at hus
    rcases le_or_gt r₂ s with hs | hs
    · -- the split grants `β₂` at least `r₂`: route through `α ⊘ β₁`
      have hsu : (s - r₂) + u = t + r₁ := by
        rw [tsub_add_eq_add_tsub hs, add_comm s u, hus,
          add_tsub_cancel_right]
      have hkey : α (t + r₁) - β₁ u ≤ β₂ s := by
        have h1 := sub_le_minDeconv α β₁ (s - r₂) u
        rw [hsu] at h1
        refine le_trans (le_trans h1 (hadm₂ (s - r₂))) ?_
        rw [tsub_add_cancel_of_le hs]
      calc α t ≤ α (t + r₁) := hαmono le_self_add
        _ ≤ (α (t + r₁) - β₁ u) + β₁ u := le_tsub_add
        _ ≤ β₂ s + β₁ u := add_le_add hkey le_rfl
        _ = β₁ u + β₂ s := add_comm _ _
    · -- the split starves `β₂`: `β₁ u` alone already covers `α t`
      have hu : t + r₁ ≤ u :=
        le_of_add_le_add_right (le_of_eq_of_le (congrArg (· + s) rfl)
          (by rw [hus]; exact add_le_add le_rfl hs.le) : t + r₁ + s ≤ u + s)
      calc α t ≤ β₁ (t + r₁) := hadm₁ t
        _ ≤ β₁ u := hβ₁mono hu
        _ ≤ β₁ u + β₂ s := le_self_add
  · -- the witness costs at most the deviation sum plus `ε`
    show ((r₁ + r₂ : ℝ≥0) : ℝ≥0∞) ≤ _
    rw [ENNReal.coe_add]
    calc (r₁ : ℝ≥0∞) + r₂
        ≤ ((hDev α β₁ : ℝ≥0∞) + ↑ε / 2)
            + ((hDev (minDeconv α β₁) β₂ : ℝ≥0∞) + ↑ε / 2) :=
          add_le_add hr₁u.le hr₂u.le
      _ = ((hDev α β₁ : ℝ≥0∞) + hDev (minDeconv α β₁) β₂)
            + (↑ε / 2 + ↑ε / 2) := add_add_add_comm _ _ _ _
      _ = ((hDev α β₁ : ℝ≥0∞) + hDev (minDeconv α β₁) β₂) + ↑ε := by
          rw [ENNReal.add_halves]

/-! ## Book restatement (the pay burst only once phenomenon)
For a tandem `A → B → C`, `hDev(A, C) ≤ hDev(A, B) + hDev(B, C)`; and the
global service-curve bound beats the per-server sum:
`hDev(α, β₁ ∗ β₂) ≤ hDev(α, β₁) + hDev(α ⊘ β₁, β₂)`, i.e. `d ≤ d₁ + d₂`
with `d₁ = hDev(α, β₁)`, `α' = α ⊘ β₁`, `d₂ = hDev(α', β₂)` — the burst
term is paid only once. -/
example (A B C : ℝ≥0 → ℝ≥0) :
    Deviation.delay A C ≤ Deviation.delay A B + Deviation.delay B C :=
  Deviation.delay_triangle A B C

example {α β₁ β₂ : ℝ≥0 → ℝ≥0∞} (hαmono : Monotone α)
    (hβ₁mono : Monotone β₁) (hβ₂mono : Monotone β₂) :
    (hDev α (minConv β₁ β₂) : ℝ≥0∞)
      ≤ hDev α β₁ + hDev (minDeconv α β₁) β₂ :=
  hDev_minConv_le_add_hDev_minDeconv hαmono hβ₁mono hβ₂mono

end DeepWiki
