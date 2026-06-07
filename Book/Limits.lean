import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Limits
One-sided limits `f(t⁻)`/`f(t⁺)` for `ℝ≥0∞`-valued functions on `ℝ≥0`,
with ε–δ characterizations equivalent to the filter (`Tendsto`) form. 
-/

namespace DeepWiki

open Topology Filter Set
open scoped Classical NNReal ENNReal

/-- `g` has left limit `L` at `t`: `Tendsto g (𝓝[<] t) (𝓝 L)`. -/
def TendstoLeft
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (L : ℝ≥0∞) : Prop :=
  Tendsto g (𝓝[<] t) (𝓝 L)

/-- `g` has right limit `L` at `t`: `Tendsto g (𝓝[>] t) (𝓝 L)`. -/
def TendstoRight
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (L : ℝ≥0∞) : Prop :=
  Tendsto g (𝓝[>] t) (𝓝 L)

/-- Pointwise `ENNReal.toReal` of `g`. -/
noncomputable def realOf (g : ℝ≥0 → ℝ≥0∞) : ℝ≥0 → ℝ :=
  fun s => (g s).toReal

/-- ε–δ left limit: ε–δ if `L` finite, `M`-blowup if `L = ⊤`. -/
def TendstoLeftED
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (L : ℝ≥0∞) : Prop :=
  (L ≠ ⊤ →
    ∀ ε : ℝ, 0 < ε → ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
      g s ≠ ⊤ ∧ |realOf g s - L.toReal| < ε) ∧
  (L = ⊤ →
    ∀ M : ℝ≥0, ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
      (M : ℝ≥0∞) < g s)

/-- ε–δ right limit: ε–δ if `L` finite, `M`-blowup if `L = ⊤`. -/
def TendstoRightED
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (L : ℝ≥0∞) : Prop :=
  (L ≠ ⊤ →
    ∀ ε : ℝ, 0 < ε → ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
      g s ≠ ⊤ ∧ |realOf g s - L.toReal| < ε) ∧
  (L = ⊤ →
    ∀ M : ℝ≥0, ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
      (M : ℝ≥0∞) < g s)

/-- Left ε–δ Cauchy condition for `realOf g` ↔ left continuity at `t`. -/
theorem real_close_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t) :
    (∀ ε : ℝ, 0 < ε → ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
        |realOf g s - realOf g t| < ε)
      ↔ ContinuousWithinAt (realOf g) (Iio t) t := by
  have hbasis : (𝓝[<] t).HasBasis (· < t) (Ioo · t) :=
    nhdsLT_basis_of_exists_lt ⟨0, ht⟩
  unfold ContinuousWithinAt
  rw [hbasis.tendsto_iff Metric.nhds_basis_ball]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδt, hδ⟩ := h ε hε
    refine ⟨δ, hδt, fun s hs => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    exact hδ s hs
  · intro h ε hε
    obtain ⟨δ, hδt, hδ⟩ := h ε hε
    refine ⟨δ, hδt, fun s hs => ?_⟩
    have := hδ s hs
    rwa [Metric.mem_ball, Real.dist_eq] at this

/-- For finite `L`, the ε–δ left limit ↔ `TendstoLeft g t L`. -/
theorem finite_tendstoLeftED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t)
    (L : ℝ≥0∞) (hLfin : L ≠ ⊤) :
    (∀ ε : ℝ, 0 < ε → ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
        g s ≠ ⊤ ∧ |realOf g s - L.toReal| < ε)
      ↔ TendstoLeft g t L := by
  unfold TendstoLeft
  have hbasis : (𝓝[<] t).HasBasis (· < t) (Ioo · t) :=
    nhdsLT_basis_of_exists_lt ⟨0, ht⟩
  constructor
  · intro h
    have hreal :
        Tendsto (realOf g) (𝓝[<] t) (𝓝 L.toReal) := by
      rw [hbasis.tendsto_iff Metric.nhds_basis_ball]
      intro ε hε
      obtain ⟨δ, hδt, hδ⟩ := h ε hε
      exact ⟨δ, hδt, fun s hs => by
        rw [Metric.mem_ball, Real.dist_eq]
        exact (hδ s hs).2⟩
    have hfin_ev : ∀ᶠ s in 𝓝[<] t, g s ≠ ⊤ := by
      rw [hbasis.eventually_iff]
      obtain ⟨δ, hδt, hδ⟩ := h 1 one_pos
      exact ⟨δ, hδt, fun s hs => (hδ s hs).1⟩
    have hcoe :
        ContinuousAt ENNReal.ofReal L.toReal :=
      ENNReal.continuous_ofReal.continuousAt
    have := hcoe.tendsto.comp hreal
    rw [ENNReal.ofReal_toReal hLfin] at this
    refine this.congr' ?_
    filter_upwards [hfin_ev] with s hs
    show ENNReal.ofReal (realOf g s) = g s
    rw [realOf, ENNReal.ofReal_toReal hs]
  · intro h
    have hfin_ev : ∀ᶠ s in 𝓝[<] t, g s ≠ ⊤ := by
      have hmem : Iio (⊤ : ℝ≥0∞) ∈ 𝓝 L :=
        Iio_mem_nhds hLfin.lt_top
      filter_upwards [h hmem] with s hs
        using (Set.mem_Iio.mp hs).ne
    have hreal :
        Tendsto (realOf g) (𝓝[<] t) (𝓝 L.toReal) := by
      have hto : ContinuousAt ENNReal.toReal L :=
        ENNReal.continuousAt_toReal hLfin
      exact hto.tendsto.comp h
    rw [hbasis.tendsto_iff Metric.nhds_basis_ball] at hreal
    intro ε hε
    obtain ⟨δ₁, hδ₁t, hδ₁⟩ := hreal ε hε
    rw [hbasis.eventually_iff] at hfin_ev
    obtain ⟨δ₂, hδ₂t, hδ₂⟩ := hfin_ev
    refine ⟨max δ₁ δ₂, max_lt hδ₁t hδ₂t, fun s hs => ?_⟩
    have hs1 : s ∈ Ioo δ₁ t :=
      ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, hs.2⟩
    have hs2 : s ∈ Ioo δ₂ t :=
      ⟨lt_of_le_of_lt (le_max_right _ _) hs.1, hs.2⟩
    exact ⟨hδ₂ hs2, hδ₁ s hs1⟩

/-- The `M`-blowup left condition ↔ `TendstoLeft g t ⊤`. -/
theorem infinite_tendstoLeftED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t) :
    (∀ M : ℝ≥0, ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
        (M : ℝ≥0∞) < g s)
      ↔ TendstoLeft g t ⊤ := by
  unfold TendstoLeft
  have hbasis : (𝓝[<] t).HasBasis (· < t) (Ioo · t) :=
    nhdsLT_basis_of_exists_lt ⟨0, ht⟩
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  constructor
  · intro h M
    obtain ⟨δ, hδt, hδ⟩ := h M
    rw [hbasis.eventually_iff]
    exact ⟨δ, hδt, fun s hs => hδ s hs⟩
  · intro h M
    have hM := h M
    rw [hbasis.eventually_iff] at hM
    obtain ⟨δ, hδt, hδ⟩ := hM
    exact ⟨δ, hδt, fun s hs => hδ hs⟩

/-- `TendstoLeftED g t L ↔ TendstoLeft g t L` for any `L`. -/
theorem tendstoLeftED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t)
    (L : ℝ≥0∞) :
    TendstoLeftED g t L ↔ TendstoLeft g t L := by
  unfold TendstoLeftED
  by_cases hfin : L = ⊤
  · subst hfin
    rw [← infinite_tendstoLeftED_iff g t ht]
    constructor
    · rintro ⟨-, h⟩; exact h rfl
    · intro h
      exact ⟨fun hne => absurd rfl hne, fun _ => h⟩
  · rw [← finite_tendstoLeftED_iff g t ht L hfin]
    constructor
    · rintro ⟨h, -⟩; exact h hfin
    · intro h
      exact ⟨fun _ => h, fun hT => absurd hT hfin⟩

/-- Right ε–δ Cauchy condition for `realOf g` ↔ right continuity at `t`. -/
theorem real_close_iff_right
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    (∀ ε : ℝ, 0 < ε → ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
        |realOf g s - realOf g t| < ε)
      ↔ ContinuousWithinAt (realOf g) (Ioi t) t := by
  have hbasis : (𝓝[>] t).HasBasis (t < ·) (Ioo t ·) :=
    nhdsGT_basis t
  unfold ContinuousWithinAt
  rw [hbasis.tendsto_iff Metric.nhds_basis_ball]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδt, hδ⟩ := h ε hε
    refine ⟨δ, hδt, fun s hs => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    exact hδ s hs
  · intro h ε hε
    obtain ⟨δ, hδt, hδ⟩ := h ε hε
    refine ⟨δ, hδt, fun s hs => ?_⟩
    have := hδ s hs
    rwa [Metric.mem_ball, Real.dist_eq] at this

/-- For finite `L`, the ε–δ right limit ↔ `TendstoRight g t L`. -/
theorem finite_tendstoRightED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0)
    (L : ℝ≥0∞) (hLfin : L ≠ ⊤) :
    (∀ ε : ℝ, 0 < ε → ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
        g s ≠ ⊤ ∧ |realOf g s - L.toReal| < ε)
      ↔ TendstoRight g t L := by
  unfold TendstoRight
  have hbasis : (𝓝[>] t).HasBasis (t < ·) (Ioo t ·) :=
    nhdsGT_basis t
  constructor
  · intro h
    have hreal :
        Tendsto (realOf g) (𝓝[>] t) (𝓝 L.toReal) := by
      rw [hbasis.tendsto_iff Metric.nhds_basis_ball]
      intro ε hε
      obtain ⟨δ, hδt, hδ⟩ := h ε hε
      exact ⟨δ, hδt, fun s hs => by
        rw [Metric.mem_ball, Real.dist_eq]
        exact (hδ s hs).2⟩
    have hfin_ev : ∀ᶠ s in 𝓝[>] t, g s ≠ ⊤ := by
      rw [hbasis.eventually_iff]
      obtain ⟨δ, hδt, hδ⟩ := h 1 one_pos
      exact ⟨δ, hδt, fun s hs => (hδ s hs).1⟩
    have hcoe :
        ContinuousAt ENNReal.ofReal L.toReal :=
      ENNReal.continuous_ofReal.continuousAt
    have := hcoe.tendsto.comp hreal
    rw [ENNReal.ofReal_toReal hLfin] at this
    refine this.congr' ?_
    filter_upwards [hfin_ev] with s hs
    show ENNReal.ofReal (realOf g s) = g s
    rw [realOf, ENNReal.ofReal_toReal hs]
  · intro h
    have hfin_ev : ∀ᶠ s in 𝓝[>] t, g s ≠ ⊤ := by
      have hmem : Iio (⊤ : ℝ≥0∞) ∈ 𝓝 L :=
        Iio_mem_nhds hLfin.lt_top
      filter_upwards [h hmem] with s hs
        using (Set.mem_Iio.mp hs).ne
    have hreal :
        Tendsto (realOf g) (𝓝[>] t) (𝓝 L.toReal) := by
      have hto : ContinuousAt ENNReal.toReal L :=
        ENNReal.continuousAt_toReal hLfin
      exact hto.tendsto.comp h
    rw [hbasis.tendsto_iff Metric.nhds_basis_ball] at hreal
    intro ε hε
    obtain ⟨δ₁, hδ₁t, hδ₁⟩ := hreal ε hε
    rw [hbasis.eventually_iff] at hfin_ev
    obtain ⟨δ₂, hδ₂t, hδ₂⟩ := hfin_ev
    refine ⟨min δ₁ δ₂, lt_min hδ₁t hδ₂t, fun s hs => ?_⟩
    have hs1 : s ∈ Ioo t δ₁ :=
      ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
    have hs2 : s ∈ Ioo t δ₂ :=
      ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩
    exact ⟨hδ₂ hs2, hδ₁ s hs1⟩

/-- The `M`-blowup right condition ↔ `TendstoRight g t ⊤`. -/
theorem infinite_tendstoRightED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    (∀ M : ℝ≥0, ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
        (M : ℝ≥0∞) < g s)
      ↔ TendstoRight g t ⊤ := by
  unfold TendstoRight
  have hbasis : (𝓝[>] t).HasBasis (t < ·) (Ioo t ·) :=
    nhdsGT_basis t
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  constructor
  · intro h M
    obtain ⟨δ, hδt, hδ⟩ := h M
    rw [hbasis.eventually_iff]
    exact ⟨δ, hδt, fun s hs => hδ s hs⟩
  · intro h M
    have hM := h M
    rw [hbasis.eventually_iff] at hM
    obtain ⟨δ, hδt, hδ⟩ := hM
    exact ⟨δ, hδt, fun s hs => hδ hs⟩

/-- `TendstoRightED g t L ↔ TendstoRight g t L` for any `L`. -/
theorem tendstoRightED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (L : ℝ≥0∞) :
    TendstoRightED g t L ↔ TendstoRight g t L := by
  unfold TendstoRightED
  by_cases hfin : L = ⊤
  · subst hfin
    rw [← infinite_tendstoRightED_iff g t]
    constructor
    · rintro ⟨-, h⟩; exact h rfl
    · intro h
      exact ⟨fun hne => absurd rfl hne, fun _ => h⟩
  · rw [← finite_tendstoRightED_iff g t L hfin]
    constructor
    · rintro ⟨h, -⟩; exact h hfin
    · intro h
      exact ⟨fun _ => h, fun hT => absurd hT hfin⟩

/-- The right-neighborhood filter `𝓝[>] t` is `NeBot` on `ℝ≥0`. -/
instance instNeBotNhdsGT (t : ℝ≥0) :
    (𝓝[>] t).NeBot := nhdsGT_neBot t

/-- Left limits are unique (needs `0 < t`, so `𝓝[<] t` is `NeBot`). -/
theorem TendstoLeft.unique
    {g : ℝ≥0 → ℝ≥0∞} {t : ℝ≥0} (ht : 0 < t) {L₁ L₂ : ℝ≥0∞}
    (h₁ : TendstoLeft g t L₁) (h₂ : TendstoLeft g t L₂) :
    L₁ = L₂ :=
  haveI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  tendsto_nhds_unique h₁ h₂

/-- Right limits are unique (`𝓝[>] t` is `NeBot` on `ℝ≥0`). -/
theorem TendstoRight.unique
    {g : ℝ≥0 → ℝ≥0∞} {t : ℝ≥0} {L₁ L₂ : ℝ≥0∞}
    (h₁ : TendstoRight g t L₁) (h₂ : TendstoRight g t L₂) :
    L₁ = L₂ :=
  tendsto_nhds_unique h₁ h₂

end DeepWiki
