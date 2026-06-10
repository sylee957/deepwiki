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

/-! The left and right ε–δ characterizations are line-by-line dual, so the
shared content is proved once over an arbitrary filter `l` with an interval
basis `l.HasBasis p S`, then specialized to `𝓝[<] t` and `𝓝[>] t`. -/

/-- Along a filter with basis `l.HasBasis p S`, the ε–δ Cauchy condition for
`realOf g` is `Tendsto (realOf g) l (𝓝 (realOf g t))`. -/
theorem real_close_iff_of_hasBasis
    {l : Filter ℝ≥0} {p : ℝ≥0 → Prop} {S : ℝ≥0 → Set ℝ≥0}
    (hbasis : l.HasBasis p S) (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    (∀ ε : ℝ, 0 < ε → ∃ δ, p δ ∧ ∀ s ∈ S δ,
        |realOf g s - realOf g t| < ε)
      ↔ Tendsto (realOf g) l (𝓝 (realOf g t)) := by
  rw [hbasis.tendsto_iff Metric.nhds_basis_ball]
  simp only [Metric.mem_ball, Real.dist_eq]

/-- For finite `L`, the ε–δ condition along a basis `l.HasBasis p S` is
`Tendsto g l (𝓝 L)`. -/
theorem finite_tendstoED_iff_of_hasBasis
    {l : Filter ℝ≥0} {p : ℝ≥0 → Prop} {S : ℝ≥0 → Set ℝ≥0}
    (hbasis : l.HasBasis p S) (g : ℝ≥0 → ℝ≥0∞)
    (L : ℝ≥0∞) (hLfin : L ≠ ⊤) :
    (∀ ε : ℝ, 0 < ε → ∃ δ, p δ ∧ ∀ s ∈ S δ,
        g s ≠ ⊤ ∧ |realOf g s - L.toReal| < ε)
      ↔ Tendsto g l (𝓝 L) := by
  constructor
  · intro h
    have hreal :
        Tendsto (realOf g) l (𝓝 L.toReal) := by
      rw [hbasis.tendsto_iff Metric.nhds_basis_ball]
      intro ε hε
      obtain ⟨δ, hδl, hδ⟩ := h ε hε
      exact ⟨δ, hδl, fun s hs => by
        rw [Metric.mem_ball, Real.dist_eq]
        exact (hδ s hs).2⟩
    have hfin_ev : ∀ᶠ s in l, g s ≠ ⊤ := by
      rw [hbasis.eventually_iff]
      obtain ⟨δ, hδl, hδ⟩ := h 1 one_pos
      exact ⟨δ, hδl, fun s hs => (hδ s hs).1⟩
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
    have hfin_ev : ∀ᶠ s in l, g s ≠ ⊤ := by
      have hmem : Iio (⊤ : ℝ≥0∞) ∈ 𝓝 L :=
        Iio_mem_nhds hLfin.lt_top
      filter_upwards [h hmem] with s hs
        using (Set.mem_Iio.mp hs).ne
    have hreal : Tendsto (realOf g) l (𝓝 L.toReal) :=
      (ENNReal.continuousAt_toReal hLfin).tendsto.comp h
    intro ε hε
    have hball : ∀ᶠ s in l, |realOf g s - L.toReal| < ε := by
      filter_upwards [Metric.tendsto_nhds.mp hreal ε hε] with s hs
      rwa [Real.dist_eq] at hs
    obtain ⟨δ, hδl, hδ⟩ :=
      hbasis.eventually_iff.mp (hfin_ev.and hball)
    exact ⟨δ, hδl, fun s hs => hδ hs⟩

/-- The `M`-blowup condition along a basis `l.HasBasis p S` is
`Tendsto g l (𝓝 ⊤)`. -/
theorem infinite_tendstoED_iff_of_hasBasis
    {l : Filter ℝ≥0} {p : ℝ≥0 → Prop} {S : ℝ≥0 → Set ℝ≥0}
    (hbasis : l.HasBasis p S) (g : ℝ≥0 → ℝ≥0∞) :
    (∀ M : ℝ≥0, ∃ δ, p δ ∧ ∀ s ∈ S δ, (M : ℝ≥0∞) < g s)
      ↔ Tendsto g l (𝓝 ⊤) := by
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  exact forall_congr' fun M => hbasis.eventually_iff.symm

/-- The combined two-case ε–δ condition along a basis `l.HasBasis p S` is
`Tendsto g l (𝓝 L)` for any `L`. -/
theorem tendstoED_iff_of_hasBasis
    {l : Filter ℝ≥0} {p : ℝ≥0 → Prop} {S : ℝ≥0 → Set ℝ≥0}
    (hbasis : l.HasBasis p S) (g : ℝ≥0 → ℝ≥0∞) (L : ℝ≥0∞) :
    ((L ≠ ⊤ →
        ∀ ε : ℝ, 0 < ε → ∃ δ, p δ ∧ ∀ s ∈ S δ,
          g s ≠ ⊤ ∧ |realOf g s - L.toReal| < ε) ∧
      (L = ⊤ →
        ∀ M : ℝ≥0, ∃ δ, p δ ∧ ∀ s ∈ S δ, (M : ℝ≥0∞) < g s))
      ↔ Tendsto g l (𝓝 L) := by
  by_cases hfin : L = ⊤
  · subst hfin
    rw [← infinite_tendstoED_iff_of_hasBasis hbasis g]
    exact ⟨fun h => h.2 rfl,
      fun h => ⟨fun hne => absurd rfl hne, fun _ => h⟩⟩
  · rw [← finite_tendstoED_iff_of_hasBasis hbasis g L hfin]
    exact ⟨fun h => h.1 hfin,
      fun h => ⟨fun _ => h, fun hT => absurd hT hfin⟩⟩

/-- Left ε–δ Cauchy condition for `realOf g` ↔ left continuity at `t`. -/
theorem real_close_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t) :
    (∀ ε : ℝ, 0 < ε → ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
        |realOf g s - realOf g t| < ε)
      ↔ ContinuousWithinAt (realOf g) (Iio t) t :=
  real_close_iff_of_hasBasis (nhdsLT_basis_of_exists_lt ⟨0, ht⟩) g t

/-- For finite `L`, the ε–δ left limit ↔ `TendstoLeft g t L`. -/
theorem finite_tendstoLeftED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t)
    (L : ℝ≥0∞) (hLfin : L ≠ ⊤) :
    (∀ ε : ℝ, 0 < ε → ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
        g s ≠ ⊤ ∧ |realOf g s - L.toReal| < ε)
      ↔ TendstoLeft g t L :=
  finite_tendstoED_iff_of_hasBasis
    (nhdsLT_basis_of_exists_lt ⟨0, ht⟩) g L hLfin

/-- The `M`-blowup left condition ↔ `TendstoLeft g t ⊤`. -/
theorem infinite_tendstoLeftED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t) :
    (∀ M : ℝ≥0, ∃ δ < t, ∀ s ∈ Set.Ioo δ t,
        (M : ℝ≥0∞) < g s)
      ↔ TendstoLeft g t ⊤ :=
  infinite_tendstoED_iff_of_hasBasis
    (nhdsLT_basis_of_exists_lt ⟨0, ht⟩) g

/-- `TendstoLeftED g t L ↔ TendstoLeft g t L` for any `L`. -/
theorem tendstoLeftED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t)
    (L : ℝ≥0∞) :
    TendstoLeftED g t L ↔ TendstoLeft g t L :=
  tendstoED_iff_of_hasBasis
    (nhdsLT_basis_of_exists_lt ⟨0, ht⟩) g L

/-- Right ε–δ Cauchy condition for `realOf g` ↔ right continuity at `t`. -/
theorem real_close_iff_right
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    (∀ ε : ℝ, 0 < ε → ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
        |realOf g s - realOf g t| < ε)
      ↔ ContinuousWithinAt (realOf g) (Ioi t) t :=
  real_close_iff_of_hasBasis (nhdsGT_basis t) g t

/-- For finite `L`, the ε–δ right limit ↔ `TendstoRight g t L`. -/
theorem finite_tendstoRightED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0)
    (L : ℝ≥0∞) (hLfin : L ≠ ⊤) :
    (∀ ε : ℝ, 0 < ε → ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
        g s ≠ ⊤ ∧ |realOf g s - L.toReal| < ε)
      ↔ TendstoRight g t L :=
  finite_tendstoED_iff_of_hasBasis (nhdsGT_basis t) g L hLfin

/-- The `M`-blowup right condition ↔ `TendstoRight g t ⊤`. -/
theorem infinite_tendstoRightED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    (∀ M : ℝ≥0, ∃ δ > t, ∀ s ∈ Set.Ioo t δ,
        (M : ℝ≥0∞) < g s)
      ↔ TendstoRight g t ⊤ :=
  infinite_tendstoED_iff_of_hasBasis (nhdsGT_basis t) g

/-- `TendstoRightED g t L ↔ TendstoRight g t L` for any `L`. -/
theorem tendstoRightED_iff
    (g : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) (L : ℝ≥0∞) :
    TendstoRightED g t L ↔ TendstoRight g t L :=
  tendstoED_iff_of_hasBasis (nhdsGT_basis t) g L

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
