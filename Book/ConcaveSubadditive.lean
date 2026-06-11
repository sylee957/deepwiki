import Book.Concave
import Book.Additivity
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Order.DenselyOrdered

/-! # Subadditive does not imply concave
The ceiling curve `x ↦ ⌈x⌉₊` over `ℝ≥0` is subadditive and finite on the
positive ray, yet not concave: it is discontinuous at `x = 1`, while a finite
concave curve would be continuous on `(0, ∞)`. This witnesses the failure of
the implication subadditive ⟹ concave. -/

namespace DeepWiki

open scoped Classical NNReal
open Set Filter Topology

/-- The ceiling curve `x ↦ ⌈x⌉₊`, a step curve coerced `ℕ → EReal`. -/
noncomputable def ceilCurve : ℝ≥0 → EReal := fun x => (⌈x⌉₊ : EReal)

/-- `ceilCurve` is subadditive: `⌈u + s⌉₊ ≤ ⌈u⌉₊ + ⌈s⌉₊` in `EReal`. -/
theorem isSubadditive_ceilCurve : IsSubadditive ceilCurve := by
  intro u s
  have hle : ⌈u + s⌉₊ ≤ ⌈u⌉₊ + ⌈s⌉₊ := Nat.ceil_add_le u s
  show (⌈u + s⌉₊ : EReal) ≤ (⌈u⌉₊ : EReal) + (⌈s⌉₊ : EReal)
  rw [← EReal.coe_coe_eq_natCast, ← EReal.coe_coe_eq_natCast,
    ← EReal.coe_coe_eq_natCast, ← EReal.coe_add, EReal.coe_le_coe_iff,
    ← Nat.cast_add, Nat.cast_le]
  exact hle

/-- `ceilCurve` is finite on `(0, ∞)`: a coerced `ℕ` is neither `⊤` nor `⊥`. -/
theorem isFiniteOnPos_ceilCurve : IsFiniteOnPos ceilCurve := by
  intro x _
  exact ⟨EReal.natCast_ne_top _, EReal.natCast_ne_bot _⟩

/-- For `1 < x ≤ 2`, `⌈x⌉₊ = 2`, so `ceilCurve x = 2`. -/
theorem ceilCurve_eq_two {x : ℝ≥0} (h1 : 1 < x) (h2 : x ≤ 2) :
    ceilCurve x = 2 := by
  have hceil : ⌈x⌉₊ = 2 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    constructor
    · simpa using h1
    · simpa using h2
  show (⌈x⌉₊ : EReal) = 2
  rw [hceil]; norm_num

/-- `ceilCurve 1 = 1`: `⌈1⌉₊ = 1`. -/
theorem ceilCurve_one : ceilCurve 1 = 1 := by
  show (⌈(1 : ℝ≥0)⌉₊ : EReal) = 1
  rw [Nat.ceil_one]; norm_num

/-- `ceilCurve` is not continuous on `(0, ∞)`: it jumps from `1` to `2` at
`x = 1`, witnessed along the right neighbourhood `𝓝[Ioi 1] 1`. -/
theorem not_continuousOn_ceilCurve :
    ¬ ContinuousOn ceilCurve {x : ℝ≥0 | 0 < x} := by
  intro hcont
  have h1mem : (1 : ℝ≥0) ∈ {x : ℝ≥0 | 0 < x} := by simp
  -- continuity within the positive ray at `1`
  have hwithin := hcont 1 h1mem
  rw [ContinuousWithinAt, ceilCurve_one] at hwithin
  -- the right-neighbourhood filter is below the within-filter and NeBot
  have hsub : Ioi (1 : ℝ≥0) ⊆ {x : ℝ≥0 | 0 < x} := fun x hx =>
    Set.mem_setOf.mpr (lt_trans one_pos hx)
  have hle : 𝓝[Ioi (1 : ℝ≥0)] 1 ≤ 𝓝[{x : ℝ≥0 | 0 < x}] 1 :=
    nhdsWithin_mono 1 hsub
  have hneBot : (𝓝[Ioi (1 : ℝ≥0)] 1).NeBot :=
    nhdsWithin_Ioi_neBot (le_refl (1 : ℝ≥0))
  -- along `Ioi 1`, `ceilCurve` is eventually `2` (it is `2` on `(1, 2)`)
  have heq : ceilCurve =ᶠ[𝓝[Ioi (1 : ℝ≥0)] 1] (fun _ => (2 : EReal)) := by
    have hmem : Iio (2 : ℝ≥0) ∈ 𝓝[Ioi (1 : ℝ≥0)] 1 := by
      apply nhdsWithin_le_nhds
      exact Iio_mem_nhds (by norm_num)
    filter_upwards [self_mem_nhdsWithin, hmem] with x hx hx2
    exact ceilCurve_eq_two hx (le_of_lt hx2)
  -- target `2` from the eventual-constant value
  have hto2 : Tendsto ceilCurve (𝓝[Ioi (1 : ℝ≥0)] 1) (𝓝 (2 : EReal)) :=
    (tendsto_congr' heq).mpr tendsto_const_nhds
  -- target `1` from the restricted continuity
  have hto1 : Tendsto ceilCurve (𝓝[Ioi (1 : ℝ≥0)] 1) (𝓝 (1 : EReal)) :=
    hwithin.mono_left hle
  -- uniqueness of limits on a NeBot filter forces `1 = 2`
  have : (1 : EReal) = 2 := tendsto_nhds_unique hto1 hto2
  norm_num at this

/-- `ceilCurve` is not concave: were it concave, finiteness would force
continuity on `(0, ∞)`, contradicting its jump at `x = 1`. -/
theorem not_concaveE_ceilCurve : ¬ IsConcaveEReal ceilCurve := by
  intro hconc
  exact not_continuousOn_ceilCurve
    (continuousOn_of_isConcaveEReal_of_finite ceilCurve hconc isFiniteOnPos_ceilCurve)

/-- There is a subadditive, positively-finite curve that is not concave:
the ceiling curve witnesses subadditive ⟹ concave is false. -/
theorem exists_subadditive_not_concaveE :
    ∃ f : ℝ≥0 → EReal, IsSubadditive f ∧ IsFiniteOnPos f ∧ ¬ IsConcaveEReal f :=
  ⟨ceilCurve, isSubadditive_ceilCurve, isFiniteOnPos_ceilCurve,
    not_concaveE_ceilCurve⟩

/-- Subadditive does not imply concave: the implication fails on `ℝ≥0 → EReal`,
refuted by `ceilCurve` (subadditive but not concave). -/
theorem not_isSubadditive_imp_concaveE :
    ¬ ∀ f : ℝ≥0 → EReal, IsSubadditive f → IsConcaveEReal f :=
  fun h => not_concaveE_ceilCurve (h ceilCurve isSubadditive_ceilCurve)

end DeepWiki
