import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! # The linear process `Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ` (§3.1, §3.2)
The general linear process / `MA(∞)` representation, built as a convergent series in the Banach
space `L²(μ)`: for an absolutely summable filter `∑ⱼ |ψⱼ| < ∞` driving a uniformly `L²`-bounded
sequence `Z` (e.g. white noise), the series `∑ⱼ ψⱼ Zₜ₋ⱼ` converges in mean square. This is the
object underlying causality (Thm 3.1.1), the `MA(∞)` processes (§3.2), and the ARMA autocovariance
(§3.3). -/

namespace DeepWiki.TimeSeries

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The summand `ψⱼ • Zₜ₋ⱼ` of the linear process is **absolutely summable** in `L²(μ)` when the
filter is summable (`∑ⱼ |ψⱼ| < ∞`) and the driving sequence is uniformly bounded in `L²`
(`‖Zₜ‖ ≤ C`): then `∑ⱼ ‖ψⱼ Zₜ₋ⱼ‖ ≤ C ∑ⱼ |ψⱼ| < ∞`. -/
theorem summable_lagSmul {ψ : ℤ → ℝ} (hψ : Summable ψ) {Z : ℤ → Lp ℝ 2 μ} {C : ℝ}
    (hZ : ∀ t, ‖Z t‖ ≤ C) (t : ℤ) :
    Summable (fun j : ℤ => ψ j • Z (t - j)) := by
  refine Summable.of_norm_bounded (g := fun j => |ψ j| * C)
    ((summable_abs_iff.mpr hψ).mul_right C) (fun j => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hZ (t - j)) (abs_nonneg _)

/-- **§3.1–§3.2: the linear process** `Xₜ = ∑_{j∈ℤ} ψⱼ Zₜ₋ⱼ`, defined as the `L²(μ)` limit (the
`tsum` in the Banach space `Lp ℝ 2 μ`) of the absolutely summable series `∑ⱼ ψⱼ Zₜ₋ⱼ`. With a
filter supported on `j ≥ 0` this is the causal `MA(∞)` representation (Definition 3.2.1). -/
noncomputable def linearProcessLp (ψ : ℤ → ℝ) (Z : ℤ → Lp ℝ 2 μ) (t : ℤ) : Lp ℝ 2 μ :=
  ∑' j : ℤ, ψ j • Z (t - j)

/-- The partial sums of the linear process converge to it in `L²` — `HasSum (ψ· • Zₜ₋·) Xₜ`. -/
theorem hasSum_linearProcessLp {ψ : ℤ → ℝ} (hψ : Summable ψ) {Z : ℤ → Lp ℝ 2 μ} {C : ℝ}
    (hZ : ∀ t, ‖Z t‖ ≤ C) (t : ℤ) :
    HasSum (fun j : ℤ => ψ j • Z (t - j)) (linearProcessLp ψ Z t) :=
  (summable_lagSmul hψ hZ t).hasSum

/-! ## Inner product through a convergent series (for the L² autocovariance) -/

/-- The `L²` inner product passes through a convergent series in the right argument:
`⟪x, ∑ⱼ fⱼ⟫ = ∑ⱼ ⟪x, fⱼ⟫` (`⟪x, ·⟫` is the continuous linear functional `innerSL ℝ x`). -/
theorem hasSum_inner_right {f : ℤ → Lp ℝ 2 μ} {a : Lp ℝ 2 μ} (x : Lp ℝ 2 μ) (hf : HasSum f a) :
    HasSum (fun j => (inner ℝ x (f j) : ℝ)) (inner ℝ x a) := by
  simpa only [coe_innerSL_apply] using (innerSL ℝ x).hasSum hf

/-- The `L²` inner product passes through a convergent series in the left argument:
`⟪∑ⱼ fⱼ, y⟫ = ∑ⱼ ⟪fⱼ, y⟫` (via the right version and symmetry of the real inner product). -/
theorem hasSum_inner_left {f : ℤ → Lp ℝ 2 μ} {a : Lp ℝ 2 μ} (y : Lp ℝ 2 μ) (hf : HasSum f a) :
    HasSum (fun j => (inner ℝ (f j) y : ℝ)) (inner ℝ a y) := by
  have h := hasSum_inner_right y hf
  have e : (fun j => (inner ℝ (f j) y : ℝ)) = (fun j => inner ℝ y (f j)) :=
    funext fun j => real_inner_comm y (f j)
  rw [e, real_inner_comm y a]
  exact h

end DeepWiki.TimeSeries
