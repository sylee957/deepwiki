import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Stochastic order notation (Brockwell–Davis Definition 6.1.4)
The `oₚ`/`Oₚ` calculus for random sequences: `Xₙ = oₚ(rₙ)` when `Xₙ / rₙ → 0` in probability, and
`Xₙ = Oₚ(rₙ)` when `Xₙ / rₙ` is bounded in probability (tight). Mathlib has `TendstoInMeasure` but not
these stochastic-order predicates. -/

open MeasureTheory Filter Topology

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`Xₙ = oₚ(rₙ)`** (Definition 6.1.4): `Xₙ / rₙ → 0` in probability. -/
def IsLittleOp (X : ℕ → Ω → ℝ) (r : ℕ → ℝ) (μ : Measure Ω) : Prop :=
  TendstoInMeasure μ (fun n ω => X n ω / r n) atTop (fun _ => 0)

/-- **`Xₙ = Oₚ(rₙ)`** (Definition 6.1.4): `Xₙ / rₙ` is bounded in probability — for every `ε > 0`
there is a bound `M` with `μ {ω | M < |Xₙ ω / rₙ|} ≤ ε` for every `n`. -/
def IsBigOp (X : ℕ → Ω → ℝ) (r : ℕ → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ n : ℕ, μ {ω | M < |X n ω / r n|} ≤ ENNReal.ofReal ε

/-- `oₚ(1)` is exactly convergence to `0` in probability. -/
theorem isLittleOp_one_iff {X : ℕ → Ω → ℝ} {μ : Measure Ω} :
    IsLittleOp X (fun _ => 1) μ ↔ TendstoInMeasure μ X atTop (fun _ => 0) := by
  simp only [IsLittleOp, div_one]

end DeepWiki.TimeSeries
