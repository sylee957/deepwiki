import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-! # Best linear prediction in a Hilbert space (§2.7)
The best (mean-square) predictor of `X` from a closed subspace `M` of a Hilbert space —
e.g. `M = ` the closed span of past values in `L²` — is the orthogonal projection `P_M X`:
it lies in `M`, the prediction error `X − P_M X` is orthogonal to `M` (the **normal /
prediction equations** `⟨X − X̂, Y⟩ = 0` for all `Y ∈ M`), and `P_M X` minimizes the
mean-square error `‖X − ·‖²` over `M`. -/

namespace DeepWiki.TimeSeries

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  (M : Submodule 𝕜 E) [M.HasOrthogonalProjection] (X : E)

/-- The best predictor of `X` from a closed (prediction) subspace `M`: the orthogonal
projection `P_M X`. -/
noncomputable def bestPredictor : E := M.starProjection X

/-- The best predictor lies in the prediction subspace `M`. -/
theorem bestPredictor_mem : bestPredictor M X ∈ M := M.starProjection_apply_mem X

/-- **Prediction (normal) equations**: the error `X − X̂` is orthogonal to `M`, i.e.
`⟨X − X̂, Y⟩ = 0` for every `Y ∈ M`. -/
theorem bestPredictor_sub_mem_orthogonal : X - bestPredictor M X ∈ Mᗮ :=
  M.sub_starProjection_mem_orthogonal X

/-- **Minimum mean-square error**: the best predictor minimizes the distance `‖X − ·‖`
(equivalently the mean-square error `‖X − ·‖²`) over `M`. -/
theorem bestPredictor_minimal : ‖X - bestPredictor M X‖ = ⨅ Y : M, ‖X - (Y : E)‖ :=
  Submodule.starProjection_minimal (U := M) X

/-- The best predictor is the **unique** element of `M` whose error is orthogonal to `M`. -/
theorem bestPredictor_eq_of_mem_orthogonal {Y : E} (hY : Y ∈ M) (h : X - Y ∈ Mᗮ) :
    bestPredictor M X = Y := M.eq_starProjection_of_mem_orthogonal hY h

/-- The closed span of a family of predictors `{Xᵢ}` — the closed linear subspace they
generate. The best linear predictor of a target given `{Xᵢ}` is the projection onto this
subspace. -/
noncomputable def predictorSpan {ι : Type*} (X : ι → E) : Submodule 𝕜 E :=
  (Submodule.span 𝕜 (Set.range X)).topologicalClosure

end DeepWiki.TimeSeries
