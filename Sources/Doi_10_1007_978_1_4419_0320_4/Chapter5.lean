import DeepWiki.TimeSeries.BestLinearPredictor
import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 5: Prediction of Stationary Processes
The book numbering lives here in the catalog; the citation is in each docstring, the DOI in
`Sources.Doi_10_1007_978_1_4419_0320_4.Source`. Chapter 5's time-domain prediction is the Ch2
Hilbert-projection theory applied to the closed span of past values; the §5.2+ recursive
algorithms (Durbin–Levinson, innovations) are algebraic recursions (see the notes). -/

namespace DeepWiki.Ts

open DeepWiki.TimeSeries

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  (M : Submodule 𝕜 E) [M.HasOrthogonalProjection] (X : E)

/-! ## §5.1 The Prediction Equations in the Time Domain (p.167)

The one-step predictor `X̂_{n+1} = P_{ℳₙ} X_{n+1}` (eq 5.1.3) is the orthogonal projection of
`X_{n+1}` onto the predictor subspace `ℳₙ = sp{X₁, …, Xₙ}` — exactly the best linear predictor of
Chapter 2 (`bestPredictor`, `= Submodule.starProjection`). The **prediction equations** (5.1.5)
`Γₙ φₙ = γₙ` are the normal equations: the prediction error `X_{n+1} − X̂_{n+1}` is orthogonal to
`ℳₙ`. **Proposition 5.1.1** (`γ(0) > 0` and `γ(h) → 0` imply the covariance matrix `Γₙ` is
non-singular for every `n`) is the solvability condition; its kernel form is `ex_1_17` (`Σ`
singular iff some non-trivial linear combination has zero variance). -/

/-- **§5.1 (eq 5.1.3)**: the best one-step linear predictor `X̂ = P_{ℳ} X` — the orthogonal
projection of `X` onto the predictor subspace `ℳ` (the Chapter 2 best linear predictor). The
library's `bestPredictor`. -/
noncomputable abbrev eq_5_1_3 := @DeepWiki.TimeSeries.bestPredictor

/-- **§5.1 (eq 5.1.5, the prediction equations)**: the prediction error `X − X̂` is orthogonal to
the predictor subspace `ℳ` — the normal equations `Γₙ φₙ = γₙ` in coordinate-free form. The
library's `bestPredictor_sub_mem_orthogonal`. -/
theorem eq_5_1_5 : X - bestPredictor M X ∈ Mᗮ :=
  bestPredictor_sub_mem_orthogonal M X

/-- **§5.1**: the best linear predictor minimizes the mean-square prediction error
`‖X − ·‖` (eq 5.2.2, `vₙ = E‖X_{n+1} − X̂_{n+1}‖²`) over the predictor subspace `ℳ`. The library's
`bestPredictor_minimal`. -/
theorem prediction_mse_minimal :
    ‖X - bestPredictor M X‖ = ⨅ Y : M, ‖X - (Y : E)‖ :=
  bestPredictor_minimal M X

/-! ## §5.2 Recursive Methods for Computing Best Linear Predictors (p.169)

**Proposition 5.2.1 (the Durbin–Levinson algorithm)** computes the prediction coefficients `φₙⱼ`
and the mean-square errors `vₙ = E‖X_{n+1} − X̂_{n+1}‖²` by the recursion
`φₙₙ = [γ(n) − ∑_{j<n} φ_{n-1,j} γ(n−j)] / v_{n-1}`, `v₀ = γ(0)`, with the **innovations algorithm**
as the companion recursion (§5.3). These are algebraic recurrences (definable as recursive
functions over `ℕ`); proving they compute the §5.1 projection requires the Hilbert-projection
theory plus induction on `n`, and is deferred. The **Wold decomposition** (`Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ + Vₜ`,
deterministic-plus-purely-nondeterministic) needs closed-subspace limits and is infra-blocked. -/

end DeepWiki.Ts
