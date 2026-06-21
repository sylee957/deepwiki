import DeepWiki.TimeSeries.BestLinearPredictor
import DeepWiki.TimeSeries.DurbinLevinson
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
`φₙₙ = [γ(n) − ∑_{j<n} φ_{n-1,j} γ(n−j)] / v_{n-1}`, `v₀ = γ(0)`, `φₙⱼ = φ_{n-1,j} − φₙₙ φ_{n-1,n-j}`
(5.2.4), `vₙ = v_{n-1}(1 − φₙₙ²)` (5.2.5). **Proposition 5.2.2 (the innovations algorithm)** is the
companion recursion `X̂_{n+1} = ∑ⱼ θₙⱼ (X_{n+1-j} − X̂_{n+1-j})` (5.2.15), valid for any process with
finite second moments.

**Proposition 5.2.1 is now FORMALIZED** (`prop_5_2_1` below, `dl_correct`): the Durbin–Levinson
recursion `dl` solves the order-`n` **prediction (normal) equations** `∑ⱼ φₙⱼ γ(k−j) = γ(k)` and the
error formula `vₙ = γ(0) − ∑ⱼ φₙⱼ γ(j)`, by a joint induction — purely as Toeplitz linear algebra on
the autocovariance, needing no `L²` layer. (Identifying the normal-equations solution with the §5.1
projection coefficients additionally uses `eq_5_1_5`; the innovations algorithm **Proposition 5.2.2**
remains an unformalized algebraic recurrence.) -/

/-- **§5.2 (eqs 5.2.4–5.2.5, the Durbin–Levinson recursion)**: the prediction coefficients `φₙⱼ` and
mean-square errors `vₙ` computed from the autocovariance. The library's `dlCoeff`/`dlError`, with the
update laws `dlCoeff_succ_of_le` (`φₙⱼ = φ_{n−1,j} − φₙₙ φ_{n−1,n−j}`) and `dlError_succ`
(`vₙ = v_{n−1}(1 − φₙₙ²)`). -/
noncomputable abbrev eq_5_2_4 := @DeepWiki.TimeSeries.dlCoeff

/-- **Proposition 5.2.1 (Durbin–Levinson)**: for an even autocovariance with nonzero prediction
errors, the recursion's coefficients solve the order-`n` prediction equations
`∑_{j=1}^n φₙⱼ γ(k−j) = γ(k)` (`k = 1,…,n`) and the error has the form `vₙ = γ(0) − ∑ⱼ φₙⱼ γ(j)`.
The library's `dl_correct`. -/
alias prop_5_2_1 := DeepWiki.TimeSeries.dl_correct

/-! ## §5.3 Recursive Prediction of an ARMA(p,q) Process (pp.177–182)

Applying §5.2 to ARMA processes gives explicit predictors: **Example 5.3.1** (AR(p)):
`X̂_{n+1} = φ₁Xₙ + ⋯ + φₚX_{n+1-p}` for `n ≥ p` — the predictor is just the autoregressive
recursion, since the innovation `Z_{n+1}` is orthogonal to the past (causality). **Example 5.3.2**
(MA(q)) and **Example 5.3.3** (ARMA(1,1), `X̂_{n+1} = φXₙ + θₙ₁(Xₙ − X̂ₙ)`) use the innovations
form, and the chapter continues with `h`-step prediction (5.3.22–5.3.24). Each is a concrete
instance of the §5.1 projection; formalizing them faithfully needs the `L²` embedding of the
process, the span of its past, and the causal orthogonality `Z_{n+1} ⊥ sp{Xₛ : s ≤ n}` — the same
projection-plus-causality layer deferred above. The **Wold decomposition**
(`Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ + Vₜ`, purely-nondeterministic plus deterministic) needs closed-subspace limits
and is infra-blocked. -/

end DeepWiki.Ts
