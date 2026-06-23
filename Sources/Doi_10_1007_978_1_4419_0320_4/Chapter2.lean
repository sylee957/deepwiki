import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import DeepWiki.TimeSeries.BestLinearPredictor
import DeepWiki.TimeSeries.LeastSquares
import Sources.Doi_10_1007_978_1_4419_0320_4.Source

/-! # Time Series catalog — Chapter 2: Hilbert Spaces
Each numbered item of the book's Chapter 2 is one declaration named by its book number.
§2.1–§2.6 are the standard inner-product- and Hilbert-space theory and point to Mathlib;
§2.7 (best linear prediction) is the substantive time-series application. The book numbering
lives here in the catalog; the citation (section, page) is in each docstring, the source's
DOI in `Sources.Doi_10_1007_978_1_4419_0320_4.Source`. -/

namespace DeepWiki.Ts

/-! ## §2.1 Inner-Product Spaces and Their Properties -/

/-- **Definition 2.1.1** (§2.1, p.42), an inner-product space: a (complex) vector space `ℋ`
equipped with an inner product `⟨x,y⟩` that is conjugate-symmetric `⟨x,y⟩ = conj⟨y,x⟩`,
additive and homogeneous in the first argument, and positive-definite (`⟨x,x⟩ ≥ 0`, `= 0`
iff `x = 0`). Mathlib's `InnerProductSpace`. -/
abbrev def_2_1_1 := @InnerProductSpace

/-- **Example 2.1.1** (§2.1, p.43), Euclidean space `ℝⁿ` (`⟨x,y⟩ = ∑ xⱼyⱼ`, 2.1.1) and `ℂᵏ`
(`⟨x,y⟩ = ∑ xⱼ ȳⱼ`, 2.1.2). Mathlib's `EuclideanSpace`. -/
abbrev ex_2_1_1 := @EuclideanSpace

/-- **Definition 2.1.2** (§2.1, p.43), the norm `‖x‖ = √⟨x,x⟩` (2.1.3) induced by the inner
product. Mathlib's `norm_eq_sqrt_re_inner` (`‖x‖ = √(re⟨x,x⟩)`). -/
alias def_2_1_2 := norm_eq_sqrt_re_inner

/-- **The Cauchy–Schwarz inequality** (§2.1, p.43, eq 2.1.4): `|⟨x,y⟩| ≤ ‖x‖ ‖y‖`. Mathlib's
`norm_inner_le_norm`. -/
alias eq_2_1_4 := norm_inner_le_norm

/-- **The triangle inequality** (§2.1, p.44, eq 2.1.8): `‖x + y‖ ≤ ‖x‖ + ‖y‖`. Mathlib's
`norm_add_le`. -/
alias eq_2_1_8 := norm_add_le

/-- **Proposition 2.1.1** (§2.1, p.45), properties of the norm: `‖x‖ ≥ 0`, `‖a·x‖ = |a|‖x‖`,
and `‖x‖ = 0 ⟺ x = 0`. Mathlib's `norm_nonneg`, `norm_smul`, `norm_eq_zero`. -/
theorem prop_2_1_1 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (a : 𝕜) (x : E) : 0 ≤ ‖x‖ ∧ ‖a • x‖ = ‖a‖ * ‖x‖ ∧ (‖x‖ = 0 ↔ x = 0) :=
  ⟨norm_nonneg x, norm_smul a x, norm_eq_zero⟩

/-- **The parallelogram law** (§2.1, p.45, eq 2.1.9): `‖x+y‖² + ‖x−y‖² = 2(‖x‖² + ‖y‖²)`.
Mathlib's `parallelogram_law_with_norm`. -/
alias eq_2_1_9 := parallelogram_law_with_norm

/-- **Proposition 2.1.2** (§2.1, p.45), continuity of the inner product: `(x,y) ↦ ⟨x,y⟩` is
continuous, so `xₙ → x` and `yₙ → y` give `⟨xₙ,yₙ⟩ → ⟨x,y⟩`. Mathlib's `continuous_inner`. -/
alias prop_2_1_2 := continuous_inner

/-! ## §2.2 Hilbert Spaces -/

/-- **Definition 2.2.1** (§2.2, p.46), a Cauchy sequence: `‖xₙ − xₘ‖ → 0` as `m, n → ∞`.
Mathlib's `CauchySeq`. -/
abbrev def_2_2_1 := @CauchySeq

/-- **Definition 2.2.2** (§2.2, p.46), a Hilbert space: an inner-product space that is
complete (every Cauchy sequence converges). Mathlib models it as the pair of instances
`[InnerProductSpace 𝕜 E] [CompleteSpace E]`; completeness is `CompleteSpace`. -/
abbrev def_2_2_2 := @CompleteSpace

/-- **Example 2.2.2** (§2.2, p.46–47), the space `L²(Ω,ℱ,P)` of square-integrable random
variables with inner product `⟨X,Y⟩ = E(XY)` (2.2.1) — the central Hilbert space of time
series (mean-square convergence is `L²`-norm convergence). Mathlib's `MeasureTheory.Lp` with
`p = 2` (an `InnerProductSpace`, complete by Riesz–Fischer). -/
abbrev ex_2_2_2 := @MeasureTheory.Lp

/-! ## §2.3 The Projection Theorem -/

/-- **Definition 2.3.1** (§2.3, p.50), a closed subspace of a Hilbert space: a linear
subspace containing all of its limit points. Mathlib's `ClosedSubmodule` (a `Submodule`
that is topologically closed). -/
abbrev def_2_3_1 := @ClosedSubmodule

/-- **Definition 2.3.2** (§2.3, p.50), the orthogonal complement
`ℳ⊥ = {x : ⟨x,y⟩ = 0 for all y ∈ ℳ}` (2.3.4). Mathlib's `Submodule.orthogonal` (`Kᗮ`). -/
abbrev def_2_3_2 := @Submodule.orthogonal

/-- **Proposition 2.3.1** (§2.3, p.50): the orthogonal complement `ℳ⊥` of any subset is a
closed subspace. Mathlib's `Submodule.isClosed_orthogonal`. -/
alias prop_2_3_1 := Submodule.isClosed_orthogonal

/-- **Theorem 2.3.1** (The Projection Theorem, §2.3, p.51): for a closed subspace `K` of a
Hilbert space and any `x`, the orthogonal projection `x̂ = K.starProjection x` is the unique
element of `K` minimizing the distance `‖x − ·‖` (2.3.5), characterized by `(x − x̂) ⊥ K`.
The library's `Submodule.starProjection` with `starProjection_apply_mem` (`x̂ ∈ K`),
`starProjection_minimal` (2.3.5), `sub_starProjection_mem_orthogonal` (orthogonality), and
`eq_starProjection_of_mem_orthogonal` (uniqueness). -/
theorem thm_2_3_1 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (x : E) :
    K.starProjection x ∈ K ∧
      ‖x - K.starProjection x‖ = ⨅ y : K, ‖x - (y : E)‖ ∧
      x - K.starProjection x ∈ Kᗮ ∧
      ∀ y ∈ K, x - y ∈ Kᗮ → K.starProjection x = y :=
  ⟨K.starProjection_apply_mem x, Submodule.starProjection_minimal (U := K) x,
    K.sub_starProjection_mem_orthogonal x,
    fun _ hy hyo => K.eq_starProjection_of_mem_orthogonal hy hyo⟩

/-- **The Prediction Equations** (§2.3, p.53, eq 2.3.8): the best approximation `x̂` to `x`
in a closed subspace `ℳ` is characterized by `(x − x̂) ⊥ ℳ` — `⟨x − x̂, y⟩ = 0` for all
`y ∈ ℳ`. The library's `bestPredictor_sub_mem_orthogonal`. -/
alias eq_2_3_8 := DeepWiki.TimeSeries.bestPredictor_sub_mem_orthogonal

/-- **Example 2.3.3** (§2.3, p.53), minimum-mean-square-error linear prediction of a
stationary process: the best linear predictor of `X` from a closed subspace `ℳ` (e.g.
`ℳ = sp̄{X₁,…,Xₙ}`, `predictorSpan`) is the orthogonal projection `X̂ = bestPredictor ℳ X`,
which minimizes `E(X − ·)² = ‖X − ·‖²` (`bestPredictor_minimal`) and solves the prediction
equations (`bestPredictor_sub_mem_orthogonal`). The library's `bestPredictor`. -/
noncomputable abbrev ex_2_3_3 := @DeepWiki.TimeSeries.bestPredictor

/-! ## §2.4 Orthonormal Sets -/

/-- **Definition 2.4.1** (§2.4, p.54), the closed span `sp̄{xₜ, t ∈ T}` of a family: the
smallest closed subspace containing every `xₜ`, i.e. `(span 𝕜 (range x)).topologicalClosure`.
The library's `predictorSpan` (the closed span onto which the best linear predictor projects). -/
noncomputable abbrev def_2_4_1 := @DeepWiki.TimeSeries.predictorSpan

/-- **Definition 2.4.2** (§2.4, p.55), an orthonormal set `{eₜ}`: `⟨eₛ,eₜ⟩ = 1` if `s = t`
and `0` otherwise (2.4.3). Mathlib's `Orthonormal`. -/
abbrev def_2_4_2 := @Orthonormal

/-- **Corollary 2.4.1** (Bessel's inequality, §2.4, p.56, eq 2.4.8): for an orthonormal set
`{eᵢ}` and any `x`, `∑ᵢ |⟨x,eᵢ⟩|² ≤ ‖x‖²`. Mathlib's `Orthonormal.sum_inner_products_le`. -/
alias cor_2_4_1 := Orthonormal.sum_inner_products_le

/-- **Theorem 2.4.1** (§2.4, p.55, eq 2.4.4): the orthogonal projection onto the span of a
finite orthonormal basis `{eᵢ}` is `P x = ∑ᵢ ⟨x,eᵢ⟩ eᵢ`. Mathlib's
`OrthonormalBasis.orthogonalProjectionOnto_apply_eq_sum`. -/
alias thm_2_4_1 := OrthonormalBasis.orthogonalProjectionOnto_apply_eq_sum

/-- **Definition 2.4.3** (§2.4, p.56), a complete orthonormal set (orthonormal basis): an
orthonormal set whose closed span is all of `ℋ`. Mathlib's `OrthonormalBasis`. -/
abbrev def_2_4_3 := @OrthonormalBasis

/-- **Definition 2.4.4** (§2.4, p.56), separability: `ℋ` has a countable complete orthonormal
set (equivalently a countable dense subset). Mathlib's `TopologicalSpace.SeparableSpace`. -/
abbrev def_2_4_4 := @TopologicalSpace.SeparableSpace

/-- **Theorem 2.4.2 / Parseval's identity** (§2.4, p.57, eq 2.4.10): for a complete
orthonormal set `{eᵢ}`, `⟨x,y⟩ = ∑ᵢ ⟨x,eᵢ⟩⟨eᵢ,y⟩` (so `‖x‖² = ∑ᵢ |⟨x,eᵢ⟩|²`). Mathlib's
`OrthonormalBasis.sum_inner_mul_inner`. -/
alias thm_2_4_2 := OrthonormalBasis.sum_inner_mul_inner

/-! ## §2.5 Projection in ℝⁿ -/

/-- **§2.5** (p.58), the Gram–Schmidt orthogonalization procedure: it converts a sequence
into an orthogonal/orthonormal one with the same closed span (so every finite-dimensional
subspace has an orthonormal basis). Mathlib's `gramSchmidt` (and `gramSchmidtOrthonormalBasis`). -/
noncomputable abbrev gramSchmidtProcedure := @InnerProductSpace.gramSchmidt

/-- **Theorem 2.5.2** (§2.5, p.59): a matrix/operator `M` is an (orthogonal) projection iff
it is symmetric and idempotent, `Mᵀ = M ∧ M² = M`. Mathlib's `isStarProjection_iff`
(`IsStarProjection ↔ IsIdempotentElem ∧ IsSelfAdjoint`). -/
alias thm_2_5_2 := isStarProjection_iff

/-- **Theorem 2.5.1** (§2.5, p.58), the least-squares **normal equations** `XᵀX β = Xᵀx`: when `β`
solves them, the residual `x − Xβ` is orthogonal to the column space of `X`, so `Xβ` is the
least-squares projection of `x` onto `col(X)`. The library's `residual_orthogonal_of_normalEquations`
(the characterization; the explicit closed form `P_ℳ = X(XᵀX)⁻¹Xᵀ` needs full-rank invertibility). -/
alias thm_2_5_1 := DeepWiki.TimeSeries.residual_orthogonal_of_normalEquations

/-! ## §2.2 (deferred item) -/

/-- **Proposition 2.2.1** (§2.2, p.48), the Cauchy criterion: in a Hilbert space (complete),
every Cauchy sequence converges. Mathlib's `cauchySeq_tendsto_of_complete`. -/
alias prop_2_2_1 := cauchySeq_tendsto_of_complete

/-- **Example 2.2.1** (§2.2, p.46), Euclidean space `ℝⁿ` is complete, hence a Hilbert space. -/
theorem ex_2_2_1 (n : ℕ) : CompleteSpace (EuclideanSpace ℝ (Fin n)) := inferInstance

/-! ## §2.6 Linear Regression and the General Linear Model -/

/-- **Equation (2.6.5)** (§2.6, p.61), the normal equations `XᵀX θ̂ = Xᵀy` of the general
linear model `y = Xθ + ε`: the least-squares fit `ŷ = Xθ̂` is the orthogonal projection of
`y` onto the column space of `X`, characterized by the residual `y − ŷ` being orthogonal to
that subspace — the prediction equations (§2.3) at `ℳ = col(X)`. So §2.6 is the regression
application of the projection theorem; the library's `bestPredictor_sub_mem_orthogonal`. -/
alias eq_2_6_5 := DeepWiki.TimeSeries.bestPredictor_sub_mem_orthogonal

/-! ## NOT YET FORMALIZED (audit 2026-06-21; subtractive — delete each item once it is formalized)
§2.5: Theorem 2.5.1 explicit closed form `P_ℳ = X(XᵀX)⁻¹Xᵀ` (needs the full-rank invertibility of
`XᵀX`) [deferred] — the normal-equations characterization `XᵀX β = Xᵀx ⇒ residual ⊥ col(X)` is done
(`thm_2_5_1`)
(§2.1–§2.4 and §2.6 are formalized.) -/

end DeepWiki.Ts


