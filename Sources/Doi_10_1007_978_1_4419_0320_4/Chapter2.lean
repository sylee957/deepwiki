import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
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

end DeepWiki.Ts


