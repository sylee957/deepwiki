import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
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

end DeepWiki.Ts


