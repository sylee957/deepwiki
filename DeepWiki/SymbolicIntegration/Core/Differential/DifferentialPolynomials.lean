import Mathlib.Algebra.MvPolynomial.Basic

/-! # Differential polynomials

Formal polynomial expressions in a base variable and derivative variables. -/

namespace DeepWiki.SymbolicIntegration

open MvPolynomial

variable {K : Type*} [Field K]

/-- The differential-variable polynomial ring with `X none` for `x` and `X (some n)` for `u^(n)`. -/
abbrev DiffPoly (K : Type*) [Field K] : Type _ := MvPolynomial (Option ℕ) K

/-- The base variable `x = X none` in `DiffPoly K`. -/
noncomputable abbrev dpX : DiffPoly K := X none

/-- The `n`-th derivative variable `u^(n) = X (some n)` in `DiffPoly K`. -/
noncomputable abbrev dpU (n : ℕ) : DiffPoly K := X (some n)

end DeepWiki.SymbolicIntegration
