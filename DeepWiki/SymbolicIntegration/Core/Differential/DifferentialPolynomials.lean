import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

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

/-- The embedding `K[x] → DiffPoly K` sending `X` to `dpX`. -/
noncomputable def dpEmbed : Polynomial K →+* DiffPoly K :=
  Polynomial.eval₂RingHom (MvPolynomial.C : K →+* DiffPoly K) (X none)

end DeepWiki.SymbolicIntegration
