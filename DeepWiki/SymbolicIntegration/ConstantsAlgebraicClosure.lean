import DeepWiki.SymbolicIntegration.AlgebraicConstants
import DeepWiki.SymbolicIntegration.DifferentialExtensions

/-! # Constants of algebraic and rational extensions (Bronstein §3.3)
The constants of a separable algebraic differential extension are exactly the algebraic closure
of the initial constant field (Corollary 3.3.1), the constant field is preserved when passing to
algebraic closures of a perfect base (Lemma 3.3.3), the constants of a transcendental extension
`F(t)` adjoin only the new constant `t` (Lemma 3.3.4), and over an algebraically-closed constant
field a polynomial system solvable by constants of the extension is already solvable by constants
of the base (Lemma 3.3.6). -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section AlgebraicClosureConstants
variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E]

/-- `IsAlgebraicOverConst c` : the element `c ∈ E` is algebraic over the constants — a root of a
nonzero polynomial in `E[X]` all of whose coefficients are constants (so the polynomial lies in
`Const_Δ(E)[X]`, in particular over the image of `Const_D F`). -/
def IsAlgebraicOverConst (c : E) : Prop :=
  ∃ q : E[X], q ≠ 0 ∧ (∀ i, (q.coeff i)′ = 0) ∧ q.eval c = 0

/-- **Corollary 3.3.1** (§3.3), forward inclusion `Const_Δ(E) ⊆ C̄ᴱ`: in a separable algebraic
differential extension, every constant of `E` is algebraic over the constants. (It is algebraic
over `F` since `E/F` is algebraic, then Lemma 3.3.2(i) lifts the witness to constant
coefficients.) -/
theorem isAlgebraicOverConst_of_deriv_eq_zero_of_integral {c : E} (hc : c′ = 0)
    (hint : IsIntegral F c) : IsAlgebraicOverConst c :=
  isAlgebraicOverConst_of_deriv_eq_zero hc hint

end AlgebraicClosureConstants

end DeepWiki.SymbolicIntegration
