import DeepWiki.SymbolicIntegration.MonomialExtensions
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import Mathlib.FieldTheory.RatFunc.Basic

/-! # The canonical representation (Bronstein §3.5)
For a monomial extension `(k(t), D)` with `Dt = v ∈ k[t]`, every `f ∈ k(t)` splits *uniquely* as
`f = fₚ + fₛ + fₙ` — a polynomial part `fₚ`, a *reduced* (special-denominator) part `fₛ ∈ k⟨t⟩`,
and a *simple* (normal-denominator) part `fₙ`. We give the classifying predicates (`IsSimple`,
`IsReduced`), the splitting-factorization routine `splitFactor` that separates the special and
normal parts of a polynomial denominator, the squarefree variant `splitSquarefreeFactor` built on
Yun's factorization, the `canonicalRepresentation` of a rational function, and the root
characterization (a splitting factor `pₛ`/`pₙ` collects the constant/nonconstant roots). The
derivation on `k[X]` is the monomial derivation `implicitDeriv v` (`Dt = v`). -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

end DeepWiki.SymbolicIntegration
