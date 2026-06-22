/-! # Source (paper): Algorithms for Partial Fraction Decomposition and Rational Function Integration
Ellis Horowitz's paper introducing the **Horowitz–Ostrogradsky method**: it computes the rational part
of `∫ A/B` by solving a single *linear system* over `K` (no factorization of `B`), writing
`∫ A/B = C/V + ∫ D/U` with `V = gcd(B, B')` and `U = B/V` the squarefree part. The defining identity
`A = C′·U + C·W + D·V` (with `W = −V′·U/V`) is `K`-linear in the degree-bounded coefficients of `C, D`,
giving an `n×n` system (`n = deg B`) with a unique solution.

Bronstein's *Symbolic Integration I* presents this as the §2.3 `HorowitzOstrogradsky` algorithm (the
companion to Hermite reduction). The `DeepWiki.SymbolicIntegration` development formalizes the method's
denominator split, reduction identity, and linear-solve framework; this catalog points at those and
tracks the remaining nonsingularity (= operator injectivity) result. -/

namespace DeepWiki.Hor

/-- DOI of the source paper (the SYMSAC '71 version of University of Wisconsin Tech. Report #91). -/
def doi : String := "10.1145/800204.806314"

/-- Title of the source paper. -/
def title : String := "Algorithms for Partial Fraction Decomposition and Rational Function Integration"

/-- Reference of the source paper. -/
def reference : String :=
  "Proc. 2nd ACM Symp. on Symbolic and Algebraic Manipulation (SYMSAC '71), 1971, pp. 441–457"

/-- Authors of the source paper. -/
def authors : List String := ["Ellis Horowitz"]

end DeepWiki.Hor
