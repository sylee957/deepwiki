import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BoundedReduction.Combination
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BoundedReduction.SortedLeading
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BoundedReduction.Representation
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BoundedReduction.DescentStep

/-! # Bounded reductions for bivariate Gröbner bases

Lexicographic Gröbner reduction of a bivariate ideal member can be represented using
only basis elements with bounded `y`-degree, and divisibility hypotheses propagate
through such bounded representations. -/
