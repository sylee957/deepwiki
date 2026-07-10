import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.SymbolicIntegration.Compute.Hermite

/-! # Computable fraction correctness

Fraction correctness now lives with the `CFrac` interface in `ComputableAlgebra.Fraction`. This module
remains as the stable import point for the compute namespace; unchecked numerator/denominator pairs are
handled only at explicit algorithm boundaries.
-/
