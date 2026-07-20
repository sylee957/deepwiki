import DeepWiki.CAlgebra.Gcd.Subresultant
import DeepWiki.CAlgebra.Gcd.Dense

/-! # Gcd of dense polynomials — area aggregator

The subresultant-PRS algorithm (`Gcd/Subresultant`) and the algorithm-selection interface
`DensePolyGcd` with its per-carrier instances (`Gcd/Dense`); the Euclidean algorithm is Mathlib's
generic `EuclideanDomain.gcd` through the computable instance in `Poly/Euclid`. -/
