import DeepWiki.ComputableAlgebra.CommRing
import DeepWiki.ComputableAlgebra.Tactic
import DeepWiki.ComputableAlgebra.Field
import DeepWiki.ComputableAlgebra.PolyRepr
import DeepWiki.ComputableAlgebra.PolyReprDense
import DeepWiki.ComputableAlgebra.PolyReprDenote
import DeepWiki.ComputableAlgebra.PolyReprDegree
import DeepWiki.ComputableAlgebra.PolyReprSparse
import DeepWiki.ComputableAlgebra.PolyReprBridge
import DeepWiki.ComputableAlgebra.PolyEngineCore
import DeepWiki.ComputableAlgebra.PolyEngineLawful
import DeepWiki.ComputableAlgebra.PolyEngineDense
import DeepWiki.ComputableAlgebra.PolyEngineSparse
import DeepWiki.ComputableAlgebra.PolyEngine
import DeepWiki.ComputableAlgebra.PolyReprConvert
import DeepWiki.ComputableAlgebra.PolyAntiderivative
import DeepWiki.ComputableAlgebra.PolyReprDivision
import DeepWiki.ComputableAlgebra.PolyReprDivisionDegree
import DeepWiki.ComputableAlgebra.PolyReprGcd
import DeepWiki.ComputableAlgebra.PolyReprResultant
import DeepWiki.ComputableAlgebra.PolyReprResultantCoprime
import DeepWiki.ComputableAlgebra.PolyResultant
import DeepWiki.ComputableAlgebra.PolyResultantDense
import DeepWiki.ComputableAlgebra.PolySubresultant
import DeepWiki.ComputableAlgebra.PolySubresultantSpec
import DeepWiki.ComputableAlgebra.PolySubresultantLawful
import DeepWiki.ComputableAlgebra.PolyEuclidean
import DeepWiki.ComputableAlgebra.PolyEuclideanDense
import DeepWiki.ComputableAlgebra.PolyGcdAlgorithms
import DeepWiki.ComputableAlgebra.PolySquarefree
import DeepWiki.ComputableAlgebra.PolyQuotient
import DeepWiki.ComputableAlgebra.PolyInterpolate
import DeepWiki.ComputableAlgebra.PolyInterpolateDense
import DeepWiki.ComputableAlgebra.PolyInterpolateSparse
import DeepWiki.ComputableAlgebra.ListDet
import DeepWiki.ComputableAlgebra.FracRepr
import DeepWiki.ComputableAlgebra.FracReprDense
import DeepWiki.ComputableAlgebra.FracReprSparse
import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.ComputableAlgebra.FractionExamples
import DeepWiki.ComputableAlgebra.FracReduce
import DeepWiki.ComputableAlgebra.LinearAlgebra
import DeepWiki.ComputableAlgebra.LinearAlgebraRat
import DeepWiki.ComputableAlgebra.LinearAlgebraRatCorrect
import DeepWiki.ComputableAlgebra.FracLinearAlgebra

/-! # Computable algebra — the generic executable field & polynomial layer

Domain-general computable algebra underlying the symbolic-integration engine: the computable
field/field-spec classes; representation-selected polynomial engines, Euclidean algorithms,
resultants, subresultants, and interpolation; the computable list determinant; and the generic
proof-carrying fraction interface `CFrac` with dense and sparse specializations.
Depends only on Mathlib and `DeepWiki.Transfer`; the `SymbolicIntegration` engine is built on top of
it. -/
