import DeepWiki.ComputableAlgebra.CommRing
import DeepWiki.ComputableAlgebra.Tactic
import DeepWiki.ComputableAlgebra.Field
import DeepWiki.ComputableAlgebra.PolyRepr
import DeepWiki.ComputableAlgebra.PolyReprDense
import DeepWiki.ComputableAlgebra.PolyReprDenote
import DeepWiki.ComputableAlgebra.PolyReprDegree
import DeepWiki.ComputableAlgebra.PolyReprSparse
import DeepWiki.ComputableAlgebra.PolyReprBridge
import DeepWiki.ComputableAlgebra.PolyEngine
import DeepWiki.ComputableAlgebra.PolyAntiderivative
import DeepWiki.ComputableAlgebra.PolyReprDivision
import DeepWiki.ComputableAlgebra.PolyReprDivisionDegree
import DeepWiki.ComputableAlgebra.PolyReprGcd
import DeepWiki.ComputableAlgebra.PolyReprResultant
import DeepWiki.ComputableAlgebra.PolyReprResultantCoprime
import DeepWiki.ComputableAlgebra.PolyResultant
import DeepWiki.ComputableAlgebra.PolySubresultant
import DeepWiki.ComputableAlgebra.PolyEuclidean
import DeepWiki.ComputableAlgebra.PolyGcdAlgorithms
import DeepWiki.ComputableAlgebra.PolySquarefree
import DeepWiki.ComputableAlgebra.PolyQuotient
import DeepWiki.ComputableAlgebra.GenericBezout
import DeepWiki.ComputableAlgebra.ListDet
import DeepWiki.ComputableAlgebra.FracRepr
import DeepWiki.ComputableAlgebra.FracReprDense
import DeepWiki.ComputableAlgebra.FracReprSparse
import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.ComputableAlgebra.FractionExamples
import DeepWiki.ComputableAlgebra.FracReduce
import DeepWiki.ComputableAlgebra.LinearAlgebra

/-! # Computable algebra — the generic executable field & polynomial layer

Domain-general computable algebra underlying the symbolic-integration engine: the computable
field/field-spec classes and the dense-list polynomial carrier `DensePoly` with its operations and
`toPoly` denotation (`GenericPolyEngine`), the generic Bézout/resultant degree API
(`GenericBezout`), the computable list determinant (`ListDet`), and the generic fraction field
`CFrac` — the differential-tower carrier — of the computable polynomial ring (`FractionField`).
Depends only on Mathlib and `DeepWiki.Transfer`; the `SymbolicIntegration` engine is built on top of
it. -/
