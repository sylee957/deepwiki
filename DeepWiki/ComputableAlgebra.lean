import DeepWiki.ComputableAlgebra.GenericPolyEngine
import DeepWiki.ComputableAlgebra.GenericBezout
import DeepWiki.ComputableAlgebra.ListDet

/-! # Computable algebra — the generic executable field & polynomial layer

Domain-general computable algebra underlying the symbolic-integration engine: the computable
field/field-spec classes and the dense-list polynomial carrier `CPoly` with its operations and
`toPolyG` denotation (`GenericPolyEngine`), the generic Bézout/resultant degree API
(`GenericBezout`), and the computable list determinant (`ListDet`). Depends only on Mathlib and
`DeepWiki.Transfer`; the `SymbolicIntegration` engine is built on top of it. -/
