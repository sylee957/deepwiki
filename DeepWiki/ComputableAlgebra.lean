import DeepWiki.ComputableAlgebra.Polynomial
import DeepWiki.ComputableAlgebra.PolyRepr
import DeepWiki.ComputableAlgebra.GenericBezout
import DeepWiki.ComputableAlgebra.ListDet
import DeepWiki.ComputableAlgebra.Fraction

/-! # Computable algebra — the generic executable field & polynomial layer

Domain-general computable algebra underlying the symbolic-integration engine: the computable
field/field-spec classes and the dense-list polynomial carrier `CPoly` with its operations and
`toPoly` denotation (`GenericPolyEngine`), the generic Bézout/resultant degree API
(`GenericBezout`), the computable list determinant (`ListDet`), and the generic fraction field
`CFrac` — the differential-tower carrier — of the computable polynomial ring (`FractionField`).
Depends only on Mathlib and `DeepWiki.Transfer`; the `SymbolicIntegration` engine is built on top of
it. -/
