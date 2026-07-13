import DeepWiki.CAlgebra.Poly.Dense
import DeepWiki.CAlgebra.Poly.Operations
import DeepWiki.CAlgebra.PolyBridge.Basic

/-! # CAlgebra — Hex-style computable algebra (greenfield)

Canonical-representation computable algebra: normalized dense polynomials whose Mathlib bridge is a
ring isomorphism, intrinsic `Laws` classes discharged per carrier, and an optional kernel-reducible
certificate path. Built in parallel with the legacy `DeepWiki.ComputableAlgebra` substrate; see
`docs/hex-style-algebra-rewrite.md` for the phased migration plan. -/
