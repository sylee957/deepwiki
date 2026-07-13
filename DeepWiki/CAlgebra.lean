import DeepWiki.CAlgebra.Matrix.Dense
import DeepWiki.CAlgebra.Matrix.Sylvester
import DeepWiki.CAlgebra.Matrix.Resultant
import DeepWiki.CAlgebra.Poly.Dense
import DeepWiki.CAlgebra.Poly.Operations
import DeepWiki.CAlgebra.Poly.Euclid
import DeepWiki.CAlgebra.Poly.Tower
import DeepWiki.CAlgebra.Poly.Derivative
import DeepWiki.CAlgebra.PolyBridge.Basic
import DeepWiki.CAlgebra.PolyBridge.Ring
import DeepWiki.CAlgebra.Frac.Dense
import DeepWiki.CAlgebra.Frac.Arithmetic
import DeepWiki.CAlgebra.Frac.Additive
import DeepWiki.CAlgebra.FracBridge.Basic
import DeepWiki.CAlgebra.Diff.DifferentialRing
import DeepWiki.CAlgebra.Diff.DifferentialBridge
import DeepWiki.CAlgebra.Frac.Additive
import DeepWiki.CAlgebra.PolyBridge.Euclid

/-! # CAlgebra — Hex-style computable algebra (greenfield)

Canonical-representation computable algebra: normalized dense polynomials whose Mathlib bridge is a
ring isomorphism, intrinsic `Laws` classes discharged per carrier, and an optional kernel-reducible
certificate path. Built in parallel with the legacy `DeepWiki.ComputableAlgebra` substrate; see
`docs/hex-style-algebra-rewrite.md` for the phased migration plan. -/
