import DeepWiki.CAlgebra.Poly.Dense
import DeepWiki.CAlgebra.Poly.Operations
import DeepWiki.CAlgebra.Poly.Division
import DeepWiki.CAlgebra.Poly.DivisionPseudo
import DeepWiki.CAlgebra.Poly.Euclid
import DeepWiki.CAlgebra.Poly.Monic
import DeepWiki.CAlgebra.Gcd
import DeepWiki.CAlgebra.Poly.Derivative
import DeepWiki.CAlgebra.Matrix.Dense
import DeepWiki.CAlgebra.Matrix.Sylvester
import DeepWiki.CAlgebra.Frac.Basic
import DeepWiki.CAlgebra.Frac.Field
import DeepWiki.CAlgebra.Diff.Basic
import DeepWiki.CAlgebra.Test.Computable

/-! # CAlgebra — Hex-style computable algebra (greenfield)

Canonical-representation computable algebra: normalized dense polynomials whose Mathlib bridge is a
ring isomorphism. Each concept module holds its computable defs *and* their Mathlib correspondence
together (no separate `*Bridge/` split); see `docs/hex-style-algebra-rewrite.md` for the plan. -/
