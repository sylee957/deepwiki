import Book.Signatures
import Book.LevelSet
import Book.Dioids
import Book.Order
import Book.CompleteDioids
import Book.ScalarDioids
import Book.DioidFunctions
import Book.FunctionDioids
import Book.NdClosure
import Book.Additivity
import Book.Closures
import Book.Limits
import Book.Continuity
import Book.RealCurves
import Book.CurveRegularity
import Book.RealCurvesAdditivity
import Book.RealCurvesConv
import Book.RealCurvesDeconv
import Book.RealCurvesDeviations
import Book.PseudoInverse
import Book.PseudoInverseCatalog
import Book.ConvolutionMinimum
import Book.MinPlusExtTopology
import Book.ConvolutionMinimumExt
import Book.Servers
import Book.RealConvolution
import Book.Shapers

/-!
# DeepWiki — autoformalized mathematics

Aggregator module for the DeepWiki formalization: a wiki of autoformalized
mathematics, mechanized in Lean 4 with Mathlib. Importing `Book` pulls in every
chapter; all declarations live in `namespace DeepWiki`.

The first entry is the algebra of (min,plus) dioids — the theory of dioids
(idempotent semirings) and the complete (min,plus) function dioids that
underlie deterministic network calculus. The chapter list is the `import`
block above.

Notation: `⊕ = +` (dioid sum / lattice join), `⊗ = *` (product), `𝟘 = 0`,
`𝟙 = 1`, canonical order `≼ = ≤`.
-/
