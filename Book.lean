import Book.Signatures
import Book.LevelSet
import Book.Dioids
import Book.Order
import Book.CompleteDioids
import Book.SubDioid
import Book.ScalarDioids
import Book.DioidFunctions
import Book.FunctionDioids
import Book.ClosuresNd
import Book.Additivity
import Book.Deconvolution
import Book.Closures
import Book.Limits
import Book.Continuity
import Book.ContinuityClosure
import Book.Concave
import Book.RealCurves
import Book.RealCurvesRegularity
import Book.RealCurvesAdditivity
import Book.RealCurvesConv
import Book.RealCurvesDeconv
import Book.Deviations
import Book.DeviationsComposition
import Book.RealCurvesDeviations
import Book.PseudoInverse
import Book.PseudoInverseCatalog
import Book.DeviationsPseudoInverse
import Book.DeviationsContinuity
import Book.ConvolutionMinimum
import Book.MinPlusExtTopology
import Book.MaxPlusExtTopology
import Book.ConvolutionMinimumExt
import Book.ConvolutionMinimumRC
import Book.ConvolutionContinuity
import Book.ClosuresEReal
import Book.CurveDioidEReal
import Book.ConcaveProps
import Book.ConcaveDioid
import Book.ConcaveSubadditive
import Book.Servers
import Book.ClosuresReal
import Book.ArrivalCurves
import Book.ArrivalCurvesMaximal
import Book.ArrivalCurvesMinimal
import Book.ArrivalCurvesCombined
import Book.DeviationsBounds
import Book.ServiceCurveMinimal
import Book.DeviationsBoundsServer
import Book.DeviationsRestricted
import Book.ServersBacklog
import Book.ServiceCurveStrict
import Book.ServiceCurveStrictMinimal
import Book.ServiceCurvePackets
import Book.ServiceCurveMaximal
import Book.ServersConcatenation
import Book.ServersConcatenationStrict
import Book.ServiceCurveStrictTandem
import Book.ServersControlTandem
import Book.ServersControlFeedback
import Book.ServersControlFeedbackWindow
import Book.ArrivalCurvesShaper
import Book.ArrivalCurvesShaperGreedy
import Book.ArrivalCurvesOutput
import Book.DeviationsBoundsTight
import Book.DeviationsCompositionTight
import Book.ServersJitter
import Book.ServersRate
import Book.ArrivalCurvesPeriodic
import Book.ArrivalCurvesAggregate
import Book.ServersMimo
import Book.ServersResidual
import Book.ServersResidualFifo

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
