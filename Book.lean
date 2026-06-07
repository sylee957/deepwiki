import Book.Signatures
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
import Book.RealCurvesAdditivity
import Book.RealCurvesConv
import Book.RealCurvesDeconv
import Book.RealCurvesDeviations
import Book.ConvolutionMinimum
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
underlie deterministic network calculus. Chapters:

- `Signatures`, `Dioids`, `Order` — the abstract algebraic tower, the dioid,
  the canonical order and isotony.
- `CompleteDioids` — complete dioids with lower semi-continuity, residuation.
- `ScalarDioids` — the carriers `MinPlus`, `MinPlusNN`, `MinPlusExt` and the
  (max,plus) duals.
- `DioidFunctions`, `FunctionDioids` — the convolution and the function dioid.
- `Additivity` — sub- and super-additivity predicates.
- `Closures` — the Kleene star and sub-additive closure.
- `Limits`, `Continuity` — right limits, left- and lower semi-continuity.
- `RealCurves`, `RealCurvesAdditivity`, `RealCurvesConv`, `RealCurvesDeconv`,
  `RealCurvesDeviations` — concrete network-calculus curves (delay, rate,
  rate-latency, token bucket), their regularity, additivity/closures,
  convolutions, deconvolutions, and horizontal/vertical deviations.
- `ConvolutionMinimum` — the convolution attains its minimum.
- `Servers`, `RealConvolution`, `Shapers` — service curves, real convolution,
  and greedy shapers.

Notation: `⊕ = +` (dioid sum / lattice join), `⊗ = *` (product), `𝟘 = 0`,
`𝟙 = 1`, canonical order `≼ = ≤`.
-/
