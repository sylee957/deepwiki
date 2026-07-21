import DeepWiki.CAlgebra.Frac.Basic
import DeepWiki.Algebra.RatFuncProper

/-! # The integral result types

The computable records produced by the integration pipeline, collected: the Hermite
output (`ResultHermite`), the Lazard–Rioboo–Trager `RootSum` log data (`ResultLrt`), and
the full rational integral (`ResultRatIntegral`). The stage algorithms producing them live with
their stages (`Hermite`, `LogPart`, `RatIntegrate`); the invariant fields carried here
are each stage's export contract. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R]

/-- Bundled Hermite output: `f = rational′ + poly + logPart`, with the log part **proper**
and its canonical (monic, coprime) denominator additionally **squarefree** — the input
contract of the logarithmic stage, carried as invariants rather than side theorems. -/
structure ResultHermite (R : Type u) [Field R] [DecidableEq R] where
  /-- The integrated rational part `G`; its derivative is its contribution. -/
  rational : DenseFrac R
  /-- The polynomial part. -/
  poly : DensePoly R
  /-- The remaining fraction, destined for the logarithmic stage. -/
  logPart : DenseFrac R
  /-- The log part's denominator is squarefree. -/
  logPart_den_squarefree : Squarefree logPart.den.toPoly
  /-- The log part is proper. -/
  logPart_isProper : RatFunc.IsProper (DenseFrac.toRatFunc logPart)

/-- Bundled Lazard–Rioboo–Trager output for a canonical fraction: the computable
`RootSum` data of the logarithmic integral — pairs `(Qᵢ, Sᵢ)` meaning
`∫ = ∑ᵢ ∑_{Qᵢ(α)=0} α · log Sᵢ(α, x)` — with the factor contract carried as an
invariant. -/
structure ResultLrt (R : Type u) [Field R] [DecidableEq R] where
  /-- The log-term pairs `(Qᵢ, Sᵢ)`. -/
  terms : List (DensePoly R × DensePoly (DensePoly R))
  /-- Every `Qᵢ` is squarefree and nonconstant. -/
  fst_squarefree : ∀ t ∈ terms, Squarefree t.1 ∧ 1 < t.1.size

/-- The full rational integral as computable data: the Hermite rational part, the
integrated polynomial part, and the `RootSum` log data. -/
structure ResultRatIntegral (R : Type u) [Field R] [DecidableEq R] where
  /-- The rational part of the antiderivative (Hermite). -/
  rational : DenseFrac R
  /-- The integrated polynomial part. -/
  poly : DensePoly R
  /-- The logarithmic part, as `RootSum` data. -/
  logs : ResultLrt R

end DensePoly

end DeepWiki.CAlgebra
