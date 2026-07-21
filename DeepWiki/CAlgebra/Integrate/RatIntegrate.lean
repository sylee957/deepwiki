import DeepWiki.CAlgebra.Integrate.LogPart

/-! # The full rational integral, bundled

`ratIntegrate` runs the whole pipeline — Hermite reduction, polynomial integration, and
the Lazard–Rioboo–Trager log stage — into one computable record:
`∫ f = rational + ∫poly + ∑ᵢ ∑_{Qᵢ(α)=0} α · log Sᵢ(α, x)`. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R] [CharZero R] [DensePolyGcd R]
  [DensePolySquarefree R]

/-- **Rational integration**: Hermite-reduce, integrate the polynomial part, and run the
LRT log stage. -/
def ratIntegrate (f : DenseFrac R) : ResultRatIntegral R where
  rational := (hermiteReduce f).rational
  poly := polyIntegrate (hermiteReduce f).poly
  logs := lrtIntegrate (hermiteReduce f).logPart

/-- The bundled rational part is Hermite's. -/
theorem ratIntegrate_rational (f : DenseFrac R) :
    (ratIntegrate f).rational = (hermiteReduce f).rational := rfl

/-- The bundled polynomial part is the integrated Hermite polynomial part. -/
theorem ratIntegrate_poly (f : DenseFrac R) :
    (ratIntegrate f).poly = polyIntegrate (hermiteReduce f).poly := rfl

/-- The bundled log data is the LRT stage of Hermite's log part. -/
theorem ratIntegrate_logs (f : DenseFrac R) :
    (ratIntegrate f).logs = lrtIntegrate (hermiteReduce f).logPart := rfl

end DensePoly

end DeepWiki.CAlgebra
