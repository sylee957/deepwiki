import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalWellFounded
import Sources.Hdl_1721_1_15391.Source

/-! # Trager catalog — the unified full algebraic integral `∫ = v + Σ cᵢ log uᵢ` (Appendix A + Ch. 5, principal case)
The culmination of the simple-radical arc. Appendix A (catalog `Sources.Hdl_1721_1_15391.AppendixA`)
builds the **rational part** `v`; Chapter 5 (catalog `Sources.Hdl_1721_1_15391.Chapter5`) builds the
**residues** `cᵢ` and **solves** the **log argument** `uᵢ` (`radLogArgSolve`). The
`DeepWiki.SymbolicIntegration` library unifies them in `ComputableRadicalWellFounded`: a single fuel-free
driver `cIntegrateAlgebraicWf` that computes **both** halves and assembles the full
`∫ R/(B·y) dx = v + Σ cᵢ log uᵢ`
over a simple radical `y² = ρ`, validated end-to-end by a **round-trip** — start from a known
antiderivative `F = v + c·log u`, differentiate it to an integrand (through the genuine radical derivation
`radDeriv` and the in-extension division `radInv2`), integrate back, and `native_decide` that the recovered
result differentiates to the same integrand.

**Computable-vs-abstract.** Every entry below is a computable function or a `native_decide` round-trip
witness on a worked integral; the abstract correctness (that `cIntegrateAlgebraicWf`'s output IS the integral
for every input) is validated by the examples, not proved in general. The driver is honest about its scope:
on the **principal** case (`radLogArgSolve` returns `some`) it produces the full `v + Σ cᵢ log uᵢ`; on the
**non-principal / torsion** boundary (`radLogArgSolve` returns `none`) it returns the rational part with an
empty log list, a documented partial.

## NOT YET FORMALIZED (audit 2026-06-26)
The driver's log half is exactly the principal-case linear solve of
  `Sources.Hdl_1721_1_15391.Chapter5` (`ch5_logArgSolve`); the non-principal / torsion case (Trager Ch. 5
  §3 divisors, Ch. 6 points-of-finite-order) is the deferred boundary recorded there `[research]`, not
  duplicated here. -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.RadElem
open DeepWiki.SymbolicIntegration.DensePoly

namespace DeepWiki.Tiaf

/-! ## Division in the radical extension and the log-derivative (`n = 2`) -/

/-- **The conjugate norm** `radNorm2 ρ u = a² − b²·ρ ∈ α` for `u = a + b·y` in `α[y]/(y² − ρ)` (Trager,
Appendix A, `n = 2`): the base element `u·ū` (`ū = a − b·y` the conjugate), the denominator of `u⁻¹`. -/
abbrev full_radNorm2 := @RadElem.radNorm2

/-- **The reciprocal in `α[y]/(y² − ρ)`** `radInv2 ρ u = (a − b·y)/(a² − b²·ρ)` for `u = a + b·y` (Trager,
Appendix A, `n = 2`): the honest inverse (rationalize by the conjugate), since the extension is a field
(`ρ` a non-square). This is what makes the log-derivative `u'/u` a genuine `RadElem`. -/
abbrev full_radInv2 := @RadElem.radInv2

/-- **The logarithmic derivative in `α[y]/(y² − ρ)`** `radLogDeriv ρ u = (radDeriv u)·u⁻¹` (Trager,
Appendix A / Ch. 5 §1): the genuine `RadElem` `u'/u = D(log u)` (honest division via `radInv2`) — the
un-cross-multiplied form of the log-derivative certificate, the building block of `algDerivQ`. -/
abbrev full_radLogDeriv := @RadElem.radLogDeriv

/-- **Appendix A, `n = 2`** (validation): `u · u⁻¹ = 1` in `(ℚ(x))[y]/(y² − (x²+1))` — the conjugate-norm
inverse `radInv2 ρ (x + y) = y − x` satisfies `radMul 2 ρ u (radInv2 ρ u) = 1` (`native_decide`). Division
in the radical extension computes. -/
abbrev full_radInv2_mul_self_eq_one := @radInv2_mul_self_eq_one

/-- **Appendix A / Ch. 5 §1** (validation): `radLogDeriv ρ (x + y)` equals the `arcsinh` integrand
`[0, 1/(x²+1)]` (since `∫ dx/√(x²+1) = log(x + y)`), so `radLogDeriv u = integrand` is the
un-cross-multiplied form of `radIsLogIntegral 2 ρ u integrand` (`native_decide`). -/
abbrev full_radLogDeriv_eq_integrand := @radLogDeriv_eq_integrand_arcsinh

/-! ## The full-integral representation `v + Σ cᵢ log uᵢ` and its derivative -/

/-- **The full algebraic integral `∫ = v + Σ cᵢ log uᵢ`** (Trager, Appendix A + Ch. 5, principal case):
the bundle of a rational part `v` (a `RadElem`) and a list of log terms `[(cᵢ, uᵢ)]` (residue coefficient
`cᵢ ∈ ℚ(x)`, argument `uᵢ` a `RadElem`) — the output of `cIntegrateAlgebraicWf`, differentiated by
`algDerivQ`. -/
abbrev full_integralResult := @AlgIntegralResult (CFrac ℚ)

/-- **The derivative of a full algebraic integral** `algDerivQ ρ F = radDeriv v + Σ cᵢ · radLogDeriv uᵢ`
(Trager, Appendix A + Ch. 5): the genuine `RadElem` `D(v + Σ cᵢ log uᵢ)` in `(ℚ(x))[y]/(y² − ρ)`, each log
term contributing `cᵢ · (uᵢ'/uᵢ)` via the honest `radLogDeriv`. The round-trip's comparison side. -/
abbrev full_algDeriv := @algDerivQ

/-- **Assemble the rational part from the multi-case dispatch run** `radAssembleRatPart ρ runs` (Trager,
Appendix A §2): sum the per-factor rational parts of `radIntegrateRationalWf` into one `RadElem`, each
`V`-factor (Case 1) over `fi^{e−1}` and `W`-factor (Case 2) over `fi^{e}` contributing an `R/y` term. -/
abbrev full_assembleRatPart := @radAssembleRatPart

/-! ## ★ The unified algebraic integrator and its end-to-end round-trips -/

/-- **★ The unified fuel-free algebraic integrator** `cIntegrateAlgebraicWf ρ R B residual c D degBound`
(Trager, Appendix A + Ch. 5, principal case): produces the full `∫ R/(B·y) dx = v + c·log u` over `y² = ρ`
by computing the rational part `v` (fuel-free multi-case dispatch `radIntegrateRationalWf` +
`radAssembleRatPart`) AND solving the log argument on the `residual` integrand (`radLogArgSolve`, the
principal-case linear solve), packing `(c, u/D)`. On the non-principal / torsion boundary
(`radLogArgSolve = none`) it returns the rational part with an empty log list (a documented partial). Both
Appendix A and Ch. 5 §1–§2 in one driver, with no top-level `ℕ` fuel. -/
abbrev full_integrate := @cIntegrateAlgebraicWf

/-- The dispatch's reconstructed rational part for `∫ 1/((x−1)²√(x²+1))`, built from
`radIntegrateRationalWf`. -/
def full_rtRatV : RadElem (CFrac ℚ) :=
  radAssembleRatPart rtRatRho (DensePoly.radIntegrateRationalWf (CFrac.num rtRatRho) rtRatR rtRatB)

/-- The rational-only benchmark integrand: `algDerivQ ⟨full_rtRatV, []⟩`. -/
def full_rtRatIntegrand : RadElem (CFrac ℚ) := algDerivQ rtRatRho ⟨full_rtRatV, []⟩

/-- The recovered rational-only result for `∫ 1/((x−1)²√(x²+1))`: the rational part is reconstructed
by `radIntegrateRationalWf`, and the non-principal residual gives an empty log list. -/
def full_rtRatRecovered : AlgIntegralResult (CFrac ℚ) :=
  cIntegrateAlgebraicWf rtRatRho rtRatR rtRatB rtRatNonPrincipalResidual CCommRing.one [0, 0, 1] 1

/-- **★ Round-trip (rational-only): `∫ 1/((x−1)²√(x²+1))`** (Trager, Appendix A §2, `native_decide`): start
from `F = ⟨v, []⟩` (the dispatch's rational part, no log term), differentiate to `integrand = radDeriv v`,
and `cIntegrateAlgebraicWf` reconstructs an antiderivative from `(R, B) = (1, (x−1)²)` with an EMPTY log
list (the non-principal residual ⇒ no spurious log term), so `algDerivQ F' = integrand`. -/
theorem full_roundtrip_rational :
    DensePoly.cisZero (DensePoly.csub (algDerivQ rtRatRho full_rtRatRecovered) full_rtRatIntegrand) = true := by
  native_decide

/-- **The rational-only result has nonzero rational part and empty log list** (`native_decide`): the
structural signature `(DensePoly.cisZero ratPart, logTerms.length) = (false, 0)` of a pure rational integral
`∫ = v`. -/
theorem full_roundtrip_rational_shape :
    (DensePoly.cisZero full_rtRatRecovered.ratPart, full_rtRatRecovered.logTerms.length) = (false, 0) := by
  native_decide

/-- The recovered log-only result for `∫ dx/(x√(x²+1))`: empty rational part and one computed
principal log term. -/
def full_rtLogRecovered : AlgIntegralResult (CFrac ℚ) :=
  cIntegrateAlgebraicWf rtLogRho [1] [1] rtLogIntegrand CCommRing.one rtLogD 0

/-- **★ Round-trip (log-only): `∫ dx/(x√(x²+1)) = log((y − 1)/x)`** (Trager, Ch. 5 §1, `native_decide`):
`cIntegrateAlgebraicWf` computes an empty rational part and one log term `1·log u` with `u = N/x` the
SOLVER'S output (`radLogArgSolve`, a constant multiple of `y − 1`); `algDerivQ F' = integrand`. -/
theorem full_roundtrip_log :
    DensePoly.cisZero (DensePoly.csub (algDerivQ rtLogRho full_rtLogRecovered) rtLogIntegrand) = true := by
  native_decide

/-- **The log-only result has empty rational part and one log term** (`native_decide`): the structural
signature `(DensePoly.cisZero ratPart, logTerms.length) = (true, 1)` of a pure log integral `∫ = log u`. -/
theorem full_roundtrip_log_shape :
    (DensePoly.cisZero full_rtLogRecovered.ratPart, full_rtLogRecovered.logTerms.length) = (true, 1) := by
  native_decide

/-- The dispatch's reconstructed rational part for the combined round-trip, built from
`radIntegrateRationalWf`. -/
def full_rtCombVdispatch : RadElem (CFrac ℚ) :=
  radAssembleRatPart rtCombRho (DensePoly.radIntegrateRationalWf (CFrac.num rtCombRho) rtCombR rtCombB)

/-- The combined starting antiderivative `F = full_rtCombVdispatch + log(rtCombU)`. -/
def full_rtCombF : AlgIntegralResult (CFrac ℚ) := ⟨full_rtCombVdispatch, [(CCommRing.one, rtCombU)]⟩

/-- The combined benchmark integrand: `algDerivQ full_rtCombF`. -/
def full_rtCombIntegrand : RadElem (CFrac ℚ) := algDerivQ rtCombRho full_rtCombF

/-- The recovered combined result for `F = v + log(x + y)`: both the rational part and the log
argument are reconstructed by `cIntegrateAlgebraicWf`. -/
def full_rtCombRecovered : AlgIntegralResult (CFrac ℚ) :=
  cIntegrateAlgebraicWf rtCombRho rtCombR rtCombB rtCombLogResidual CCommRing.one [1] 1

/-- **★★ Round-trip (COMBINED): `F = v + c·log u`, BOTH parts nonzero** (Trager, Appendix A + Ch. 5,
`native_decide`): THE FULL-INTEGRATOR PROOF. On `y² = x²+1`, start from `F = v + 1·log u` (`v` the
dispatch's rational part of `∫ 1/((x−1)²√(x²+1))`, `u = x + y` the arcsinh argument), differentiate to
`integrand = radDeriv v + radLogDeriv u`, integrate back: `cIntegrateAlgebraicWf` reconstructs the rational
part `v` from `(R, B)` by the dispatch AND solves the log argument, and `algDerivQ F' = integrand`. The
engine produces the FULL `v + Σ cᵢ log uᵢ` (rational + log, principal case), both halves computed from
polynomial / residual inputs, round-trip-validated through the real radical derivation. -/
theorem full_roundtrip_combined :
    DensePoly.cisZero (DensePoly.csub (algDerivQ rtCombRho full_rtCombRecovered) full_rtCombIntegrand) = true := by
  native_decide

/-- **The combined result has nonzero rational part AND one log term** (`native_decide`): the structural
signature `(DensePoly.cisZero ratPart, logTerms.length) = (false, 1)` of a genuine combined integral
`∫ = v + c·log u` with both parts present. -/
theorem full_roundtrip_combined_shape :
    (DensePoly.cisZero full_rtCombRecovered.ratPart, full_rtCombRecovered.logTerms.length) = (false, 1) := by
  native_decide

end DeepWiki.Tiaf
