import DeepWiki.SymbolicIntegration.ComputableRadicalIntegrateFull
import Sources.Hdl_1721_1_15391.Source

/-! # Trager catalog — the unified full algebraic integral `∫ = v + Σ cᵢ log uᵢ` (Appendix A + Ch. 5, principal case)
The culmination of the simple-radical arc. Appendix A (catalog `Sources.Hdl_1721_1_15391.AppendixA`)
builds the **rational part** `v`; Chapter 5 (catalog `Sources.Hdl_1721_1_15391.Chapter5`) builds the
**residues** `cᵢ` and **solves** the **log argument** `uᵢ` (`radLogArgSolve`). The
`DeepWiki.SymbolicIntegration` library unifies them in `ComputableRadicalIntegrateFull`: a single driver
`cIntegrateAlgebraic` that computes **both** halves and assembles the full `∫ R/(B·y) dx = v + Σ cᵢ log uᵢ`
over a simple radical `y² = ρ`, validated end-to-end by a **round-trip** — start from a known
antiderivative `F = v + c·log u`, differentiate it to an integrand (through the genuine radical derivation
`radDeriv` and the in-extension division `radInv2`), integrate back, and `native_decide` that the recovered
result differentiates to the same integrand.

**Computable-vs-abstract.** Every entry below is a computable function or a `native_decide` round-trip
witness on a worked integral; the abstract correctness (that `cIntegrateAlgebraic`'s output IS the integral
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
open DeepWiki.SymbolicIntegration.CPolyG

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
un-cross-multiplied form of the log-derivative certificate, the building block of `algDeriv`. -/
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
`cᵢ ∈ ℚ(x)`, argument `uᵢ` a `RadElem`) — the output of `cIntegrateAlgebraic`, differentiated by
`algDeriv`. -/
abbrev full_integralResult := @AlgIntegralResult

/-- **The derivative of a full algebraic integral** `algDeriv ρ F = radDeriv v + Σ cᵢ · radLogDeriv uᵢ`
(Trager, Appendix A + Ch. 5): the genuine `RadElem` `D(v + Σ cᵢ log uᵢ)` in `(ℚ(x))[y]/(y² − ρ)`, each log
term contributing `cᵢ · (uᵢ'/uᵢ)` via the honest `radLogDeriv`. The round-trip's comparison side. -/
abbrev full_algDeriv := @algDeriv

/-- **Assemble the rational part from the multi-case dispatch run** `radAssembleRatPart ρ runs` (Trager,
Appendix A §2): sum the per-factor rational parts of `radIntegrateRational` into one `RadElem`, each
`V`-factor (Case 1) over `fi^{e−1}` and `W`-factor (Case 2) over `fi^{e}` contributing an `R/y` term. -/
abbrev full_assembleRatPart := @radAssembleRatPart

/-! ## ★ The unified algebraic integrator and its end-to-end round-trips -/

/-- **★ The unified algebraic integrator** `cIntegrateAlgebraic fuel ρ R B residual c D degBound` (Trager,
Appendix A + Ch. 5, principal case): produces the full `∫ R/(B·y) dx = v + c·log u` over `y² = ρ` by
computing the rational part `v` (multi-case dispatch `radIntegrateRational` + `radAssembleRatPart`) AND
solving the log argument on the `residual` integrand (`radLogArgSolve`, the principal-case linear solve),
packing `(c, u/D)`. On the non-principal / torsion boundary (`radLogArgSolve = none`) it returns the
rational part with an empty log list (a documented partial). Both Appendix A and Ch. 5 §1–§2 in one driver. -/
abbrev full_integrate := @cIntegrateAlgebraic

/-- **★ Round-trip (rational-only): `∫ 1/((x−1)²√(x²+1))`** (Trager, Appendix A §2, `native_decide`): start
from `F = ⟨v, []⟩` (the dispatch's rational part, no log term), differentiate to `integrand = radDeriv v`,
and `cIntegrateAlgebraic` reconstructs the SAME `v` from `(R, B) = (1, (x−1)²)` with an EMPTY log list (the
non-principal residual ⇒ no spurious log term), so `algDeriv F' = integrand`. The rational half closes. -/
abbrev full_roundtrip_rational := @rt_rational_only

/-- **The rational-only result has nonzero rational part and empty log list** (`native_decide`): the
structural signature `(radIsZero ratPart, logTerms.length) = (false, 0)` of a pure rational integral
`∫ = v`. -/
abbrev full_roundtrip_rational_shape := @rt_rational_only_shape

/-- **★ Round-trip (log-only): `∫ dx/(x√(x²+1)) = log((y − 1)/x)`** (Trager, Ch. 5 §1, `native_decide`):
`cIntegrateAlgebraic` computes an empty rational part and one log term `1·log u` with `u = N/x` the
SOLVER'S output (`radLogArgSolve`, a constant multiple of `y − 1`); `algDeriv F' = integrand`. The log half
closes. -/
abbrev full_roundtrip_log := @rt_log_only

/-- **The log-only result has empty rational part and one log term** (`native_decide`): the structural
signature `(radIsZero ratPart, logTerms.length) = (true, 1)` of a pure log integral `∫ = log u`. -/
abbrev full_roundtrip_log_shape := @rt_log_only_shape

/-- **★★ Round-trip (COMBINED): `F = v + c·log u`, BOTH parts nonzero** (Trager, Appendix A + Ch. 5,
`native_decide`): THE FULL-INTEGRATOR PROOF. On `y² = x²+1`, start from `F = v + 1·log u` (`v` the
dispatch's rational part of `∫ 1/((x−1)²√(x²+1))`, `u = x + y` the arcsinh argument), differentiate to
`integrand = radDeriv v + radLogDeriv u`, integrate back: `cIntegrateAlgebraic` reconstructs the rational
part `v` from `(R, B)` by the dispatch AND solves the log argument, and `algDeriv F' = integrand`. The
engine produces the FULL `v + Σ cᵢ log uᵢ` (rational + log, principal case), both halves computed from
polynomial / residual inputs, round-trip-validated through the real radical derivation. -/
abbrev full_roundtrip_combined := @rt_combined

/-- **The combined result has nonzero rational part AND one log term** (`native_decide`): the structural
signature `(radIsZero ratPart, logTerms.length) = (false, 1)` of a genuine combined integral
`∫ = v + c·log u` with both parts present. -/
abbrev full_roundtrip_combined_shape := @rt_combined_shape

end DeepWiki.Tiaf
