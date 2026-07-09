import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogArgGenericExamples
import DeepWiki.SymbolicIntegration.Engine.ElementaryIntegrate
import DeepWiki.SymbolicIntegration.Engine.ElementaryIntegrateExamples
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalRationalTower

/-! # Bronstein-1990 catalog — the FULL elementary integral `v + Σ log u` over a tower, both halves COMPUTED
The completion of the concrete grand-unification arc cataloged in
`Sources.Doi_10_1016_S0747_7171_08_80027_2.ElementaryIntegration` (where the algebraic-radical *rational*
part was carried over a transcendental tower base but the log argument was supplied by hand). Three further
library files realize the **complete** elementary integral `∫ = v + Σ cᵢ log uᵢ` (rational part `v` **and**
log part `Σ cᵢ log uᵢ`) of an algebraic-radical integrand over a transcendental tower `α = ℚ(x)(θ)`, with
**both** halves COMPUTED by the engine — Bronstein 1990's "elementary = transcendental + algebraic" for a
concrete `∫`, the principal case:

* `DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogArgGenericExamples` — **computes the log
  argument** `u` over a tower via the `[CField β]`-generic solver
  (`gaussElimG`/`kernelVectorG`/`radLogArgSolveG`), the whole linear solve running over the tower field
  `β = ℚ(x)`; headline `∫ dx/√(eˣ+1) = log((y−1)/(y+1))` over ℚ(x)(eˣ).
* `DeepWiki.SymbolicIntegration.Engine.ElementaryIntegrate` — the **unified integrator**
  `cIntegrateElementaryG` assembling `v + Σ cᵢ log uᵢ` (output `AlgIntegralResultG`, differentiated by the
  ACTUAL-tower-derivation `algDerivG`); round-trip `∫√(eˣ+1) dx = 2√(eˣ+1) + log((y−1)/(y+1))`.
* `DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalRationalTower` — the **rational half COMPUTED over a tower**
  (`radIntegrateCase3G` with the actual `θ' = θ` derivation), closing the last supplied gap so BOTH halves
  are the engine's output (`rtFull_both_halves_computed`).

**Computable-vs-abstract.** Every entry is a computable value or a `native_decide` witness on a worked
integral. The **general** decision procedure (the recursion over arbitrary deeper towers coupled with the
Risch differential equation, the symbolic log part over towers, curve-Hermite on general curves over a
liouvillian ground field, the non-principal / torsion case) is the research-grade remainder recorded in
`Sources.Doi_10_1016_S0747_7171_08_80027_2.Coverage`. -/

open DeepWiki.SymbolicIntegration

namespace DeepWiki.Bie

/-! ## Computing the log argument over a tower: the ℚ → generic-`CField` Gaussian elimination -/

/-- **Generic Gaussian elimination over `[CField β]`** (Bronstein 1990, Integration of Elementary Functions,
JSC 9:117-173 — elementary integral `v + Σ log u` over a transcendental tower, log part): `gaussElimG`
row-reduces a `β`-matrix to reduced row-echelon form, the `[CField β]`-generic analogue of the ℚ-pinned
`ratRref`. Pure `CField`-arithmetic (`CField.isZero`/`CField.div`/`CField.sub`/`CField.mul`), so the linear
solve underlying log-argument computation runs over any computable tower level `β`, not just ℚ. -/
abbrev bie_gaussElim_generic := @gaussElimG

/-- **A nonzero kernel vector over `[CField β]`** (Bronstein 1990, log part; the generic linear-solve core):
`kernelVectorG` returns a nonzero solution of a homogeneous `β`-linear system (or `none` when only the
trivial kernel exists), the `[CField β]`-generic analogue of `ratKernelVector`. This is what extracts the
log-argument numerator `N` from the cleared log-derivative system over a tower field. -/
abbrev bie_kernelVector_generic := @kernelVectorG

/-- **★ Solve for the log argument `u = N/D` over a transcendental tower** (Bronstein 1990, Integration of
Elementary Functions, JSC 9:117-173 — elementary integral `v + Σ log u` over a transcendental tower,
principal case, log part COMPUTED): `radLogArgSolveG ρ integrand D degBound` builds the cleared
log-derivative `β`-linear system `radDeriv(N)·D − N·D' − radMul(N,integrand)·D = 0` over `α = QFunNZG β`,
finds a nonzero kernel vector via `kernelVectorG`, and reassembles the radical-extension numerator
`N = a₀ + a₁·y`. The **whole linear solve runs over the tower field `β`**, so the log argument is computed
over a transcendental tower (`β = ℚ(x)`, `α = ℚ(x)(eˣ)`), not just over ℚ. -/
abbrev bie_logarg_over_tower := @radLogArgSolveG

/-- **★ `radLogArgSolveG` COMPUTES `u = (y−1)/(y+1)` for `∫ dx/√(eˣ+1)` over ℚ(x)(eˣ)** (Bronstein 1990,
Integration of Elementary Functions, JSC 9:117-173 — elementary integral `v + Σ log u` over a transcendental
tower, principal case, log part COMPUTED; `native_decide`): over `α = ℚ(x)(eˣ)` with the **exponential**
derivation (`θ' = θ`), the generic solver — its entire Gaussian elimination running over `β = ℚ(x)` —
returns `N = (θ+2) − 2y`, and the COMPUTED `u = N/θ` passes the log-derivative certificate
`radIsLogIntegral`. So `∫ dx/√(eˣ+1) = log((y−1)/(y+1))` is COMPUTED over the transcendental tower — the
grand unification extended from the rational part to the LOG part, the argument now an engine OUTPUT. -/
abbrev bie_logarg_exp := @expArg_isLogIntegral

/-- **`radLogArgSolveG` reproduces the arcsinh log argument `u = x + y` at the ℚ base** (Bronstein 1990, log
part; `native_decide`): at `β = ℚ` (`α ≅ ℚ(x)`) the generic solver computes the same `N` as the ℚ-specific
`radLogArgSolve` for `∫ dx/√(x²+1) = log(x + y)` and the computed `u = N/1` passes the certificate — the
ℚ → generic-`CField` generalization is conservative (it specializes back to the base level). -/
abbrev bie_logarg_arcsinh_base := @genArg_arcsinh_isLogIntegral

/-! ## The unified integrator `cIntegrateElementaryG`: assembling `v + Σ cᵢ log uᵢ` over a tower -/

/-- **The tower-generic full elementary integral `∫ = v + Σ cᵢ log uᵢ`** (Bronstein 1990, Integration of
Elementary Functions, JSC 9:117-173 — elementary integral `v + Σ log u` over a transcendental tower):
`AlgIntegralResultG α` bundles a rational part `v` (a `RadElem α`) plus log terms `[(c₁, u₁), …]` over an
arbitrary base field `α` (the tower level `QFunNZG β`). The generic analogue of `AlgIntegralResult`; the
OUTPUT of `cIntegrateElementaryG`, differentiated by `algDerivG`. -/
abbrev bie_alg_integral_result := @AlgIntegralResultG

/-- **The ACTUAL-derivation derivative of a tower-generic elementary integral** (Bronstein 1990, elementary
integral `v + Σ log u` over a transcendental tower): `algDerivG ρ F = radDeriv v + Σ cᵢ · radLogDeriv uᵢ`
in `α[y]/(y² − ρ)`, with the base derivation the **ACTUAL** tower derivation `CDiffField.cderiv` (NOT the
formal `cderivG`). Over `α = ℚ(x)(eˣ)` with the exponential derivation it is the genuine exp-tower
derivative (`θ' = θ`); the round-trip compares `algDerivG ρ (cIntegrateElementaryG …)` to the integrand. -/
abbrev bie_unified_deriv := @algDerivG

/-- **★ The UNIFIED elementary integrator over a transcendental tower** (Bronstein 1990, Integration of
Elementary Functions, JSC 9:117-173 — elementary integral `v + Σ log u` over a transcendental tower,
principal case): `cIntegrateElementaryG` fuses the rational part and the log part over a tower base
`α = QFunNZG β`. Given the log-solve data, it **COMPUTES** the log argument on the residual via
`radLogArgSolveG` (the ACTUAL tower derivation) and assembles `v + c·log(N/D)` as an `AlgIntegralResultG`,
returning the rational-only partial `⟨v, []⟩` when the log solve is non-principal. The general
`v + Σ cᵢ log uᵢ` assembler — ONE driver for the full elementary integral over a transcendental tower. -/
abbrev bie_unified_integrate := @cIntegrateElementaryG

/-- **★★ THE COMBINED ROUND-TRIP `∫√(eˣ+1) dx = 2√(eˣ+1) + log((y−1)/(y+1))` over ℚ(x)(eˣ)** (Bronstein 1990,
Integration of Elementary Functions, JSC 9:117-173 — elementary integral `v + Σ log u` over a transcendental
tower, principal case, fully computed; `native_decide`): starting from `F = ⟨2y, [(1, u)]⟩` over the tower,
the ACTUAL exp-tower derivative `algDerivG F = y` (the integrand `√(eˣ+1)`); fed back to
`cIntegrateElementaryG`, the engine COMPUTES the log half (`radLogArgSolveG → N = (θ+2)−2y`, `u = N/θ`),
assembles `F' = ⟨2y, [(1, u)]⟩`, and `algDerivG F' = y` — BOTH halves, over the tower, through the real
exponential derivation. The integrand `y` has a rational part `v = 2y` AND a log part `log u`. -/
abbrev bie_unified_roundtrip := @rt_elementary_combined

/-! ## The rational half COMPUTED over a tower: Case-3 degree-lowering with the actual derivation -/

/-- **The generic leading-term Case-3 cofactor** (Bronstein 1990, Integration of Elementary Functions, JSC
9:117-173 — elementary integral `v + Σ log u` over a transcendental tower, rational part COMPUTED):
`radCase3CofactorTower der f g C = B = b·θ^m` cancels the leading term of `C` in the `C/y` degree-lowering
for **any** radicand-level derivation `der` (with `B' = der B`), NOT just the formal `θ' = 1`. The monomial
degree `m = deg C − deg g` and leading coefficient `b = lcf(C)/κ` (`κ = lcf(der(θ^m)·f + θ^m·g)`) are read
off `der` itself, so the cofactor shape follows the ACTUAL derivation (degree-lowering for `θ' = 1`,
degree-preserving for `θ' = θ`). -/
abbrev bie_case3_cofactor_tower := @CPoly.radCase3CofactorTower

/-- **One Case-3 degree-lowering step over a tower** (Bronstein 1990, elementary integral `v + Σ log u` over
a transcendental tower, rational part COMPUTED): `radReduceCase3IterateG` is the fuel-free Case-3 iterator
with the cofactor swapped to `radCase3CofactorTower der`, so the **ACTUAL** derivation drives both the
cofactor `B` and the residual `D = der B·f + Bg − C`. It recurses directly on the degree of `C`,
accumulating `B·f` into the rational-part numerator, and bottoms at `deg C < deg f`. -/
abbrev bie_case3_iterate_tower := @CPoly.radReduceCase3IterateG

/-- **★ The `∫ C/y` rational-part driver COMPUTED over a transcendental tower** (Bronstein 1990, Integration
of Elementary Functions, JSC 9:117-173 — elementary integral `v + Σ log u` over a transcendental tower,
principal case, rational part COMPUTED): `radIntegrateCase3G der ρ g C` runs `radReduceCase3IterateG` with
the ACTUAL derivation `der` (e.g. `cmonomialDeriv [θ]`, `θ' = θ` over the exp tower) and no runtime fuel to
**compute** the rational-part numerator. Over `α = ℚ(x)(eˣ)` for `∫√(eˣ+1) dx` it computes `vNum = 2ρ`, so
the rational part `v = 2y = 2√(eˣ+1)` — an OUTPUT, no longer a supplied constant. -/
abbrev bie_rational_over_tower := @CPoly.radIntegrateCase3G

/-- **★★ BOTH halves COMPUTED: `∫√(eˣ+1) dx = 2√(eˣ+1) + log((y−1)/(y+1))` over ℚ(x)(eˣ), no supplied `v`**
(Bronstein 1990, Integration of Elementary Functions, JSC 9:117-173 — elementary integral `v + Σ log u` over
a transcendental tower, principal case, fully computed; `native_decide`): the full elementary integral with
**NEITHER** half supplied — the rational part `v = 2y` COMPUTED by `radIntegrateCase3G` (the actual `θ' = θ`
derivation), the log argument `u = (y−1)/(y+1)` COMPUTED by `radLogArgSolveG`, and `algDerivG F' = y` (the
integrand) over the tower through the real radical derivation. The unified elementary integral is computed
end-to-end over the transcendental tower. -/
abbrev bie_both_halves_computed := @rtFull_both_halves_computed

/-- **`radIntegrateCase3G cderivG` reduces to the ℚ-base fuel-free Case-3 driver** (Bronstein 1990,
rational part; `native_decide`): at the ℚ base (`α ≅ ℚ(x)`, `θ' = 1`) the generic Case-3-G driver and
`radIntegrateCase3Wf` produce the **identical** `(Crem, vNum)` on `∫ x⁴/√(x³+1)` — the ACTUAL-derivation
generalization is conservative (`radCase3CofactorTower cderivG` specializes back to `radCase3Cofactor`). -/
abbrev bie_case3_tower_base_conservative := @stretch_case3G_eq_case3_base

end DeepWiki.Bie
