import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalOverTower

/-! # Bronstein-1990 catalog — concrete elementary integration over a transcendental tower
The **first formalized content** of this catalog. The library file
`DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalOverTower` realizes the Bronstein-1990 grand unification
(elementary = transcendental monomial θ + algebraic radical y) for **concrete** integrals: the
algebraic-radical arc (`radDeriv`, `radMul`, the diagonal derivation) running **over** a transcendental
tower base `α = ℚ(x)(θ)`, with θ exponential (`θ' = θ`, `θ = eˣ`) or logarithmic (`θ' = 1/x`, `θ = log x`).

The headlines are two `native_decide`-validated elementary integrals — `∫ eˣ/√(eˣ+1) dx = 2√(eˣ+1)` over
ℚ(x)(eˣ) and `∫ dx/(x√(log x)) = 2√(log x)` over ℚ(x)(log x) — each validated through the **actual**
radical derivation `radDeriv` with the tower's `CDiffField` derivation. The radicand `ρ` is a genuine
field element of the transcendental tower, not a polynomial indeterminate. Plus the carrier checks
(`y² = ρ`, the diagonal `D(y) = (ρ'/(2ρ))·y`, `D(θ) = θ`/`1/x`) and the generic rational-part driver run
over a tower base.

**Computable-vs-abstract.** Every entry is a computable value or a `native_decide` witness on a worked
integral; the **general** recursion (Thm 1/2 over arbitrary towers, the log part over towers, Hermite on
general curves over liouvillian ground fields) is the research-grade remainder recorded in
`Sources.Doi_10_1016_S0747_7171_08_80027_2.Coverage`. -/

open DeepWiki.SymbolicIntegration

namespace DeepWiki.Bie

/-! ## The exponential tower base `α = ℚ(x)(eˣ)` and its derivation -/

/-- **The exponential `CDiffField (ℚ(x)(t₁))` instance** (Bronstein 1990, Integration of Elementary
Functions, JSC 9:117-173 — elementary = transcendental θ + algebraic y, exponential case): the level-2
tower derivation `towerDerivQFunNZG [t₁]` whose new-monomial derivative is `Dt₁ = t₁` (so `t₁' = t₁`, i.e.
`t₁ = eˣ`). A local instance supplied explicitly to the radical ops via `@`, leaving the library default
`t₁' = 1` tower untouched. -/
abbrev bie_exp_tower_diff := @expTowerDiff

/-- **`D(t₁) = t₁` over ℚ(x)(eˣ)** (Bronstein 1990, exponential case; `native_decide`): the local derivation
`expTowerDiff` sends the monomial `t₁` to itself, confirming `t₁ = eˣ`, `t₁' = t₁`. The exponential tower
derivation computes. -/
abbrev bie_exp_theta_deriv := @expTheta_deriv_eq_self

/-- **`D(t₁+1) = t₁` over ℚ(x)(eˣ)** (Bronstein 1990, exponential case; `native_decide`): the radicand
derivative `ρ' = (eˣ+1)' = eˣ`, the numerator `ρ'` of `y' = ρ'/(2y)`. -/
abbrev bie_exp_radicand_deriv := @expRadicand_deriv_eq_theta

/-! ## The radical `y² = eˣ+1` over the exponential tower -/

/-- **`y·y = eˣ+1` over ℚ(x)(eˣ)** (Bronstein 1990, Integration of Elementary Functions, JSC 9:117-173 —
elementary = transcendental θ + algebraic y, concrete case; `native_decide`): the square of `y = √(eˣ+1)`
in `(ℚ(x)(eˣ))[y]/(y² − (eˣ+1))` reduces, via `radMul`'s `y² → ρ` fold, to `ρ = eˣ+1`. The radical carrier
computes over the transcendental tower, with `ρ` a genuine ℚ(x)(eˣ) field element. -/
abbrev bie_radical_over_tower := @expRadGen_sq_eq_radicand

/-- **`D(y) = (eˣ/(2(eˣ+1)))·y` over ℚ(x)(eˣ)** (Bronstein 1990, concrete case; `native_decide`): the
diagonal radical derivation of `y = √(eˣ+1)` with the exponential base derivation (`ρ' = eˣ`) is `ℓ·y`,
`ℓ = ρ'/(2ρ)`. The algebraic arc (the diagonal derivation) runs over the exponential engine. -/
abbrev bie_radDeriv_over_tower := @expRadDeriv_radGen_eq

/-! ## ★ The headline: `∫ eˣ/√(eˣ+1) dx = 2√(eˣ+1)` over ℚ(x)(eˣ) -/

/-- **★ `∫ eˣ/√(eˣ+1) dx = 2√(eˣ+1)` over ℚ(x)(eˣ)** (Bronstein 1990, Integration of Elementary Functions,
JSC 9:117-173 — elementary = transcendental θ + algebraic y, concrete case; `native_decide`): THE GRAND
UNIFICATION. The actual radical derivation `radDeriv` (with the exponential base derivation `t₁' = t₁`) of
the antiderivative `2y = 2√(eˣ+1)` equals the rationalized integrand `eˣ/√(eˣ+1) = (eˣ/(eˣ+1))·y`. The
algebraic-radical arc runs over a transcendental tower base — Bronstein-1990 elementary integration
(transcendental + algebraic) for a concrete `∫`. -/
abbrev bie_exp_integral := @expIntegral_eq

/-! ## The logarithmic companion: `∫ dx/(x√(log x)) = 2√(log x)` over ℚ(x)(log x) -/

/-- **The logarithmic `CDiffField (ℚ(x)(t₁))` instance** (Bronstein 1990, logarithmic case): the level-2
tower derivation `towerDerivQFunNZG [1/x]` whose new-monomial derivative is `Dt₁ = 1/x` (so `t₁' = 1/x`,
i.e. `t₁ = log x`). A local instance supplied via `@`. -/
abbrev bie_log_tower_diff := @logTowerDiff

/-- **`D(t₁) = 1/x` over ℚ(x)(log x)** (Bronstein 1990, logarithmic case; `native_decide`): the local
derivation `logTowerDiff` sends `t₁ = log x` to `1/x`, confirming `t₁ = log x`, `t₁' = 1/x`. The log tower
derivation computes. -/
abbrev bie_log_theta_deriv := @logTheta_deriv_eq_oneOverX

/-- **`y·y = log x` over ℚ(x)(log x)** (Bronstein 1990, concrete case; `native_decide`): the square of
`y = √(log x)` reduces, via `radMul`'s `y² → ρ` fold, to `ρ = log x`. The radical carrier computes over the
logarithmic tower. -/
abbrev bie_log_radical_over_tower := @logRadGen_sq_eq_radicand

/-- **★ `∫ dx/(x√(log x)) = 2√(log x)` over ℚ(x)(log x)** (Bronstein 1990, Integration of Elementary
Functions, JSC 9:117-173 — elementary = transcendental θ + algebraic y, concrete case; `native_decide`):
the actual radical derivation `radDeriv` (with the logarithmic base derivation `t₁' = 1/x`) of `2y =
2√(log x)` equals the rationalized integrand `(1/x)/√(log x) = ((1/x)/(log x))·y`. The algebraic arc
carries over both transcendental kinds (exp, log). -/
abbrev bie_log_integral := @logIntegral_eq

/-! ## Stretch: the generic rational-part driver runs over a transcendental-tower base -/

/-- **★ The generic Case-2 driver integrates over a TOWER base** (Bronstein 1990, concrete case;
`native_decide`): over the stacked radical extension `(ℚ(x)(t₁))[y]/(y² − (t₁³−t₁))`, the actual diagonal
derivation `radDeriv 2` of the driver's iterated Case-2 rational part `v = vNum/(θ²√ρ)` equals the rational
part of `1/(θ²·√(θ³−θ))` — the master identity `D(∫) = rational-part` over a transcendental-tower base, with
no driver code changed (only the base field is the tower level ℚ(x)). -/
abbrev bie_driver_over_tower := @drvDriver_integrates

/-- **★ The full fuel-free multi-case driver `radIntegrateRationalWf` computes over the tower base**
(Bronstein 1990, concrete case; `native_decide`): the squarefree-decomposition + partial-fraction +
V/W-classification + dispatch pipeline runs over `α = ℚ(x)` (`CFracGcdCoreWf (QFunNZG ℚ)` resolving
recursively), producing exactly one per-factor record for the single `W`-factor `θ` of `B = θ²`. The entire
generic rational-part driver instantiates at a tower-level base field with no top-level fuel. -/
abbrev bie_full_driver_over_tower := @drvFullRun_length

end DeepWiki.Bie
