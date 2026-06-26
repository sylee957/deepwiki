import DeepWiki.SymbolicIntegration.ComputableAlgebraicResidues
import DeepWiki.SymbolicIntegration.ComputableRadicalLogIntegral
import Sources.Hdl_1721_1_15391.Source

/-! # Trager catalog — Chapter 5: The Logarithmic Part (residue resultant §2 + log-differential check §1)
After the simple-radical rational part is reduced (Appendix A, catalog
`Sources.Hdl_1721_1_15391.AppendixA`), the heart of the **logarithmic** part is the residue
resultant of Chapter 5 §2 (thesis p.56–59, eq. 7): the polynomial over the constant field `K`
whose roots are the residues of the differential, divided by their branch orders. The
`DeepWiki.SymbolicIntegration` library renders this for simple radicals (`F = yⁿ − ρ`, focus
`n = 2`) in `ComputableAlgebraicResidues`, validated by `native_decide`. This catalog also covers
the **verification side** of Chapter 5 §1 (logarithmic differentials, Appendix A): for the cases where
a closed log term `u` is known (or, for the finite-pole case, derived), the log-derivative certificate
`radDeriv u = radMul u integrand` confirms `∫(integrand) dx = log u` directly through the engine's real
diagonal derivation (`ComputableRadicalLogIntegral`).

**Computable-vs-abstract.** The residue resultant, its membership test, and the integer-residue
failure certificate are computable functions over `K`, `native_decide`-validated on
`∫ dx/((x−1)√x)` on `y² = x`; the log-derivative certificates are likewise `native_decide` witnesses on
worked integrals. The abstract correctness (Trager Theorem 2, that the resultant's roots ARE the
residues) is validated by the examples, not proved in general.

**The hard next step is OUT OF SCOPE** (see the block below): this delivers the residues `cᵢ`, the
minimal-extension polynomial `R(Z)`, and the *verification* that a supplied `u` is the log term — but NOT
the general COMPUTATION of the log arguments `vᵢ`, which needs the divisor construction (Ch. 5 §3), the
principal-divisor test, and the torsion / points-of-finite-order bound (Ch. 6).

## NOT YET FORMALIZED (audit 2026-06-26)
Ch. 5 §3 The Divisor Construction: building the divisor of a candidate logarithmic term from a
  residue (the place-by-place pole/zero data on the curve) `[infra]`.
Ch. 6 The Principal Divisor Test / Torsion Bound: deciding whether a divisor's integer multiple
  is principal (good reduction, the points-of-finite-order bound on the Jacobian) — the genuine
  obstruction to expressing the integral `[research]`.
Ch. 5 §2–§3: the general COMPUTATION of the log arguments `vᵢ` (the polynomials inside `Σ cᵢ log vᵢ`)
  from the residues and the principal divisors — only the VERIFICATION that a supplied/derived `u` is
  the log term is realized (`ch5_log_*` below), not the construction of `u` `[infra]`.
Ch. 5 §1 / App. A §3: the residue at infinity (the log term of a residue-at-infinity differential such
  as `arcsinh`/`arccosh`, whose divisor sits at `∞`) — the log-derivative check validates such `u`
  directly, but computing it from the residue-at-infinity is deferred `[infra]`.
Ch. 5 §2: splitting `R(Z)` over its splitting field `K'` (algebraic factoring) to extract the
  residues symbolically when they are not rational `[infra]`.
General algebraic curves (beyond simple radicals `yⁿ = ρ`): the GENERAL (non-radical) integral basis
  (Ch. 2 §2 idealizer / Round-2; the simple-radical `[1, y/d]` basis IS done — catalog
  `Sources.Hdl_1721_1_15391.Chapter2`), absolute irreducibility / the curve's function field (Ch. 3),
  the rational part on a general curve (Ch. 4) `[infra]`. -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.RadElem
open DeepWiki.SymbolicIntegration.CPolyG

namespace DeepWiki.Tiaf

/-! ## The `n = 2` residue resultant (Ch. 5 §2, eq. 7) -/

/-- **The inner residue norm at a node** (Trager, Chapter 5 §2, eq. 7, p.56): `cAlgResidueNorm`
is eq. 7's inner `resultant_Y(Z·D'(X) − g(X,Y), y² − ρ)` for the simple radical `F = y² − ρ`,
`g = g₀ + g₁·y`, evaluated at `Z = c` — the norm `(c·D' − g₀)² − g₁²·ρ ∈ K[X]` of the linear-in-`y`
form. -/
abbrev ch5_residue_norm := @cAlgResidueNorm

/-- **The `n = 2` residue resultant** `R(Z) = res_X((Z·D' − g₀)² − g₁²·ρ, D)` (Trager, Chapter 5
§2, eq. 7, p.56–59): `cAlgResidueResultant`, the polynomial over `K` whose roots are the residues
divided by their branch orders. Computed by the evaluation + Lagrange-interpolation template of
the transcendental Rothstein–Trager resultant, replacing the operand by the inner norm. Restricted
to `n = 2` (the linear-in-`y` reduction collapses eq. 7's inner `resultant_Y` to one norm). -/
abbrev ch5_residue_resultant := @cAlgResidueResultant

/-- **Residue membership test** (Trager, Chapter 5 §2): `cIsResidue` tests `(Z − c) ∣ R(Z)` — is
`c ∈ K` a root of the residue resultant, hence a residue (divided by its branch order)? -/
abbrev ch5_is_residue := @cIsResidue

/-- **Integer-residue / factorization certificate** (Trager, Chapter 5 §2, the failure test):
`cResiduesMatch` checks that `R(Z)` equals (monic) a claimed product `∏ (Z − cᵢ)` of integer
linear factors — the certificate that a `df/f`-type differential passes Trager's "all residues
are integers" elementarity test. -/
abbrev ch5_residues_match := @cResiduesMatch

/-! ## Validation: `∫ dx/((x−1)·y)` on `y² = x` (Ch. 5 §2, eq. 7) -/

/-- **Chapter 5 §2, eq. 7** (validation): for `∫ dx/((x−1)√x)` on `y² = x` (so `g = y`,
`D = x²−x`), the residue resultant is `R(Z) = Z⁴ − Z² = Z²(Z−1)(Z+1)` (`native_decide`). -/
abbrev ch5_resultant_value := @algResExX_resultant_eq

/-- **Chapter 5 §2, eq. 7** (validation): the residues of `∫ dx/((x−1)√x)` are `±1` — both
`Z = 1` and `Z = −1` are roots of `R(Z)`, the residue `g/D' = (±1)/(2·1−1) = ±1` at the simple
pole `x = 1` on the two sheets (`native_decide`). -/
abbrev ch5_residues_pm_one := @algResExX_residues_pm_one

/-- **Chapter 5 §2, eq. 7** (validation): `Z = 2` is NOT a residue of `∫ dx/((x−1)√x)` — the
membership test rejects a non-root (`native_decide`). -/
abbrev ch5_two_not_residue := @algResExX_two_not_residue

/-- **Chapter 5 §2** (the integer-residue failure test): all residues of `∫ dx/((x−1)√x)` are
integers (`R = Z²(Z−1)(Z+1)`, the `±1` plus the `Z = 0` branch-place root), so this `df/f`-type
differential passes Trager's "all residues are integers" elementarity test (`native_decide`). -/
abbrev ch5_all_residues_integer := @algResExX_all_residues_integer

/-! ## The log-derivative certificate (Ch. 5 §1 / App. A) — VERIFYING `∫ = log u`

The verification side of the logarithmic differentials of Chapter 5 §1 (Appendix A): for an element
`u ∈ α[y]/(yⁿ − ρ)`, `D(log u) = (radDeriv u)/u`, so `∫(integrand) dx = log u` holds iff the division-free
equality `radDeriv u = radMul u integrand` holds — a pure `RadElem`-equality, `native_decide`-checkable.
This delivers the actual log terms (when `u` is known/derived), complementing the residue resultant §2. -/

/-- **The log-derivative certificate** `radIsLogIntegral n ρ u integrand` (Trager, Chapter 5 §1 / App. A):
the boolean check that `∫(integrand) dx = log u` in `α[y]/(yⁿ − ρ)`, i.e. `D(log u) = (radDeriv u)/u =
integrand`. Since `D(log u)·u = radDeriv u`, this is the division-free equality
`radDeriv u = radMul u integrand`, read off by `radIsZero` of the difference. -/
abbrev ch5_isLogIntegral := @radIsLogIntegral

/-- **The log-derivative certificate as a `Prop`** `RadIsLogIntegral n ρ u integrand` (Trager, Chapter 5
§1 / App. A): the certificate `radIsLogIntegral … = true` read as a proposition — the faithful semantic
(`radIsZero`, cross-multiplied) statement that `∫(integrand) dx = log u`, `Decidable`/`native_decide`-able. -/
abbrev ch5_isLogIntegral_prop := @RadIsLogIntegral

/-- **An `R/y` integrand lift** `radInvYLift ρ R = [0, R/ρ]` (Trager, Chapter 5 §1 / App. A): the pure-`y`
element representing `R/y` in `α[y]/(y² − ρ)` (since `1/y = y/ρ`), the `n = 2` integrand form for the
log-derivative check. -/
abbrev ch5_invYLift := @radInvYLift

/-- **★ `∫ dx/√(x²+1) = log(x + √(x²+1)) = arcsinh x`** (Trager, Chapter 5 §1 / App. A, `native_decide`):
the log-derivative certificate `radDeriv u = radMul u integrand` holds for `u = x + y`, `integrand =
[0, 1/(x²+1)]` over `ℚ(x)`, `y² = x²+1` — the engine VERIFIES the algebraic-log integral `∫ = log u`
through the real diagonal derivation `radDeriv` (the actual log term, a residue-at-infinity differential). -/
abbrev ch5_log_arcsinh := @radLog_arcsinh

/-- **★ `∫ dx/√(x²−1) = log(x + √(x²−1)) = arccosh x`** (Trager, Chapter 5 §1 / App. A, `native_decide`):
the same log argument `u = x + y` validates against `integrand = [0, 1/(x²−1)]` on the curve `y² = x²−1`,
by the log-derivative certificate. The companion classic to `arcsinh`. -/
abbrev ch5_log_arccosh := @radLog_arccosh

/-- **★ `∫ dx/(x√(x²+1)) = log((√(x²+1) − 1)/x)`** (Trager, Chapter 5 §1 / App. A, `native_decide`): a
genuine FINITE-pole example (pole at `x = 0`), with log argument `u = (y − 1)/x` DERIVED by requiring the
log-derivative certificate `radDeriv u = radMul u integrand` — the engine verifies a finite-residue
algebraic-log integral `∫ = log u`. -/
abbrev ch5_log_finitePole := @radLog_finitePole

/-- **Negative control: `(y + 1)/x` is NOT the log argument** (Trager, Chapter 5 §1 / App. A,
`native_decide`): the wrong-sign candidate fails the log-derivative certificate
(`radIsLogIntegral … = false`), so only `u = (y − 1)/x` integrates `∫ dx/(x√(x²+1))` — the check pins the
CORRECT log term, not merely a plausible shape. -/
abbrev ch5_log_finitePole_wrong_sign := @radLog_finitePole_wrong_sign

/-- **★ The finite-pole residues are `±1`** (Trager, Chapter 5 §2, eq. 7, `native_decide`):
`cAlgResidueResultant` for `∫ dx/(x√(x²+1))` returns `R(Z) = 16·Z⁴(Z² − 1)`, so `Z = ±1` are residues
(the finite pole at `x = 0` on sheets `y = ±1`) and `Z = 0` is a residue (the branch places `x = ±i`).
The residue computation PREDICTS `cᵢ = ±1`, which the log-derivative check confirmed for `u = (y − 1)/x`. -/
abbrev ch5_log_finitePole_residues := @radLog_finitePole_residues

/-- **★ The finite-pole residues are all integers** (Trager, Chapter 5 §2, the failure test,
`native_decide`): `R(Z)` factors with integer linear factors `0,0,0,0,1,−1`, so the residues `±1` of
`∫ dx/(x√(x²+1))` are integers — its `df/f`-type log part `log((y − 1)/x)` has integer coefficients and is
elementary, exactly what the log-derivative check verified directly. -/
abbrev ch5_log_finitePole_residues_integer := @radLog_finitePole_residues_integer

/-- **Heuristic log argument for `∫ dx/√(x² + bx + c)`** `radQuadraticLogArg b = [b/2, 1]` (Trager,
Chapter 5 §1 / App. A, STRETCH): the element `u = x + b/2 + y` (completing the square,
`∫ dx/√(x² + bx + c) = log(x + b/2 + √(x² + bx + c))`) — a first step toward COMPUTING (not just
verifying) algebraic-log arguments. -/
abbrev ch5_quadraticLogArg := @radQuadraticLogArg

/-- **★ The quadratic heuristic computes a valid log argument** (Trager, Chapter 5 §1 / App. A,
`native_decide`): for `∫ dx/√(x² + 2x + 2)` the heuristic `u = x + b/2 + y = (x + 1) + y` satisfies the
log-derivative certificate over `ℚ(x)`, `y² = x²+2x+2` — `u` COMPUTED from the coefficients (not supplied)
and `radDeriv`-validated, a first step toward computing, not only verifying, algebraic-log arguments. -/
abbrev ch5_log_quadratic_heuristic := @radLog_quadratic_heuristic

end DeepWiki.Tiaf
