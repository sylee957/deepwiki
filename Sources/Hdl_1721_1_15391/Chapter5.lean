import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgebraicResiduesExamples
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogIntegral
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalResidueInfinity
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogArgument
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

**The PRINCIPAL case is now COMPUTED** (the `ch5_logArgSolve` / `ch5_logArg_*` section below): the
log-derivative condition is ℚ-linear in the candidate `u = N/D`, so for a bounded ansatz it is a finite
homogeneous ℚ-linear system whose nonzero kernel vector IS the log argument `N` — the engine SOLVES for `u`
(`arcsinh`, `arccosh`, the finite-pole `∫ dx/(x√(x²+1))`), no longer merely verifying a supplied one. The
**residue at infinity** is likewise now computed (the `ch5_residueAtInfinity*` section below) by the
`x = 1/t` transform reusing the eq. 7 norm at the place `t = 0`. **What remains OUT OF SCOPE** (see the
block below) is the **non-principal / torsion** case — when no bounded `N/D` ansatz exists (the linear
solve returns `none`): expressing such an integral needs the divisor construction (Ch. 5 §3), the
principal-divisor test, and the torsion / points-of-finite-order bound (Ch. 6).

## NOT YET FORMALIZED (audit 2026-06-26)
Ch. 5 §3 Cantor composition / reduction + Ch. 6 The Principal Divisor Test / Torsion Bound: the
  Jacobian arithmetic and the principal-divisor / points-of-finite-order decision — the genuine
  obstruction in the NON-PRINCIPAL case (where the principal-case linear solve `ch5_logArgSolve`
  returns `none`, e.g. a double pole). The divisor REPRESENTATION (the Mumford pair `(u, v)`) and the
  residue-divisor CONSTRUCTION of Ch. 5 §3 ARE done — catalog `Sources.Hdl_1721_1_15391.Chapter6`,
  which carries its own NOT-YET-FORMALIZED list of the deferred Cantor/principal/torsion pieces
  `[research]`.
Ch. 5 §2: the general degree bound for the log-argument ansatz (how large `N`/`D` must be taken before
  `ch5_logArgSolve` is guaranteed to find the principal-case kernel) — only fixed worked bounds are
  exercised `[infra]`.
Ch. 5 §2 / Ch. 2 §3: the residue at infinity for ODD `deg ρ`, where the place over `∞` is a branch
  (Puiseux `ỹ = √t`) point — the even-degree arcsinh/arccosh transform IS done (`ch5_residueAtInfinity*`),
  the odd-degree ramified case needs the local Puiseux parametrization `[deferred]`.
Ch. 5 §2: splitting `R(Z)` over its splitting field `K'` (algebraic factoring) to extract the
  residues symbolically when they are not rational `[infra]`.
General algebraic curves (beyond simple radicals `yⁿ = ρ`): the GENERAL (non-radical) integral basis
  (Ch. 2 §2 idealizer / Round-2; the simple-radical `[1, y/d]` basis IS done — catalog
  `Sources.Hdl_1721_1_15391.Chapter2`), absolute irreducibility / the curve's function field (Ch. 3),
  the rational part on a general curve (Ch. 4) `[infra]`. -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.RadElem
open DeepWiki.SymbolicIntegration.DensePoly

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

/-! ## ★ COMPUTING the log argument `u` (Ch. 5 §1–§2, the principal-case linear solve)

The log-derivative condition `∫(integrand) dx = log(N/D)` is ℚ-linear in the numerator `N = a₀ + a₁·y`:
clearing `D`, it reads `radDeriv(N)·D − N·D' − radMul(N, integrand)·D = 0`, a finite homogeneous ℚ-linear
system in the coefficients of `a₀, a₁` (bounded-degree ansatz). A nonzero kernel vector IS the log argument
`N` (log arguments are determined up to a multiplicative constant ⇒ a 1-dimensional kernel is exactly
right), so the engine SOLVES for `u`, rather than being handed it. The PRINCIPAL case (a bounded `N/D`
ansatz exists); the non-principal / torsion case returns `none` (the boundary). -/

/-- **Reduce a ℚ-matrix to reduced row-echelon form** `ratRref nCols rows = (rrefRows, pivotCols)`
(Trager, Chapter 5 §2, the linear solve): standard Gauss–Jordan over ℚ — the inner step of solving the
cleared log-derivative system for the log argument. Exact ℚ-arithmetic. -/
abbrev ch5_ratRref := @ratRref

/-- **A nonzero kernel vector of a ℚ-matrix** `ratKernelVector nCols rows = some c` with `M · c = 0`,
`c ≠ 0` (Trager, Chapter 5 §2, the linear solve): reads a kernel vector off a free column after `ratRref`,
or `none` if the kernel is trivial. The nonzero kernel vector assembles into the log-argument numerator
`N`. -/
abbrev ch5_ratKernelVector := @ratKernelVector

/-- **The cleared log-derivative residual** `radLogResidualQ ρ integrand D N = radDeriv(N)·D − N·D' −
radMul(N, integrand)·D` (Trager, Chapter 5 §1, the cleared `df/f` relation): the `RadElem` whose vanishing
(both ℚ(x)-coefficients zero) says `∫(integrand) dx = log(N/D)`. ℚ-linear in `N`. -/
abbrev ch5_logResidual := @radLogResidualQ

/-- **The ℚ-matrix of the cleared log-derivative system** `radLogMatrixQ ρ integrand D degBound` (Trager,
Chapter 5 §2): evaluate the residual on the monomial basis `Nⱼ ∈ {[xᵏ,0], [0,xᵏ]}` (the residual is
ℚ-linear), clear each rational-function entry to a polynomial numerator over a common denominator, and read
off the `x`-power coefficients — one row per `x`-power per component, one column per basis index. A kernel
vector solves for `N`. -/
abbrev ch5_logMatrix := @radLogMatrixQ

/-- **★ Solve for the log argument** `radLogArgSolveQ ρ integrand D degBound = some N` (Trager, Chapter 5
§1–§2, the principal case): the radical-extension numerator `N = a₀ + a₁·y` with `∫(integrand) dx =
log(N/D)`, COMPUTED by building the ℚ-matrix `radLogMatrixQ` (undetermined coefficients) and finding a
nonzero kernel vector (`ratKernelVector`). Returns `none` on the non-principal / torsion boundary (trivial
kernel at the degree bound, OUT OF SCOPE — Ch. 5 §3 / Ch. 6). The OUTPUT is `u = N/D`: `u` is computed, not
supplied. -/
abbrev ch5_logArgSolve := @radLogArgSolveQ

/-- **★ `radLogArgSolveQ` COMPUTES `u = x + y` for `∫ dx/√(x²+1)` (arcsinh)** (Trager, Chapter 5 §1–§2,
`native_decide`): with `ρ = x²+1`, `D = 1`, ansatz degree `1`, the solver returns `some N` (a nonzero
kernel vector of the cleared linear system), and the COMPUTED `u = N/1` passes the log-derivative
certificate `radIsLogIntegral` — `∫ dx/√(x²+1) = log N`. The engine computes the algebraic-log argument. -/
abbrev ch5_logArg_arcsinh := @radArg_arcsinh_compute_verify

/-- **★ `radLogArgSolveQ` COMPUTES `u = x + y` for `∫ dx/√(x²−1)` (arccosh)** (Trager, Chapter 5 §1–§2,
`native_decide`): the arccosh companion — the same linear solve recovers the log argument from `ρ = x²−1`,
`D = 1`, and the computed `u` passes the log-derivative certificate. -/
abbrev ch5_logArg_arccosh := @radArg_arccosh_compute_verify

/-- **★ `radLogArgSolveQ` COMPUTES `u = (y − 1)/x` for `∫ dx/(x√(x²+1))`** (Trager, Chapter 5 §1–§2,
`native_decide`): the genuine FINITE-POLE case — with the FIXED denominator `D = x` (pole at `x = 0`), the
solver returns `some N` (a constant multiple of `y − 1`, the correct sign), and the COMPUTED `u = N/x`
passes the log-derivative certificate — `∫ dx/(x√(x²+1)) = log((y − 1)/x)`. The engine computes the
finite-pole log argument. -/
abbrev ch5_logArg_finitePole := @radArg_finitePole_compute_verify

/-- **The computed arcsinh `N` is a nonzero constant multiple of `x + y`** (Trager, Chapter 5 §1–§2,
`native_decide`): the solver's `N = [a₀, a₁]` satisfies `a₁ ≠ 0` and `a₀ = a₁·x` (so `a₀/a₁ = x`), matching
the known closed form `u = x + y` exactly up to the log argument's intrinsic scalar freedom. -/
abbrev ch5_logArg_arcsinh_matches := @radArg_arcsinh_matches_closed_form

/-- **★ Negative control: the double-pole target has NO bounded log argument** (Trager, Chapter 5 §1–§2,
the torsion boundary, `native_decide`): `radLogArgSolveQ (ρ = x²+1) (1/(x²y)) (D = x²) 1 = none` — the
cleared linear system has only the trivial kernel, so `∫ dx/(x²√(x²+1))` is non-principal at this degree
bound: its log part needs the `(1/m)·log` divisor/torsion machinery (Ch. 5 §3 / Ch. 6). The boundary of the
principal-case linear solve. -/
abbrev ch5_logArg_double_pole_none := @radArg_double_pole_none

/-! ## ★ The residue at infinity (Ch. 5 §2 + Ch. 2 §3, normalize at infinity via `x = 1/t`)

The residue at infinity of `f dx` is the FINITE residue at `t = 0` of the differential transformed under
`x = 1/t`, `dx = −dt/t²` (Trager Ch. 2 §3, normalize at infinity). So no new resultant is needed: transform
the data `(ρ, g₀, g₁, D)` into `(ρ̃, g̃₀, g̃₁, D̃)` in `t`, then read the residue at the place `t = 0` off
the EXISTING eq. 7 norm. For the arcsinh/arccosh-class integrals `∫ dx/√(x² ± 1)` the finite residues all
vanish and the entire log term comes from the place over `∞`. -/

/-- **The `x = 1/t` coordinate transform at infinity** `radTransformAtInfinity ρ g₀ g₁ D = (ρ̃, g̃₀, g̃₁,
D̃)` (Trager, Chapter 2 §3, normalize at infinity): for the simple-radical differential
`f dx = (g₀ + g₁·y)/D dx` on `y² = ρ`, with `revₖ p := tᵏ·p(1/t)`, sets `ρ̃ = rev_{2m} ρ`, raw
`g̃₀ = −tᵐ·rev_N g₀`, raw `g̃₁ = −rev_N g₁`, raw `D̃ = t^{m+2}·rev_N D` (`m = ⌈deg ρ/2⌉`), then cancels the
common `t`-power so the place over `∞` stays a SIMPLE pole. The residue at `∞` is the residue at the place
`t = 0` of `(g̃₀ + g̃₁·ỹ)/D̃ dt` on `ỹ² = ρ̃`. -/
abbrev ch5_residueAtInfinity_transform := @radTransformAtInfinity

/-- **Full residue-at-infinity resultant** `cAlgResidueAtInfinity fuel ρ g₀ g₁ D = R̃(Z)` (Trager, Chapter 5
§2 + Ch. 2 §3): the EXISTING eq. 7 residue resultant `cAlgResidueResultant` on the `x = 1/t`-transformed
data; the residue at infinity is the `t = 0` factor. For the clean even-degree arcsinh/arccosh
differentials the nonzero roots of `R̃` are exactly the residues at `∞` (the rest is a `Z`-power from
zero-residue branch places). Reuses the resultant — no new elimination. -/
abbrev ch5_residueAtInfinity_resultant := @cAlgResidueAtInfinity

/-- **Isolated residue at the place `t = 0`** (= the residue at infinity) `cResidueAtInfinityPlace fuel ρ g₀
g₁ D = (Z·D̃'(0) − g̃₀(0))² − g̃₁(0)²·ρ̃(0)` (Trager, Chapter 5 §2 + Ch. 2 §3): the `t = 0` factor of the
eq. 7 norm with the TRUE transformed derivative `D̃'` — the genuinely-localized residue at `∞` that stays
correct (residue `0`) even when `∞` is not a pole, the form needed for the residue-theorem cross-check on
mixed differentials. -/
abbrev ch5_residueAtInfinity_place := @cResidueAtInfinityPlace

/-- **★ The `x = 1/t` transform reproduces Trager's normalize-at-infinity data** (Trager, Chapter 2 §3,
`native_decide`): for `∫ dx/√(x²+1)` the transform of `(x²+1, 0, 1, x²+1)` is exactly the
normalize-at-infinity data `(ρ̃, g̃₀, g̃₁, D̃) = (1 + t², 0, −1, t(1 + t²))` — the common `t²` cancelled so
`D̃ = t(1 + t²)` keeps the place over `∞` a simple pole. -/
abbrev ch5_residueAtInfinity_transform_eq := @arcsinhInf_transform_eq

/-- **★ Residue at infinity of `∫ dx/√(x²+1)` is `±1`** (Trager, Chapter 5 §2 + Ch. 2 §3, `native_decide`):
the isolated `t = 0` place residue resultant is `Z² − 1 = (Z − 1)(Z + 1)`, so the residues at `∞` are `±1`
— exactly the log term `log(x + √(x²+1)) = arcsinh(x)`. The arcsinh class is generated at infinity. -/
abbrev ch5_residueAtInfinity_arcsinh := @arcsinhInf_residue_eq

/-- **★ Residue at infinity of `∫ dx/√(x²−1)` (arccosh) is `±1`** (Trager, Chapter 5 §2 + Ch. 2 §3,
`native_decide`): same as arcsinh with `ρ = x²−1`, the isolated `t = 0` place residue resultant is again
`Z² − 1`, residues `±1` — the log term `log(x + √(x²−1)) = arccosh(x)` is generated at infinity. -/
abbrev ch5_residueAtInfinity_arccosh := @arccoshInf_residue_eq

/-- **★ The residue theorem for `∫ dx/√(x²+1)`: finite + ∞ residues sum to `0`** (Trager, Chapter 5 §2,
`native_decide`): the finite eq. 7 resultant is a pure `Z`-power (every finite residue `0`) while the
residues at `∞` are `±1` (`cResiduesMatch` on the isolated place `Z² − 1 = (Z − 1)(Z + 1)`); their grand
sum `0 + (+1) + (−1) = 0`. The arcsinh log term comes entirely from infinity. -/
abbrev ch5_residueAtInfinity_residueTheorem := @arcsinhInf_residue_theorem

/-- **★ A differential with BOTH finite and ∞ residues nonzero: `∫ √(x²+1)/(x²−x) dx`** (Trager, Chapter 5
§2, `native_decide`): the finite eq. 7 resultant is `(Z²−1)(Z²−2)` (finite residues `±1` at `x = 0` and
`±√2` — an irrational residue — at `x = 1`) AND the residue at infinity is `Z² − 1` (residues `±1`,
`f ~ 1/x` at `∞` a genuine simple pole); the residue theorem holds by Vieta (each resultant's root-sum is
`0`). The engine computes the complete residue picture at both ends. -/
abbrev ch5_residueAtInfinity_bothEnds := @bothInf_residue_theorem

/-- **The odd-degree transform leaves a ramified radicand** (Trager, Chapter 2 §3, `native_decide`):
`∫ dx/√(x³)` transforms to `ρ̃ = t` (so `ỹ² = ρ̃` is ramified at `t = 0`, `ỹ = √t` a Puiseux place over
`∞`) — the documented obstruction for ODD `deg ρ`: the simple-pole residue resultant does not extract an
honest residue at a ramified place (the even-degree arcsinh/arccosh case is the resolved one). The
transformed radicand is `[0, 1] = t`. -/
abbrev ch5_residueAtInfinity_oddRamified := @oddInf_radicand_ramified

end DeepWiki.Tiaf
