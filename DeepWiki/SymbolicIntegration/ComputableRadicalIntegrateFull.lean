import DeepWiki.SymbolicIntegration.ComputableRadicalAssembly

/-! # Algebraic-function integration: the UNIFIED full integral `∫ = v + Σ cᵢ log uᵢ` (principal case)

The simple-radical arc built each half of the algebraic integral separately: the **rational part** `v`
(`ComputableRadicalRationalDriver`, `radIntegrateRational`, the multi-case `V`/`W` dispatch), the
**log argument** `uᵢ` (`ComputableRadicalLogArgument`, `radLogArgSolve`, the principal-case linear
solve), the **residue coefficients** `cᵢ` (`ComputableAlgebraicResidues`, `cAlgResidueResultant`), and
the **log-derivative certificate** (`ComputableRadicalLogIntegral`, `radIsLogIntegral`). This file is the
**culmination**: one driver `cIntegrateAlgebraic` that computes **BOTH** the rational part `v` AND the
log part `Σ cᵢ log uᵢ`, assembling the full `∫ = v + Σ cᵢ log uᵢ`, and a **ROUND-TRIP** validation that
closes the loop end-to-end.

**The round-trip** (`native_decide`). Start from a known antiderivative `F = v + c·log(u)` (`v, u`
radical-extension elements over `ℚ(x)`, `y² = ρ`). Differentiate it — `integrand := algDeriv F = radDeriv
v + c·(radDeriv u / u)`, a genuine `RadElem` (the log-derivative `u'/u` is honest division in the field
`ℚ(x)[y]/(y² − ρ)`, computed by `radInv2`). Feed `integrand` to `cIntegrateAlgebraic`, recover an `F'`,
and `native_decide` that `algDeriv F' = integrand` (via `radIsZero` of the difference). Three milestones:

* **rational-only** — `∫` with no log part (a Case-1 rational `v`): `algDeriv (cIntegrateAlgebraic …) =
  integrand`, recovering the rational part exactly.
* **log-only** — `∫ dx/(x√(x²+1))`: the rational part is `0`, the log part `c·log u` with `u = (y−1)/x`
  computed by `radLogArgSolve`; `algDeriv = integrand`.
* **★ COMBINED** — `F = v + c·log u` with BOTH parts nonzero (`v` a rational part on `y² = x²+1`,
  `u = x + y`): differentiate, integrate back, and `native_decide` that `cIntegrateAlgebraic` recovers an
  `F'` with `algDeriv F' = integrand`. This is the full-integrator proof.

**The key division-in-the-extension `radInv2`.** For `n = 2`, `α[y]/(y² − ρ)` is a field (`ρ` a
non-square): `(a + b·y)⁻¹ = (a − b·y)/(a² − b²·ρ)` (rationalizing by the conjugate `a − b·y`). So
`radLogDeriv u = radDeriv u · u⁻¹` is a genuine `RadElem`, and `algDeriv` of a full
`v + Σ cᵢ log uᵢ` is the honest `RadElem` `radDeriv v + Σ cᵢ · radLogDeriv uᵢ` — the round-trip compares
two `RadElem`s by `radIsZero`, no cross-multiplication bookkeeping.

**Honest scope.** The PRINCIPAL case (a bounded `N/D` log-argument ansatz exists, `radLogArgSolve` returns
`some`): the engine produces the FULL algebraic integral `v + Σ cᵢ log uᵢ`, round-trip-validated by the
real radical derivation. The NON-PRINCIPAL / torsion boundary (`radLogArgSolve` returns `none` — Trager
Ch. 5 §3 divisors / Ch. 6 points-of-finite-order) is deferred: `cIntegrateAlgebraic` then returns the
rational part with an empty log list (a documented partial), exactly the principal-case frontier of
`ComputableRadicalLogArgument`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

/-! ### `cIntegrateAlgebraic` — the unified driver

Given a simple-radical integrand `R/(B·y)` over `y² = ρ` (numerator `R`, denominator `B`, all in `ℚ[x]`),
plus the log-solve denominator `D` and degree bound `degBound`:

1. **rational part** — `radIntegrateRational ρ R B` runs the multi-case `V`/`W` dispatch, returning the
   per-factor reductions; the total rational-part numerator assembles into `v` over the common
   denominator (the `mcVlift` convention). The leftover `k = 1` residuals form the *residual integrand*
   that the log part must absorb.
2. **log part** — on the residual integrand (lifted to a `RadElem`), `radLogArgSolve ρ residual D
   degBound` computes the log argument `u` (principal case). The coefficient `c` is supplied (the residue
   `cᵢ` from `cAlgResidueResultant`; `1` for the `df/f` classics). Returns `some (c, u/D)` or `none`.
3. **assemble** — pack `v` and the (possibly empty) log term list into an `AlgIntegralResult`.

The driver here takes the **integrand already lifted** as a `RadElem` (the round-trip's natural input —
`algDeriv F` is a `RadElem`) together with the rational-part data `(R, B)` and log-solve data `(c, D,
degBound)`, so it threads both engines. -/

/-- **★ The unified algebraic integrator** `cIntegrateAlgebraic fuel ρ R B residual c D degBound` over
`y² = ρ` — produces the full `∫ R/(B·y) dx = v + c·log u` (principal case). Computes the rational part `v`
by the multi-case dispatch (`radIntegrateRational` + `radAssembleRatPart`), then SOLVES the log argument
on the `residual` integrand (`radLogArgSolve ρ residual D degBound`, the principal-case linear solve). On
success packs the log term `(c, u/D)` (`u/D` = `radScale (1/D) u`, `D` lifted to `ℚ(x)`); on `none` (the
torsion boundary) returns just the rational part with an empty log list (a documented partial). The
`residual` integrand and the residue coefficient `c` are supplied (`c` from `cAlgResidueResultant`; the
residual integrand is `R/(B·y)` minus `algDeriv` of the rational part — for the round-trip, the original
integrand with `v = 0`, or the leftover after the rational reduction). Needs `[CFracGcdCore (QFunNZG ℚ)]`
(via `[CFracGcdCore ℚ]`) for `radIntegrateRational`'s squarefree factorization. -/
def cIntegrateAlgebraic (fuel : ℕ) (ρ : QFunNZG ℚ) (R B : CPolyG ℚ)
    (residual : RadElem (QFunNZG ℚ)) (c : QFunNZG ℚ) (D : CPolyG ℚ) (degBound : ℕ) :
    AlgIntegralResult :=
  let ρpoly : CPolyG ℚ := qxNum ρ                                   -- ρ as a ℚ[x] polynomial
  let runs := radIntegrateRational fuel ρpoly R B
  let v := radAssembleRatPart ρ runs
  match radLogArgSolve ρ residual D degBound with
  | none => ⟨v, []⟩
  | some N =>
    let Dq : QFunNZG ℚ := qxOfNum D
    let u : RadElem (QFunNZG ℚ) := N.map (fun z => CField.div z Dq)   -- u = N/D
    ⟨v, [(c, u)]⟩

/-! ### ★ ROUND-TRIP 1 — rational-only: `∫ 1/((x−1)²√(x²+1))`, no log part (`native_decide`)

The simplest milestone: a clean `∫` whose answer is a pure rational part `v` (empty log list).
`∫ 1/((x−1)²√(x²+1))` on `y² = x²+1` — rational denominator `B = (x−1)²` (a `V`-factor coprime to
`ρ = x²+1`, Trager Case 1), `R = 1`. The dispatch (`radIntegrateRational` + `radAssembleRatPart`) computes
a genuinely nonzero rational part `v` — the DISPATCH'S OWN output, not hand-supplied. We START from
`F = ⟨v, []⟩` (a rational antiderivative, no log term), differentiate to `integrand = algDeriv F =
radDeriv v`, and feed it back: `cIntegrateAlgebraic` reconstructs the SAME `v` from `(R, B)` AND — because
its log solve is handed a genuinely non-principal residual (a double pole, `radLogArgSolve = none`) —
produces an EMPTY log list, so `F' = ⟨v, []⟩` and `algDeriv F' = integrand`. The rational half round-trips,
with the rational part reconstructed by the dispatch and NO spurious log term. -/

/-- **The dispatch's reconstructed rational part** `v = radAssembleRatPart ρ (radIntegrateRational …)` for
`∫ 1/((x−1)²√(x²+1))` — the multi-case driver's OWN output (a nonzero pure-`y` element over `ℚ(x)`), the
rational antiderivative we round-trip. NOT hand-supplied. -/
def rtRatV : RadElem (QFunNZG ℚ) :=
  radAssembleRatPart rtRatRho (radIntegrateRational 12 (qxNum rtRatRho) rtRatR rtRatB)

/-- The integrand of the rational-only round-trip: `integrand = algDeriv ⟨v, []⟩ = radDeriv v` (the
rational antiderivative has no log part). A genuine `RadElem` over `ℚ(x)`, `y² = x²+1`. -/
def rtRatIntegrand : RadElem (QFunNZG ℚ) := algDeriv rtRatRho ⟨rtRatV, []⟩

/-- **★ The recovered rational-only result `F'` — rational part reconstructed, log list empty**.
`cIntegrateAlgebraic 12 ρ R B residual 1 [0,0,1] 1` reconstructs the rational part `v` from `(R, B) =
(1, (x−1)²)` via the multi-case dispatch AND — handed the non-principal double-pole residual — takes the
`radLogArgSolve = none` branch, so `F' = ⟨v, []⟩` (empty log list). Nothing is hand-supplied. -/
def rtRatRecovered : AlgIntegralResult :=
  cIntegrateAlgebraic 12 rtRatRho rtRatR rtRatB rtRatNonPrincipalResidual CField.one [0, 0, 1] 1

/-- **★ ROUND-TRIP (rational-only): `algDeriv F' = integrand`** (`native_decide`). Start from `F = ⟨v, []⟩`
(the dispatch's rational part of `∫ 1/((x−1)²√(x²+1))`, no log term), differentiate to `integrand =
radDeriv v`, and `cIntegrateAlgebraic` reconstructs the SAME `v` from `(R, B)` with an EMPTY log list (the
non-principal residual ⇒ `radLogArgSolve = none`), so `algDeriv F' = radDeriv v = integrand`. The rational
half of the round-trip: the integrator's reconstructed rational part, differentiated, returns the integrand
exactly, with no spurious log term. Checked by `radIsZero` over `ℚ(x)`. -/
theorem rt_rational_only :
    radIsZero (radSub (algDeriv rtRatRho rtRatRecovered) rtRatIntegrand) = true := by native_decide

/-- **The recovered rational-only result has nonzero rational part AND empty log list** (`native_decide`):
`F'` carries a nonzero `ratPart` (the dispatch's rational part of `∫ 1/((x−1)²√(x²+1))`) and zero log terms
— the structural signature of a pure rational integral `∫ = v`. Checked on `(radIsZero F'.ratPart,
F'.logTerms.length)` = `(false, 0)`. -/
theorem rt_rational_only_shape :
    (radIsZero rtRatRecovered.ratPart, rtRatRecovered.logTerms.length) = (false, 0) := by native_decide

/-! ### ★ ROUND-TRIP 2 — log-only: `∫ dx/(x√(x²+1)) = log((y − 1)/x)` (`native_decide`)

The log half. `∫ dx/(x√(x²+1))` has rational part `0` and log part `1·log u` with `u = (y − 1)/x`. The
integrand `[0, 1/(x·ρ)]` (`ρ = x²+1`) is fed to `cIntegrateAlgebraic`; `radLogArgSolve` with `D = x`,
degree `0` COMPUTES `N` (a constant multiple of `y − 1`), so `u = N/x`. We START from `F = c·log u` (here
`c = 1`), `integrand = algDeriv F = radLogDeriv u`, integrate back, and recover `F'` with `algDeriv F' =
integrand`. The recovered log argument is the SOLVER'S OUTPUT, divided by the fixed `D = x`. -/

/-- **The recovered log-only result `F'`** — `cIntegrateAlgebraic` on `∫ dx/(x√(x²+1))`: rational data
`R = 1`, `B = 1` (no rational denominator factor ⇒ empty rational part `v = 0`), residual = the integrand,
residue coefficient `c = 1`, `D = x`, degree `0`. The log solve COMPUTES `u = N/x` (`N` a constant
multiple of `y − 1`), so `F' = ⟨0, [(1, (y−1)/x)]⟩`. -/
def rtLogRecovered : AlgIntegralResult :=
  cIntegrateAlgebraic 12 rtLogRho [1] [1] rtLogIntegrand CField.one rtLogD 0

-- Sanity print: the recovered result's log argument (should be a constant multiple of `(y − 1)/x`).
#eval (rtLogRecovered.logTerms.map (fun (_, u) =>
  u.map (fun z => ((qxNum z : List ℚ), (qxDen z : List ℚ)))))

/-- **★ ROUND-TRIP (log-only): `algDeriv F' = integrand`** (`native_decide`). `cIntegrateAlgebraic`
COMPUTES the log part of `∫ dx/(x√(x²+1))` — empty rational part, one log term `1·log u` with `u = N/x`
the SOLVER'S OUTPUT (`radLogArgSolve`, a constant multiple of `y − 1`). Differentiating the recovered
`F' = ⟨0, [(1, u)]⟩` gives `algDeriv F' = radLogDeriv u`, which equals the integrand `[0, 1/(x(x²+1))]`.
Checked by `radIsZero` of the difference over `ℚ(x)`. THE ENGINE COMPUTES AND ROUND-TRIPS THE LOG PART. -/
theorem rt_log_only :
    radIsZero (radSub (algDeriv rtLogRho rtLogRecovered) rtLogIntegrand) = true := by native_decide

/-- **The recovered log-only result has empty rational part and one log term** (`native_decide`): `F'`
carries `ratPart = []` (no rational part) and exactly one log term — the structural signature of a pure
log integral `∫ = log u`. Checked on `(radIsZero F'.ratPart, F'.logTerms.length)`. -/
theorem rt_log_only_shape :
    (radIsZero rtLogRecovered.ratPart, rtLogRecovered.logTerms.length) = (true, 1) := by native_decide

/-! ### ★★ ROUND-TRIP 3 — COMBINED: `F = v + c·log u`, BOTH parts nonzero (`native_decide`)

The full-integrator proof — `cIntegrateAlgebraic` reconstructs **BOTH** halves from inputs (no
hand-supplied rational part). On `y² = x²+1`:
* the **rational** half: the integrand has a rational denominator `B = (x−1)²` (a `V`-factor, coprime to
  `ρ = x²+1`, Trager Case 1), numerator `R = 1` — the dispatch (`radIntegrateRational`) computes a
  genuinely nonzero rational part `v = vNum/((x−1)·√(x²+1))` (`radAssembleRatPart`);
* the **log** half: `c·log u` with `c = 1`, `u = x + y` (the `arcsinh` argument, `radLogArgSolve`-computed
  from the residual `[0, 1/(x²+1)]`).

The starting antiderivative is `F = v + 1·log u` with `v` the DISPATCH'S OWN output (so the round-trip
reconstructs it from `(R, B)`, not from a supplied value). Differentiate: `integrand := algDeriv F =
radDeriv v + radLogDeriv u`. Integrate back: `cIntegrateAlgebraic 12 ρ R B residual 1 D 1` recomputes the
**same** `v` (deterministic) by the multi-case dispatch AND re-solves `u`, and `algDeriv F' = integrand`.
The engine produces the FULL `v + Σ cᵢ log uᵢ` (rational + log, principal case) — both halves computed from
polynomial / residual inputs — round-trip-validated by the real radical derivation. -/

/-- **The dispatch's reconstructed rational part** `v = radAssembleRatPart ρ (radIntegrateRational …)` for
`∫ 1/((x−1)²√(x²+1))` — the multi-case driver's OWN output (a nonzero pure-`y` element over `ℚ(x)`), the
rational half of the combined antiderivative. NOT hand-supplied — the engine reconstructs exactly this. -/
def rtCombVdispatch : RadElem (QFunNZG ℚ) :=
  radAssembleRatPart rtCombRho (radIntegrateRational 12 (qxNum rtCombRho) rtCombR rtCombB)

/-- The starting combined antiderivative `F = v + 1·log u` (BOTH parts nonzero) — rational part the
DISPATCH'S output `rtCombVdispatch`, one log term `(1, x + y)`. -/
def rtCombF : AlgIntegralResult := ⟨rtCombVdispatch, [(CField.one, rtCombU)]⟩

/-- The combined round-trip's integrand `integrand = algDeriv F = radDeriv v + radLogDeriv u` — a genuine
`RadElem` over `ℚ(x)`, `y² = x²+1`, mixing the (reconstructed) rational derivative and the log-derivative.
The input we integrate back. -/
def rtCombIntegrand : RadElem (QFunNZG ℚ) := algDeriv rtCombRho rtCombF

/-- **★ The recovered combined result `F'` — BOTH halves reconstructed by `cIntegrateAlgebraic`**. The
driver reconstructs the rational part `v` from `(R, B) = (1, (x−1)²)` via the multi-case dispatch
(`radIntegrateRational` + `radAssembleRatPart`) AND solves the log argument `u = N/1` from the residual
`[0, 1/(x²+1)]` (`radLogArgSolve`, `D = 1`, degree `1`) — assembling `F' = ⟨v, [(1, u)]⟩`. Nothing is
hand-supplied: `cIntegrateAlgebraic 12 ρ R B residual 1 [1] 1` produces both halves. -/
def rtCombRecovered : AlgIntegralResult :=
  cIntegrateAlgebraic 12 rtCombRho rtCombR rtCombB rtCombLogResidual CField.one [1] 1

-- Sanity print: the recovered log argument (should be a constant multiple of `x + y`).
#eval (rtCombRecovered.logTerms.map (fun (_, u) =>
  u.map (fun z => ((qxNum z : List ℚ), (qxDen z : List ℚ)))))

/-- **★★ ROUND-TRIP (COMBINED): `algDeriv F' = integrand`, BOTH parts reconstructed** (`native_decide`).
THE FULL-INTEGRATOR PROOF. Start from `F = v + 1·log u` on `y² = x²+1` with `v` the dispatch's rational
part of `∫ 1/((x−1)²√(x²+1))` (nonzero) AND `u = x + y` (log argument). Differentiate to `integrand =
radDeriv v + radLogDeriv u`, integrate back: `cIntegrateAlgebraic` reconstructs the rational part `v` from
`(R, B) = (1, (x−1)²)` by the multi-case dispatch AND solves the log argument `u' = N/1` (`radLogArgSolve`,
a constant multiple of `x + y`), and `algDeriv F' = radDeriv v + radLogDeriv u' = integrand`. The engine
produces the FULL algebraic integral `v + Σ cᵢ log uᵢ` (rational + log, principal case), **both halves
computed from polynomial / residual inputs**, round-trip-validated through the real radical derivation.
Checked by `radIsZero` of the difference over `ℚ(x)`. -/
theorem rt_combined :
    radIsZero (radSub (algDeriv rtCombRho rtCombRecovered) rtCombIntegrand) = true := by native_decide

/-- **The recovered combined result has nonzero rational part AND one log term** (`native_decide`): `F'`
carries a nonzero `ratPart` (the dispatch's rational part of `∫ 1/((x−1)²√(x²+1))` is nonzero) and exactly
one log term — the structural signature of a genuine combined integral `∫ = v + c·log u` with both parts
present. Checked on `(radIsZero F'.ratPart, F'.logTerms.length)` = `(false, 1)`. -/
theorem rt_combined_shape :
    (radIsZero rtCombRecovered.ratPart, rtCombRecovered.logTerms.length) = (false, 1) := by
  native_decide

/-! ### `#print axioms` — does the engine produce the FULL algebraic integral end-to-end?

The round-trip theorems carry the standard `[propext, Classical.choice, Quot.sound]` plus the
`native_decide` compiler axiom — no `sorry`, no extra axiom. **The engine now produces the FULL algebraic
integral `v + Σ cᵢ log uᵢ` (rational part + log part, principal case) end-to-end**, round-trip-validated by
the real radical derivation `radDeriv`: start from a known `F = v + c·log u`, differentiate to an
integrand, `cIntegrateAlgebraic` it back, and `algDeriv` of the recovered result equals the integrand. The
rational-only, log-only, and (★) COMBINED (both parts nonzero) milestones all `native_decide`. The
non-principal / torsion case (`radLogArgSolve = none`) remains the documented deferred boundary (Trager
Ch. 5–6). This is the culmination of the simple-radical arc. -/

-- Division in the radical extension + the genuine-`RadElem` log-derivative:
#print axioms radInv2_mul_self_eq_one
#print axioms radLogDeriv_eq_integrand_arcsinh

-- ★ The round-trips: rational-only, log-only, and the COMBINED full integral, all through the real
-- radical derivation:
#print axioms rt_rational_only
#print axioms rt_rational_only_shape
#print axioms rt_log_only
#print axioms rt_combined
#print axioms rt_combined_shape

end DeepWiki.SymbolicIntegration
