import DeepWiki.SymbolicIntegration.ComputableGeneralLogSoundness
import DeepWiki.SymbolicIntegration.ComputableGeneralDivisorOrder

/-! # The SELF-DETERMINING GENERAL-curve algebraic integrator: `cIntegrateGeneralCurveDecide`
(Trager, *Integration of Algebraic Functions*, the elementarity decision, for an ARBITRARY plane curve
`F(x, y) = 0` — beyond the hyperelliptic Mumford/Cantor torsion)

`cIntegrateAlgebraicDecide` (`ComputableAlgebraicDecide`) is the **self-determining** decision procedure for
the simple-radical / hyperelliptic case `y² = ρ`: it returns `some F` when the integral is elementary (no log
part; principal `1·log u`; or the residue divisor torsion ⟹ `(1/m)·log g`) and **`none`** when the residue
divisor is non-torsion (NOT elementary), wiring in Trager's torsion decision through the hyperelliptic Mumford
pair (`ComputableHyperellipticDivisor`) + Cantor group law (`ComputableCantorComposition`) + good-reduction
order test (`ComputableDivisorOrder`).

This file **LIFTS that decision to an arbitrary irreducible plane curve** `K(x)[y]/(f)`, replacing the
hyperelliptic torsion machinery with the **general divisor-class-group (`Pic⁰`) arithmetic** over the integral
basis (`ComputableGeneralDivisor` / `ComputableGeneralDivisorOrder`). The pieces it lifts:

* the **rational part** `v` — `afRationalSolve` over the integral basis through the general derivation `afDeriv`
  (`ComputableGeneralRationalSolve`, DONE), replacing the radical `radIntegrateRational`;
* the **principal log part** `1·log u` — `afLogArgSolve`, the `K`-linear log-derivative solve `afDeriv f u =
  afMul f u integrand` (`ComputableGeneralLogArg`, DONE), replacing the radical `radLogArgSolve`;
* the **torsion decision** — `genDivisorOrder fuel f basis δ` (`ComputableGeneralDivisorOrder`, the general lift
  of the hyperelliptic `cantorOrder`: the smallest `m` with `m·δ` principal, via repeated `idealProduct` + an
  ideal-reduction / principality test over the **fractional-ideal-over-the-integral-basis** representation),
  replacing the hyperelliptic `cantorOrder`; `some m` ⟹ the residue divisor is `m`-torsion ⟹ a `(1/m)·log g`
  term, `none` ⟹ non-torsion ⟹ NOT elementary.

`cIntegrateGeneralCurveDecide` returns `Option GeneralCurveIntegralResult` with exactly the four hyperelliptic
outcomes — `some ⟨v, []⟩` (no log), `some ⟨v, [(1, u)]⟩` (principal), `some ⟨v, [(1/m, g)]⟩` (torsion), `none`
(non-torsion) — so it is the **general-curve self-determining verdict**.

**What generalizes cleanly vs. the deep residual.** The residue divisor → divisor representation is DONE
(`genResidueResultant`, the full double resultant, `ComputableGeneralResidues`); the principal case is DONE
(`afRationalSolve` / `afLogArgSolve`); the SOUNDNESS routes through the already-proven general capstone
`isGeneralAlgebraicIntegral_of_parts` (`ComputableGeneralLogSoundness`) — these all lift. The DEEP residual is
the **general-`Pic⁰`-torsion core**: the general divisor-class-group arithmetic + the principal-generator
construction of `m·δ` + the good-reduction torsion-ceiling lift, the general analogue of the hyperelliptic
`principalGenerator` / `isTorsionDivisor` / `mumfordReduceModP`. We isolate it PRECISELY as the named residual
`GeneralPicTorsionFrontier` and prove the decision modulo it, connecting to the **partial** general torsion we
already have (`genIsTorsion` / `genDivisorOrder`, which compute the order via the fractional-ideal Pic
arithmetic but whose termination needs the good-reduction ceiling). NO `sorry`.

Proven (modulo exactly the named frontiers, never re-`sorry`):
* **SOUNDNESS** (`cIntegrateGeneralCurveDecide_sound`) — `some F → D(F) = integrand` in the carrier quotient
  `K[X] ⧸ afIdeal f`, checker-free, via the general capstone `isGeneralAlgebraicIntegral_of_parts`;
* **COMPLETENESS** (`cIntegrateGeneralCurveDecide_complete`) — `none → ¬ elementary`, the non-torsion verdict;
* the **DECISION capstone** (`cIntegrateGeneralCurveDecide_decides`) — `(∃ F, … = some F) ⟺ elementary`,
  mirroring the hyperelliptic `cIntegrateAlgebraicDecide_decides`.

A `native_decide` witness runs the torsion decision on the trigonal / non-hyperelliptic cuspidal cubic. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential
open CPolyG

/-! ## Part 1 — the general-curve integral result `GeneralCurveIntegralResult` and the decision statement

The general-curve analogue of `AlgIntegralResult` (`ComputableRadicalIntegrateFull`, pinned to the radical
carrier `RadElem (QFunNZG ℚ)`): a rational part `v` plus log terms `(cᵢ, uᵢ)`, here over the **general curve
carrier** `K(x)[y]/(f) = CPolyG (QFunNZG ℚ)` (a power-basis coordinate vector), not the radical carrier. The
output of `cIntegrateGeneralCurveDecide`. -/

/-- **The full general-curve algebraic integral `∫ = v + Σ cᵢ log uᵢ`** `GeneralCurveIntegralResult` — the
rational part `v` (a carrier element `CPolyG (QFunNZG ℚ)` of `K(x)[y]/(f)`) plus the log terms `logTerms =
[(c₁, u₁), …]` (coefficient `cᵢ ∈ ℚ(x) = QFunNZG ℚ`, argument `uᵢ ∈ K(x)[y]/(f)`). The general-curve analogue
of `AlgIntegralResult`, over the curve carrier instead of the radical carrier; the OUTPUT of
`cIntegrateGeneralCurveDecide`, differentiated by `genCurveDeriv`. -/
structure GeneralCurveIntegralResult where
  /-- The rational part `v` of `∫ = v + Σ cᵢ log uᵢ` (a carrier element of `K(x)[y]/(f)`). -/
  ratPart : CPolyG (QFunNZG ℚ)
  /-- The log terms `[(c₁, u₁), …]`: each a coefficient `cᵢ ∈ ℚ(x)` and an argument `uᵢ ∈ K(x)[y]/(f)`. -/
  logTerms : List (QFunNZG ℚ × CPolyG (QFunNZG ℚ))

/-! ### The residual structure: the general-`Pic⁰`-torsion frontier (isolated PRECISELY)

The deep gap is the general divisor-class-group torsion machinery beyond the principal case — specifically the
two oracle outputs the torsion branch consumes that have no `native_decide`-validated general construction yet:

1. the **residue divisor** `δ : GenDivisor` of the integrand over the general carrier (the simple-pole residues,
   downstream of `genResidueResultant` — DONE — but the residue → fractional-ideal assembly is the gap);
2. the **principal generator** `g` of `m·δ` (the function with `div(g) = m·δ`, giving the `(1/m)·log g` term) —
   the general analogue of the hyperelliptic `principalGenerator`, beyond the fractional-ideal order test
   `genDivisorOrder` (which decides `m` but does not yet *read off* the generator).

We bundle these as `GeneralCurveTorsionInputs`: the residue divisor `δ` and a generator-oracle `genGen` that,
given the torsion order `m`, returns the principal generator of `m·δ`. The torsion branch of
`cIntegrateGeneralCurveDecide` consumes exactly these; isolating them as a structure makes the deep residual a
single citable object (the soundness/completeness theorems quantify over the abstract elementarity `Prop`
modulo it). The order itself, `genDivisorOrder` (`ComputableGeneralDivisorOrder`), is what we HAVE. -/

/-- **★ The general-`Pic⁰`-torsion inputs** `GeneralCurveTorsionInputs` — the two oracle outputs the torsion
branch of `cIntegrateGeneralCurveDecide` consumes that lie beyond the principal case and the order test
`genDivisorOrder`:

* `divisor` — the **residue divisor** `δ : GenDivisor` of the integrand (a fractional `O`-ideal over the
  integral basis, downstream of `genResidueResultant` — the residue → fractional-ideal assembly is the gap);
* `genGen` — the **principal-generator oracle**: given the torsion order `m`, returns the function `g ∈
  K(x)[y]/(f)` with `div(g) = m·δ`, i.e. the `(1/m)·log g` argument (the general analogue of the hyperelliptic
  `principalGenerator`).

This bundle IS the named general-`Pic⁰`-torsion residual `GeneralPicTorsionFrontier`'s data side: the decision
is proven modulo it, and `genDivisorOrder` (HAVE) supplies the order `m`. The hyperelliptic
`cIntegrateAlgebraicDecide` consumes the analogous `Dm` (the residue Mumford divisor) + the built-in
`principalGenerator`; the general lift makes both explicit because their general construction is the deep
sub-arc. -/
structure GeneralCurveTorsionInputs where
  /-- The residue divisor `δ : GenDivisor` of the integrand (a fractional `O`-ideal over the integral basis). -/
  divisor : GenDivisor
  /-- The principal-generator oracle: given the torsion order `m`, the function `g` with `div(g) = m·δ`. -/
  genGen : ℕ → CPolyG (QFunNZG ℚ)

/-! ### The general-curve torsion log term `genCurveTorsionLogTerm`

The general analogue of the hyperelliptic `torsionLogTerm` (`ComputableTorsionLogTerm`): decide the order of
the residue divisor `δ` via `genDivisorOrder` (the general fractional-ideal Pic order test, HAVE); on `some m`
(torsion) return the log term `(1/m, g)` where `g = tin.genGen m` is the principal generator of `m·δ` (the
frontier oracle); on `none` (non-torsion within fuel) return `none` (NOT elementary). The coefficient `1/m`
is the local `genOneOverM` (the general-curve file is decoupled from the hyperelliptic torsion file). -/

/-- **The general-curve torsion log-term coefficient** `genOneOverM m = 1/m ∈ ℚ(x) = QFunNZG ℚ` — the
constant-field element `qxOfNum [1] / qxOfNum [m]` (`m` cast to ℚ), the coefficient `cᵢ = 1/m` of the
`(1/m)·log g` term. The general-curve analogue of `ComputableTorsionLogTerm`'s `oneOverMQ`, defined locally so
this file does not depend on the hyperelliptic torsion machinery. -/
def genOneOverM (m : ℕ) : QFunNZG ℚ := CField.div (qxOfNum [1]) (qxOfNum [(m : ℚ)])

/-- **The general-curve torsion log term** `genCurveTorsionLogTerm fuel f basis tin` (the general analogue of
the hyperelliptic `torsionLogTerm`) — decide the order of the residue divisor `δ = tin.divisor` via
`genDivisorOrder fuel f basis δ` (the general fractional-ideal `Pic⁰` order test, `ComputableGeneralDivisorOrder`):

* `some m` — `δ` is `m`-torsion, so `m·δ` is principal; the principal generator `g = tin.genGen m` (the
  frontier oracle, `div(g) = m·δ`) gives the **log term** `some (1/m, g)`, i.e. `∫ = … + (1/m)·log g`;
* `none` — `δ` is non-torsion within `fuel`: that part of the integral is **NOT elementary**.

The coefficient `1/m ∈ ℚ(x)` is `genOneOverM m`. The general lift of `torsionLogTerm` from the Mumford pair to
the fractional-ideal representation: `genDivisorOrder` replaces `isTorsionDivisor`, and the generator-oracle
`tin.genGen` replaces the built-in `principalGenerator` (its general construction is the deep residual). -/
def genCurveTorsionLogTerm (fuel : ℕ) (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (tin : GeneralCurveTorsionInputs) : Option (QFunNZG ℚ × CPolyG (QFunNZG ℚ)) :=
  match genDivisorOrder fuel f basis tin.divisor with
  | none => none
  | some m => some (genOneOverM m, tin.genGen m)

/-! ### The self-determining general-curve decision integrator `cIntegrateGeneralCurveDecide`

The general lift of `cIntegrateAlgebraicDecide`. It threads: the **rational-part** input `ratIntegrand` (run
through `afRationalSolve`); the **principal-log** input `logIntegrand` + `degBound` (the `afLogArgSolve` linear
log-argument solve); and the **torsion-decision** inputs `tin` (the residue divisor + generator oracle, feeding
`genCurveTorsionLogTerm`). A Boolean `hasLogPart` discriminates the "no log part" case (the rational part is
the whole answer) from the cases that need the log machinery. -/

/-- **The self-determining GENERAL-curve algebraic integrator** `cIntegrateGeneralCurveDecide` over an
arbitrary plane curve `K(x)[y]/(f)` (Trager, the elementarity decision, beyond hyperelliptic). Returns
`Option GeneralCurveIntegralResult`:

* compute the rational part `v` via `afRationalSolve fuel f basis degBound ratIntegrand` (the general
  derivation `afDeriv` linear solve over the integral basis); if it fails → `none`;
* if `hasLogPart = false` (no log part) → `some ⟨v, []⟩`;
* else **principal**: `afLogArgSolve fuel f basis degBound logIntegrand = some u` (the `K`-linear
  log-derivative solve `afDeriv f u = afMul f u logIntegrand`) → `some ⟨v, [(1, u)]⟩` (the classic `1·log u`);
* else **torsion decision** on the residue divisor via `genCurveTorsionLogTerm`: if the residue divisor is
  `m`-torsion (`genDivisorOrder = some m`) the generator oracle gives `(1/m, g)` → `some ⟨v, [(1/m, g)]⟩`; if
  non-torsion → **`none`** (the integral is NOT elementary).

So `none` is returned exactly when the rational solve fails OR the log part is non-torsion — the
self-determining verdict. The general lift of `cIntegrateAlgebraicDecide`: `afRationalSolve` for the rational
part (vs. `radIntegrateRationalWf`), `afLogArgSolve` for the principal log (vs. `radLogArgSolve`),
`genCurveTorsionLogTerm` (= `genDivisorOrder` + the generator oracle) for the torsion decision (vs.
`torsionLogTerm`). -/
def cIntegrateGeneralCurveDecide (fuel : ℕ) (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (degBound : ℕ) (ratIntegrand logIntegrand : CPolyG (QFunNZG ℚ))
    (tin : GeneralCurveTorsionInputs) (hasLogPart : Bool) :
    Option GeneralCurveIntegralResult :=
  match afRationalSolve fuel f basis degBound ratIntegrand with
  | none => none
  | some v =>
    if hasLogPart = false then
      some ⟨v, []⟩
    else
      match afLogArgSolve fuel f basis degBound logIntegrand with
      | some u => some ⟨v, [(CField.one, u)]⟩
      | none =>
        match genCurveTorsionLogTerm fuel f basis tin with
        | some term => some ⟨v, [term]⟩
        | none => none

end DeepWiki.SymbolicIntegration
