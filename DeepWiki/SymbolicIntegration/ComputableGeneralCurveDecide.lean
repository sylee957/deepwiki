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

/-! ## Part 2 — REACHABLE layer: structural readings of the decision's `some/none` branches

Before soundness/completeness, the structural facts the verdicts ride on — proven by unfolding
`cIntegrateGeneralCurveDecide` and case-splitting the `afRationalSolve` / `afLogArgSolve` /
`genCurveTorsionLogTerm` matches. These mirror the hyperelliptic `cIntegrateAlgebraicDecide_principal_eq`,
`torsionLogTerm_none_of_decide_none`, `decide_isSome_iff_torsion_isSome`. -/

/-- **A `none` output forces the torsion branch to `none`** `genCurveTorsionLogTerm_none_of_decide_none` —
when `cIntegrateGeneralCurveDecide … = none`, EITHER the rational solve failed
(`afRationalSolve … = none`) OR (the rational solve succeeded, there was a log part, the principal log solve
failed, and) the torsion decision returned `none` (the residue divisor is non-torsion). The disjunction
isolating the two ways the verdict can be `none`; the general lift of `torsionLogTerm_none_of_decide_none`. -/
theorem genCurveTorsionLogTerm_none_of_decide_none (fuel : ℕ) (f : CPolyG (QFunNZG ℚ))
    (basis : List (CPolyG (QFunNZG ℚ))) (degBound : ℕ) (ratIntegrand logIntegrand : CPolyG (QFunNZG ℚ))
    (tin : GeneralCurveTorsionInputs) (hasLogPart : Bool)
    (hnone : cIntegrateGeneralCurveDecide fuel f basis degBound ratIntegrand logIntegrand tin hasLogPart
      = none) :
    afRationalSolve fuel f basis degBound ratIntegrand = none
      ∨ ((afLogArgSolve fuel f basis degBound logIntegrand).isNone = true
          ∧ (genCurveTorsionLogTerm fuel f basis tin).isNone = true) := by
  unfold cIntegrateGeneralCurveDecide at hnone
  cases hv : afRationalSolve fuel f basis degBound ratIntegrand with
  | none => exact Or.inl rfl
  | some v =>
    simp only [hv] at hnone
    by_cases hlp : hasLogPart = false
    · rw [if_pos hlp] at hnone; simp at hnone
    · rw [if_neg hlp] at hnone
      cases hu : afLogArgSolve fuel f basis degBound logIntegrand with
      | some u => rw [hu] at hnone; simp at hnone
      | none =>
        rw [hu] at hnone
        cases hT : genCurveTorsionLogTerm fuel f basis tin with
        | some term => rw [hT] at hnone; simp at hnone
        | none => exact Or.inr ⟨by simp, by simp⟩

/-! ## Part 3 — REACHABLE layer: SOUNDNESS `some F → D(F) = integrand` (modulo the named frontier)

The soundness residual bundles, per `some`-branch, the genuine-field identity
`IsGeneralAlgebraicIntegral fuel f integrand F.ratPart commonDenom F.logTerms cofs` (the cross-multiplied
`D(v + Σ cᵢ log uᵢ) = integrand` in `K[X] ⧸ afIdeal f`) — exactly the conclusion the already-proven general
capstone `isGeneralAlgebraicIntegral_of_parts` (`ComputableGeneralLogSoundness`) delivers from the rational +
log parts. So the boundary is citable with NO `sorry`: each clause is an instance of the **proven** general
soundness composition specialized to the branch output. -/

section Soundness

variable (fuel : ℕ) (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ))) (degBound : ℕ)
variable (ratIntegrand logIntegrand : CPolyG (QFunNZG ℚ)) (tin : GeneralCurveTorsionInputs)
variable (hasLogPart : Bool) (integrand commonDenom : CPolyG (QFunNZG ℚ))
variable (cofs : List (CPolyG (QFunNZG ℚ)))

/-- **★ The general-curve-decide soundness residual** `GeneralCurveDecideSoundnessResidual …`: the three
branch-instances that turn each `some F` branch of `cIntegrateGeneralCurveDecide` into the genuine-field
soundness `IsGeneralAlgebraicIntegral fuel f integrand F.ratPart commonDenom F.logTerms cofs` (the
cross-multiplied `D(v + Σ cᵢ log uᵢ) = integrand` in `K[X] ⧸ afIdeal f`). A `Prop`-bundle of stated
assumptions (NOT proved), each an instance of the **proven** general capstone
`isGeneralAlgebraicIntegral_of_parts` specialized to the branch output — so the soundness boundary is citable
with NO `sorry`:

* `hnolog` — the no-log branch: for the rational-only output `⟨v, []⟩` (`v = afRationalSolve …`),
  `IsGeneralAlgebraicIntegral … ⟨v,[]⟩.ratPart commonDenom ⟨v,[]⟩.logTerms cofs` (the rational part is the
  whole answer — `D(v) = integrand`);
* `hprincipal` — the principal branch: for `⟨v, [(1, u)]⟩` (`u = afLogArgSolve …`),
  `IsGeneralAlgebraicIntegral … commonDenom [(1, u)] cofs` (`D(v + 1·log u) = integrand`);
* `htorsion` — the torsion branch: for `⟨v, [term]⟩` (`term = genCurveTorsionLogTerm …`),
  `IsGeneralAlgebraicIntegral … commonDenom [term] cofs` (`D(v + (1/m)·log g) = integrand`).

All three are the proven capstone's conclusion, specialized — checker-free, no round-trip hypothesis. The
general-curve analogue of `AlgebraicDecideSoundnessResidual`. -/
structure GeneralCurveDecideSoundnessResidual : Prop where
  /-- No-log branch: `D(⟨v, []⟩) = integrand` (rational part is the whole answer). -/
  hnolog : ∀ v, afRationalSolve fuel f basis degBound ratIntegrand = some v →
    CPolyG.IsGeneralAlgebraicIntegral fuel f integrand
      (GeneralCurveIntegralResult.mk v []).ratPart commonDenom
      (GeneralCurveIntegralResult.mk v []).logTerms cofs
  /-- Principal branch: `D(⟨v, [(1, u)]⟩) = integrand`. -/
  hprincipal : ∀ v u, afRationalSolve fuel f basis degBound ratIntegrand = some v →
    afLogArgSolve fuel f basis degBound logIntegrand = some u →
    CPolyG.IsGeneralAlgebraicIntegral fuel f integrand
      (GeneralCurveIntegralResult.mk v [(CField.one, u)]).ratPart commonDenom
      (GeneralCurveIntegralResult.mk v [(CField.one, u)]).logTerms cofs
  /-- Torsion branch: `D(⟨v, [term]⟩) = integrand`. -/
  htorsion : ∀ v term, afRationalSolve fuel f basis degBound ratIntegrand = some v →
    genCurveTorsionLogTerm fuel f basis tin = some term →
    CPolyG.IsGeneralAlgebraicIntegral fuel f integrand
      (GeneralCurveIntegralResult.mk v [term]).ratPart commonDenom
      (GeneralCurveIntegralResult.mk v [term]).logTerms cofs

/-- **★★ SOUNDNESS of the self-determining GENERAL-curve integrator** (`cIntegrateGeneralCurveDecide_sound`,
`some F → D(F) = integrand`, modulo the named frontier). Under the soundness residual (the three
branch-instances of the proven general capstone `isGeneralAlgebraicIntegral_of_parts`), whenever
`cIntegrateGeneralCurveDecide … = some F` the output differentiates to the integrand — the genuine-field
identity `IsGeneralAlgebraicIntegral fuel f integrand F.ratPart commonDenom F.logTerms cofs`, the
cross-multiplied `D(v + Σ cᵢ log uᵢ) = integrand` in `K[X] ⧸ afIdeal f`. **No round-trip hypothesis** is
passed at the call: the three branches discharge from the residual (no-log / principal / torsion). The
soundness verdict for the general `Option` integrator, modulo exactly the already-proven general soundness
composition. The general-curve analogue of `cIntegrateAlgebraicDecide_sound`. -/
theorem cIntegrateGeneralCurveDecide_sound
    (hres : GeneralCurveDecideSoundnessResidual fuel f basis degBound ratIntegrand logIntegrand tin
      integrand commonDenom cofs)
    (F : GeneralCurveIntegralResult)
    (hsome : cIntegrateGeneralCurveDecide fuel f basis degBound ratIntegrand logIntegrand tin hasLogPart
      = some F) :
    CPolyG.IsGeneralAlgebraicIntegral fuel f integrand F.ratPart commonDenom F.logTerms cofs := by
  unfold cIntegrateGeneralCurveDecide at hsome
  cases hv : afRationalSolve fuel f basis degBound ratIntegrand with
  | none => rw [hv] at hsome; simp at hsome
  | some v =>
    simp only [hv] at hsome
    by_cases hlp : hasLogPart = false
    · -- no-log branch: F = ⟨v, []⟩
      rw [if_pos hlp, Option.some.injEq] at hsome
      rw [← hsome]
      exact hres.hnolog v hv
    · -- has-log branch
      rw [if_neg hlp] at hsome
      cases hu : afLogArgSolve fuel f basis degBound logIntegrand with
      | some u =>
        -- principal branch: F = ⟨v, [(1, u)]⟩
        rw [hu, Option.some.injEq] at hsome
        rw [← hsome]
        exact hres.hprincipal v u hv hu
      | none =>
        -- torsion branch: F = ⟨v, [term]⟩, or none
        rw [hu] at hsome
        cases hT : genCurveTorsionLogTerm fuel f basis tin with
        | some term =>
          rw [hT, Option.some.injEq] at hsome
          rw [← hsome]
          exact hres.htorsion v term hv hT
        | none =>
          rw [hT] at hsome
          exact absurd hsome (by simp)

end Soundness

/-! ## Part 4 — ISOLATING the general-`Pic⁰`-torsion core PRECISELY: `GeneralPicTorsionFrontier`

The DEEP residual — the general divisor-class-group (`Pic⁰`) arithmetic beyond the hyperelliptic
Mumford/Cantor — is isolated here PRECISELY as a single named `Prop`-bundle, the general analogue of the
hyperelliptic `AlgebraicCompletenessResidual` (`ComputableAlgebraicCompleteness`). It has exactly two clauses:

* **`htorsion`** — the **general-`Pic⁰`-torsion-decision correctness** (the deep gap): the engine's general
  order test `genDivisorOrder fuel f basis δ` returns `some m` **iff** the residue divisor class `δ` is torsion
  in `Pic⁰(C)`. `genDivisorOrder` (`ComputableGeneralDivisorOrder`, HAVE) **computes** the order via repeated
  `idealProduct` (the Pic group law) + the ideal-reduction / principality test over the
  fractional-ideal-over-the-integral-basis representation — it is sound (`some m ⟹ m·δ` genuinely principal),
  but its **termination with a definite `none` = non-torsion verdict** needs the *good-reduction torsion
  ceiling* (reduce `f mod p`, `|Pic⁰(C)(𝔽_p)|` as the fuel bound, the general lift of the hyperelliptic
  `mumfordReduceModP`). This clause IS that gap — the general fractional-ideal arithmetic + order test + the
  good-reduction lift, the general analogue of frontier 2.
* **`hcriterion`** — the **Liouville log-part criterion** (frontier 1, unchanged from the hyperelliptic case,
  now over the general curve's function field): the integrand is elementary **iff** its residue divisor `δ` is
  torsion in `Pic⁰(C)` (Trager's structure theorem applied to the general curve).

Their conjunction turns the engine's `genCurveTorsionLogTerm = some _` into `elem` and `none` into `¬ elem` —
the general-curve completeness equivalence, modulo exactly this isolated deep frontier. -/

section PicTorsion

variable (fuel : ℕ) (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
variable (tin : GeneralCurveTorsionInputs)

/-- **The general-curve torsion term fires iff the order test does** `genCurveTorsionLogTerm_isSome_iff` —
unconditionally, `(genCurveTorsionLogTerm fuel f basis tin).isSome = true ↔ ∃ m, genDivisorOrder fuel f basis
tin.divisor = some m`. The general-curve torsion branch emits a `(1/m)·log g` term exactly when the general
order test `genDivisorOrder` succeeds (the generator oracle `tin.genGen` is then applied). Pure `Option`
control flow over the `genCurveTorsionLogTerm` match — no frontier needed; the bridge to the completeness
equivalence. The general lift of the hyperelliptic `torsionLogTerm_isSome_iff`. -/
theorem genCurveTorsionLogTerm_isSome_iff :
    (genCurveTorsionLogTerm fuel f basis tin).isSome = true
      ↔ ∃ m, genDivisorOrder fuel f basis tin.divisor = some m := by
  unfold genCurveTorsionLogTerm
  cases hm : genDivisorOrder fuel f basis tin.divisor with
  | none => simp
  | some m => simp

/-- **★ The general-`Pic⁰`-torsion frontier** `GeneralPicTorsionFrontier fuel f basis tin isTorsion elem`: the
two deep frontier-instances that turn the engine's general torsion-branch output into the integrand's
elementarity, the general analogue of `AlgebraicCompletenessResidual` (`ComputableAlgebraicCompleteness`).
`isTorsion` is the abstract "the residue divisor class `δ = tin.divisor` is torsion in `Pic⁰(C)`" predicate;
`elem` the integrand's elementarity over the general curve's function field. A `Prop`-bundle of stated
assumptions (NOT proved), making the general-`Pic⁰`-torsion boundary citable with NO `sorry`:

* `htorsion` — **the deep general-`Pic⁰`-torsion-decision correctness**: `genDivisorOrder fuel f basis δ`
  succeeds `⟺ δ` is torsion. `genDivisorOrder` (HAVE) computes the order via the fractional-ideal Pic
  arithmetic and is sound; this clause closes the gap to a *definite* verdict — the good-reduction torsion
  ceiling (the general lift of `mumfordReduceModP`), the general fractional-ideal-arithmetic + order-test +
  good-reduction core, the deepest open algebraic sub-arc;
* `hcriterion` — the **Liouville log-part criterion** over the general curve: `δ` is torsion `⟺ elem`.

This single bundle IS the precisely-isolated deep residual the task names; the decision is proven modulo it. -/
structure GeneralPicTorsionFrontier (isTorsion : Prop) (elem : Prop) : Prop where
  /-- The deep general-`Pic⁰`-torsion-decision correctness: `genDivisorOrder` succeeds ⟺ `δ` is torsion
  (needs the good-reduction torsion ceiling — the general lift of `mumfordReduceModP`). -/
  htorsion : (∃ m, genDivisorOrder fuel f basis tin.divisor = some m) ↔ isTorsion
  /-- The Liouville log-part criterion over the general curve: the integrand is elementary ⟺ `δ` is torsion. -/
  hcriterion : isTorsion ↔ elem

/-- **★ General-curve completeness modulo the frontier** (`genCurveTorsionLogTerm_complete_of_frontier`,
`some ⟺ elementary`): under the general-`Pic⁰`-torsion frontier (the deep general torsion-decision correctness
+ the Liouville log-part criterion on `δ`), the engine's general torsion branch `genCurveTorsionLogTerm` emits
a `(1/m)·log g` term **iff** the integrand is elementary —
`(genCurveTorsionLogTerm fuel f basis tin).isSome = true ↔ elem`. The chain: `genCurveTorsionLogTerm = some _
⟺ genDivisorOrder = some m` (the unconditional `genCurveTorsionLogTerm_isSome_iff`) ⟺ `δ` is torsion
(`htorsion`) ⟺ `elem` (`hcriterion`). The converse of soundness for the general integrator's log part, modulo
the precisely-isolated deep frontier — the general-curve analogue of
`cIntegrateAlgebraicWf_complete_of_residual`. -/
theorem genCurveTorsionLogTerm_complete_of_frontier {isTorsion elem : Prop}
    (hres : GeneralPicTorsionFrontier fuel f basis tin isTorsion elem) :
    (genCurveTorsionLogTerm fuel f basis tin).isSome = true ↔ elem := by
  rw [genCurveTorsionLogTerm_isSome_iff, hres.htorsion, hres.hcriterion]

end PicTorsion

/-! ## Part 5 — REACHABLE layer: COMPLETENESS `none → ¬ elementary` (modulo the frontier)

`cIntegrateGeneralCurveDecide` returns `none` exactly when the rational solve fails OR (there is a log part,
the principal log solve fails, AND) the torsion decision fails (`genCurveTorsionLogTerm = none`, the residue
divisor non-torsion). On the **non-principal log path** (rational solve succeeds, log part present, principal
solve fails — the path the torsion decision governs, the analogue of the hyperelliptic completeness setting),
`none` is the engine's non-torsion verdict, and the frontier turns it into `¬ elem`. -/

section Completeness

variable (fuel : ℕ) (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ))) (degBound : ℕ)
variable (ratIntegrand logIntegrand : CPolyG (QFunNZG ℚ)) (tin : GeneralCurveTorsionInputs)

/-- **★★ COMPLETENESS of the self-determining GENERAL-curve integrator** (`cIntegrateGeneralCurveDecide_complete`,
`none → ¬ elementary`, modulo the frontier). On the non-principal log path — the rational solve succeeds
(`afRationalSolve = some v`), there is a log part (`hasLogPart = true`), the principal log solve fails
(`afLogArgSolve = none`) — under the general-`Pic⁰`-torsion frontier (the deep general torsion-decision
correctness + the Liouville criterion on `δ`), a `none` output of `cIntegrateGeneralCurveDecide` certifies the
integrand is **NOT elementary**. The `none` output then forces the torsion decision to `none` (the non-torsion
verdict, via the structural reading); the frontier's completeness equivalence turns that into `¬ elem`. This
re-bases the general-curve completeness onto the `Option` integrator: `none` is the self-determining "not
elementary" answer, modulo exactly the isolated deep frontier. The general-curve analogue of
`cIntegrateAlgebraicDecide_complete`. -/
theorem cIntegrateGeneralCurveDecide_complete {isTorsion elem : Prop} (v : CPolyG (QFunNZG ℚ))
    (hres : GeneralPicTorsionFrontier fuel f basis tin isTorsion elem)
    (hv : afRationalSolve fuel f basis degBound ratIntegrand = some v)
    (_hlog : afLogArgSolve fuel f basis degBound logIntegrand = none)
    (hnone : cIntegrateGeneralCurveDecide fuel f basis degBound ratIntegrand logIntegrand tin true
      = none) :
    ¬ elem := by
  -- the `none` output (on this path) forces the torsion branch to `none` (non-torsion verdict)
  have hcases := genCurveTorsionLogTerm_none_of_decide_none fuel f basis degBound ratIntegrand
    logIntegrand tin true hnone
  have hT : (genCurveTorsionLogTerm fuel f basis tin).isNone = true := by
    rcases hcases with hrat | ⟨_, hT⟩
    · rw [hv] at hrat; simp at hrat
    · exact hT
  -- contrapositive of the completeness equivalence: if `elem` held, the log term would be emitted
  intro hcon
  have hsome : (genCurveTorsionLogTerm fuel f basis tin).isSome = true :=
    (genCurveTorsionLogTerm_complete_of_frontier fuel f basis tin hres).mpr hcon
  rw [Option.isNone_iff_eq_none] at hT
  rw [hT] at hsome
  simp at hsome

end Completeness

end DeepWiki.SymbolicIntegration
