import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalExtension
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalWellFounded
import DeepWiki.SymbolicIntegration.Computable.Tower.Field
import DeepWiki.SymbolicIntegration.Computable.Tower.Deriv
import DeepWiki.SymbolicIntegration.Computable.Tower.GcdFFCore

/-! # The grand unification: simple radicals over a TRANSCENDENTAL tower (Bronstein 1990)
The radical-extension engine (`ComputableRadicalExtension`) integrates **algebraic** functions `F(y)`
with `yⁿ = f ∈ F`; the differential-tower engine (`ComputableTowerField`/`ComputableTowerDeriv`) builds
the **transcendental** tower `ℚ ⊂ ℚ(x) ⊂ ℚ(x)(t₁) ⊂ …` with its computable `CDiffField` derivation. Up to
now the two ran *separately*: the radical's base field `F` was a *single* level (`QFunNZG ℚ ≅ ℚ(x)`), or
the radicand lived in the polynomial ring `ℚ(x)[θ]` over a tower with `θ` a formal indeterminate.

This file performs the **Bronstein 1990 grand unification** ("Integration of Elementary Functions"):
*elementary functions = transcendental monomials WITH an algebraic radical on top*. We instantiate
`RadExt` at `α = a transcendental tower level` — concretely `α = ℚ(x)(eˣ) = QFunNZG (QFunNZG ℚ)` with the
**exponential** derivation `t₁' = t₁` — so the radical `y² = ρ` has radicand `ρ = eˣ+1 ∈ ℚ(x)(eˣ)`, a
genuine field element of the transcendental tower (not a polynomial indeterminate). The algebraic arc
(`radDeriv`, `radMul`, the diagonal derivation) then runs **over** the exponential engine.

* **The exponential `CDiffField` instance** `expTowerDiff` — the default tower derivation
  `instCDiffFieldQFunNZG` makes the new monomial *independent* (`t₁' = 1`, as level-1's `x` has `Dx = 1`).
  For `t₁ = eˣ` we need `t₁' = t₁`; this is exactly `towerDerivQFunNZG [t₁]` (the fraction-field quotient
  rule whose monomial derivative is `Dt₁ = t₁`, i.e. `Dt₁ = [0,1]` as a `CPolyG (QFunNZG ℚ)`). We supply
  this as a **local** `CDiffField (QFunNZG (QFunNZG ℚ))` (passed explicitly to the radical ops via `@`),
  *not* a global instance — the default `t₁'=1` instance stays in place for the rest of the library.

* **The headline** (`native_decide`): over `α = ℚ(x)(eˣ)`, `n = 2`, `ρ = eˣ+1`, the integrand
  `eˣ/√(eˣ+1) = θ/y = [0, θ/(θ+1)]` (a pure-`y` `RadElem`) integrates to `2√(eˣ+1) = 2y = [0, 2]`,
  validated through the **actual** `radDeriv`: `radDeriv [0,2] = [0, θ/(θ+1)]` (since `y' = ρ'/(2y) =
  θ'/(2y) = θ/(2y)`, so `radDeriv(2y) = 2·[0, ρ'/(2ρ)] = [0, θ/(θ+1)]`). This is `∫ eˣ/√(eˣ+1) dx =
  2√(eˣ+1)` validated over the transcendental tower — Bronstein-1990 elementary integration
  (transcendental + algebraic) for a concrete case.

* **The `log` companion** (`native_decide`): the same arc with a **logarithmic** monomial `θ = log x`
  (`θ' = 1/x`), validating `∫ dx/(x√(log x)) = 2√(log x)` over `α = ℚ(x)(log x)` — `radDeriv [0,2] =
  [0, (1/x)/(log x)]`. Two transcendental kinds (exp, log) carry the radical arc.

Everything reduces in the native compiler: `RadElem (QFunNZG (QFunNZG ℚ))` is a list over the computable
ℚ(x)(t₁), the exponential/log derivation `towerDerivQFunNZG [t₁]` is list arithmetic, the subtype proofs
are `Prop`-erased. The instantiation is **pure reuse** — the radical ops and the tower's `CField`/derivation
are taken verbatim; only the choice of monomial derivative (`[t₁]` vs `[1]`) is local to this file. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem

/-! ### The exponential tower base `α = ℚ(x)(eˣ) = QFunNZG (QFunNZG ℚ)`

`Lvl2 = QFunNZG (QFunNZG ℚ)` is the field ℚ(x)(t₁) (from `ComputableTowerField`). To make `t₁ = eˣ` we
override its derivation: the level-2 `CField` and `CFieldDomain` instances are reused as-is, but the
`CDiffField` becomes `towerDerivQFunNZG [t₁]` (so `t₁' = t₁`) instead of the default `towerDerivQFunNZG
[1]` (`t₁' = 1`). We expose `t₁` and the radicand `ρ = t₁+1` as concrete `Lvl2` values. -/

/-- A level-2 scalar `c ∈ Lvl2 = ℚ(x)(t₁)` from a numerator `CPolyG (QFunNZG ℚ)` over the denominator `1`
(`[1]` is `cisZeroG`-nonzero). The level-2 analogue of `qxOfNum`. -/
def lvl2OfNum (num : CPolyG (QFunNZG ℚ)) : Lvl2 :=
  ⟨(num, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

/-- The exponential monomial `θ = t₁ = eˣ ∈ ℚ(x)(t₁)` (numerator `[0, 1]` over ℚ(x): `t₁ = 0 + 1·t₁`,
denominator `[1]`). -/
def expTheta : Lvl2 := lvl2OfNum [(CField.zero : QFunNZG ℚ), CField.one]

/-- The radicand `ρ = θ + 1 = eˣ + 1 ∈ ℚ(x)(t₁)` (numerator `[1, 1]` over ℚ(x): `1 + t₁`). The `F`-element
with `y² = ρ`. -/
def expRadicand : Lvl2 := lvl2OfNum [(CField.one : QFunNZG ℚ), CField.one]

/-- The new-monomial derivative `Dt₁ = t₁ = [0, 1] ∈ CPolyG (QFunNZG ℚ) = ℚ(x)[t₁]` — the data that makes
`t₁` **exponential** (`t₁' = t₁`), to be fed to `towerDerivQFunNZG`. (The default tower uses `[1]`, which
makes `t₁` an independent variable `t₁' = 1`.) -/
def expDt1 : CPolyG (QFunNZG ℚ) := [(CField.zero : QFunNZG ℚ), CField.one]

/-- **The exponential `CDiffField (QFunNZG (QFunNZG ℚ))` instance** — `cderiv := towerDerivQFunNZG [t₁]`,
the fraction-field quotient rule whose new-monomial derivative is `Dt₁ = t₁` (so `t₁' = t₁`, i.e.
`t₁ = eˣ`). A **local** instance (a `def`, not a global `instance`) supplied explicitly to the radical ops
via `@`, so the library's default `t₁'=1` tower derivation is untouched. Computable (`towerDerivQFunNZG`
is list arithmetic, the `CFieldDomain` proofs are `Prop`-erased), so it reduces under `native_decide`.
`@[reducible]` (a `def` of class type), so the explicit `@`-applications unfold to the engine ops. -/
@[reducible] def expTowerDiff : CDiffField Lvl2 where
  cderiv := QFunNZG.towerDerivQFunNZG expDt1

/-- **★ `D(t₁) = t₁` over ℚ(x)(t₁) for the exponential instance** (`native_decide`): the local derivation
`expTowerDiff` (`towerDerivQFunNZG [t₁]`) sends the monomial `t₁` to itself — confirming `t₁ = eˣ`,
`t₁' = t₁`. Tested by `isZeroNZG` of `D(t₁) − t₁`. THE EXPONENTIAL TOWER DERIVATION COMPUTES. -/
theorem expTheta_deriv_eq_self :
    CField.isZero (CField.sub (@CDiffField.cderiv _ _ expTowerDiff expTheta) expTheta)
      = true := by native_decide

/-- **`D(t₁+1) = t₁` over ℚ(x)(t₁)** (`native_decide`): the radicand derivative `ρ' = (t₁+1)' = t₁`
(the constant `1` is annihilated), matching `θ' = θ`. The numerator `ρ' = θ` of `y' = ρ'/(2y)`. -/
theorem expRadicand_deriv_eq_theta :
    CField.isZero (CField.sub (@CDiffField.cderiv _ _ expTowerDiff expRadicand) expTheta)
      = true := by native_decide

/-! ### The radical `y² = eˣ+1` over the exponential tower (`native_decide`)

`α = ℚ(x)(eˣ)` (with `expTowerDiff`), `n = 2`, `f = ρ = eˣ+1`. The generator `y = √(eˣ+1)`. We check the
defining relation `y·y = ρ` (`radMul`'s `y² → ρ` fold) and the diagonal derivation `D(y) = (ρ'/(2ρ))·y =
(θ/(2(θ+1)))·y` (the `radDeriv` with the **exponential** base derivation). Both run in the native compiler
over the level-2 tower carrier. -/

/-- The diagonal multiplier `ℓ = ρ'/(2ρ) = θ/(2(θ+1)) ∈ ℚ(x)(eˣ)` for `D(y) = ℓ·y`, computed by
`logDerRadicand` at the **exponential** instance `expTowerDiff` (so `ρ' = θ`). -/
def expRadLogDer : Lvl2 := @logDerRadicand _ _ expTowerDiff 2 expRadicand

/-- **★ `y·y = eˣ+1` over ℚ(x)(eˣ)** (`native_decide`): the square of `y = √(eˣ+1)` in
`(ℚ(x)(eˣ))[y]/(y² − (eˣ+1))` reduces, via `radMul`'s `y² → ρ` fold, to `ρ = eˣ+1`. Checked by `radIsZero`
of `y·y − ρ`. THE RADICAL CARRIER COMPUTES OVER THE TRANSCENDENTAL TOWER — the radicand is a genuine
ℚ(x)(eˣ) field element, not a polynomial indeterminate. -/
theorem expRadGen_sq_eq_radicand :
    radIsZero (radSub (radMul 2 expRadicand (radGen : RadElem Lvl2) radGen) [expRadicand])
      = true := by native_decide

/-- **★ `D(y) = (θ/(2(θ+1)))·y` over ℚ(x)(eˣ)** (`native_decide`): the diagonal radical derivation of
`y = √(eˣ+1)`, with the **exponential** base derivation (`ρ' = θ`), is `ℓ·y` with `ℓ = ρ'/(2ρ) =
θ/(2(θ+1))`. Checked by `radIsZero` of `D(y) − [0, ℓ]`. THE RADICAL DERIVATION COMPUTES OVER THE EXP
TOWER — and it is diagonal (`D(y)` has only a `y`-component), the algebraic arc on top of the
exponential engine. -/
theorem expRadDeriv_radGen_eq :
    radIsZero (radSub (@radDeriv _ _ expTowerDiff 2 expRadicand (radGen : RadElem Lvl2))
        [CField.zero, expRadLogDer]) = true := by native_decide

/-! ### ★ THE HEADLINE: `∫ eˣ/√(eˣ+1) dx = 2√(eˣ+1)` over ℚ(x)(eˣ) (`native_decide`)

The Bronstein-1990 elementary integral, validated through the **actual** `radDeriv` over the
transcendental tower. The integrand `eˣ/√(eˣ+1) = θ/y`. Rationalizing, `θ/y = θ·y/y² = θ·y/ρ =
(θ/(θ+1))·y`, a pure-`y` `RadElem`: `integrand = [0, θ/(θ+1)]`. The claimed antiderivative `2√(eˣ+1) = 2y`
is the `RadElem` `[0, 2]`. The validation: `radDeriv [0, 2] = integrand`, since `(2y)' = 2·y' =
2·(ρ'/(2ρ))·y = (ρ'/ρ)·y = (θ/(θ+1))·y`. -/

/-- The integrand `eˣ/√(eˣ+1) = θ/y` as the pure-`y` `RadElem` `[0, θ/(θ+1)]` over ℚ(x)(eˣ): rationalize
`θ/y = θy/y² = θy/ρ = (θ/(θ+1))y`, so the only coefficient is the `y`-coefficient `θ/(θ+1) = eˣ/(eˣ+1)`. -/
def expIntegrand : RadElem Lvl2 :=
  [CField.zero, CField.div expTheta expRadicand]

/-- The antiderivative `2√(eˣ+1) = 2y` as the `RadElem` `[0, 2]` over ℚ(x)(eˣ) (the constant `0` plus
`2·y`). -/
def expAntideriv : RadElem Lvl2 :=
  [CField.zero, CField.add CField.one CField.one]

/-- **★★ THE GRAND UNIFICATION: `∫ eˣ/√(eˣ+1) dx = 2√(eˣ+1)` over ℚ(x)(eˣ)** (`native_decide`) — the
**actual** radical derivation `radDeriv` (with the exponential base derivation `t₁' = t₁`) of the
antiderivative `2y = [0, 2]` equals the integrand `θ/y = [0, θ/(θ+1)]`. Since `(2y)' = 2·(ρ'/(2ρ))·y =
(ρ'/ρ)·y = (θ/(θ+1))·y` and `θ/(θ+1) = eˣ/(eˣ+1)` is exactly the rationalized integrand `eˣ/√(eˣ+1)`,
this is `∫ eˣ/√(eˣ+1) dx = 2√(eˣ+1)` validated through `radDeriv` OVER A TRANSCENDENTAL TOWER. Checked by
`radIsZero` of `radDeriv(2y) − integrand`. THE ALGEBRAIC ARC RUNS OVER THE EXPONENTIAL ENGINE —
Bronstein 1990's elementary integration (transcendental + algebraic) for a concrete `∫`. -/
theorem expIntegral_eq :
    radIsZero (radSub (@radDeriv _ _ expTowerDiff 2 expRadicand expAntideriv) expIntegrand)
      = true := by native_decide

/-! ### The `log` companion: `∫ dx/(x√(log x)) = 2√(log x)` over ℚ(x)(log x) (`native_decide`)

The same algebraic arc with a **logarithmic** monomial `θ = log x` (so `v = x`, `θ' = v'/v = 1/x ∈ ℚ(x)`).
Base tower `α = ℚ(x)(log x) = QFunNZG (QFunNZG ℚ)`, but now the new-monomial derivative is `Dt₁ = 1/x ∈
ℚ(x)` (a degree-`0` element of `ℚ(x)[t₁]`, the field element `1/x`), so `t₁' = 1/x`. Radicand `ρ = θ =
log x` (`y² = log x`, `y = √(log x)`). The integrand `1/(x√(log x)) = (1/x)/y = (1/x)·y/y² = (1/x)·y/ρ =
((1/x)/(log x))·y = [0, (1/x)/(log x)]`; the antiderivative `2√(log x) = 2y = [0, 2]`. Validation:
`radDeriv [0,2] = integrand`, since `(2y)' = (ρ'/ρ)·y = ((1/x)/(log x))·y`. -/

/-- The level-2 element `1/x ∈ ℚ(x) ⊂ ℚ(x)(log x)` as a `Lvl2` value: numerator `[1] ∈ ℚ(x)[t₁]` whose
single coefficient is `1/x ∈ ℚ(x)`, over denominator `[1]`. (`1/x` as `QFunNZG ℚ` is `1` over `x`.) -/
def lvl2OneOverX : Lvl2 :=
  lvl2OfNum [qxOfFrac [1] [0, 1] (by decide)]

/-- The logarithmic monomial `θ = t₁ = log x ∈ ℚ(x)(log x)` (numerator `[0, 1]`, denominator `[1]`).
Same carrier value as `expTheta`; only the derivation differs (`log` vs `exp`). -/
def logTheta : Lvl2 := lvl2OfNum [(CField.zero : QFunNZG ℚ), CField.one]

/-- The radicand `ρ = θ = log x ∈ ℚ(x)(log x)` (`y² = log x`), numerator `[0, 1]`, denominator `[1]`. -/
def logRadicandT : Lvl2 := lvl2OfNum [(CField.zero : QFunNZG ℚ), CField.one]

/-- The new-monomial derivative `Dt₁ = θ' = 1/x ∈ CPolyG (QFunNZG ℚ) = ℚ(x)[t₁]` for `θ = log x`: the
degree-`0` polynomial `[1/x]` (a single `ℚ(x)` coefficient `1/x`). This makes `t₁` **logarithmic**
(`t₁' = 1/x`), as opposed to `[t₁]` (exp) or `[1]` (independent). -/
def logDt1 : CPolyG (QFunNZG ℚ) := [qxOfFrac [1] [0, 1] (by decide)]

/-- **The logarithmic `CDiffField (QFunNZG (QFunNZG ℚ))` instance** — `cderiv := towerDerivQFunNZG [1/x]`,
the fraction-field quotient rule whose new-monomial derivative is `Dt₁ = 1/x` (so `t₁' = 1/x`, i.e.
`t₁ = log x`). A **local** instance supplied explicitly via `@`. Computable, so it `native_decide`s.
`@[reducible]` (a `def` of class type). -/
@[reducible] def logTowerDiff : CDiffField Lvl2 where
  cderiv := QFunNZG.towerDerivQFunNZG logDt1

/-- **★ `D(t₁) = 1/x` over ℚ(x)(log x) for the logarithmic instance** (`native_decide`): the local
derivation `logTowerDiff` (`towerDerivQFunNZG [1/x]`) sends `t₁ = log x` to `1/x` — confirming
`t₁ = log x`, `t₁' = 1/x`. Tested by `isZeroNZG` of `D(t₁) − 1/x`. THE LOG TOWER DERIVATION COMPUTES. -/
theorem logTheta_deriv_eq_oneOverX :
    CField.isZero (CField.sub (@CDiffField.cderiv _ _ logTowerDiff logTheta) lvl2OneOverX)
      = true := by native_decide

/-- The diagonal multiplier `ℓ = ρ'/(2ρ) = (1/x)/(2·log x) ∈ ℚ(x)(log x)` for `D(y) = ℓ·y`, at the
**logarithmic** instance `logTowerDiff` (so `ρ' = 1/x`). -/
def logRadLogDer : Lvl2 := @logDerRadicand _ _ logTowerDiff 2 logRadicandT

/-- **★ `y·y = log x` over ℚ(x)(log x)** (`native_decide`): the square of `y = √(log x)` reduces, via
`radMul`'s `y² → ρ` fold, to `ρ = log x`. Checked by `radIsZero` of `y·y − ρ`. THE RADICAL CARRIER
COMPUTES over the logarithmic tower. -/
theorem logRadGen_sq_eq_radicand :
    radIsZero (radSub (radMul 2 logRadicandT (radGen : RadElem Lvl2) radGen) [logRadicandT])
      = true := by native_decide

/-- The integrand `1/(x√(log x)) = (1/x)/y` as the pure-`y` `RadElem` `[0, (1/x)/(log x)]` over
ℚ(x)(log x): rationalize `(1/x)/y = (1/x)y/ρ = ((1/x)/(log x))y`. -/
def logIntegrand : RadElem Lvl2 :=
  [CField.zero, CField.div lvl2OneOverX logRadicandT]

/-- The antiderivative `2√(log x) = 2y` as the `RadElem` `[0, 2]` over ℚ(x)(log x). -/
def logAntideriv : RadElem Lvl2 :=
  [CField.zero, CField.add CField.one CField.one]

/-- **★★ `∫ dx/(x√(log x)) = 2√(log x)` over ℚ(x)(log x)** (`native_decide`) — the **actual** radical
derivation `radDeriv` (with the logarithmic base derivation `t₁' = 1/x`) of `2y = [0, 2]` equals the
integrand `(1/x)/y = [0, (1/x)/(log x)]`. Since `(2y)' = (ρ'/ρ)·y = ((1/x)/(log x))·y`, this is
`∫ dx/(x√(log x)) = 2√(log x)` validated through `radDeriv` over the **logarithmic** transcendental
tower. The algebraic arc carries over both transcendental kinds (exp, log). -/
theorem logIntegral_eq :
    radIsZero (radSub (@radDeriv _ _ logTowerDiff 2 logRadicandT logAntideriv) logIntegrand)
      = true := by native_decide

/-! ### Stretch: the generic rational-part DRIVER runs over a tower base (`native_decide`)

The previous sections used a *headline antiderivative* validated through `radDeriv`. This section runs the
**generic multi-case rational-part driver** (`radIntegrateCase2Wf` / `radIntegrateRationalWf`) over a
tower-level base field — the drivers are `[CField α]`-generic (with `CFracGcdCoreWf α` at the full-driver
front end), and `CFracGcdCoreWf (QFunNZG ℚ)` resolves recursively, so they instantiate at
`α = QFunNZG ℚ ≅ ℚ(x)` with **no** new code. The radical then lives over `ℚ(x)[θ]` (`θ = t₁` an independent
monomial over ℚ(x), `θ' = 1`), i.e. the **stacked** extension `(ℚ(x)(t₁))[y]/(y² − ρ)`.

Concretely: radicand `ρ = θ³ − θ = θ(θ−1)(θ+1) ∈ ℚ(x)[θ]` (squarefree), `W = θ` (a branch place, `W ∣ ρ`),
integrand `1/(θ²·√(θ³−θ))`. The driver `radIntegrateCase2Wf` runs two Case-2 Hermite steps (`k = 2 → 1`), and
its output is validated through the **actual** `radDeriv 2` at **level 2** (`α = Lvl2 = ℚ(x)(t₁)`, the
default independent-`t₁` derivation): `radDeriv(vNum/(θ²√ρ)) = 1/(θ²√ρ) − Crem/(θ√ρ)` — the master identity
`D(∫) = rational-part`. The full multi-case driver `radIntegrateRationalWf` likewise computes over the
tower base (dispatching the squarefree decomposition through `CFracGcdCoreWf (QFunNZG ℚ)`). -/

open CPolyG

/-- Driver-over-tower radicand `ρ = θ³ − θ = θ(θ−1)(θ+1) ∈ ℚ(x)[θ]` (`y² = ρ`, squarefree), the
`CPolyG (QFunNZG ℚ)` `[0, −1, 0, 1]` with genuine ℚ(x) coefficients (`−1, 1 ∈ ℚ(x)` via `qxOfNum`). -/
def drvRho : CPolyG (QFunNZG ℚ) := [CField.zero, qxOfNum [-1], CField.zero, qxOfNum [1]]

/-- Driver-over-tower squarefree factor `W = θ ∈ ℚ(x)[θ]` (a branch place, `W ∣ ρ`), `[0, 1]`. -/
def drvW : CPolyG (QFunNZG ℚ) := [CField.zero, CField.one]

/-- Driver-over-tower numerator `C₀ = 1 ∈ ℚ(x)[θ]` (integrand `1/(θ²·√(θ³−θ))`), `[1]`. -/
def drvC : CPolyG (QFunNZG ℚ) := [CField.one]

/-- **The generic fuel-free Case-2 driver run over the tower base** `radIntegrateCase2Wf W ρ 2 C =
(Crem, vNum)` on
`∫ 1/(θ²·√(θ³−θ))` over `α = QFunNZG ℚ ≅ ℚ(x)` — two Case-2 Hermite steps (`k = 2 → 1`), returning the
`k = 1` residual `Crem` and the accumulated rational-part numerator `vNum` over the common denominator
`W² = θ²`. The driver is taken **verbatim**; only the base field is the tower level ℚ(x). -/
def drvRun : CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ) := radIntegrateCase2Wf drvW drvRho 2 drvC

/-- The radicand `ρ = θ³ − θ` lifted to a level-2 scalar `ρ ∈ ℚ(x)(t₁) = Lvl2` (numerator `ρ` over `[1]`),
the radicand for `radDeriv 2` at level 2. -/
def drvRhoLvl2 : Lvl2 := lvl2OfNum drvRho

/-- The common-denominator power `W² = θ²` over `ℚ(x)[θ]` (the denominator of `vNum`), `cpowG W 2`. -/
def drvW2 : CPolyG (QFunNZG ℚ) := cpowG drvW 2

/-- The rational part `v = vNum/(W²·y)` lifted to `RadElem Lvl2` — the pure-`y` element `[0, vNum/(W²·ρ)]`
over ℚ(x)(t₁) (an `R/y` form is `[0, R/ρ]` since `R/y = (R/ρ)·y`), with `vNum, W², ρ` lifted to level-2
scalars by `lvl2OfNum`. -/
def drvVlift : RadElem Lvl2 :=
  [CField.zero, CField.div (lvl2OfNum drvRun.2) (lvl2OfNum (cmulG drvW2 drvRho))]

/-- The integrand's rational part `C₀/(W²y) − Crem/(Wy)` lifted to `RadElem Lvl2` — the pure-`y` element
`[0, C₀/(W²·ρ) − Crem/(W·ρ)]` over ℚ(x)(t₁). -/
def drvRatLift : RadElem Lvl2 :=
  [CField.zero,
    CField.sub (CField.div (lvl2OfNum drvC) (lvl2OfNum (cmulG drvW2 drvRho)))
      (CField.div (lvl2OfNum drvRun.1) (lvl2OfNum (cmulG drvW drvRho)))]

/-- **★ The generic Case-2 driver integrates over a TOWER base** (`native_decide`): over the stacked
radical extension `(ℚ(x)(t₁))[y]/(y² − (t₁³−t₁))`, the **actual** diagonal derivation `radDeriv 2` (the
default independent-`t₁` derivation, `t₁' = 1`) of the driver's iterated Case-2 rational part `v =
vNum/(θ²√ρ)` equals `1/(θ²√ρ) − Crem/(θ√ρ)`, the rational part of `1/(θ²·√(θ³−θ))`. Checked by `radIsZero`
of the difference at level 2. THE GENERIC MULTI-CASE RATIONAL DRIVER (`radIntegrateCase2Wf`) RUNS — and
`D(∫) = rational-part` holds — OVER A TRANSCENDENTAL TOWER BASE, with no driver code changed: only the
base field is the tower level ℚ(x). -/
theorem drvDriver_integrates :
    radIsZero (radSub (radDeriv 2 drvRhoLvl2 drvVlift) drvRatLift) = true := by native_decide

/-- Full-driver denominator `B = θ² ∈ ℚ(x)[θ]` (the `W`-factor `θ` at multiplicity `2`), `[0, 0, 1]`. -/
def drvB : CPolyG (QFunNZG ℚ) := [CField.zero, CField.zero, CField.one]

/-- **The full fuel-free multi-case driver run over the tower base** `radIntegrateRationalWf ρ R B` on
`∫ 1/(θ²·√(θ³−θ))` over `α = QFunNZG ℚ ≅ ℚ(x)` — squarefree-decomposes `B = θ²`, classifies `θ` as a
`W`-factor (`θ ∣ ρ`), partial-fractions, and dispatches to the fuel-free iterated Case-2 reduction, **all**
through `CFracGcdCoreWf (QFunNZG ℚ)` (resolved recursively). Returns one per-factor record. -/
def drvFullRun :
    List (Bool × CPolyG (QFunNZG ℚ) × ℕ × CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ)) :=
  radIntegrateRationalWf drvRho drvC drvB

/-- **★ The full fuel-free multi-case driver `radIntegrateRationalWf` computes over the tower base**
(`native_decide`): the squarefree-decomposition + partial-fraction + V/W-classification + dispatch pipeline
runs over `α = ℚ(x)` (the squarefree factorization through the recursive `CFracGcdCoreWf (QFunNZG ℚ)`),
producing exactly one per-factor record for the single `W`-factor `θ` of `B = θ²`. THE ENTIRE GENERIC
RATIONAL-PART DRIVER INSTANTIATES AT A TOWER-LEVEL BASE FIELD — `CFracGcdCoreWf` resolving recursively is
what makes it run. -/
theorem drvFullRun_length : drvFullRun.length = 1 := by native_decide

/-! ### `#print axioms` — the headline over-tower results

Each over-tower headline carries the standard `[propext, Classical.choice, Quot.sound]` plus the
`native_decide` compiler axiom — no `sorry`, no extra axiom. The radical carrier `y² = ρ`, the diagonal
derivation `D(y) = (ρ'/(2ρ))·y`, and the end-to-end `∫ = 2√ρ` all reduce in the native compiler over the
transcendental tower (exponential and logarithmic), with the base field's `CDiffField` derivation a
genuine tower derivation. The algebraic-radical arc runs over a TRANSCENDENTAL TOWER base — the
Bronstein-1990 grand unification (elementary = transcendental + algebraic) for a concrete `∫`. -/

-- Exponential tower base: `t₁' = t₁`, radicand `ρ = eˣ+1`:
#print axioms expTheta_deriv_eq_self
#print axioms expRadGen_sq_eq_radicand
#print axioms expRadDeriv_radGen_eq

-- ★★ The headline: `∫ eˣ/√(eˣ+1) dx = 2√(eˣ+1)` over ℚ(x)(eˣ):
#print axioms expIntegral_eq

-- Logarithmic companion: `t₁' = 1/x`, `∫ dx/(x√(log x)) = 2√(log x)` over ℚ(x)(log x):
#print axioms logTheta_deriv_eq_oneOverX
#print axioms logIntegral_eq

-- Stretch: the generic rational-part driver runs (and `D(∫) = rational-part`) over a tower base ℚ(x):
#print axioms drvDriver_integrates
#print axioms drvFullRun_length

end DeepWiki.SymbolicIntegration
