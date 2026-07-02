import DeepWiki.SymbolicIntegration.ComputableHyperexpSpecial
import DeepWiki.SymbolicIntegration.ComputableHyperexpNormalCore
import DeepWiki.SymbolicIntegration.ComputableTowerWellFounded

/-! # The hyperexponential normal part via residual feedback (Bronstein §5.9)
`ComputableHyperexpSpecial` closed the §5.10 **special** part of a hyperexponential integral
(`∫ 1/exp = −1/exp`); `ComputableHyperexpBoundary` characterized the §5.9 **normal**-part frontier
explicitly. For a hyperexponential monomial `t` (`Dt = η·t`) the Rothstein–Trager logarithmic step
**overshoots**: the §5.6 residue construction gives a log part `∑ᵢ cᵢ·log(vᵢ)` whose derivative is
`fₙ + R`, not `fₙ`, where the residual

```
  R = η · ∑ᵢ cᵢ   ∈ k   (one tower level down — a rational function of x)
```

is exactly the `extendDeriv_logPart_eq_div_add_residual` leftover `C(η·∑ res)`. Since `R ∈ k` is
elementary-integrable, the correct integral is

```
  ∫ fₙ = (∑ᵢ cᵢ·log vᵢ)  −  ∫ R         (the §5.9 HyperexponentialReduce feedback)
```

and `∫ R` is a **base** integral over `k = QFunNZG ℚ = ℚ(x)`, solved by the recursive Risch-DE oracle
in its pure-integration mode `CRischField.crischDESolve 0 R` (`Dy = R`). This file builds that feedback
and demonstrates the **worked example** `∫ 1/(exp x − 1) dx = log(exp x − 1) − x` by `native_decide`.

## §5.9 the algorithm
1. Run `cIntegrateReducedG` on the normal part `fₙ` — its Hermite rational part `g` is correct, but its
   Rothstein–Trager `logs = [(cᵢ, vᵢ)]` overshoot by `R`.
2. Read the residual `R = η · ∑ᵢ cᵢ` (`cHyperexpResidualG`), `η = cExpEtaG Dt`, `∑ᵢ cᵢ` the sum of the
   §5.6 residue coefficients (the `logs` coefficients).
3. Integrate the base residual `∫ R` over `k` by `CRischField.crischDESolve 0 R` (the §6 pure-integration
   `Dy = R`); `none` if `R` is non-elementary as a function of `x` (it never is for a genuine `k`-rational
   `R`, but the unreduced-fraction representation can block the solve — see the scope note).
4. Subtract: `∫ fₙ = g − ∫R + ∑ᵢ cᵢ·log vᵢ` (the rational part `g` adjusted by `−∫R`, a constant in `t`).

**★ The headline `native_decide`** integrates `∫ 1/(exp x − 1) dx = log(exp x − 1) − x` over `ℚ(x)[t]`
(`t = exp x`, `Dt = η·t`, `η = 1`): the RT step lands `log(t−1)` with `D(log(t−1)) = t/(t−1) = fₙ + 1`,
so `R = η·∑res = 1·1 = 1`; the base integral `∫1 = x` feeds back, giving `∫fₙ = log(t−1) − x`, certified
`D(∫f) = f` by `checkIdentityG`. The plain `cIntegrateReducedG` overshoots (`checkIdentityG = false`) —
the companion `_reduced_overshoots` fact. Everything stays `[CField α]`/`[CDiffField α]`/`[CRischField
α]`-only (`Prop`-erased subtype proofs), so `native_decide` reduces.

**Scope.** §5.9 for a hyperexponential monomial with an elementary base residual `R`. The headline lands
the residual `R = 1` (a genuine `k`-constant, kept reduced); a genuinely non-constant base residual
`R = η·∑res` (e.g. `t = exp(x²)`, `η = 2x`, residue `1/(2x)`, again `R = 1` but assembled as the
**unreduced** fraction `2x/2x`) is held back not by non-elementarity but by the deliberately
**unreduced** `QFunNZG` fraction representation (`ComputableTowerField`: "Fractions are kept unreduced"):
`crischDESolve` over `k` reads the un-cancelled `2x/2x` and its weak-normalizer/normal-denominator stages
trip on the spurious denominator. Reducing `QFunNZG` fractions (a gcd-cancel layer) is the precise
remaining gap — engine work, out of scope here. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

/-! ### The hyperexponential residual `R = η · ∑ᵢ cᵢ` (Bronstein §5.9, the overshoot)

For a hyperexponential `t` (`Dt = η·t`), the §5.6 logarithmic construction `∑ᵢ cᵢ·log(vᵢ)` of a normal
part `fₙ` has derivative `fₙ + R` with `R = C(η·∑ res α) ∈ k` (the `extendDeriv_logPart_eq_div_add_residual`
residual). The residue coefficients `cᵢ` ARE the §5.6 residues `res α`, so `∑ res α = ∑ᵢ cᵢ` is the sum
of the `logs` coefficients and `R = η · ∑ᵢ cᵢ ∈ α` is a constant in `t` — a base-field element. -/

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]

/-! ### The §5.9 normal-part integrator `∫ fₙ = logPart − ∫R`

`cIntegrateHyperexpNormalG` integrates a **normal** part `fₙ = a/d` of a hyperexponential monomial by
running the reduced capstone (`cIntegrateReducedG` — correct Hermite rational part `g`, overshooting RT
logs), reading the residual `R = η·∑res` (`cHyperexpResidualG`), integrating the base residual `∫R` over
`α` by `CRischField.crischDESolve 0 R` (the pure-integration `Dy = R`), and subtracting `∫R` from the
rational part. The result `g − ∫R + ∑ᵢ cᵢ·log vᵢ` differentiates back to `fₙ` exactly (the `R` cancels). -/

/-- **The §5.9 hyperexponential normal-part integral** `cIntegrateHyperexpNormalG Dt fuel a d cands`
(Bronstein §5.9, the residual feedback): integrate a **normal** part `fₙ = a/d` of a hyperexponential
monomial `t` (`Dt = η·t`), correcting the §5.6 Rothstein–Trager overshoot. Steps:
(1) `cIntegrateReducedG` gives the (correct) Hermite rational part `g = gnum/gden` and the (overshooting)
residue logs `[(cᵢ, vᵢ)]`;
(2) the residual `R = η·∑ᵢ cᵢ = cHyperexpResidualG η logs` (`η = cExpEtaG Dt`) is the overshoot
`D(∑ cᵢ·log vᵢ) − fₙ`;
(3) the **base** integral `∫R` over `α` is `CRischField.crischDESolve 0 R` (the §6 pure integration
`Dy = R`); `none` if unsolvable;
(4) subtract: the new rational part is `g − ∫R = (gnum − (∫R)·gden)/gden` (`∫R ∈ α` a constant in `t`),
keeping the same logs, so `D(result) = D(g) − R + (fₙ + R) = fₙ`.
Returns `some ⟨(gnum − (∫R)·gden, gden), logs⟩`, or `none` if `∫R` is non-elementary. For `η = 0`
(primitive) `R = 0`, `∫R = 0`, and this collapses to `cIntegrateReducedG`. `[CField α] [CDiffField α]
[CRischField α]`-generic — runs at any tower level. -/
def cIntegrateHyperexpNormalG (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α) :
    Option (IntegralResultG α) :=
  let red := cIntegrateReducedG Dt fuel a d cands
  let η : α := cExpEtaG Dt
  let R : α := cHyperexpResidualG η red.logs
  match CRischField.crischDESolve (CField.zero : α) R with
  | none => none
  | some intR =>
    let (gnum, gden) := red.rational
    let newNum := csubG gnum (cmulG [intR] gden)
    some ⟨(newNum, gden), red.logs⟩

/-! ### The full hyperexponential integral driver `cIntegrateHyperexpFullG` (§5.4 + §5.10 + §5.9)

`cIntegrateHyperexpFullG` mirrors `cIntegrateHyperexpG` (§5.10 special part) but routes the normal part
through the §5.9 residual feedback `cIntegrateHyperexpNormalG` instead of the bare `cIntegrateReducedG`,
so special **and** normal parts of a hyperexponential integral are both correct. -/

/-- **The full hyperexponential integral with normal feedback** `cIntegrateHyperexpFullG Dt fuel a d cands`
(Bronstein §5.4 + §5.10 + §5.9): integrate `f = a/d ∈ k(t)` for a hyperexponential monomial `t`
(`Dt = η·t`), combining the §5.10 special-part Laurent integration with the §5.9 normal-part residual
feedback. Steps:
(1) `canonicalRepresentationFastG` splits `f = fₚ + (b/dₛ) + (cₙ/dₙ)`;
(2) the **Laurent part** `fₚ + b/dₛ` by `cIntegrateHyperexpLaurentG η` (§5.10, each coefficient through the
RDE oracle);
(3) the **normal part** `cₙ/dₙ` by `cIntegrateHyperexpNormalG` (§5.9: Hermite + RT logs − the residual
base integral `∫R`);
(4) combine the two rational parts `(qₗₐᵤᵣ/denₗₐᵤᵣ) + (gₙ/gₙd)`. `none` if either the §5.10 Laurent step or
the §5.9 base residual is non-elementary. The §5.9-corrected analogue of `cIntegrateHyperexpG` (whose
normal part overshoots on a hyperexponential monomial). `[CField α] [CDiffField α] [CRischField
α]`-generic — runs at any hyperexponential tower level. -/
def cIntegrateHyperexpFullG (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α) :
    Option (IntegralResultG α) :=
  let η : α := cExpEtaG Dt
  let (fp, (b, ds), (cn, dn)) := canonicalRepresentationFastG Dt fuel a d
  let neg : List α := cHyperexpSpecialNegG b ds
  match cIntegrateHyperexpLaurentG η fp neg with
  | none => none
  | some (lnum, lden) =>
    match cIntegrateHyperexpNormalG Dt fuel cn dn cands with
    | none => none
    | some nrm =>
      let (gnum, gden) := nrm.rational
      let num := caddG (cmulG lnum gden) (cmulG gnum lden)
      let den := cmulG lden gden
      some ⟨(num, den), nrm.logs⟩

end CPolyG

/-! ### ★ THE KEY VALIDATION: `∫ 1/(exp x − 1) dx = log(exp x − 1) − x` (`native_decide`)

The deliverable. We integrate `f = 1/(t−1) = 1/(exp x − 1)` over `ℚ(x)[t]` where `t = exp x` is a
**hyperexponential** monomial (`Dt = η·t`, `η = 1`, so `Dt = [0, 1]`), with base field `Lvl1 = QFunNZG ℚ =
ℚ(x)`. The integrand `f = 1/(t−1)` is a **normal** part (`gcd(t−1, Dt) = gcd(t−1, t) = 1`), so the §5.6
Rothstein–Trager step returns `1·log(t−1)`, whose derivative `D(t−1)/(t−1) = t/(t−1)` (since `D(t−1) = Dt =
t`, *not* `1`) **overshoots** the intended `1/(t−1)` by the hyperexponential residual `R = η·∑res = 1·1 =
1`. The §5.9 feedback integrates `∫R = ∫1 = x` (the base poly integration over ℚ(x), `crischDESolve 0 1`
gives `q = x`) and subtracts it: `∫fₙ = log(t−1) − x`.

We pin BOTH: the plain `cIntegrateReducedG` overshoots (`checkIdentityG = false`), and the new
`cIntegrateHyperexpNormalG` lands `log(t−1) − x` with the antiderivative identity `D(res) = f`
(`checkIdentityG`, cleared of denominators over ℚ(x)[t]). All scalars are ℚ-constants lifted into `Lvl1 =
ℚ(x)`, so the engine genuinely runs the level-1 `CField`/`CDiffField`/`CRischField` instances; the oracle
recurses ℚ(x) → ℚ for the base integral. Everything is `[CField …]`-computable with `Prop`-erased subtype
proofs, so `native_decide` reduces — the §5.9 hyperexponential normal part GENUINELY COMPUTES via the
residual feedback. -/

open CPolyG

/-- The base field `Lvl1 = QFunNZG ℚ = ℚ(x)` over which the hyperexponential monomial `t = exp x` sits
(re-exported for this file; same as `ComputableHyperexpSpecial.Lvl1`). -/
abbrev NLvl1 : Type := QFunNZG ℚ

/-- The base variable `x ∈ Lvl1 = ℚ(x)` (the monomial of ℚ(x) = QFunNZG ℚ), as the unreduced fraction
`[0, 1]/[1] = x/1`. The base integral `∫1 dx = x`, so `cIntegrateHyperexpNormalG` lands a rational part
`−x` on the worked example. -/
def nLvl1X : NLvl1 := ⟨([CField.zero, CField.one], [CField.one]), by native_decide⟩

/-- The hyperexponential monomial derivative `Dt = η·t = [0, 1]` over `CPolyG NLvl1 = ℚ(x)[t]` (`t = exp x`,
`η = 1`): the coefficient of `t¹` is `η = 1`. -/
def nHyperexpDt : CPolyG NLvl1 := [CField.zero, CField.one]

/-- The integrand numerator `a = 1` over `CPolyG NLvl1 = ℚ(x)[t]` for `f = 1/(t−1) = 1/(exp x − 1)`. -/
def nNormInvA : CPolyG NLvl1 := [CField.one]

/-- The integrand denominator `d = t − 1 = [−1, 1]` over `CPolyG NLvl1 = ℚ(x)[t]` for
`f = 1/(t−1) = 1/(exp x − 1)` (a normal factor: `gcd(t−1, Dt) = 1`). -/
def nNormInvD : CPolyG NLvl1 := [CField.neg CField.one, CField.one]

/-- The residue candidate set `{0, 1, −1}` as `Lvl1 = ℚ(x)` constants for the `1/(exp x − 1)` integral
(the genuine residue is `1`). -/
def nNormInvCands : List NLvl1 := [CField.zero, CField.one, CField.neg CField.one]

/-- **The hyperexponential residual `R = 1` on `f = 1/(exp x − 1)`** (`native_decide`): for the normal part
`fₙ = 1/(t−1)` over ℚ(x)[t] (`Dt = η·t`, `η = 1`), the §5.6 Rothstein–Trager log part is `1·log(t−1)` with a
single residue `c₁ = 1`, so the §5.9 residual is `R = η·∑ᵢ cᵢ = 1·1 = 1` (`cHyperexpResidualG` of the
reduced capstone's logs), confirmed by `CField.isZero (R − 1) = true`. This is the exact overshoot
`D(log(t−1)) − fₙ = t/(t−1) − 1/(t−1) = 1` that the feedback subtracts. -/
theorem nNormInv_residual_eq_one :
    CField.isZero (CField.sub
      (cHyperexpResidualG (cExpEtaG nHyperexpDt)
        (cIntegrateReducedGWf nHyperexpDt nNormInvA nNormInvD nNormInvCands).logs)
      (CField.one : NLvl1)) = true := by native_decide

/-- **The base residual integral `∫R = ∫1 = x`** (`native_decide`): the §5.9 feedback integrates the
residual `R = 1 ∈ ℚ(x)` as a base Risch-DE `Dy = 1` over `k = ℚ(x)` (`crischDESolve 0 1`), recovering
`y = x` — the classic base polynomial integration, recursing ℚ(x) → ℚ. Certified by `CField.isZero (y − x)
= true`. This `x` is what is subtracted from the log part to land `log(t−1) − x`. -/
theorem nNormInv_baseIntegral_eq_x :
    (match CRischField.crischDESolve (CField.zero : NLvl1) (CField.one : NLvl1) with
      | some y => CField.isZero (CField.sub y nLvl1X)
      | none => false) = true := by native_decide

/-- **The plain reduced driver overshoots on `f = 1/(exp x − 1)`** (`native_decide`, the companion): the
§5.6 reduced capstone `cIntegrateReducedG` returns `1·log(t−1)`, whose derivative `D(t−1)/(t−1) = t/(t−1)`
overshoots `fₙ = 1/(t−1)` by the hyperexponential residual `R = 1`, so the antiderivative identity
`D(res) = f` **fails** — `checkIdentityG = false`. This is exactly the §5.9 frontier the residual feedback
closes (contrast `nNormInv_landsNormalPart`). -/
theorem nNormInv_reduced_overshoots :
    CPolyG.checkIdentityG nHyperexpDt
      (cIntegrateReducedGWf nHyperexpDt nNormInvA nNormInvD nNormInvCands)
      nNormInvA nNormInvD = false := by native_decide

/-- **★ The §5.9 driver lands `∫ 1/(exp x − 1) = log(exp x − 1) − x`, and `D(∫f) = f`** (`native_decide`,
the headline). On the hyperexponential **normal** integrand `f = 1/(t−1) = 1/(exp x − 1)` over `ℚ(x)[t]`
(`Dt = η·t`, `η = 1`) — on which the reduced `cIntegrateReducedG` overshoots by the residual `R = 1`
(`nNormInv_reduced_overshoots`) — the §5.9 driver `cIntegrateHyperexpNormalG` (reduced capstone + residual
`R = η·∑res = 1` + base integral `∫R = x` + subtraction) returns `some res`, and `res` satisfies the
antiderivative identity `D(res) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f` (`checkIdentityG`, cleared of denominators over
ℚ(x)[t]). The returned object is `log(t−1) − x` (rational part `−x`, one log `(1, t−1)`). **This is the
deliverable: the hyperexponential normal part — built on the §5.9 residual feedback and the recursive base
integral — computes and differentiates back to `f`, completing hyperexponential integration (special §5.10
+ normal §5.9).** -/
theorem nNormInv_landsNormalPart :
    (match CPolyG.cIntegrateHyperexpNormalGWf nHyperexpDt nNormInvA nNormInvD nNormInvCands with
      | some res => CPolyG.checkIdentityG nHyperexpDt res nNormInvA nNormInvD
      | none => false) = true := by native_decide

/-- **The §5.9 driver's result IS `log(t−1) − x`** (`native_decide`): the returned `IntegralResultG` of
`cIntegrateHyperexpNormalG` on `f = 1/(exp x − 1)` has rational part exactly `−x` (a single `t⁰`
coefficient `−x ∈ ℚ(x)`) and a single logarithm with argument `t − 1` — i.e. `log(t−1) − x`, the textbook
antiderivative. Pins the *shape*, not just the derivative identity. -/
theorem nNormInv_result_is_logTMinus1_minus_x :
    (match CPolyG.cIntegrateHyperexpNormalGWf nHyperexpDt nNormInvA nNormInvD nNormInvCands with
      | some res =>
        CPolyG.cisZeroG (CPolyG.csubG res.rational.1 [CField.neg nLvl1X])
          && res.logs.length == 1
          && (res.logs.all (fun cv => CPolyG.cisZeroG (CPolyG.csubG cv.2 nNormInvD)))
      | none => false) = true := by native_decide

#print axioms nNormInv_landsNormalPart

/-! ### ★★ The special + normal mix: `∫ (1/exp + 1/(exp−1)) = −1/exp + log(exp−1) − x` (`native_decide`)

The combined §5.10 + §5.9 driver on `f = 1/t + 1/(t−1) = (2t−1)/(t²−t)` over `ℚ(x)[t]` (`t = exp`,
`Dt = η·t`, `η = 1`): the canonical split is `fₛ = 1/t` (special — `t` is the hyperexponential special
factor) and `fₙ = 1/(t−1)` (normal). The §5.10 special part lands `−1/t`; the §5.9 normal part lands
`log(t−1) − x` (residual `R = 1`, base integral `x`). So `∫f = −1/t + log(t−1) − x`. The full driver
`cIntegrateHyperexpFullG` routes the special part through `cIntegrateHyperexpLaurentG` and the normal part
through the §5.9 feedback, and the assembled result satisfies `D(∫f) = f` (`checkIdentityG`).

This is the **clean special + normal hyperexponential integral** that was the documented frontier in
`ComputableHyperexpSpecial` (where `cIntegrateHyperexpG` *ran* on this input but its normal log part
overshot): with the §5.9 feedback the WHOLE mix now differentiates back to `f`. -/

/-- The integrand numerator `a = 2t − 1` for `f = (2t−1)/(t²−t) = 1/t + 1/(t−1)` over `CPolyG NLvl1`. -/
def nSpecNormA : CPolyG NLvl1 := [CField.neg CField.one, CField.add CField.one CField.one]

/-- The integrand denominator `d = t² − t = t(t−1)` for `f = (2t−1)/(t²−t)` over `CPolyG NLvl1` (split:
special factor `t`, normal factor `t−1`). -/
def nSpecNormD : CPolyG NLvl1 := [CField.zero, CField.neg CField.one, CField.one]

/-- The residue candidate set `{0, 1, −1}` as `Lvl1 = ℚ(x)` constants for the special+normal mix. -/
def nSpecNormCands : List NLvl1 := [CField.zero, CField.one, CField.neg CField.one]

/-- **The §5.10-only driver still overshoots on the special+normal mix** (`native_decide`, the contrast):
the §5.10 driver `cIntegrateHyperexpG` (special part correct, normal part via the bare `cIntegrateReducedG`)
runs on `f = 1/t + 1/(t−1)` over ℚ(x)[t] and returns `some`, but its normal log part `log(t−1)` overshoots
`1/(t−1)` by the §5.9 residual `R = 1`, so the full-`f` antiderivative identity `D(res) = f` **fails**
(`checkIdentityG = false`) — exactly the gap the §5.9 feedback (`cIntegrateHyperexpFullG`) closes. -/
theorem nSpecNorm_specialOnly_overshoots :
    (match CPolyG.cIntegrateHyperexpG nHyperexpDt 24 nSpecNormA nSpecNormD nSpecNormCands with
      | some res => CPolyG.checkIdentityG nHyperexpDt res nSpecNormA nSpecNormD
      | none => false) = false := by native_decide

/-- **★★ The full §5.10 + §5.9 driver lands `∫ (1/exp + 1/(exp−1)) = −1/exp + log(exp−1) − x`, and
`D(∫f) = f`** (`native_decide`, the stretch). On `f = 1/t + 1/(t−1)` over `ℚ(x)[t]` (`t = exp`, `Dt = η·t`,
`η = 1`) — a **special part `1/t` AND a normal part `1/(t−1)`** — the combined driver
`cIntegrateHyperexpFullG` integrates the special part by §5.10 Laurent (`−1/t`) and the normal part by the
§5.9 residual feedback (`log(t−1) − x`), recombining to `−1/t + log(t−1) − x`, and `res` satisfies the
antiderivative identity `D(res) = f` (`checkIdentityG`, cleared of denominators over ℚ(x)[t]). The whole
special-AND-normal hyperexponential integral computes and differentiates back to `f` — the clean mix that
was the §5.9 frontier in `ComputableHyperexpSpecial`. -/
theorem nSpecNorm_full_lands :
    (match CPolyG.cIntegrateHyperexpFullGWf nHyperexpDt nSpecNormA nSpecNormD nSpecNormCands with
      | some res => CPolyG.checkIdentityG nHyperexpDt res nSpecNormA nSpecNormD
      | none => false) = true := by native_decide

#print axioms nSpecNorm_full_lands

/-! ### ★★ A genuinely NON-CONSTANT base residual: `∫ 2x/(exp(x²) − 1) = log(exp(x²) − 1) − x²` (`native_decide`)

The headline residual `R = 1` is a `k`-constant. Here the §5.9 feedback handles a genuinely **non-constant**
base residual. Take `t = exp(x²)`, so `Dt = η·t` with `η = 2x` (non-constant in `x`), over `ℚ(x)[t]`, and
`fₙ = 2x/(t−1)`. The §5.6 residue is `A(1)/(δd)(1) = 2x/(η·1) = 2x/(2x) = 1` — a genuine δ-constant residue
(the `η` in the numerator cancels the `η` from `δd = D(t−1) = η·t`, so the residue is the *constant* `1`,
valid for the Rothstein–Trager criterion). The log part `1·log(t−1)` overshoots by `R = η·∑res = 2x·1 =
2x`, a **non-constant** rational function of `x`. The §5.9 feedback integrates the base residual `∫R = ∫2x
dx = x²` over `k = ℚ(x)` (`crischDESolve 0 (2x)` runs the §6 pipeline over ℚ[x], recursing to ℚ) and
subtracts it: `∫fₙ = log(t−1) − x²`.

This exercises the residual feedback with a **non-constant `R`** (the stretch): `R = 2x` is stored as the
reduced fraction `2x/1` (the numerator-`η` cancellation keeps the residue constant, so `R = η·1` carries no
spurious denominator — unlike the unreduced `2x/2x` of a non-δ-constant residue), so `crischDESolve` over
ℚ(x) genuinely integrates the non-constant `2x` to `x²`, and `cIntegrateHyperexpNormalG` lands
`log(t−1) − x²` with `D(∫f) = f`. -/

/-- The base value `x² ∈ Lvl1 = ℚ(x)` (the antiderivative of `2x`), as `x·x`. -/
def nLvl1XSq : NLvl1 := CField.mul nLvl1X nLvl1X

/-- The hyperexponential coefficient `η = 2x ∈ ℚ(x)` for `t = exp(x²)` (the monomial of ℚ(x) is `x`). -/
def nLvl1TwoX : NLvl1 := CField.mul (CField.add CField.one CField.one) nLvl1X

/-- The hyperexponential monomial derivative `Dt = η·t = [0, 2x]` over `CPolyG NLvl1 = ℚ(x)[t]`
(`t = exp(x²)`, `η = 2x`): the coefficient of `t¹` is the **non-constant** `η = 2x ∈ ℚ(x)`. -/
def nVarDt : CPolyG NLvl1 := [CField.zero, nLvl1TwoX]

/-- The integrand numerator `a = 2x` over `CPolyG NLvl1` for `f = 2x/(t−1) = 2x/(exp(x²) − 1)`. The
numerator carries the `η = 2x` factor so the §5.6 residue `2x/(η·1) = 1` is a genuine δ-constant. -/
def nVarNormA : CPolyG NLvl1 := [nLvl1TwoX]

/-- The integrand denominator `d = t − 1` over `CPolyG NLvl1` for `f = 2x/(t−1)` (a normal factor:
`gcd(t−1, Dt) = 1`). -/
def nVarNormD : CPolyG NLvl1 := [CField.neg CField.one, CField.one]

/-- The residue candidate set `{0, 1, −1}` as `Lvl1 = ℚ(x)` constants for `2x/(exp(x²) − 1)` (the genuine
δ-constant residue is `1`). -/
def nVarNormCands : List NLvl1 := [CField.zero, CField.one, CField.neg CField.one]

/-- **The non-constant base residual `R = 2x` on `f = 2x/(exp(x²) − 1)`** (`native_decide`): for the normal
part `fₙ = 2x/(t−1)` over ℚ(x)[t] (`Dt = η·t`, `η = 2x` **non-constant**), the §5.6 residue `2x/(η·1) = 1` is
a genuine δ-constant, so `∑res = 1` and the §5.9 residual `R = η·∑res = 2x·1 = 2x` is a genuinely
**non-constant** rational function of `x` (`cHyperexpResidualG`), confirmed by `CField.isZero (R − 2x) =
true`. The non-constant overshoot the feedback must integrate. -/
theorem nVarNorm_residual_eq_twoX :
    CField.isZero (CField.sub
      (cHyperexpResidualG (cExpEtaG nVarDt)
        (cIntegrateReducedGWf nVarDt nVarNormA nVarNormD nVarNormCands).logs)
      nLvl1TwoX) = true := by native_decide

/-- **The non-constant base residual integral `∫R = ∫2x = x²`** (`native_decide`): the §5.9 feedback
integrates the **non-constant** residual `R = 2x ∈ ℚ(x)` as a base Risch-DE `Dy = 2x` over `k = ℚ(x)`
(`crischDESolve 0 (2x)`, running the §6 pipeline over ℚ[x] and recursing to ℚ), recovering `y = x²` —
genuine non-constant base polynomial integration. Certified by `CField.isZero (y − x²) = true`. -/
theorem nVarNorm_baseIntegral_eq_xSq :
    (match CRischField.crischDESolve (CField.zero : NLvl1) nLvl1TwoX with
      | some y => CField.isZero (CField.sub y nLvl1XSq)
      | none => false) = true := by native_decide

/-- **★★ The §5.9 driver lands `∫ 2x/(exp(x²) − 1) = log(exp(x²) − 1) − x²`, and `D(∫f) = f`**
(`native_decide`, the non-constant-residual stretch). On the hyperexponential **normal** integrand
`f = 2x/(t−1)` over `ℚ(x)[t]` with `t = exp(x²)` (`Dt = η·t`, `η = 2x` **non-constant**), the §5.9 driver
`cIntegrateHyperexpNormalG` reads the **non-constant** residual `R = 2x` (`nVarNorm_residual_eq_twoX`),
integrates the base residual `∫R = x²` (`nVarNorm_baseIntegral_eq_xSq`), and subtracts it from the log
part, returning `log(t−1) − x²` (rational part `−x²`, one log `(1, t−1)`) with the antiderivative identity
`D(res) = f` (`checkIdentityG`, over ℚ(x)[t]). **The residual feedback handles a genuinely non-constant
base residual** — the §5.9 reduction is not limited to constant `R`. -/
theorem nVarNorm_landsNormalPart :
    (match CPolyG.cIntegrateHyperexpNormalGWf nVarDt nVarNormA nVarNormD nVarNormCands with
      | some res =>
        CPolyG.checkIdentityG nVarDt res nVarNormA nVarNormD
          && CPolyG.cisZeroG (CPolyG.csubG res.rational.1 [CField.neg nLvl1XSq])
          && res.logs.length == 1
      | none => false) = true := by native_decide

#print axioms nVarNorm_landsNormalPart

end DeepWiki.SymbolicIntegration
