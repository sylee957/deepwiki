import DeepWiki.SymbolicIntegration.ComputableRadicalExtension

/-! # Algebraic-function integration: the simple-radical rational-part driver (Trager Appendix A)

`ComputableRadicalExtension` built the simple-radical carrier `RadExt α n f = α[y]/(yⁿ − f)`, the
diagonal derivation `radDeriv`, the `Tᵢ` decoupling, and the **single-step** rational-part reductions
(`radCase1*` for `C/(Vᵏy)`, `radCase2*` for `C/(Wᵏy)`, `radCase3*` for `C/y`, plus the `θ = log v` /
`θ = exp v` variants). Each single step *lowers* the integrand one notch (multiplicity `k → k−1` in
Cases 1–2, degree in Case 3) and was `native_decide`-validated on its cleared Hermite identity.

This file **consolidates the reductions into a driver** that *iterates* a single-step reduction to
completion and **assembles the accumulated rational part `v`**, so that `∫ R/y = v + (remaining lower
part)` is realized end-to-end — and then proves, with the *actual* derivation `radDeriv`, the capstone
`D(v) = (rational part of the integrand)`.

* **`radReduceCase1Iterate`** (Trager Appendix A §2.1, iterated) — fuel-bounded iteration of the
  single-step Case-1 reduction. Starting from `C/(Vᵏ⁰y)` it runs the Hermite step `k → k−1` repeatedly,
  **accumulating** each cofactor contribution `Bⱼf/(V^{kⱼ−1}y)` into a running numerator `vNum` over the
  common denominator `V^{k₀−1}` (the term at multiplicity `kⱼ` enters as `Bⱼf·V^{k₀−kⱼ}`), and recursing
  on the negated residual `−Dⱼ` at multiplicity `kⱼ−1`. The structural fuel is the initial `k₀`. Returns
  `(Crem, vNum)`: the residual numerator `Crem` at multiplicity `1` plus the accumulated `vNum`, with the
  master identity `∫ C/(V^{k₀}y) = vNum/(V^{k₀−1}y) + ∫ Crem/(Vy)`.

* **`radIntegrateCase1`** (the driver) — wraps `radReduceCase1Iterate`: given the `C/(Vᵏ⁰y)` integrand
  over a simple radical `yⁿ = f` with `V` squarefree coprime to `f`, it `Tᵢ`-decouples (the integrand is
  already in `R/y` form), runs the iterated Case-1 reduction, and assembles the rational part. The lower
  coefficient (`Crem/(Vy)`, the `k = 1` Risch-ODE residue) and the logarithmic part are the documented
  next steps (wire `cRischDEG` and Trager Ch. 5–6 later).

* **★ The end-to-end `native_decide`** — for `y² = x` (so `y = √x`), `V = x − 1`, `k₀ = 3`, `C₀ = 1`
  (the integrand `1/((x−1)³√x)`), the driver runs **two** Case-1 steps (`k = 3 → 2 → 1`) and produces a
  rational part `v = vNum/(V²·√x)`. Lifting `v` and the integrand's rational part from `ℚ[x]` to the
  *genuine radical extension* `(QFunNZG ℚ)[y]/(y² − x)` (a `R/y` element is `(R/(W·f))·y`, a pure-`y`
  `RadElem` over `ℚ(x)`), we check with the **actual** diagonal derivation `radDeriv 2 x` that
  `D(v) = C₀/(V³y) − Crem/(Vy)` — i.e. the driver's accumulated `v` integrates the rational part of the
  integrand, modulo the leftover `k = 1` term. **This is "the driver actually integrates"** — `D(∫) =
  rational-part` for a multi-step simple-radical rational integral, validated by the real derivation.

**Deferred** (documented): the `k = 1` lower-coefficient solve (Risch first-order ODE — `cRischDEG`
glue), the multi-`Vᵢ` / Case-2 / Case-3 dispatch front-end (partial-fraction over each squarefree factor,
reusing `cSplitFactorFast`/`cSqfreeYunFF`), and the entire logarithmic part (residues / divisors, Trager
Ch. 5–6). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### The iterated Case-1 rational-part reduction (Trager Appendix A §2.1)

The single step `radCase1Cofactor`/`radCase1Residual` solves the Hermite congruence and produces, at
multiplicity `k`, a cofactor `B` and residual `D` with the cleared identity
`(1−k)V'fB − C + V(B'f + Bg) = V·D` — i.e. (over the radical) `∫ C/(Vᵏy) = Bf/(V^{k−1}y) − ∫ D/(V^{k−1}y)`.
**Iterating** this from `k = k₀` down to `k = 1` telescopes the rational part:
`∫ C/(V^{k₀}y) = Σ Bf/(V^{k−1}y) + ∫ Crem/(Vy)`. Because successive steps feed `−D` forward (the integral
sign flips each level), the running residual numerator alternates sign; we track it explicitly. The
accumulated rational part is collected over the **single** common denominator `V^{k₀−1}`: a step at
multiplicity `k` contributes `Bf/(V^{k−1}y)`, which over `V^{k₀−1}` is `Bf·V^{k₀−k}`. -/

/-- **Iterated Case-1 reduction** `radReduceCase1Iterate der fuel V Df f g k0 k C vNum = (Crem, vNumOut)`
(Trager Appendix A §2.1, iterated). One structural step per unit of `fuel` (call with `fuel = k0`): at
multiplicity `k ≥ 2` it solves the Hermite cofactor `B = radCase1Cofactor`, forms the residual
`D = radCase1Residual`, **accumulates** the contribution `B·f·V^{k0−k}` into `vNum` (the numerator of the
rational part over the common denominator `V^{k0−1}·y`), and recurses on the negated residual `−D` at
multiplicity `k−1`. Bottoms out at `k ≤ 1` returning `(C, vNum)` — the leftover `k = 1` numerator and the
assembled rational-part numerator. `der` is the level's base derivation on `α[θ]` (`cderivG` for `θ' = 1`,
`cmonomialDeriv [θ']` on a tower); `Df = V'`, `g` (from `(f/y)' = g/y`) are passed in. Generic over
`[CField α]`. -/
def radReduceCase1Iterate (der : CPolyG α → CPolyG α) (V Df f g : CPolyG α) (k0 : ℕ) :
    ℕ → ℕ → CPolyG α → CPolyG α → CPolyG α × CPolyG α
  | 0, _, C, vNum => (C, vNum)
  | fuel + 1, k, C, vNum =>
    if k ≤ 1 then (C, vNum)
    else
      let B := radCase1Cofactor k V Df f C
      let Bder := der B
      let D := radCase1Residual k V Df f g B C Bder
      -- contribution `B·f/(V^{k−1}y)` over the common denominator `V^{k0−1}`: `B·f·V^{k0−k}`
      let contrib := cmulG (cmulG B f) (cpowG V (k0 - k))
      radReduceCase1Iterate der V Df f g k0 fuel (k - 1) (cnegG D) (caddG vNum contrib)

/-- **The simple-radical rational-part driver (Case 1)** `radIntegrateCase1 der V f g k0 C = (Crem, vNum)`
(Trager Appendix A §2.1) — the `∫ C/(V^{k0}y)` driver over a simple radical `yⁿ = f` with `V` squarefree
coprime to `f`. Computes `Df = V'` (via the level derivation `der`) and runs the iterated Case-1 reduction
`radReduceCase1Iterate` from multiplicity `k0` down to `1` (structural fuel `k0`), returning the leftover
`k = 1` numerator `Crem` and the accumulated rational-part numerator `vNum` over the common denominator
`V^{k0−1}·y`. The master identity it realizes is `∫ C/(V^{k0}y) = vNum/(V^{k0−1}y) + ∫ Crem/(Vy)`. The
leftover `∫ Crem/(Vy)` (a `k = 1` first-order-ODE residue) and the logarithmic part are deferred. `der` is
the level's base derivation (`cderivG` for `θ' = 1`); `g` is read off `(f/y)' = g/y`. Generic over
`[CField α]`. -/
def radIntegrateCase1 (der : CPolyG α → CPolyG α) (V f g : CPolyG α) (k0 : ℕ) (C : CPolyG α) :
    CPolyG α × CPolyG α :=
  radReduceCase1Iterate der V (der V) f g k0 k0 k0 C []

end CPolyG

/-! ### ★ The driver integrates `∫ 1/((x−1)³√x)` end-to-end (`native_decide`)

The headline: a **full simple-radical rational integral** taken end-to-end by the driver, with the result
validated by the **actual** radical derivation `radDeriv`.

* **Picture A** (where the Case lemmas live): `F = ℚ` (constants), `θ = x` (`θ' = 1`, base derivation
  `cderivG` on `ℚ[x]`), radicand `y² = f = x` (`n = 2`, `y = √x`), denominator factor `V = x − 1`
  (squarefree, coprime to `f = x`), initial multiplicity `k₀ = 3`, numerator `C₀ = 1` — the integrand
  `1/((x−1)³√x)`. The Case-1 helper data is `g = ((n−1)/n)·f' = (1/2)·1 = 1/2`. `radIntegrateCase1` runs
  **two** Hermite steps (`k = 3 → 2 → 1`): it accumulates `vNum = (3/4)x² − (5/4)x` (the rational-part
  numerator over the common denominator `V² = (x−1)²`) and leaves `Crem = 3/8` (the `k = 1` residual
  numerator). So `∫ 1/((x−1)³√x) = ((3/4)x² − (5/4)x)/((x−1)²√x) + ∫ (3/8)/((x−1)√x)` — the rational part
  fully extracted, only a single `k = 1` log-type term left.

* **Picture B** (the genuine radical extension, where `radDeriv` lives): `F = ℚ(x) = QFunNZG ℚ`, the
  same `y² = x` over `ℚ(x)`, elements `RadElem (QFunNZG ℚ)`. An `R(x)/y` form lifts to a **pure-`y`**
  element `[0, R/f]` (since `R/y = R·y/y² = (R/f)·y`). So the rational part `v = vNum/(V²·y)` lifts to
  `[0, vNum/(V²·f)]` and the integrand's rational part `C₀/(V³y) − Crem/(Vy)` lifts to
  `[0, C₀/(V³f) − Crem/(Vf)]`, both with `ℚ(x)` coefficients (the `/V…f` divisions are `QFunNZG ℚ`
  field divisions).

* **The check**: `radDeriv 2 x (lift v) = lift (rational part of the integrand)`, verified by `radIsZero`
  of the difference over `ℚ(x)`. The diagonal radical derivation `radDeriv` — the *real* `d/dx` extended
  to `ℚ(x)[√x]` — confirms the driver's accumulated `v` integrates the rational part of `1/((x−1)³√x)`. -/

open RadElem CPolyG

/-- Driver example radicand `f = x` (`y² = x`, `y = √x`), as `ℚ[x]` `[0, 1]`. -/
def sqrtxF : CPolyG ℚ := [0, 1]

/-- Driver example denominator factor `V = x − 1` (squarefree, coprime to `f = x`), `[−1, 1]`. -/
def sqrtxV : CPolyG ℚ := [-1, 1]

/-- Driver example Case-1 helper `g = ((n−1)/n)·f' = (1/2)·1 = 1/2` (`n = 2`, `(f/y)' = g/y`), `[1/2]`. -/
def sqrtxG : CPolyG ℚ := cscaleG (1/2 : ℚ) (cderivG sqrtxF)

/-- Driver example numerator `C₀ = 1` (integrand `1/((x−1)³√x)`), `[1]`. -/
def sqrtxC : CPolyG ℚ := [1]

/-- **The driver run** `radIntegrateCase1 cderivG V f g 3 C = (Crem, vNum)` on `∫ 1/((x−1)³√x)` — runs two
Case-1 Hermite steps (`k = 3 → 2 → 1`), returning the `k = 1` residual `Crem` and the accumulated
rational-part numerator `vNum` over the common denominator `V² = (x−1)²`. -/
def sqrtxRun : CPolyG ℚ × CPolyG ℚ := radIntegrateCase1 cderivG sqrtxV sqrtxF sqrtxG 3 sqrtxC

/-- **The accumulated rational-part numerator is `vNum = (3/4)x² − (5/4)x`** (`native_decide`): the driver
collects the two cofactor contributions over `V² = (x−1)²` into `(3/4)x² − (5/4)x` (`cisZeroG` of the
difference against `[0, −5/4, 3/4]`). The rational part is `v = ((3/4)x² − (5/4)x)/((x−1)²√x)`. -/
theorem sqrtxRun_vNum_eq :
    cisZeroG (csubG sqrtxRun.2 [(0 : ℚ), -5/4, 3/4]) = true := by native_decide

/-- **The leftover `k = 1` residual is `Crem = 3/8`** (`native_decide`): after the two Hermite steps the
driver leaves the single `k = 1` term `∫ (3/8)/((x−1)√x)` (`cisZeroG` of `Crem − 3/8`) — the irreducible
first-order-ODE / logarithmic remainder, the documented next step. -/
theorem sqrtxRun_remainder_eq :
    cisZeroG (csubG sqrtxRun.1 [(3/8 : ℚ)]) = true := by native_decide

/-- The radicand `f = x` lifted to `ℚ(x)` (`QFunNZG ℚ`), the Picture-B radicand for `radDeriv 2`. -/
def sqrtxFqx : QFunNZG ℚ := qxOfNum [0, 1]

/-- The common-denominator power `V² = (x−1)²` as a `ℚ[x]` polynomial (the denominator of `vNum`). -/
def sqrtxV2 : CPolyG ℚ := cpowG sqrtxV 2

/-- The initial denominator power `V³ = (x−1)³` as a `ℚ[x]` polynomial (the integrand's denominator). -/
def sqrtxV3 : CPolyG ℚ := cpowG sqrtxV 3

/-- **The rational part `v` lifted to the radical extension** `RadElem (QFunNZG ℚ)` — the pure-`y` element
`[0, vNum/(V²·f)]` realizing `v = vNum/(V²·y)` over `ℚ(x)` (an `R/y` form is `[0, R/f]` since
`R/y = (R/f)·y`). The `y`-coefficient is the `ℚ(x)` division `vNum/((x−1)²·x)`. -/
def sqrtxVlift : RadElem (QFunNZG ℚ) :=
  [CField.zero, CField.div (qxOfNum sqrtxRun.2) (qxOfNum (cmulG sqrtxV2 sqrtxF))]

/-- **The integrand's rational part lifted to the radical extension** `RadElem (QFunNZG ℚ)` — the pure-`y`
element `[0, C₀/(V³·f) − Crem/(V·f)]` realizing `C₀/(V³y) − Crem/(Vy)` over `ℚ(x)` (the part of the
integrand the driver's `v` is to integrate, the leftover `Crem/(Vy)` subtracted off). -/
def sqrtxRatLift : RadElem (QFunNZG ℚ) :=
  [CField.zero,
    CField.sub (CField.div (qxOfNum sqrtxC) (qxOfNum (cmulG sqrtxV3 sqrtxF)))
      (CField.div (qxOfNum sqrtxRun.1) (qxOfNum (cmulG sqrtxV sqrtxF)))]

/-- **★ The driver integrates `∫ 1/((x−1)³√x)`: `D(v) = rational part of the integrand`**
(`native_decide`). Over the genuine radical extension `(QFunNZG ℚ)[y]/(y² − x)`, the **actual** diagonal
radical derivation `radDeriv 2 x` of the driver's accumulated rational part `v = vNum/(V²√x)` equals the
rational part `C₀/(V³√x) − Crem/(V√x)` of the integrand `1/((x−1)³√x)` (with the leftover `k = 1` term
subtracted). Checked by `radIsZero` of `radDeriv 2 x (lift v) − lift(ratPart)` over `ℚ(x)`. **THE DRIVER
ACTUALLY INTEGRATES** — `D(∫) = rational-part` for a multi-step (`k = 3 → 2 → 1`) simple-radical rational
integral, validated by the real derivation, not just the per-step cleared identity. The accumulated `v`
from the iterated Hermite reductions is a correct antiderivative of the integrand's rational part. -/
theorem sqrtxDriver_integrates :
    radIsZero (radSub (radDeriv 2 sqrtxFqx sqrtxVlift) sqrtxRatLift) = true := by native_decide

/-! ### ★ The driver integrates `∫ 1/((x−1)³√(x³+1))` end-to-end (`native_decide`)

The same driver on the carrier's **headline radicand** `y² = x³ + 1` (`y = √(x³+1)`, the
`radGen_sq_eq_radicand` curve — a genuine elliptic-curve radical, not the trivial `√x`). With `V = x − 1`
(coprime to `f = x³+1`, since `f(1) = 2 ≠ 0`), `k₀ = 3`, `C₀ = 1` — the integrand `1/((x−1)³√(x³+1))` —
`radIntegrateCase1` again runs **two** Case-1 steps (`k = 3 → 2 → 1`), assembling `vNum` (a degree-4
`ℚ[x]` numerator over `V² = (x−1)²`) and leaving `Crem` (the `k = 1` residual). The end-to-end check is
the *same shape*: with the **actual** diagonal derivation `radDeriv 2 (x³+1)`, the lift of the assembled
rational part `v = vNum/(V²·√(x³+1))` differentiates to the lift of the integrand's rational part
`C₀/(V³√(x³+1)) − Crem/(V√(x³+1))`. The driver integrates over a nontrivial algebraic curve. -/

/-- Headline-radicand example `f = x³ + 1` (`y² = x³+1`, `y = √(x³+1)`), as `ℚ[x]` `[1,0,0,1]`. -/
def cubeF : CPolyG ℚ := [1, 0, 0, 1]

/-- Headline-radicand denominator factor `V = x − 1` (coprime to `f = x³+1`: `f(1) = 2 ≠ 0`), `[−1, 1]`. -/
def cubeV : CPolyG ℚ := [-1, 1]

/-- Headline-radicand Case-1 helper `g = ((n−1)/n)·f' = (1/2)·3x² = (3/2)x²` (`n = 2`, `(f/y)' = g/y`). -/
def cubeG : CPolyG ℚ := cscaleG (1/2 : ℚ) (cderivG cubeF)

/-- Headline-radicand numerator `C₀ = 1` (integrand `1/((x−1)³√(x³+1))`), `[1]`. -/
def cubeC : CPolyG ℚ := [1]

/-- **The driver run** on `∫ 1/((x−1)³√(x³+1))` — two Case-1 Hermite steps (`k = 3 → 2 → 1`), returning the
`k = 1` residual `Crem` and the accumulated rational-part numerator `vNum` over `V² = (x−1)²`. -/
def cubeRun : CPolyG ℚ × CPolyG ℚ := radIntegrateCase1 cderivG cubeV cubeF cubeG 3 cubeC

/-- The headline radicand `f = x³ + 1` lifted to `ℚ(x)` (`QFunNZG ℚ`), the Picture-B radicand. -/
def cubeFqx : QFunNZG ℚ := qxOfNum [1, 0, 0, 1]

/-- The rational part `v = vNum/(V²·y)` lifted to `RadElem (QFunNZG ℚ)` — the pure-`y` element
`[0, vNum/(V²·f)]` over `ℚ(x)`. -/
def cubeVlift : RadElem (QFunNZG ℚ) :=
  [CField.zero, CField.div (qxOfNum cubeRun.2) (qxOfNum (cmulG (cpowG cubeV 2) cubeF))]

/-- The integrand's rational part `C₀/(V³y) − Crem/(Vy)` lifted to `RadElem (QFunNZG ℚ)` — the pure-`y`
element `[0, C₀/(V³·f) − Crem/(V·f)]` over `ℚ(x)`. -/
def cubeRatLift : RadElem (QFunNZG ℚ) :=
  [CField.zero,
    CField.sub (CField.div (qxOfNum cubeC) (qxOfNum (cmulG (cpowG cubeV 3) cubeF)))
      (CField.div (qxOfNum cubeRun.1) (qxOfNum (cmulG cubeV cubeF)))]

/-- **★ The driver integrates `∫ 1/((x−1)³√(x³+1))`: `D(v) = rational part of the integrand`**
(`native_decide`). On the carrier's headline radicand `y² = x³ + 1` (a genuine elliptic-curve radical),
the **actual** diagonal radical derivation `radDeriv 2 (x³+1)` of the driver's accumulated rational part
`v = vNum/(V²√(x³+1))` equals the rational part `C₀/(V³√(x³+1)) − Crem/(V√(x³+1))` of the integrand
`1/((x−1)³√(x³+1))`. Checked by `radIsZero` of the difference over `ℚ(x)`. **THE DRIVER INTEGRATES OVER A
NONTRIVIAL ALGEBRAIC CURVE** — `D(∫) = rational-part` for the multi-step (`k = 3 → 2 → 1`) simple-radical
rational integral on `√(x³+1)`, validated by the real derivation. -/
theorem cubeDriver_integrates :
    radIsZero (radSub (radDeriv 2 cubeFqx cubeVlift) cubeRatLift) = true := by native_decide

/-! ### `#print axioms` — the driver headline

The end-to-end `D(v) = rational-part` identity and the driver's `vNum`/`Crem` values carry the standard
`[propext, Classical.choice, Quot.sound]` plus the `native_decide` compiler axiom — no `sorry`, no extra
axiom. The iterated Case-1 reductions assemble a rational part `v` whose **actual** radical derivative is
the rational part of the integrand: the simple-radical rational integral `∫ 1/((x−1)³√x)` is integrated
end-to-end, leaving only the documented `k = 1` first-order-ODE / logarithmic term. -/

-- The driver's assembled rational-part numerator and the leftover `k = 1` residual:
#print axioms sqrtxRun_vNum_eq
#print axioms sqrtxRun_remainder_eq

-- ★ The driver integrates: `D(v) = rational part of the integrand`, by the real radical derivation:
#print axioms sqrtxDriver_integrates

-- ★ The same, on the headline radicand `y² = x³+1` (a genuine elliptic-curve radical `√(x³+1)`):
#print axioms cubeDriver_integrates

end DeepWiki.SymbolicIntegration
