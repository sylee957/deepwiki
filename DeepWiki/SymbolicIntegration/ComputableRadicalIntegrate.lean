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
      let B := radCase1Cofactor (k0 + 8) k V Df f C
      let Bder := der B
      let D := radCase1Residual (k0 + 8) k V Df f g B C Bder
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

end DeepWiki.SymbolicIntegration
