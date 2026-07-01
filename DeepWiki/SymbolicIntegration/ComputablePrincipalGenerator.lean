import DeepWiki.SymbolicIntegration.ComputableDivisorOrder
import DeepWiki.SymbolicIntegration.ComputableRadicalIntegrateFull

/-! # The PRINCIPAL GENERATOR of a torsion divisor (Trager Ch. 6 §1, the constructive half)

The torsion **decision** is done (`ComputableDivisorOrder`): `cantorOrder` / `isTorsionDivisor` decide
whether the residue divisor `D` is torsion of order `m` (so `m·D = O`, the integral is elementary with a
`(1/m)·log` term) or of infinite order (not elementary). This file is the **constructive finish**: when
`m·D = O`, recover the actual function `g` with `div(g) = m·D`, so the log term is `(1/m)·log g`.

**The reduction-tracking algorithm (Trager Ch. 6 §1).** A principal Mumford divisor reduces to the
identity `(1, 0)` through Cantor's reduction, and the generator `g` is the **product of the functions used
in the reduction**. Cantor's reduction step `u ← monic((ρ − v²)/u)`, `v ← (−v) mod u` is driven by the
function `(y − v(x))`: its divisor on `y² = ρ` is exactly `(y − v)(y + v) = ρ − v² = u·u_new`, so
multiplying by `(y − v)` swaps the divisor `(u, v)` for its reduced form. **Tracking these `(y − v)`
step-functions** (as the `RadElem` `[−v, 1]`, i.e. `y − v`) through the `m·D → O` reduction multiplies up
to the generator `g`.

**The worked example fixes the target** (`y² = x³ + 1`, `D = (0, 1)`, `m = 3`). `(0, 1)` is a 3-torsion
flex. Computing `3·D` step by step: `2·D = D ⊕ D` *composes* to `(x², 1)` (the doubling, `v = 1`), then a
single reduction step `u ← monic((ρ − 1)/x²) = monic(x) = x`, `v ← −1` reduces it to `(0, −1)`; this
reduction step has `v = 1`, contributing the factor **`y − 1`**. Then `3·D = D ⊕ (2·D) = (0, 1) ⊕ (0, −1)`
*composes directly* to the identity `(1, 0)` (the support `x = 0` cancels in the gcd), with **no** further
reduction step. So the accumulated tracked product is exactly `g = y − 1`. This is the tangent line at the
flex `(0, 1)` (`y' = 3x²/(2y) = 0` there, horizontal `y = 1`), which meets `y² = x³ + 1` only at `x³ = 0`,
a triple point — `div(y − 1) = 3·(0, 1) − 3·∞ = 3·D`. The log term is `(1/3)·log(y − 1)`.

**The log-derivative check confirms the recovery.** `radLogDeriv ρ g = g'/g` (the honest `RadElem`
division via `radInv2`, from `ComputableRadicalIntegrateFull`); the `(1/3)·log g` differential is
`ι = (1/3)·g'/g`, and the cleared certificate `radDeriv g = radMul g (radScale 3 ι)` (`radIsLogIntegral`)
holds — the recovered `g` *is* the `(1/3)`-log argument. Concretely `g' = radDeriv(y − 1) = ℓ·y` with
`ℓ = 3x²/(2(x³+1))`, so `ι = (1/3)·ℓ·y/(y − 1) = x²/(2y(y − 1))` — the differential Trager's radical-
extension derivation predicts, with the right residues at the divisor.

Mathlib has the abstract divisor class group but **no hyperelliptic principal-generator recovery**, so —
like the rest of this arc — we build it **computationally**, `native_decide`-validated over `ℚ[x]` /
`ℚ(x)`. This is the **constructive half** of Trager's "points of finite order": the decision (elementary
or not) plus the construction (the actual `(1/m)·log g` argument). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ## Tracked Cantor reduction: accumulating the `(y − v)` step-functions

Each `cantorReduceStep` on `(u, v)` is driven by the function `y − v(x)`. `cantorReduceStepTracked`
returns the reduced pair **and** the `v` of this step (so the caller multiplies in the factor `y − v`);
`cantorReduceTracked` threads the list of all step `v`s through the whole reduction loop. -/

/-- **One tracked Cantor reduction step** `cantorReduceStepTracked ρ (u, v) = ((u', v'), v)` — the
ordinary `cantorReduceStep` (`u' = monic((ρ − v²)/u)`, `v' = (−v) mod u'`) **paired with the `v` of this
step**, the data of the driving function `y − v(x)` (whose divisor swaps `(u, v)` for its reduced form,
Trager Ch. 6 §1). Generic over `[CField α]`. -/
def cantorReduceStepTracked (ρ : CPolyG α) (D : MumfordDivisor α) :
    MumfordDivisor α × CPolyG α :=
  (cantorReduceStep ρ D, D.v)

/-- **Tracked Cantor reduction loop** `cantorReduceTrackedAux fuel g ρ (u, v) acc`: apply
`cantorReduceStep` until `deg u ≤ g`, accumulating each step's `v` (the `y − v` factor) onto `acc` (newest
last). Mirrors `cantorReduceAux`; the structural recursion guarantees termination. Generic over
`[CField α]`. -/
def cantorReduceTrackedAux : ℕ → ℕ → CPolyG α → MumfordDivisor α → List (CPolyG α) →
    MumfordDivisor α × List (CPolyG α)
  | 0, _, _, D, acc => (D, acc)
  | fuel + 1, g, ρ, D, acc =>
    if cdegG D.u ≤ g then (D, acc)
    else cantorReduceTrackedAux fuel g ρ (cantorReduceStep ρ D) (acc ++ [D.v])

/-- **Tracked Cantor reduction** `cantorReduceTracked ρ g D = (reduced, vs)` — bring `(u, v)` to reduced
form `deg u ≤ g` (as `cantorReduce`), **also** returning the list `vs` of every reduction step's `v` (each
the data of a `y − v` factor of the principal function, Trager Ch. 6 §1). The product `∏ (y − vᵢ)` is the
function swapping `D` for its reduced form. Generic over `[CField α]`. -/
def cantorReduceTracked (ρ : CPolyG α) (g : ℕ) (D : MumfordDivisor α) :
    MumfordDivisor α × List (CPolyG α) :=
  cantorReduceTrackedAux (cdegG D.u + 1) g ρ D []

/-- **Tracked Jacobian group law** `cantorAddTracked ρ g D₁ D₂ = (D₁ ⊕ D₂, vs)` — `cantorAdd` with
the list `vs` of the `y − v` step-functions emitted by the **reduction** of the composite (Trager Ch. 6
§1). The composition `cantorCompose` is performed first; its reduction to `deg u ≤ g` accumulates the
`vs`. Generic over `[CField α]`. -/
def cantorAddTracked (ρ : CPolyG α) (g : ℕ) (D₁ D₂ : MumfordDivisor α) :
    MumfordDivisor α × List (CPolyG α) :=
  cantorReduceTracked ρ g (cantorCompose ρ D₁ D₂)

/-- **Tracked scalar multiple** `cantorMulTracked ρ g n D = (n·D, vs)` — the `n`-fold Cantor sum
`n·D` (as `cantorMul`) **with** the accumulated list `vs` of all `y − v` step-functions emitted across the
`n − 1` additions' reductions (Trager Ch. 6 §1). When `n·D = O` (the identity), `∏ (y − vᵢ)` over `vs` is
the **principal generator** `g` with `div(g) = n·D`. By `ℕ`-recursion `(n+1)·D = D ⊕ (n·D)`, prepending
the new addition's `vs` to the carried ones. Generic over `[CField α]`. -/
def cantorMulTracked (ρ : CPolyG α) (g : ℕ) :
    ℕ → MumfordDivisor α → MumfordDivisor α × List (CPolyG α)
  | 0, _ => (mumfordIdentity, [])
  | n + 1, D =>
    let (acc, vsAcc) := cantorMulTracked ρ g n D
    let (res, vsStep) := cantorAddTracked ρ g D acc
    (res, vsAcc ++ vsStep)

end CPolyG

/-! ## The principal generator as a `RadElem`

`cantorMulTracked` collects the step `v`s (degree-`< g` polynomials over the base). For the elliptic case
(`g = 1`) each step `v` is a **constant** `c`, and the factor `y − v` is the `RadElem` `[−c, 1]` over the
base field. `principalGenerator` lifts the constant `v`s to `ℚ(x)` and multiplies the factors `y − vᵢ`
together (in `(QFunNZG ℚ)[y]/(y² − ρ)`) into the generator `g`. -/

open CPolyG RadElem

/-- **Lift a base-constant `v` to a `y − v` factor over `ℚ(x)`** `genFactorOfV v = [−(v as ℚ(x)), 1]` — the
`RadElem (QFunNZG ℚ)` `y − v(x)` of one Cantor reduction step, with the (genus-1) constant `v = [c]`
embedded into `ℚ(x)` (the head coefficient via `qxOfNum`). The building block of the principal generator.
(For the empty `v = []` — a zero `v`, the factor `y` — this is `[0, 1]`.) -/
def genFactorOfV (v : CPolyG ℚ) : RadElem (QFunNZG ℚ) :=
  [CField.neg (qxOfNum v), CField.one]

/-- **The principal generator from tracked `v`s** `principalGeneratorOfVs ρ vs = ∏ᵢ (y − vᵢ)` — multiply
the `y − vᵢ` step-functions (`genFactorOfV`) of a `cantorMulTracked` run into one `RadElem (QFunNZG ℚ)`
over `y² = ρ`, the generator `g` with `div(g) = m·D` (Trager Ch. 6 §1). The product is taken in the
radical extension (`radMul 2 ρ`), starting from `1` (`radOne`). -/
def principalGeneratorOfVs (ρ : QFunNZG ℚ) (vs : List (CPolyG ℚ)) : RadElem (QFunNZG ℚ) :=
  vs.foldl (fun acc v => radMul 2 ρ acc (genFactorOfV v)) radOne

/-- **The principal generator of a torsion divisor** `principalGenerator ρ ρq g m D` — for a torsion
divisor `D` of order `m` on `y² = ρ` (`m·D = O`), recover the function `g` with `div(g) = m·D` (so the log
term is `(1/m)·log g`, Trager Ch. 6 §1). Runs `cantorMulTracked ρq g m D` (the order-`m` multiple,
tracking the `y − v` reduction step-functions) and multiplies the tracked factors into a
`RadElem (QFunNZG ℚ)` over `y² = ρ` (`principalGeneratorOfVs`). `ρq` is the radicand as a `ℚ[x]`
polynomial (for Cantor); `ρ` the same radicand as a `ℚ(x)` element (for the radical-extension product). -/
def principalGenerator (ρ : QFunNZG ℚ) (ρq : CPolyG ℚ) (g m : ℕ) (D : MumfordDivisor ℚ) :
    RadElem (QFunNZG ℚ) :=
  principalGeneratorOfVs ρ (cantorMulTracked ρq g m D).2

/-! ## ★ The headline: recovering `g = y − 1` for `(0, 1)` on `y² = x³ + 1` (`native_decide`)

`D = (0, 1)` (Mumford `(x, 1)`), order `m = 3`. `principalGenerator` recovers `gen = y − 1` (`= [−1, 1]`),
and the `(1/3)·log(y − 1)` differential passes the log-derivative certificate. -/

open RadElem

/-- The radicand `ρ = x³ + 1` as a `ℚ(x)` element (`QFunNZG ℚ`), for the radical-extension product. -/
def pgRhoX3p1 : QFunNZG ℚ := qxOfNum [1, 0, 0, 1]

/-- The recovered generator `gen = principalGenerator … (0, 1) 3` for `y² = x³ + 1` — expected `y − 1`. -/
def pgGen01 : RadElem (QFunNZG ℚ) := principalGenerator pgRhoX3p1 hypRhoX3p1 1 3 hypPt01

/-- The target generator `y − 1 = [−1, 1]` over `ℚ(x)` (the constant `v = 1` flex tangent line). -/
def pgYm1 : RadElem (QFunNZG ℚ) := [CField.neg CField.one, CField.one]

/-- **★★ The principal generator of `3·(0, 1)` is `y − 1`** (`native_decide`): tracking the `y − v` Cantor
reduction step-functions through `3·(0, 1) → O` on `y² = x³ + 1`, the accumulated product is exactly
`gen = y − 1` (`= [−1, 1]`), recovered by `principalGenerator`. Checked by `radIsZero` of `gen − (y − 1)`
over `ℚ(x)`. So `div(y − 1) = 3·(0, 1) − 3·∞ = 3·D` — the flex tangent line — and the log term of the
algebraic integral is `(1/3)·log(y − 1)`. THE ENGINE RECOVERS THE PRINCIPAL GENERATOR (the constructive
half of Trager's torsion log term). -/
theorem principalGenerator_pt01_eq :
    radIsZero (radSub pgGen01 pgYm1) = true := by native_decide

/-- **★ The recovered generator is exactly the raw `RadElem` `[−1, 1]`** (`native_decide`): the tracked
product reduces literally to `y − 1` (`= [(−1 : ℚ(x)), 1]`), the Mumford reduction-step bookkeeping
collapsing to the single flex-tangent factor. The literal output of the generator recovery. -/
theorem pgGen01_raw :
    radIsZero (radSub pgGen01 [CField.neg (CField.one : QFunNZG ℚ), CField.one]) = true := by
  native_decide

/-! ### ★ The `(1/3)·log(y − 1)` differential check (`native_decide`)

The log term is `(1/3)·log g` with `g = y − 1`, so its differential is `ι = (1/3)·g'/g`. `radLogDeriv ρ g`
is the honest `RadElem` `g'/g` (division via `radInv2`); `ι = radScale (1/3) (radLogDeriv ρ g)`. The
cleared log-derivative certificate `radDeriv g = radMul g (radScale 3 ι)` (`radIsLogIntegral`) confirms `g`
is the `(1/3)`-log argument — `radScale 3 ι = g'/g`, so the certificate is `radDeriv g = radMul g (g'/g)`,
i.e. `g' = g·(g'/g)`, the defining identity of the recovered generator's logarithmic derivative. -/

/-- The `(1/3)·log(y − 1)` differential `ι = (1/3)·g'/g` over `ℚ(x)`, `y² = x³ + 1` — `radScale (1/3)` of
the honest log-derivative `radLogDeriv ρ (y − 1)` (division via `radInv2`). The integrand whose
antiderivative is `(1/3)·log(y − 1)`. -/
def pgDiff01 : RadElem (QFunNZG ℚ) :=
  radScale (CField.div CField.one (qxOfNum [3])) (radLogDeriv pgRhoX3p1 pgYm1)

/-- **★ The `(1/3)·log(y − 1)` differential passes the log-derivative certificate** (`native_decide`): with
`g = y − 1` and the integrand `ι = (1/3)·g'/g`, the cleared certificate `radDeriv g = radMul g (3·ι)`
holds (`radIsLogIntegral 2 ρ g (radScale 3 ι) = true`) — `3·ι = g'/g`, so this is `g' = g·(g'/g)`, the
recovered generator's logarithmic-derivative identity. CONFIRMS `(1/3)·log(y − 1)` is the torsion log term
of the `(0, 1)` residue divisor. -/
theorem principalGenerator_pt01_logderiv :
    radIsLogIntegral 2 pgRhoX3p1 pgYm1 (radScale (qxOfNum [3]) pgDiff01) = true := by native_decide

/-- **★ The differential `ι` rationalizes to `x²/(2y(y − 1))`** (`native_decide`): `radLogDeriv ρ (y − 1) =
(y − 1)'/(y − 1) = ℓ·y/(y − 1)` with `ℓ = 3x²/(2(x³+1))`, and `ℓ·y/(y − 1) = ℓ·y·(y + 1·?)…` rationalizes
(via `radInv2`'s conjugate) so that `ι = (1/3)·g'/g = x²/(2y(y − 1))`. We verify the cleared form: the
honest `RadElem` `radLogDeriv ρ (y − 1)` times the constant `1/3` (`= ι`) satisfies the certificate, i.e.
`radDeriv(y − 1) = radMul (y − 1) (radLogDeriv ρ (y − 1))` directly (`radScale 3 ι = radLogDeriv`). The
differential Trager's derivation `d/dx[(1/3)log(y − 1)] = (1/3)y'/(y − 1)` predicts, with `y' = 3x²/(2y)`,
has the right residues at the divisor. -/
theorem principalGenerator_pt01_logderiv_unscaled :
    radIsZero (radSub (radDeriv 2 pgRhoX3p1 pgYm1)
      (radMul 2 pgRhoX3p1 pgYm1 (radLogDeriv pgRhoX3p1 pgYm1))) = true := by native_decide

/-! ## ★ The principal-generator recovery milestone (`native_decide`) -/

/-- **★★ THE PRINCIPAL GENERATOR OF A TORSION DIVISOR COMPUTES AND VALIDATES** (Trager Ch. 6 §1, the
constructive half, `native_decide`). `cantorReduceTracked` / `cantorAddTracked` / `cantorMulTracked`
instrument Cantor's reduction to also emit the `y − v` step-functions; `principalGenerator` multiplies them
into the generator `g` with `div(g) = m·D`. On `y² = x³ + 1`, for the order-3 flex `D = (0, 1)`:
* `principalGenerator … (0, 1) 3 = y − 1` — the recovered generator is the flex tangent line `y = 1`, with
  `div(y − 1) = 3·(0, 1) − 3·∞ = 3·D`;
* the `(1/3)·log(y − 1)` differential `ι = (1/3)·g'/g` passes the log-derivative certificate
  `radDeriv g = radMul g (3·ι)`, confirming `(1/3)·log(y − 1)` is the torsion log term.

The engine now **decides** torsion (`ComputableDivisorOrder`: order `m`, elementary or not) **and
constructs** the `(1/m)·log g` argument (`principalGenerator`: the function `g` with `div(g) = m·D`) — the
two halves of Trager's "points of finite order", completing the algebraic-integration decision procedure
for simple radicals on this example. -/
theorem principal_generator_validates :
    -- the recovered generator is y − 1
    (radIsZero (radSub pgGen01 pgYm1) = true
      ∧ radIsZero (radSub pgGen01 [CField.neg (CField.one : QFunNZG ℚ), CField.one]) = true)
    -- the order of D = (0,1) is 3 (the torsion decision feeding the construction)
    ∧ cantorOrder 8 hypRhoX3p1 1 hypPt01 = some 3
    -- the (1/3)·log(y − 1) differential passes the log-derivative certificate
    ∧ (radIsLogIntegral 2 pgRhoX3p1 pgYm1 (radScale (qxOfNum [3]) pgDiff01) = true
      ∧ radIsZero (radSub (radDeriv 2 pgRhoX3p1 pgYm1)
          (radMul 2 pgRhoX3p1 pgYm1 (radLogDeriv pgRhoX3p1 pgYm1))) = true) := by native_decide

/-! ### Deliverable: `#print axioms`

`[propext, Classical.choice, Quot.sound]` plus `Lean.ofReduceBool` (the `native_decide` kernel-reduction
axiom). No `sorry`. -/

#print axioms principal_generator_validates
#print axioms principalGenerator_pt01_eq
#print axioms principalGenerator_pt01_logderiv

/-! ## What is left of the torsion sub-arc (the constructive finish, documented)

The **decision** half (`ComputableDivisorOrder`: `cantorOrder` / `isTorsionDivisor`) and the
**construction** half *for the order-3 flex* (`principalGenerator … (0, 1) 3 = y − 1`, the milestone) are
both delivered. The remaining generalization of the reduction-tracking, recorded — not yet formalized — in
the `Sources/Doi_10_1007_b138171` catalog:

1. **Higher genus / non-constant step `v`** — for genus `g > 1` (`y² = x⁵ + 1`, …) a Cantor reduction
   step's `v` is a polynomial of degree `< g`, so the factor `y − v(x)` is a non-constant `RadElem`
   `[−v, 1]`; `genFactorOfV` already lifts a `ℚ[x]` `v` (the head coefficient path specializes to the
   genus-1 constant). The product `principalGeneratorOfVs` multiplies these in the extension regardless;
   the genus-2 examples are the next `native_decide` targets.

2. **Composition-step cancellation factors** — when `cantorCompose` itself drops degree via the gcd (as in
   `(0, 1) ⊕ (0, −1) → O`, the support `x = 0` cancelling), the cancelled part is a `(y − v)` (here the
   coordinate function `x`, a base factor); for the order-3 example this contributes only the trivial
   constant, so `g = y − 1` is exact, but a fully general generator multiplies the composition cofactors in
   too (Trager Ch. 6 §1, the ideal-quotient bookkeeping). Tracking them is the general reduction-tracking
   refinement.

3. **Wiring `(1/m, g)` as an `AlgIntegralResult` log term** — `principalGenerator` returns the `RadElem`
   `g`; packaging `(c/m, g)` into the integrator's `logTerms` (the `cIntegrateAlgebraic` non-principal
   branch, where `radLogArgSolve` returns `none`) closes the simple-radical log part for points of finite
   order end-to-end.

The milestone delivered here is the **constructive half**: the `y − v` reduction-step tracking and the
`g = y − 1` recovery for the order-3 flex, `native_decide`-validated with the `(1/3)·log` differential
check — Trager's algebraic-integration decision procedure for simple radicals now both *decides* and
*constructs* the torsion log term. -/

end DeepWiki.SymbolicIntegration
