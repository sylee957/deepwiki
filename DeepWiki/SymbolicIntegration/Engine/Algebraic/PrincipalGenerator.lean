import DeepWiki.SymbolicIntegration.Engine.Algebraic.DivisorOrder
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalAssembly

/-! # Principal generator of a torsion divisor

For a torsion residue divisor `D` of order `m` on `y² = ρ`, recover the function `g` with
`div(g) = m·D` (so the log term of the integral is `(1/m)·log g`) by tracking the `y − v`
step-functions of Cantor's reduction through the `m·D → O` computation: the product of the
tracked factors is the generator. Validated on `y² = x³ + 1` with the order-3 flex `D = (0, 1)`,
where `g = y − 1`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

variable {α : Type*} [CField α]

/-! ## Tracked Cantor reduction: accumulating the `(y − v)` step-functions

Each `cantorReduceStep` on `(u, v)` is driven by the function `y − v(x)`. `cantorReduceStepTracked`
returns the reduced pair **and** the `v` of this step (so the caller multiplies in the factor `y − v`);
`cantorReduceTracked` threads the list of all step `v`s through the whole reduction loop. -/

/-- One tracked Cantor reduction step `cantorReduceStepTracked ρ (u, v) = ((u', v'), v)`: the
ordinary `cantorReduceStep` (`u' = monic((ρ − v²)/u)`, `v' = (−v) mod u'`) paired with the `v` of
this step, the data of the driving function `y − v(x)`. -/
def cantorReduceStepTracked (ρ : DensePoly α) (D : MumfordDivisor α) :
    MumfordDivisor α × DensePoly α :=
  (cantorReduceStep ρ D, D.v)

/-- Tracked Cantor reduction loop `cantorReduceTrackedAux fuel g ρ (u, v) acc`: apply
`cantorReduceStep` until `deg u ≤ g`, accumulating each step's `v` (the `y − v` factor) onto `acc`
(newest last), stopping when the structural `fuel` counter is exhausted. -/
def cantorReduceTrackedAux : ℕ → ℕ → DensePoly α → MumfordDivisor α → List (DensePoly α) →
    MumfordDivisor α × List (DensePoly α)
  | 0, _, _, D, acc => (D, acc)
  | fuel + 1, g, ρ, D, acc =>
    if cdeg D.u ≤ g then (D, acc)
    else cantorReduceTrackedAux fuel g ρ (cantorReduceStep ρ D) (acc ++ [D.v])

/-- Tracked Cantor reduction `cantorReduceTracked ρ g D = (reduced, vs)`: bring `(u, v)` to reduced
form `deg u ≤ g` (as `cantorReduce`), also returning the list `vs` of every reduction step's `v`.
The product `∏ (y − vᵢ)` is the function swapping `D` for its reduced form. -/
def cantorReduceTracked (ρ : DensePoly α) (g : ℕ) (D : MumfordDivisor α) :
    MumfordDivisor α × List (DensePoly α) :=
  cantorReduceTrackedAux (cdeg D.u + 1) g ρ D []

/-- Tracked Jacobian group law `cantorAddTracked ρ g D₁ D₂ = (D₁ ⊕ D₂, vs)`: `cantorAdd` with the
list `vs` of the `y − v` step-functions emitted by the reduction of the composite. The composition
`cantorCompose` is performed first; its reduction to `deg u ≤ g` accumulates the `vs`. -/
def cantorAddTracked (ρ : DensePoly α) (g : ℕ) (D₁ D₂ : MumfordDivisor α) :
    MumfordDivisor α × List (DensePoly α) :=
  cantorReduceTracked ρ g (cantorCompose ρ D₁ D₂)

/-- Tracked scalar multiple `cantorMulTracked ρ g n D = (n·D, vs)`: the `n`-fold Cantor sum `n·D`
(as `cantorMul`) with the accumulated list `vs` of all `y − v` step-functions emitted across the
`n − 1` additions' reductions. When `n·D = O`, `∏ (y − vᵢ)` over `vs` is the principal generator `g`
with `div(g) = n·D`. By `ℕ`-recursion `(n+1)·D = D ⊕ (n·D)`. -/
def cantorMulTracked (ρ : DensePoly α) (g : ℕ) :
    ℕ → MumfordDivisor α → MumfordDivisor α × List (DensePoly α)
  | 0, _ => (mumfordIdentity, [])
  | n + 1, D =>
    let (acc, vsAcc) := cantorMulTracked ρ g n D
    let (res, vsStep) := cantorAddTracked ρ g D acc
    (res, vsAcc ++ vsStep)

end DensePoly

/-! ## The principal generator as a `RadElem`

`cantorMulTracked` collects the step `v`s (degree-`< g` polynomials over the base). For the elliptic case
(`g = 1`) each step `v` is a **constant** `c`, and the factor `y − v` is the `RadElem` `[−c, 1]` over the
base field. `principalGenerator` lifts the constant `v`s to `ℚ(x)` and multiplies the factors `y − vᵢ`
together (in `(CFrac ℚ)[y]/(y² − ρ)`) into the generator `g`. -/

open DensePoly RadElem

/-- Lift a base `v` to a `y − v` factor over `ℚ(x)`: `genFactorOfV v = [−(v as ℚ(x)), 1]`, the
`RadElem (CFrac ℚ)` `y − v(x)` of one Cantor reduction step, with the (genus-1) constant `v = [c]`
embedded into `ℚ(x)` via `qxOfNum`. For the empty `v = []` (the factor `y`) this is `[0, 1]`. -/
def genFactorOfV (v : DensePoly ℚ) : RadElem (CFrac ℚ) :=
  [CField.neg (qxOfNum v), CField.one]

/-- The principal generator from tracked `v`s: `principalGeneratorOfVs ρ vs = ∏ᵢ (y − vᵢ)`, the
product of the `y − vᵢ` step-functions (`genFactorOfV`) of a `cantorMulTracked` run, taken in the
radical extension (`radMul 2 ρ`) starting from `radOne`. -/
def principalGeneratorOfVs (ρ : CFrac ℚ) (vs : List (DensePoly ℚ)) : RadElem (CFrac ℚ) :=
  vs.foldl (fun acc v => radMul 2 ρ acc (genFactorOfV v)) radOne

/-- The principal generator of a torsion divisor `principalGenerator ρ ρq g m D` — for `D` of
order `m` on `y² = ρ`, the function `g` with `div(g) = m·D`: runs `cantorMulTracked ρq g m D`
and multiplies the tracked `y − v` factors (`principalGeneratorOfVs`). `ρq` is the radicand as
a `ℚ[x]` polynomial, `ρ` the same radicand as a `ℚ(x)` element. -/
def principalGenerator (ρ : CFrac ℚ) (ρq : DensePoly ℚ) (g m : ℕ) (D : MumfordDivisor ℚ) :
    RadElem (CFrac ℚ) :=
  principalGeneratorOfVs ρ (cantorMulTracked ρq g m D).2

/-! ## Recovering `g = y − 1` for `(0, 1)` on `y² = x³ + 1`

`D = (0, 1)` (Mumford `(x, 1)`), order `m = 3`. `principalGenerator` recovers `gen = y − 1`
(`= [−1, 1]`), and the `(1/3)·log(y − 1)` differential passes the log-derivative certificate. -/

open RadElem

/-- The radicand `ρ = x³ + 1` as a `ℚ(x)` element (`CFrac ℚ`), for the radical-extension product. -/
def pgRhoX3p1 : CFrac ℚ := qxOfNum [1, 0, 0, 1]

/-- The recovered generator `gen = principalGenerator … (0, 1) 3` for `y² = x³ + 1` — expected `y − 1`. -/
def pgGen01 : RadElem (CFrac ℚ) := principalGenerator pgRhoX3p1 hypRhoX3p1 1 3 hypPt01

/-- The target generator `y − 1 = [−1, 1]` over `ℚ(x)` (the constant `v = 1` flex tangent line). -/
def pgYm1 : RadElem (CFrac ℚ) := [CField.neg CField.one, CField.one]

/-- The principal generator of `3·(0, 1)` on `y² = x³ + 1` is `y − 1` (`= [−1, 1]`): so
`div(y − 1) = 3·(0, 1) − 3·∞ = 3·D` and the log term is `(1/3)·log(y − 1)`. -/
theorem principalGenerator_pt01_eq :
    radIsZero (radSub pgGen01 pgYm1) = true := by native_decide

/-- The recovered generator is the raw `RadElem` `[−1, 1]` (`= y − 1`). -/
theorem pgGen01_raw :
    radIsZero (radSub pgGen01 [CField.neg (CField.one : CFrac ℚ), CField.one]) = true := by
  native_decide

/-! ### The `(1/3)·log(y − 1)` differential check

The log term is `(1/3)·log g` with `g = y − 1`, so its differential is `ι = (1/3)·g'/g`
(`radLogDeriv ρ g` is the `RadElem` `g'/g`). The cleared certificate
`radDeriv g = radMul g (radScale 3 ι)` confirms `g` is the `(1/3)`-log argument. -/

/-- The `(1/3)·log(y − 1)` differential `ι = (1/3)·g'/g` over `ℚ(x)`, `y² = x³ + 1`. -/
def pgDiff01 : RadElem (CFrac ℚ) :=
  radScale (CField.div CField.one (qxOfNum [3])) (radLogDeriv pgRhoX3p1 pgYm1)

/-- The `(1/3)·log(y − 1)` differential passes the log-derivative certificate
`radDeriv g = radMul g (3·ι)`, confirming `(1/3)·log(y − 1)` is the torsion log term of the
`(0, 1)` residue divisor. -/
theorem principalGenerator_pt01_logderiv :
    radIsLogIntegral 2 pgRhoX3p1 pgYm1 (radScale (qxOfNum [3]) pgDiff01) = true := by native_decide

/-- The unscaled certificate `radDeriv(y − 1) = radMul (y − 1) (radLogDeriv ρ (y − 1))` holds
directly, so `radLogDeriv ρ (y − 1) = (y − 1)'/(y − 1)` (the differential rationalizing to
`x²/(2y(y − 1))`). -/
theorem principalGenerator_pt01_logderiv_unscaled :
    radIsZero (radSub (radDeriv 2 pgRhoX3p1 pgYm1)
      (radMul 2 pgRhoX3p1 pgYm1 (radLogDeriv pgRhoX3p1 pgYm1))) = true := by native_decide

/-! ## The principal-generator recovery milestone -/

/-- The principal generator of a torsion divisor computes and validates. On `y² = x³ + 1`, for
the order-3 flex `D = (0, 1)`: `principalGenerator … (0, 1) 3 = y − 1` (with
`div(y − 1) = 3·(0, 1) − 3·∞ = 3·D`), and the `(1/3)·log(y − 1)` differential `ι = (1/3)·g'/g`
passes the log-derivative certificate `radDeriv g = radMul g (3·ι)`. -/
theorem principal_generator_validates :
    -- the recovered generator is y − 1
    (radIsZero (radSub pgGen01 pgYm1) = true
      ∧ radIsZero (radSub pgGen01 [CField.neg (CField.one : CFrac ℚ), CField.one]) = true)
    -- the order of D = (0,1) is 3 (the torsion decision feeding the construction)
    ∧ cantorOrder 8 hypRhoX3p1 1 hypPt01 = some 3
    -- the (1/3)·log(y − 1) differential passes the log-derivative certificate
    ∧ (radIsLogIntegral 2 pgRhoX3p1 pgYm1 (radScale (qxOfNum [3]) pgDiff01) = true
      ∧ radIsZero (radSub (radDeriv 2 pgRhoX3p1 pgYm1)
          (radMul 2 pgRhoX3p1 pgYm1 (radLogDeriv pgRhoX3p1 pgYm1))) = true) := by native_decide

/-! ### Axiom check -/

#print axioms principal_generator_validates
#print axioms principalGenerator_pt01_eq
#print axioms principalGenerator_pt01_logderiv

end DeepWiki.SymbolicIntegration
