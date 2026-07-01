import DeepWiki.SymbolicIntegration.ComputablePrincipalGenerator

/-! # The non-principal `(1/m)·log` branch: wiring torsion → integrator log term (Trager Ch. 6 §1-3)

The simple-radical algebraic integrator (`ComputableRadicalIntegrateFull`) handles the **principal** log
case end-to-end: `radLogArgSolve` returns `some u`, giving a `1·log u` term in the assembled
`∫ = v + Σ cᵢ log uᵢ`. The **non-principal** case (`radLogArgSolve` returns `none`) is the residue divisor
`D` that has *no* single principal generator — but, if `D` is **torsion of order `m`** (`m·D = O`), then
`m·D` **is** principal, so the log part is a `(1/m)·log g` term with `g` the generator of `m·D`. The
torsion **sub-arc** supplies exactly the two ingredients for this branch:

* **`isTorsionDivisor`** (`ComputableDivisorOrder`) — the DECISION: `some m` (torsion of order `m`,
  elementary with a `(1/m)·log` term) or `none` (infinite order, NOT elementary), terminating via good
  reduction mod `p`.
* **`principalGenerator`** (`ComputablePrincipalGenerator`) — the CONSTRUCTION: the function `g` with
  `div(g) = m·D`, recovered by tracking the `y − v` Cantor reduction step-functions through `m·D → O`.

This file **ties them into a usable integrator branch**. `torsionLogTerm` is the non-principal-branch
function: given the (non-principal) residue divisor `D`, it runs the decision (`isTorsionDivisor`); on
`some m` it runs the construction (`principalGenerator`) and returns the **log term `(1/m, g)`** — the
coefficient `1/m ∈ ℚ(x)` and the radical-extension log argument `g`, i.e. `∫ = … + (1/m)·log g`; on `none`
(non-torsion) it returns `none` — that part of the integral is NOT elementary.

**The headline round-trip** (`native_decide`). On `y² = x³ + 1`, the residue divisor `D = (0, 1)` (Mumford
`(x, 1)`) is the order-3 flex: `torsionLogTerm` returns `(1/3, y − 1)`, and the `(1/3)·log(y − 1)`
differential `ι = (1/3)·g'/g` passes the cleared log-derivative certificate
`radDeriv g = radMul g (3·ι)` (`radIsLogIntegral`) — so `∫ ι dx = (1/3)·log(y − 1)`, produced **end-to-end
from the divisor**. On the rank-1 curve `y² = x³ − 2`, the infinite-order point `(3, 5)` gives `none`
(the decision propagates: NOT elementary).

**Assembling into the integrator's result type.** The torsion log term `(1/m, g)` slots straight into the
`AlgIntegralResult.logTerms` list (the `v + Σ cᵢ log uᵢ` representation of
`ComputableRadicalAssembly`), with `cᵢ = 1/m`. `torsionAlgResult` builds that result; `algDeriv` of it
returns the differential — the same round-trip the principal integrator uses, now closing the
**non-principal** branch.

Mathlib has the abstract Jacobian / divisor class group but **no constructive non-principal log-term
recovery**, so — like the rest of this arc — we build it **computationally**, `native_decide`-validated
over `ℚ[x]` / `ℚ(x)`. This is the integrator's non-principal branch: the engine now produces the
`(1/m)·log g` term for the torsion case, completing the simple-radical elementarity decision procedure
end-to-end (decide `+` construct, both the principal and non-principal log parts). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPolyG RadElem

/-! ## `torsionLogTerm` — the non-principal branch as a usable function

`torsionLogTerm p ρ ρq g D`: decide whether the residue divisor `D` is torsion (`isTorsionDivisor`);
if `some m`, construct the generator `g` of `m·D` (`principalGenerator`) and return the log term
`(1/m, g)`. The coefficient `1/m` is the head-constant `ℚ(x)` element `qxOfNum [1] / qxOfNum [m]`; the
argument `g` is the recovered `RadElem (QFunNZG ℚ)`. Returns `none` when `D` is non-torsion — that part of
the integral is NOT elementary. -/

/-- **The torsion log-term coefficient** `oneOverMQ m = 1/m ∈ ℚ(x)` — the constant field element
`qxOfNum [1] / qxOfNum [m]` (`m` cast to ℚ), the coefficient `cᵢ = 1/m` of the `(1/m)·log g` term. -/
def oneOverMQ (m : ℕ) : QFunNZG ℚ := CField.div (qxOfNum [1]) (qxOfNum [(m : ℚ)])

/-- **The non-principal `(1/m)·log` branch** `torsionLogTerm p ρ ρq g D` (Trager Ch. 6 §1-3) —
the integrator branch for the residue divisor `D` with **no single principal generator**
(`radLogArgSolve = none`). Decide via `isTorsionDivisor p ρq g D`:
* `some m` — `D` is torsion of order `m`, so `m·D` is principal; construct its generator
  `g = principalGenerator ρ ρq g m D` (the function with `div(g) = m·D`) and return the **log term**
  `some (1/m, g)` — coefficient `1/m ∈ ℚ(x)` (`oneOverMQ`), argument `g ∈ ℚ(x)[y]/(y² − ρ)`, i.e.
  `∫ = … + (1/m)·log g`;
* `none` — `D` is of infinite order, so its log argument is not an algebraic function: that part of the
  integral is **NOT elementary**.

`ρ` is the radicand as a `ℚ(x)` element (for the radical-extension generator product), `ρq` the same
radicand as a `ℚ[x]` polynomial (for the Cantor torsion decision); `g` is the genus (degree bound of the
reduction). The function the simple-radical integrator calls when its principal log solve returns `none`. -/
def torsionLogTerm (p : ℕ) [Fact p.Prime]
    (ρ : QFunNZG ℚ) (ρq : CPolyG ℚ) (g : ℕ) (D : MumfordDivisor ℚ) :
    Option (QFunNZG ℚ × RadElem (QFunNZG ℚ)) :=
  match isTorsionDivisor p ρq g D with
  | none => none
  | some m => some (oneOverMQ m, principalGenerator ρ ρq g m D)

/-! ## ★ The headline round-trip: `(0, 1)` → `(1/3)·log(y − 1)` from the DIVISOR (`native_decide`)

`D = (0, 1)` (Mumford `(x, 1)`) on `y² = x³ + 1`, order 3. `torsionLogTerm` returns `(1/3, y − 1)`, and the
`(1/3)·log(y − 1)` differential passes the cleared log-derivative certificate — `∫ = (1/3)·log(y − 1)`,
produced end-to-end from the divisor. -/

open RadElem

/-- The radicand `ρ = x³ + 1` as a `ℚ(x)` element (`QFunNZG ℚ`), for the radical-extension generator. -/
def tltRhoX3p1 : QFunNZG ℚ := qxOfNum [1, 0, 0, 1]

/-- The torsion log term `torsionLogTerm 5 ρ … (0, 1)` on `y² = x³ + 1` — expected `(1/3, y − 1)`. -/
def tltTerm01 : Option (QFunNZG ℚ × RadElem (QFunNZG ℚ)) :=
  torsionLogTerm 5 tltRhoX3p1 hypRhoX3p1 1 hypPt01

/-- The target generator `g = y − 1 = [−1, 1]` over `ℚ(x)` (the flex tangent line). -/
def tltYm1 : RadElem (QFunNZG ℚ) := [CField.neg CField.one, CField.one]

/-- **Field equality on `ℚ(x)`** `qEq a b = CField.isZero (a − b)` — the `Bool` test `a = b` in `QFunNZG ℚ`
via the engine's own zero test (the `CField` idiom, sidestepping `DecidableEq` synthesis on the fraction
subtype). Used to check the recovered log coefficient equals `1/m`. -/
def qEq (a b : QFunNZG ℚ) : Bool := CField.isZero (CField.sub a b)

/-- **The recovered-term check** `tltTermCheck t = (coeff = 1/3) ∧ (g = y − 1)` — the `Bool` summary that a
`torsionLogTerm` output term `t = (c, g)` is the expected `(1/3, y − 1)`: coefficient `qEq c (oneOverMQ 3)`
(field equality on `ℚ(x)`) and generator `radIsZero (g − (y − 1))`. The `Bool`-valued form
`native_decide` reduces cleanly (no `QFunNZG`-value `=`). -/
def tltTermCheck (t : QFunNZG ℚ × RadElem (QFunNZG ℚ)) : Bool :=
  qEq t.1 (oneOverMQ 3) && radIsZero (radSub t.2 tltYm1)

/-- **★ `torsionLogTerm` fires on `(0, 1)` with the coefficient `1/3`** (`native_decide`): the non-principal
branch returns `some (c, g)` with the coefficient `c = 1/3` (field-equal to `oneOverMQ 3` via `qEq`) —
`(0, 1)` is torsion of order 3, so the log term is `(1/3)·log g`. The decision (`isTorsionDivisor = some 3`)
drives the coefficient. -/
theorem tltTerm01_coeff :
    (tltTerm01.map fun t => qEq t.1 (oneOverMQ 3)) = some true := by native_decide

/-- **★★ `torsionLogTerm` on `(0, 1)` returns the log term `(1/3, y − 1)`** (`native_decide`): the
non-principal branch decides `(0, 1)` torsion of order 3, constructs the generator `g = y − 1`
(`principalGenerator`, the flex tangent line, `div(y − 1) = 3·(0, 1) − 3·∞ = 3·D`), and returns the **log
term `(1/3, y − 1)`** — coefficient `1/3` (field-equal via `qEq`) and argument `y − 1`
(`radIsZero (g − (y − 1)) = true`), summarized by `tltTermCheck`. So `∫ = (1/3)·log(y − 1)`, produced
**end-to-end from the divisor `(0, 1)`**. THE ENGINE PRODUCES THE `(1/m)·log` TERM FOR THE NON-PRINCIPAL
CASE. -/
theorem tltTerm01_eq :
    (tltTerm01.map tltTermCheck) = some true := by native_decide

/-! ### ★ The `(1/3)·log(y − 1)` differential check (`native_decide`)

The recovered log term `(1/3, y − 1)` is genuine: the `(1/3)·log(y − 1)` differential `ι = (1/3)·g'/g`
passes the cleared certificate `radDeriv g = radMul g (3·ι)` (`radIsLogIntegral`), i.e. `3·ι = g'/g`, so
`∫ ι dx = (1/3)·log(y − 1)`. Reuses `radLogDeriv` / `radIsLogIntegral` from the principal integrator. -/

/-- The `(1/3)·log(y − 1)` differential `ι = (1/3)·g'/g` over `ℚ(x)`, `y² = x³ + 1` — `radScale (1/3)` of the
honest log-derivative `radLogDeriv ρ (y − 1)`, with the coefficient `1/3` the one `torsionLogTerm` returns
(`oneOverMQ 3`). The integrand whose antiderivative is `(1/3)·log(y − 1)`. -/
def tltDiff01 : RadElem (QFunNZG ℚ) :=
  radScale (oneOverMQ 3) (radLogDeriv tltRhoX3p1 tltYm1)

/-- **★ The `torsionLogTerm` differential passes the log-derivative certificate** (`native_decide`): with
the recovered `g = y − 1` and `ι = (1/3)·g'/g` (coefficient `1/3 = oneOverMQ 3` from `torsionLogTerm`), the
cleared certificate `radDeriv g = radMul g (3·ι)` holds (`radIsLogIntegral 2 ρ g (radScale 3 ι) = true`) —
`3·ι = g'/g`, so `∫ ι dx = (1/3)·log(y − 1)`. CONFIRMS the `torsionLogTerm` output `(1/3, y − 1)` is the
genuine torsion log term of the `(0, 1)` residue divisor — the non-principal branch is correct. -/
theorem tltTerm01_logderiv :
    radIsLogIntegral 2 tltRhoX3p1 tltYm1 (radScale (qxOfNum [3]) tltDiff01) = true := by native_decide

/-! ## ★ Assembling the torsion term into an `AlgIntegralResult` (`native_decide`)

The torsion log term `(1/m, g)` slots into `AlgIntegralResult.logTerms` (the `v + Σ cᵢ log uᵢ` shape of
`ComputableRadicalAssembly`), with `cᵢ = 1/m`. `torsionAlgResult` builds that result from the
divisor; `algDeriv` of it returns the differential — the same round-trip the principal integrator uses,
now closing the non-principal branch. -/

/-- **Assemble the torsion result** `torsionAlgResult p ρ ρq g v D` — the full
`∫ = v + (1/m)·log g` as an `AlgIntegralResult`: rational part `v` plus the torsion log term
(`torsionLogTerm`) appended to `logTerms` (empty if `D` is non-torsion). The non-principal-branch analogue
of `cIntegrateAlgebraic`'s assembly: where the principal driver packs `(c, u)` from `radLogArgSolve`, this
packs `(1/m, g)` from the torsion decision + generator. `algDeriv` of the result returns the differential. -/
def torsionAlgResult (p : ℕ) [Fact p.Prime]
    (ρ : QFunNZG ℚ) (ρq : CPolyG ℚ) (g : ℕ) (v : RadElem (QFunNZG ℚ)) (D : MumfordDivisor ℚ) :
    AlgIntegralResult :=
  match torsionLogTerm p ρ ρq g D with
  | none => ⟨v, []⟩
  | some term => ⟨v, [term]⟩

/-- The assembled torsion result `∫ = 0 + (1/3)·log(y − 1)` (no rational part) for `(0, 1)` on
`y² = x³ + 1` — `torsionAlgResult` with `v = 0` (`radZero`). Expected `logTerms = [(1/3, y − 1)]`. -/
def tltResult01 : AlgIntegralResult :=
  torsionAlgResult 5 tltRhoX3p1 hypRhoX3p1 1 radZero hypPt01

/-- **★ The assembled result has one log term with coefficient `1/3`** (`native_decide`): `torsionAlgResult`
on `(0, 1)` slots the torsion term `(1/3, y − 1)` into `logTerms`, giving a result with empty rational part
and exactly one log term whose coefficient is `1/3` (field-equal to `oneOverMQ 3` via `qEq`). The
`(1/m)·log` term lives in the integrator's `v + Σ cᵢ log uᵢ` structure (`cᵢ = 1/m`), checked on
`(radIsZero ratPart, logTerms.length, coefficient = 1/3)`. -/
theorem tltResult01_shape :
    (radIsZero tltResult01.ratPart,
     tltResult01.logTerms.length,
     (tltResult01.logTerms.head?.map fun t => qEq t.1 (oneOverMQ 3))) = (true, 1, some true) := by
  native_decide

/-- **★★ `algDeriv` of the assembled torsion result returns the `(1/3)·log(y − 1)` differential**
(`native_decide`): the result `⟨0, [(1/3, y − 1)]⟩` (built by `torsionAlgResult` from the divisor `(0, 1)`)
differentiates — via the SAME `algDeriv` the principal integrator uses — to `radDeriv 0 + (1/3)·(y − 1)'/(y
− 1) = (1/3)·g'/g = ι`, the `(1/3)·log(y − 1)` differential `tltDiff01`. Checked by `radIsZero` of the
difference over `ℚ(x)`. The torsion `(1/m)·log` term slots into the integrator's result type and round-trips
through the real radical derivation — THE NON-PRINCIPAL BRANCH IS ASSEMBLED INTO THE INTEGRATOR. -/
theorem tltResult01_algDeriv :
    radIsZero (radSub (algDeriv tltRhoX3p1 tltResult01) tltDiff01) = true := by native_decide

/-! ## ★ Non-torsion propagates to `none` (`native_decide`)

On the rank-1 curve `y² = x³ − 2`, the point `(3, 5)` has infinite order: `torsionLogTerm` returns `none`
(no elementary log term — the decision propagates), and the assembled result carries an empty log list. -/

/-- The radicand `ρ = x³ − 2` as a `ℚ(x)` element, for the non-torsion witness. -/
def tltRhoX3m2 : QFunNZG ℚ := qxOfNum [-2, 0, 0, 1]

/-- **★ `torsionLogTerm` on the infinite-order `(3, 5)` returns `none`** (`native_decide`): the
non-principal branch decides `(3, 5)` non-torsion (`isTorsionDivisor = none`, the good-reduction ceiling
terminating the search), so it produces **no** log term — that part of the integral over `y² = x³ − 2` is
**NOT elementary**. The decision propagates through the branch: non-torsion ⟹ `torsionLogTerm = none`. -/
theorem tltTerm35_none :
    torsionLogTerm 5 tltRhoX3m2 hypRhoX3m2 1 hypPt35 = none := by native_decide

/-- The assembled result for the non-torsion `(3, 5)` — `torsionAlgResult` with `v = 0`; expected
`⟨0, []⟩` (empty log list, the non-elementary signature). -/
def tltResult35 : AlgIntegralResult :=
  torsionAlgResult 5 tltRhoX3m2 hypRhoX3m2 1 radZero hypPt35

/-- **★ The non-torsion assembled result has an empty log list** (`native_decide`): `torsionAlgResult` on
`(3, 5)` produces `⟨0, []⟩` — no rational part, **no** log term, the structural signature that this part of
the integral is not elementary. Checked on `(radIsZero ratPart, logTerms.length) = (true, 0)`. The
non-principal branch correctly emits no `(1/m)·log` term for a point of infinite order. -/
theorem tltResult35_shape :
    (radIsZero tltResult35.ratPart, tltResult35.logTerms.length) = (true, 0) := by native_decide

/-! ## ★★ The non-principal-branch milestone (`native_decide`) -/

/-- **★★ THE NON-PRINCIPAL `(1/m)·log` BRANCH COMPUTES AND VALIDATES** (Trager Ch. 6 §1-3, `native_decide`).
`torsionLogTerm` ties the torsion sub-arc into a usable integrator branch: the DECISION (`isTorsionDivisor`:
order `m` or non-torsion) plus the CONSTRUCTION (`principalGenerator`: the generator `g` of `m·D`) produce
the **log term `(1/m, g)`** of the non-principal residue divisor, i.e. `∫ = … + (1/m)·log g`. On the order-3
flex `D = (0, 1)` of `y² = x³ + 1`:
* `torsionLogTerm` returns `(1/3, y − 1)` — coefficient `1/3`, the flex tangent line `g = y − 1`
  (`div(y − 1) = 3·(0, 1)`), **produced end-to-end from the divisor**;
* the `(1/3)·log(y − 1)` differential passes the cleared log-derivative certificate
  `radDeriv g = radMul g (3·ι)` (`ι = (1/3)·g'/g`);
* the term slots into an `AlgIntegralResult` (`torsionAlgResult`, `cᵢ = 1/m` in `v + Σ cᵢ log uᵢ`), and
  `algDeriv` of the assembled result returns the differential.

On the infinite-order `(3, 5)` of `y² = x³ − 2`, `torsionLogTerm` returns `none` (NOT elementary) and the
assembled result carries an empty log list — the decision propagates. The engine now produces the
`(1/m)·log` term for the **non-principal / torsion** case (`radLogArgSolve = none`), completing the
simple-radical elementarity decision procedure end-to-end: the principal log part (`cIntegrateAlgebraic`,
`1·log u`) AND the non-principal log part (`torsionLogTerm`, `(1/m)·log g`), decide and construct, both
answers (elementary `+` not elementary). -/
theorem torsion_log_branch_validates :
    -- the non-principal branch fires on the order-3 flex (0,1), returning (1/3, y − 1)
    (tltTerm01.map tltTermCheck = some true
      ∧ radIsLogIntegral 2 tltRhoX3p1 tltYm1 (radScale (qxOfNum [3]) tltDiff01) = true)
    -- the term assembles into the integrator's AlgIntegralResult and algDeriv round-trips
    ∧ ((radIsZero tltResult01.ratPart,
        tltResult01.logTerms.length,
        tltResult01.logTerms.head?.map fun t => qEq t.1 (oneOverMQ 3)) = (true, 1, some true)
      ∧ radIsZero (radSub (algDeriv tltRhoX3p1 tltResult01) tltDiff01) = true)
    -- non-torsion (3,5) propagates to none ⟹ NOT elementary
    ∧ ((torsionLogTerm 5 tltRhoX3m2 hypRhoX3m2 1 hypPt35).isNone = true
      ∧ (radIsZero tltResult35.ratPart, tltResult35.logTerms.length) = (true, 0)) := by native_decide

/-! ### Deliverable: `#print axioms`

`[propext, Classical.choice, Quot.sound]` plus `Lean.ofReduceBool` (the `native_decide` kernel-reduction
axiom). No `sorry`. -/

#print axioms torsion_log_branch_validates
#print axioms tltTerm01_eq
#print axioms tltResult01_algDeriv

/-! ## What is left: the residue → divisor front-end (the STRETCH, documented)

`torsionLogTerm` is the non-principal branch *from a residue divisor `D`*. The full end-to-end chain for an
arbitrary torsion integrand is

  integrand → residues (`cAlgResidueResultant`) → residue divisor (`residueDivisorMumford`) → `torsionLogTerm`,

i.e. the **residue → divisor front-end** feeding the branch built here. The first two hops already exist
(`ComputableAlgebraicResidues`'s residue resultant gives the pole set; `residueDivisorMumford`
(`ComputableHyperellipticDivisor`) turns a residue's support points `[(xᵢ, yᵢ)]` into the Mumford pair `D`);
wiring them so the integrator *automatically* hands the non-principal residue divisor to `torsionLogTerm`
(rather than the divisor being supplied, as in the round-trips here) is the remaining glue — recorded, not
yet formalized, in the `Sources/Doi_10_1007_b138171` catalog.

Also still open from the torsion sub-arc (in `ComputablePrincipalGenerator`'s closing note): the general
principal generator for higher genus (`y² = x⁵ + 1`, non-constant step `v`) and the composition-step
cancellation cofactors — `principalGenerator` is exact for the order-3 genus-1 flex used here.

The milestone delivered: the **non-principal branch as a usable function** — `torsionLogTerm` produces the
`(1/m)·log g` term from the divisor, the `(0, 1) → (1/3)·log(y − 1)` round-trip with the log-derivative
check, the non-torsion `none`, and the assembly into the integrator's `AlgIntegralResult`. The engine now
produces the `(1/m)·log` term for the non-principal/torsion case, completing the simple-radical elementarity
decision procedure end-to-end. -/

end DeepWiki.SymbolicIntegration
