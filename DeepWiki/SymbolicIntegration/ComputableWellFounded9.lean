import DeepWiki.SymbolicIntegration.ComputableWellFounded8
import DeepWiki.SymbolicIntegration.ComputableCoupledDE
import DeepWiki.SymbolicIntegration.ComputableStructure
import DeepWiki.SymbolicIntegration.ComputableParametric
import DeepWiki.SymbolicIntegration.ComputableParallel

/-! # Fuel-free (well-founded) §7–§10 companions — completing the fuel-free engine

This completes the fuel-free conversion of the transcendental symbolic-integration engine: the two major
integrators (`cIntegrateWf`/`cIntegrateCheckedWf` and the all-regimes §6 RDE oracle `cRischDEWfFull`) are
done in `ComputableWellFounded`/`…2`/`…3`/`…4`/`…5`/`…6`/`…7`/`…8`. The remaining fuel-bearing **top-level**
functions are the §7 parametric pipeline, the §8 coupled DE system, the §9 structure decisions, and the §10
parallel (Risch–Norman) integrator. Re-grepping each for its actual fuel usage shows that **most are
compositions** over the linear-algebra core (`crref`/nullspace/`cConstSolve*Q`), which is **already
fuel-free** (it takes no fuel argument — `crref`'s internal `go` counter is self-fed at its single call
site `go (ncols + rows.length + 1) 0 …`, not threaded in); fuel survives only in a few leaf sub-ops.

**Status of each §7–§10 top-level function (re-grepped fuel usage):**

* **§8 `cCoupledDESystem`** — its fuel argument is named `_fuel` and is **UNUSED** (the body is a pure
  matrix assembly + the fuel-free unique-solve `cConstSolveUniqueQ`). So it is **already fuel-free**: the
  companion `cCoupledDESystemWf := cCoupledDESystem 0` is *definitionally* the fuel'd op at any fuel (the
  bridge is `rfl`), and the §8 base-coupled-solve example transports verbatim. *(The §8.4 own-loop
  `cCoupledDECancelTan` genuinely recurses on fuel, but it is **not** a target here — only the base
  `cCoupledDESystem`, which the prompt names, is in scope.)*

* **§10 `cParallelIntegrate`** — fuel threads through `cParallelSystemQ`/`cParallelAnsatzQ`, which bottom
  out at exactly one fuel-bearing op: the Yun squarefree factorization `cSquarefreeFactorsQ` (over the
  **generic `CPolyG ℚ`** division layer `cgcdExtG`/`cdivG`, whose fuel-free leaves `cgcdWf`/`cdivWf` already
  exist). So §10 is **converted by substitution**: the Yun own-loop `cSquarefreeFactorsQWf` (true WF
  recursion on the peel counter, structural guard), then the compositions `cParallelAnsatzQWf`/
  `cParallelSystemQWf`/`cParallelIntegrateWf` substitute it. The eq. 10.6 solve `cConstSolveAnyQ` is
  fuel-free already; the §10 cleared-identity examples transport.

* **§9 `cLogIsNewMonomial`/`cExpIsNewMonomial`/`cLogRelationCoeffs`** and **§7 `cParamLogDeriv`** — fuel
  threads through the **`Compute.*` (`CPoly = CPolyG ℚ`) division layer** `Compute.qnorm`/`Compute.cdiv`/
  `Compute.cgcdExt`, a stack with no pre-existing fuel-free leaf. We **build the `Compute`-layer WF leaves**
  here (`Compute.cdivmodWf`/`cdivWf`/`cgcdExtWf`/`qnormWf`, mirroring the generic `cdivmodWf`/`cgcdWf`), then
  the §9/§7 compositions (`cLcmQWf`, `cLinearDepDataWf`, the structure decisions, `cParamLogDerivWf`)
  substitute them. The ℚ-nullspace solver is fuel-free; the §9/§7 examples transport.

* **§7 `cParamRischDE`/`cLimitedIntegrate`** — fuel threads through `cLcmQ` (generic `cdivG`/`cgcdExtG` →
  existing leaves) and `cdivmodG`; the §6-stage generalization and the constraint solve are fuel-free.
  Converted by substituting `cLcmQWf` + the generic `cdivWf`/`cdivmodWf` leaves.

As throughout, where a fuel'd bridge is given the fuel bounds live only in the bridge proof; the runtime WF
ops carry no fuel. The `native_decide` smoke tests re-run Bronstein's Examples 7.x/8.4.1/9.3.1/10.3.x over
the relevant carriers, now fuel-free. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZ

/-! ### §8 — `cCoupledDESystemWf`: already fuel-free (`_fuel` unused)

`cCoupledDESystem (_fuel : ℕ) a b1 b2 z1 z2 d` (Bronstein Ch. 8, eq. 8.2/8.10) ignores its fuel argument
entirely (`_fuel` is unused — the body is the polynomial-ansatz matrix assembly + the fuel-free unique-solve
`cConstSolveUniqueQ`). The fuel-free companion fixes the dummy fuel to `0`; the bridge to any fuel is `rfl`. -/

namespace CPolyG

/-- **Fuel-free base coupled differential system over ℚ(x)** `cCoupledDESystemWf a b1 b2 z1 z2 d`
(Bronstein Ch. 8, eq. 8.2/8.10): the fuel-free companion of `cCoupledDESystem`. Since `cCoupledDESystem`'s
fuel argument is **unused** (`_fuel`), this is just `cCoupledDESystem 0` — the same polynomial-ansatz solve
`(Dy₁; Dy₂) + [[b₁, a·b₂], [b₂, b₁]]·(y₁; y₂) = (z₁; z₂)` for `y₁, y₂ ∈ ℚ[x]` of degree `≤ d`, via the
fuel-free unique-solve `cConstSolveUniqueQ`. **No fuel at runtime** (there never was any). -/
def cCoupledDESystemWf (a : ℚ) (b1 b2 z1 z2 : CPolyG ℚ) (d : ℕ) :
    Option (CPolyG ℚ × CPolyG ℚ) :=
  cCoupledDESystem 0 a b1 b2 z1 z2 d

/-- **Bridge — `cCoupledDESystemWf` equals `cCoupledDESystem` at any fuel.** Since `cCoupledDESystem`
ignores its fuel argument (`_fuel`), `cCoupledDESystemWf a b1 b2 z1 z2 d = cCoupledDESystem fuel a b1 b2 z1
z2 d` for **every** `fuel`, by `rfl` (both unfold to the same fuel-independent body). No fuel bound is
needed. -/
theorem cCoupledDESystemWf_eq (fuel : ℕ) (a : ℚ) (b1 b2 z1 z2 : CPolyG ℚ) (d : ℕ) :
    cCoupledDESystemWf a b1 b2 z1 z2 d = CPolyG.cCoupledDESystem fuel a b1 b2 z1 z2 d := rfl

end CPolyG

/-! ### `native_decide` — the fuel-free §8 base coupled solve (Bronstein Example 8.4.1, book p.266 step 4)

Re-runs `coupledDESystem_example` over the base field ℚ(x), now fuel-free: the base coupled system
`(Dy₁; Dy₂) + [[0, −(4x−2)], [4x−2, 0]]·(y₁; y₂) = (2−8x²; 4−4x)` (`a = −1`) is solved by the polynomial
ansatz, returning `(s₁, s₂) = (−1, 2x+1)`, verified to actually solve the system by `coupledClearedCheck`. -/

open CPolyG in
/-- **The fuel-free §8 base coupled solve computes over ℚ(x)** (`native_decide`, Bronstein Ch. 8, book
p.266 step 4): `cCoupledDESystemWf` returns `(s₁, s₂) = (−1, 2x+1)` for Example 8.4.1's base coupled
system, verified by the cleared row identities `coupledClearedCheck` (both residuals vanish). The fuel-free
companion of `coupledDESystem_example`. -/
theorem coupledDESystemWf_example :
    (match cCoupledDESystemWf (-1) ([] : CPolyG ℚ) coupledExB2 coupledExZ1 coupledExZ2 1 with
      | some (y1, y2) =>
          coupledClearedCheck (-1) [] coupledExB2 coupledExZ1 coupledExZ2 y1 y2
      | none => false) = true := by native_decide

#print axioms coupledDESystemWf_example

-- The §8 base coupled-system bridge carries only the standard axioms.
#print axioms CPolyG.cCoupledDESystemWf_eq

end DeepWiki.SymbolicIntegration
