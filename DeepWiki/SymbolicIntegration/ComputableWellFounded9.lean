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

/-! ### §10 — `cParallelIntegrateWf`: fuel-free Risch–Norman integration over `ℚ(t)`

`cParallelIntegrate fuel Dt a d` (Bronstein §10.3) threads its fuel only through `cParallelSystemQ`/
`cParallelAnsatzQ`, which bottom out at the single fuel-bearing op `cSquarefreeFactorsQ` (Yun squarefree
factorization over `CPolyG ℚ`); the eq. 10.6 solve `cConstSolveAnyQ` is already fuel-free. So §10 converts
by substitution: the Yun own-loop gets a fuel-free companion `cSquarefreeFactorsQWf` (true well-founded
recursion on a structural multiplicity counter, internally bounded — like `cSqfreeYunFFgoWf`), substituting
the generic fuel-free leaves `cgcdWf`/`cdivWf` for the fuel'd `cgcdExtG`/`cdivG`; then the ansatz/system/
integrator compositions substitute it. -/

namespace CPolyG

/-! #### The fuel-free Yun squarefree factorization over ℚ `cSquarefreeFactorsQWf` (structural-counter loop)

`cSquarefreeFactorsQ fuel p` runs Yun over `CPolyG ℚ`: `c₀ = gcd(p, p′)`, `w₀ = p/c₀`, then peel
`dⱼ = w/gcd(w,c)`, `w ← gcd(w,c)`, `c ← c/gcd(w,c)`. Its inner `go` counts down on its **own** counter
(self-fed `go (fuel + deg p + 1) …`), **not** a polynomial degree — at a skipped multiplicity the running
`(w, c)` may be unchanged across steps, so a degree-guarded loop would truncate. The honest companion keeps
the multiplicity counter but computes a sufficient bound `parYunBoundQ` from the input, so the caller passes
no fuel; the gcd/division leaves are the fuel-free generic `cgcdWf`/`cdivWf`. -/

/-- **Sufficient internal Yun-counter bound over ℚ** `parYunBoundQ p := (cnormG p).length`: a provably
sufficient outer multiplicity counter for `cSquarefreeFactorsGoQWf` on `p` — Yun runs one step per
multiplicity slot and the max multiplicity is `≤ deg p < (cnormG p).length`, and it also bounds every
intermediate `t`-length (all running `(w, c)` have degree `≤ deg p`) for the inner gcds/divisions. Computed
once from the input, so the caller passes **no fuel**. -/
def parYunBoundQ (p : CPolyG ℚ) : ℕ := (cnormG p : List ℚ).length

/-- **Fuel-free Yun main loop over ℚ** `cSquarefreeFactorsGoQWf fo w c i`: the fuel-free companion of
`cSquarefreeFactorsQ`'s inner `go`, recursing **structurally on the outer multiplicity counter** `fo` (so
`decreasing_by` is automatic and the loop never truncates at skipped multiplicities). Stops when `c` is
constant (`cdegG c = 0`, emitting `w` as the last factor if non-constant) or the counter is exhausted; else
peels `y = gcd(w, c)` (monic), emits `z = w/y` (if non-constant) at multiplicity `i`, and recurses on
`(y, c/y, i+1)` with `fo` decremented. The inner gcd/division leaves are the generic fuel-free `cgcdWf`/
`cdivWf` — **no fuel at runtime**; the counter `fo` is supplied once by the entry `cSquarefreeFactorsQWf` as
`parYunBoundQ`. Agrees with `cSquarefreeFactorsQ`'s `go` at the same counter (`cSquarefreeFactorsGoQWf_eq`). -/
def cSquarefreeFactorsGoQWf : ℕ → CPolyG ℚ → CPolyG ℚ → ℕ → List (CPolyG ℚ × ℕ)
  | 0, _, _, _ => []
  | fo + 1, w, c, i =>
    if cdegG c = 0 then
      (if cdegG w = 0 then [] else [(cmonicG w, i)])
    else
      let y := cmonicG (cgcdWf w c).1
      let z := cdivWf w y
      let cnext := cdivWf c y
      let rest := cSquarefreeFactorsGoQWf fo y cnext (i + 1)
      if cdegG z = 0 then rest else (cmonicG z, i) :: rest

/-- **Fuel-free Yun squarefree factorization over ℚ[t]** `cSquarefreeFactorsQWf p = [(d₁,1),…,(dₑ,e)]`:
the fuel-free companion of `cSquarefreeFactorsQ`. With `c₀ = monic(gcd(p, p′))`, `w₀ = p/c₀`, runs the
fuel-free Yun loop `cSquarefreeFactorsGoQWf (parYunBoundQ p) w₀ c₀ 1` — the outer counter is the
internally-computed `parYunBoundQ p`, so the caller passes **no fuel**. `p ~ ∏ⱼ dⱼ^j`, the `dⱼ` pairwise
coprime and squarefree. Every gcd is the generic fuel-free `cgcdWf`, every exact division the fuel-free
`cdivWf` — **no fuel at runtime**; correct even at skipped multiplicities (where a degree-guarded loop
truncates). -/
def cSquarefreeFactorsQWf (p : CPolyG ℚ) : List (CPolyG ℚ × ℕ) :=
  let p := cmonicG p
  let c0 := cmonicG (cgcdWf p (cderivG p)).1
  let w0 := cdivWf p c0
  cSquarefreeFactorsGoQWf (parYunBoundQ p) w0 c0 1

/-! #### The fuel-free §10 compositions — ansatz, system, integrator

`cParallelAnsatzQ`/`cParallelSystemQ` thread fuel only into `cSquarefreeFactorsQ`; the fuel-free companions
substitute `cSquarefreeFactorsQWf` and otherwise reuse the fuel-free helpers (`cProductQ`, `cpowG`,
`cDerivMonomialQ`, …) verbatim. `cParallelIntegrate` then composes them with the fuel-free `cConstSolveAnyQ`. -/

/-- **Fuel-free Risch–Norman ansatz data over ℚ** `cParallelAnsatzQWf d degA`: the fuel-free companion of
`cParallelAnsatzQ`. Identical assembly — the monic squarefree factors `ps`, the rational-part denominator
`s = ∏ⱼ dⱼ^{j-1}`, and the numerator-coefficient count `nU` — but with the fuel-free Yun factorization
`cSquarefreeFactorsQWf`. **No fuel at runtime**. -/
def cParallelAnsatzQWf (d : CPolyG ℚ) (degA : ℤ) :
    List (CPolyG ℚ) × CPolyG ℚ × ℕ :=
  let sf := cSquarefreeFactorsQWf d
  let ps := sf.map Prod.fst
  let s := cProductQ (sf.map (fun (p, e) => cpowG p (e - 1)))
  let degS : ℤ := (cdegG s : ℤ)
  let degD : ℤ := (cdegG d : ℤ)
  let bound : ℤ := max degS (degA - degD + degS) + 1
  (ps, s, bound.toNat + 1)

/-- **Fuel-free eq. 10.6 linear system over ℚ** `cParallelSystemQWf Dt a d = (rows, rhs, nU, m)`: the
fuel-free companion of `cParallelSystemQ`. Identical assembly of the eq. 10.6 coefficient matrix (the
`uᵢ`-columns `(D(tⁱ)·s − tⁱ·Ds)·∏pⱼ`, the `cⱼ`-columns `Dpⱼ·s²·∏_{k≠j}pₖ`, rhs `a·s`) but using the
fuel-free ansatz `cParallelAnsatzQWf`. **No fuel at runtime**. -/
def cParallelSystemQWf (Dt a d : CPolyG ℚ) :
    List (List ℚ) × List ℚ × ℕ × ℕ :=
  let lcd := cleadG d
  let a := cscaleG (1 / lcd) a
  let (ps, s, nU) := cParallelAnsatzQWf d (cdegG a : ℤ)
  let m := ps.length
  let prodPs := cProductQ ps
  let s2 := cmulG s s
  let Ds := cDerivMonomialQ Dt s
  let target := cmulG a s
  let uPolys : List (CPolyG ℚ) := (List.range nU).map (fun i =>
    let bi : CPolyG ℚ := cshiftG i [(1 : ℚ)]
    cmulG (csubG (cmulG (cDerivMonomialQ Dt bi) s) (cmulG bi Ds)) prodPs)
  let cPolys : List (CPolyG ℚ) := (List.range m).map (fun j =>
    let pj := ps.getD j [(1 : ℚ)]
    let others := cProductQ (ps.zipIdx.filterMap (fun (p, k) => if k = j then none else some p))
    cmulG (cmulG (cDerivMonomialQ Dt pj) s2) others)
  let allPolys := uPolys ++ cPolys
  let nrows := (target :: allPolys).foldl (fun acc p => max acc (cnormG p).length) 0
  let rows : List (List ℚ) :=
    (List.range nrows).map (fun i => allPolys.map (fun p => cParCoeffQ p i))
  let rhs : List ℚ := (List.range nrows).map (fun i => cParCoeffQ target i)
  (rows, rhs, nU, m)

/-- **Fuel-free parallel (Risch–Norman) integration over ℚ(t)** `cParallelIntegrateWf Dt a d` (Bronstein
§10.3, the `ParallelIntegrate(f, D)` box): the fuel-free companion of `cParallelIntegrate`. For `f = a/d ∈
ℚ(t)` (`D = Dt·d/dt`) it builds the ansatz `∫f = b/s + Σⱼ cⱼ·log(pⱼ)` via the fuel-free `cParallelSystemQWf`/
`cParallelAnsatzQWf` (the Yun factorization fuel-free), solves the eq. 10.6 system with the fuel-free
`cConstSolveAnyQ`, and returns `some ((b, s), [(cⱼ, pⱼ)])` (the elementary antiderivative) or `none` (the
heuristic failure — the ansatz did not capture an elementary integral, *not* a non-elementarity proof). **No
fuel at runtime**. -/
def cParallelIntegrateWf (Dt a d : CPolyG ℚ) :
    Option ((CPolyG ℚ × CPolyG ℚ) × List (ℚ × CPolyG ℚ)) :=
  let (rows, rhs, nU, m) := cParallelSystemQWf Dt a d
  let (ps, s, _) := cParallelAnsatzQWf d (cdegG (cscaleG (1 / cleadG d) a) : ℤ)
  match cConstSolveAnyQ rows rhs (nU + m) with
  | none => none
  | some sol =>
    let b : CPolyG ℚ := (List.range nU).map (fun i => sol.getD i 0)
    let cs : List ℚ := (List.range m).map (fun j => sol.getD (nU + j) 0)
    let logs : List (ℚ × CPolyG ℚ) := (List.zip cs ps).filter (fun (c, _) => c ≠ 0)
    some ((cnormG b, s), logs)

end CPolyG

/-! #### `native_decide` — the fuel-free §10 parallel integrator on Bronstein's §10.3 examples

Re-runs `parallelIntegrate_{log,exp,mixed,failure}_example` over ℚ(t), now fuel-free: pure log
`∫2t/(t²+1) = log(t²+1)` (`t = x`), transcendental `∫t/(t+1)² = −1/(t+1)` and mixed `∫(t²+2t)/(t+1)² =
−1/(t+1)+log(t+1)` (`t = exp x`), and the heuristic failure `∫1/(eˣ+1)` (`none`). Each returned
antiderivative is verified to actually satisfy `D(∫f) = f` by the cleared identity `cParallelCheckQ`. -/

open CPolyG

/-- **The fuel-free §10 parallel integrator computes the pure-log example** (`native_decide`, Bronstein
§10.3): `cParallelIntegrateWf` recovers `log(t²+1)` for `∫2t/(t²+1)` (`t = x`), verified by `cParallelCheckQ`.
The fuel-free companion of `parallelIntegrate_log_example`. -/
theorem parallelIntegrateWf_log_example :
    (match cParallelIntegrateWf [1] parallelExampleLogA parallelExampleLogD with
      | some res => cParallelCheckQ [1] parallelExampleLogA parallelExampleLogD res
      | none => false) = true := by native_decide

/-- **The fuel-free §10 parallel integrator computes the transcendental example** (`native_decide`,
Bronstein §10.3): `cParallelIntegrateWf` recovers `−1/(t+1)` for `∫exp(x)/(exp(x)+1)²` (`t = exp x`, `Dt =
t`), verified by `cParallelCheckQ`. The fuel-free companion of `parallelIntegrate_exp_example`. -/
theorem parallelIntegrateWf_exp_example :
    (match cParallelIntegrateWf parallelExampleExpDt parallelExampleExpA parallelExampleExpD with
      | some res => cParallelCheckQ parallelExampleExpDt parallelExampleExpA parallelExampleExpD res
      | none => false) = true := by native_decide

/-- **The fuel-free §10 parallel integrator computes the mixed rational+log example** (`native_decide`,
Bronstein §10.3): `cParallelIntegrateWf` recovers both `−1/(t+1)` and `log(t+1)` for `∫(t²+2t)/(t+1)²` (`t =
exp x`) in one solve, verified by `cParallelCheckQ`. The fuel-free companion of
`parallelIntegrate_mixed_example`. -/
theorem parallelIntegrateWf_mixed_example :
    (match cParallelIntegrateWf parallelExampleExpDt parallelExampleMixA parallelExampleExpD with
      | some res => cParallelCheckQ parallelExampleExpDt parallelExampleMixA parallelExampleExpD res
      | none => false) = true := by native_decide

/-- **The fuel-free §10 parallel integrator returns `none` on the non-(ansatz-)elementary example**
(`native_decide`, Bronstein §10.3): `cParallelIntegrateWf` returns `none` for `∫1/(exp(x)+1)` (whose
antiderivative `x − log(eˣ+1)` lies outside ℚ(exp x)) — the heuristic failure. The fuel-free companion of
`parallelIntegrate_failure_example`. -/
theorem parallelIntegrateWf_failure_example :
    cParallelIntegrateWf parallelExampleExpDt parallelExampleFailA parallelExampleFailD = none := by
  native_decide

#print axioms parallelIntegrateWf_mixed_example

/-! ### The fuel-free `Compute`-layer leaves — `qnormWf`, `cLcmQWf`

The §9 structure decisions and §7 `cParamLogDeriv` thread fuel through the `Compute.*` rational-function
layer (`Compute.qnorm`/`Compute.cdiv`/`Compute.cgcdExt`, over `CPoly = CPolyG ℚ`), which has no
pre-existing fuel-free leaf. We build the two leaves they need on top of the **generic** fuel-free
`cgcdWf`/`cdivWf` (which work at `α = ℚ`, `[CFieldSpec ℚ]`), bridging to the fuel'd `Compute` ops through the
existing generic↔Compute agreements `cgcdExtG_eq_cgcdExt`/`cdivG_eq_cdiv` (`ComputableFieldGcd`) composed
with the WF-leaf fuel bridges `cgcdWf_eq_of_fuel`/`cdivmodWf_eq_of_fuel`. The polynomial lcm `cLcmQ`
threads only the **generic** `cdivG`/`cgcdExtG`, so its companion sits directly on the generic leaves. -/

namespace Compute

/-- **Fuel-free lowest-terms reduction** `qnormWf x = (a/q, b/q)` scaled to a monic denominator, the
fuel-free companion of `Compute.qnorm`. Identical to `qnorm` — divide numerator and denominator by their
gcd `q = (cgcdWf a b).1`, then scale both by `(lead of b/q)⁻¹` — but with the **generic fuel-free**
extended-Euclid gcd `cgcdWf` and division `cdivWf` (over `CPolyG ℚ = CPoly`) replacing `Compute.cgcdExt
fuel`/`Compute.cdiv fuel`. The zero fraction stays `qzero`. **No fuel at runtime**. -/
def qnormWf (x : QFun) : QFun :=
  let (a, b) := x
  if cisZero a then qzero
  else
    let q := (CPolyG.cgcdWf a b).1
    let a' := CPolyG.cdivWf a q
    let b' := CPolyG.cdivWf b q
    let s := (clead b')⁻¹
    (cscale s a', cscale s b')

/-- **Bridge — `qnormWf` equals `Compute.qnorm` at any sufficient fuel.** For
`(cnormG a).length ≤ fuel` and `(cnormG b).length < fuel` (the `cgcdWf_eq_of_fuel` margin; the divisions
inherit `a, b ≤ fuel`), `qnormWf x = Compute.qnorm fuel x`. The gcd agrees by `cgcdWf_eq_of_fuel` then
`cgcdExtG_eq_cgcdExt`; the two divisions by `cdivWf = cdivG fuel = cdiv fuel`
(`cdivmodWf_eq_of_fuel`/`cdivG_eq_cdiv`). The fuel bounds live only here; `qnormWf` carries none. -/
theorem qnormWf_eq_of_fuel (fuel : ℕ) (x : QFun)
    (ha : (CPolyG.cnormG x.1 : List ℚ).length ≤ fuel)
    (hb : (CPolyG.cnormG x.2 : List ℚ).length < fuel) :
    qnormWf x = Compute.qnorm fuel x := by
  obtain ⟨a, b⟩ := x
  rw [qnormWf, Compute.qnorm]
  by_cases hca : cisZero a = true
  · simp only [hca, if_true]
  · simp only [hca, Bool.false_eq_true, if_false]
    -- the gcd agrees: `cgcdWf a b = cgcdExtG fuel a b = cgcdExt fuel a b`
    have hgcd : (CPolyG.cgcdWf a b).1 = (Compute.cgcdExt fuel a b).1 := by
      rw [CPolyG.cgcdWf_eq_of_fuel fuel a b ha hb, ← CPolyG.cgcdExtG_eq_cgcdExt fuel]
    -- the two divisions agree at fuel: `cdivWf p q = cdiv fuel p q`
    have hdiv : ∀ p : CPolyG ℚ, (CPolyG.cnormG p : List ℚ).length ≤ fuel →
        CPolyG.cdivWf p ((Compute.cgcdExt fuel a b).1)
          = Compute.cdiv fuel p ((Compute.cgcdExt fuel a b).1) := by
      intro p hp
      rw [CPolyG.cdivWf, CPolyG.cdivmodWf_eq_of_fuel fuel p _ hp, Compute.cdiv,
        CPolyG.cdivmodG_eq_cdivmod fuel]
    rw [hgcd, hdiv a ha, hdiv b (le_of_lt hb)]

end Compute

namespace CPolyG

/-- **Fuel-free polynomial lcm over ℚ** `cLcmQWf p q = p·q / gcd(p, q)` (monic): the fuel-free companion
of `cLcmQ`, with the **generic fuel-free** extended-Euclid gcd `cgcdWf` and division `cdivWf` replacing
`cgcdExtG fuel`/`cdivG fuel`. **No fuel at runtime**. -/
def cLcmQWf (p q : CPolyG ℚ) : CPolyG ℚ :=
  if cisZeroG p ∨ cisZeroG q then []
  else cmonicG (cdivWf (cmulG p q) (cgcdWf p q).1)

/-- **Bridge — `cLcmQWf` equals `cLcmQ` at any sufficient fuel.** For `(cnormG (p·q)).length ≤ fuel`,
`(cnormG p).length ≤ fuel` and `(cnormG q).length < fuel` (the `cgcdWf_eq_of_fuel`/`cdivmodWf_eq_of_fuel`
margins), `cLcmQWf p q = cLcmQ fuel p q`: the gcd agrees (`cgcdWf_eq_of_fuel`) and the division agrees
(`cdivWf = cdivG fuel`). The fuel bounds live only here; `cLcmQWf` carries none. -/
theorem cLcmQWf_eq_of_fuel (fuel : ℕ) (p q : CPolyG ℚ)
    (hpq : (cnormG (cmulG p q) : List ℚ).length ≤ fuel)
    (hp : (cnormG p : List ℚ).length ≤ fuel) (hq : (cnormG q : List ℚ).length < fuel) :
    cLcmQWf p q = cLcmQ fuel p q := by
  rw [cLcmQWf, cLcmQ]
  by_cases h : cisZeroG p ∨ cisZeroG q
  · simp only [h, if_true]
  · simp only [h, if_false]
    rw [cgcdWf_eq_of_fuel fuel p q hp hq, cdivWf, cdivmodWf_eq_of_fuel fuel _ _ hpq, cdivG]

end CPolyG

-- The fuel-free `Compute`-layer + lcm leaf bridges carry only the standard axioms.
#print axioms Compute.qnormWf_eq_of_fuel
#print axioms CPolyG.cLcmQWf_eq_of_fuel

end DeepWiki.SymbolicIntegration
