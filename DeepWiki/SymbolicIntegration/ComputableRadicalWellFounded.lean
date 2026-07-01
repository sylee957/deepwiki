import DeepWiki.SymbolicIntegration.ComputableRadicalRationalDriver
import DeepWiki.SymbolicIntegration.ComputableFuelFreeDiophantine
import DeepWiki.SymbolicIntegration.ComputableTowerWellFounded
import DeepWiki.SymbolicIntegration.ComputableRadicalIntegrateFull

/-! # Fuel-free (well-founded) ALGEBRAIC simple-radical rational-part integration

The simple-radical rational-part integrator (`ComputableRadicalIntegrate` /
`ComputableRadicalRationalDriver`) is `radDeriv`-validated and gate-clean, but every Hermite descent carries
an explicit `fuel : ℕ` (a structural counter `fuel + 1 → fuel`, called with a data-derived budget — the
initial multiplicity `k₀`, or `deg C + 1`). This file builds the **fuel-free** companions `…Wf` of the
core algebraic-integration recursions by the same well-founded-recursion technique the TRANSCENDENTAL tower
uses (`ComputableTowerWellFounded` / `ComputableTowerRischDEWellFounded`): recurse on the genuine decreasing
measure, with `termination_by`/`decreasing_by`, then validate the Wf top-level directly by the radical
derivation.

The simple-radical rational part has exactly **three** Hermite descents, each with a transparent measure:

* **`radReduceCase1IterateWf`** (Trager Appendix A §2.1) — the `C/(Vᵏy)` Hermite step `k → k−1`, `V` coprime
  to the radicand. Genuine measure: the **multiplicity `k`** (strictly drops `k → k−1`, bottoms at `k ≤ 1`).
  `termination_by k`; `decreasing_by` discharges `k − 1 < k` (at `k ≥ 2`).
* **`radReduceCase2IterateWf`** (Trager Appendix A §2.2) — the `C/(Wᵏy)` Hermite step at a branch place
  `W ∣ ρ`. Same measure (multiplicity `k`).
* **`radReduceCase3IterateWf`** (Trager Appendix A §2.3) — the leftover `C/y` degree-lowering. Genuine
  measure: the **degree `cdegG C`** (the residual `D` strictly drops it, bottoming at `deg C < deg f`).
  `termination_by (cnormG C).length`, under the structural runtime guard `(cnormG D).length < (cnormG C).length`,
  so `decreasing_by` is `assumption`. If the guard ever fails, the runtime returns the current state rather
  than taking an unjustified recursive step.

The wrappers `radIntegrateCase1Wf` / `radIntegrateCase2Wf` / `radIntegrateCase3Wf` are the fuel-free entries
(they compute the budget internally, like `radIntegrateCase{1,2,3}` did with `k0` / `deg C + 1`), and
`radPartialFractionCoprime` is already a fuel-free partial-fraction front-end (structural list recursion,
with the inner Bézout the fuel-free `cdiophantineGWf`). Every `…Wf` is `[CField α]`-only on the fuel-free fragment
(plus `[CFracGcdCore α]` where the multi-case driver's squarefree factorization needs it) — never
`[CFieldSpec α]`, so the whole arc still `native_decide`s over the noncomputable `ℚ(x)` tower.

**Scope-map of the remaining algebraic-integration path**:

* `radIntegrateRational` (`ComputableRadicalRationalDriver`) — **flat composition, no recursion of its own**;
  a fuel-free `radIntegrateRationalWf` only needs to substitute fuel-free leaves: `cSqfreeYunFFGWf` (the
  tower's squarefree factorization, already fuel-free), `cgcdWf`/`cdivWf` (already fuel-free leaves), this
  file's `radReduceCase{1,2}IterateWf` for the dispatch, and the shared `radPartialFractionCoprime`. The
  top-level validation below checks the Wf output directly.
* `cIntegrateAlgebraic` (`ComputableRadicalIntegrateFull`) — flat composition over `radIntegrateRationalWf`
  (above) + `radLogArgSolve`. **No recursion of its own.**
* `radLogArgSolve` (`ComputableRadicalLogArgument`) — flat composition (`radLogMatrix` + `ratKernelVector`
  + a `List.foldl` over the kernel vector). **No recursion of its own**; fuel-free once its matrix/kernel
  leaves are fuel-free.
* `radPartialFractionCoprime` — structural recursion on the **list of prime-powers** (`G :: rest → rest`),
  already structural and already using the fuel-free `cdiophantineGWf`; no Wf companion is needed.
* `afIntegrateAlgebraicWf` (`ComputableGeneralWellFounded`, the GENERAL non-radical algebraic curve) — now
  fuel-free by leaf substitution over the integral-basis linear solves; its log part is flat (residue
  resultants + a linear solve).
* The residue resultants (`cAlgResidueResultant`, `ComputableAlgebraicResidues`) bottom out at the generic
  fuel-free `cresultantWf` (`ComputableFuelFreeResultant`) — flat, no descent.

So after this file the **entire** algebraic-integration path is fuel-free, with the general-curve layer
handled by `afIntegrateAlgebraicWf`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

namespace CPolyG

variable {α : Type*} [CField α]

/-! ## Part 1 — the fuel-free Case-1 Hermite descent `radReduceCase1IterateWf`

`radReduceCase1Iterate der V Df f g k0 fuel k C vNum` recurses `k → k−1` (multiplicity), stopping at
`k ≤ 1` or when the structural fuel is exhausted. The genuine termination witness is the **multiplicity
`k`** — it strictly drops each step and never increases. The fuel-free companion recurses directly on `k`
(`termination_by k`); the only step taken is `k → k − 1` under `¬ k ≤ 1` (i.e. `k ≥ 2`), so `k − 1 < k`. -/

/-- **Fuel-free iterated Case-1 reduction** `radReduceCase1IterateWf der V Df f g k0 k C vNum = (Crem,
vNumOut)` (Trager Appendix A §2.1): the fuel-free companion of `radReduceCase1Iterate`, recursing **directly
on the multiplicity `k`** with **no fuel at runtime**. At `k ≥ 2` it solves the Hermite cofactor
`B = radCase1Cofactor k V Df f C`, forms the residual `D = radCase1Residual`, accumulates the
contribution `B·f·V^{k0−k}` into `vNum`, and recurses on `−D` at `k − 1`. Bottoms at `k ≤ 1` returning
`(C, vNum)`. The inner cofactor/residual leaves are already fuel-free. True well-founded
recursion on `k`; the single recursive call is at `k − 1 < k` (since `k ≥ 2`), so `decreasing_by` is the
`Nat.sub_lt` witness. `[CField α]`-only, so it `native_decide`s over the noncomputable `ℚ(x)` tower. -/
def radReduceCase1IterateWf (der : CPolyG α → CPolyG α) (V Df f g : CPolyG α) (k0 : ℕ) :
    ℕ → CPolyG α → CPolyG α → CPolyG α × CPolyG α
  | k, C, vNum =>
    if hk : k ≤ 1 then (C, vNum)
    else
      let B := radCase1Cofactor k V Df f C
      let Bder := der B
      let D := radCase1Residual k V Df f g B C Bder
      let contrib := cmulG (cmulG B f) (cpowG V (k0 - k))
      radReduceCase1IterateWf der V Df f g k0 (k - 1) (cnegG D) (caddG vNum contrib)
termination_by k => k
decreasing_by exact Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.lt_of_not_le hk).le) Nat.zero_lt_one

/-- **The fuel-free simple-radical rational-part driver (Case 1)** `radIntegrateCase1Wf der V f g k0 C =
(Crem, vNum)` (Trager Appendix A §2.1): the fuel-free companion of `radIntegrateCase1`. Computes `Df = V'`
(`der V`) and runs `radReduceCase1IterateWf` from multiplicity `k0` down to `1` — **no fuel**, since the
descent is well-founded on `k`. Master identity `∫ C/(V^{k0}y) = vNum/(V^{k0−1}y) + ∫ Crem/(Vy)`.
`[CField α]`-only. -/
def radIntegrateCase1Wf (der : CPolyG α → CPolyG α) (V f g : CPolyG α) (k0 : ℕ) (C : CPolyG α) :
    CPolyG α × CPolyG α :=
  radReduceCase1IterateWf der V (der V) f g k0 k0 C []

/-! ## Part 2 — the fuel-free Case-2 Hermite descent `radReduceCase2IterateWf`

Identical structure to Case 1 — the branch-place (`W ∣ ρ`) Hermite step `k → k−1`, genuine measure the
multiplicity `k`, the inner cofactor/residual the corrected `radCase2CofactorC`/`radCase2ResidualC`. The
common-denominator bookkeeping differs (contribution scaled by `W^{k0−k}` over `W^{k0}`), but the recursion
shape and measure are the same. -/

/-- **Fuel-free iterated Case-2 reduction** `radReduceCase2IterateWf W h ρ k0 k C vNum = (Crem, vNumOut)`
(Trager Appendix A §2.2): the fuel-free companion of `radReduceCase2Iterate`, recursing **directly on the
multiplicity `k`** with **no fuel at runtime**. At `k ≥ 2` it solves the corrected Case-2 cofactor
`B = radCase2CofactorC k W h C`, forms the residual `D = radCase2ResidualC`, accumulates the
contribution `B·ρ·W^{k0−k}` into `vNum` (over the common denominator `W^{k0}·y`), and recurses on `−D` at
`k − 1`. Bottoms at `k ≤ 1` returning `(C, vNum)`. `W` (a squarefree factor of `ρ`), `h = ρ/W`, the
radicand `ρ` passed in. True well-founded recursion on `k` (`decreasing_by`: `k − 1 < k`). `[CField α]`-only. -/
def radReduceCase2IterateWf (W h ρ : CPolyG α) (k0 : ℕ) :
    ℕ → CPolyG α → CPolyG α → CPolyG α × CPolyG α
  | k, C, vNum =>
    if hk : k ≤ 1 then (C, vNum)
    else
      let B := radCase2CofactorC k W h C
      let D := radCase2ResidualC k W h C B
      let contrib := cmulG (cmulG B ρ) (cpowG W (k0 - k))
      radReduceCase2IterateWf W h ρ k0 (k - 1) (cnegG D) (caddG vNum contrib)
termination_by k => k
decreasing_by exact Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.lt_of_not_le hk).le) Nat.zero_lt_one

/-- **The fuel-free simple-radical rational-part driver (Case 2)** `radIntegrateCase2Wf W ρ k0 C = (Crem,
vNum)` (Trager Appendix A §2.2): the fuel-free companion of `radIntegrateCase2`. Computes `h = ρ/W`
(`cdivWf ρ W` — the fuel-free exact division, same as the file's other divisions) and runs
`radReduceCase2IterateWf` from multiplicity `k0` down to `1` — **no fuel** anywhere. Master identity
`∫ C/(W^{k0}y) = vNum/(W^{k0}y) + ∫ Crem/(Wy)`. `[CField α]`-only. -/
def radIntegrateCase2Wf (W ρ : CPolyG α) (k0 : ℕ) (C : CPolyG α) : CPolyG α × CPolyG α :=
  radReduceCase2IterateWf W (cdivWf ρ W) ρ k0 k0 C []

/-! ## Part 3 — the fuel-free Case-3 (`C/y`) degree-lowering `radReduceCase3IterateWf`

`radReduceCase3Iterate der f g fuel C vNum` lowers `deg C` (cancelling the leading term) until
`deg C < deg f`. The genuine measure is `cdegG C` (equivalently `(cnormG C).length`), which strictly drops
each successful step. Unlike Cases 1–2 (where the measure `k` drops by a fixed `−1`), the degree drop is
**data-driven**. The `…Wf` recurses under the structural runtime guard
`(cnormG D).length < (cnormG C).length` (`decreasing_by assumption`). -/

/-- **Fuel-free iterated Case-3 reduction** `radReduceCase3IterateWf der f g C vNum = (Crem, vNumOut)`
(Trager Appendix A §2.3): the fuel-free companion of `radReduceCase3Iterate`, recursing on the **degree of
`C`** (`(cnormG C).length`) with **no fuel at runtime**. While `deg C ≥ deg f` it cancels the leading term
with `B = radCase3Cofactor f g C`, forms the residual `D = radCase3Residual f g B C (der B)`, accumulates
`B·f` into `vNum` (over the common denominator `y`), and recurses on `−D`. Bottoms at `deg C < deg f` (or
`C = 0`) returning `(C, vNum)`. The recursion is taken **only under the structural guard**
`(cnormG (cnegG D)).length < (cnormG C).length`, so `decreasing_by` is `assumption`; on a real run the guard
never fails (`deg D < deg C`). `der` the base derivation (`cderivG` for `θ' = 1`), `f` the radicand, `g`
(from `(f/y)' = g/y`) passed in. `[CField α]`-only. -/
def radReduceCase3IterateWf (der : CPolyG α → CPolyG α) (f g : CPolyG α) :
    CPolyG α → CPolyG α → CPolyG α × CPolyG α
  | C, vNum =>
    if cisZeroG C || cdegG C < cdegG f then (C, vNum)
    else
      let B := radCase3Cofactor f g C
      let D := radCase3Residual f g B C (der B)
      if (cnormG (cnegG D) : List α).length < (cnormG C : List α).length then
        radReduceCase3IterateWf der f g (cnegG D) (caddG vNum (cmulG B f))
      else (C, vNum)   -- unreachable on a real run (the leading term cancels, `deg D < deg C`)
termination_by C => (cnormG C : List α).length
decreasing_by assumption

/-- **The fuel-free simple-radical rational-part driver (Case 3)** `radIntegrateCase3Wf der f g C = (Crem,
vNum)` (Trager Appendix A §2.3): the fuel-free companion of `radIntegrateCase3`. Runs the fuel-free
`C/y` degree-lowering — **no fuel** (well-founded on `cdegG C`). Master identity `∫ C/y = vNum/y + ∫
Crem/y`. `der = cderivG` for `θ' = 1`; `g` read off `(f/y)' = g/y`. `[CField α]`-only. -/
def radIntegrateCase3Wf (der : CPolyG α → CPolyG α) (f g C : CPolyG α) : CPolyG α × CPolyG α :=
  radReduceCase3IterateWf der f g C []

end CPolyG

/-! ## Part 4 — the shared fuel-free partial-fraction front-end

`radPartialFractionCoprime R Gs` recurses **structurally on the list `Gs`** of pairwise-coprime
prime-powers (`G :: rest → rest`) and carries no fuel argument. Its inner Bezout split is already the
generic fuel-free `cdiophantineGWf` (`ComputableFuelFreeDiophantine`), so the Wf top-level shares the same
helper directly. -/

/-! ## Part 5 — `native_decide` validation: the fuel-free iterates reproduce the validated runs

The fuel-free Case-1, Case-2, and Case-3 iterates produce **exactly** the same `(Crem, vNum)` as the
validated fueled runs (`sqrtxRun`/`cubeRun`, `c2itRun`, `c3itRun`), so every `radDeriv`-validated identity
there holds verbatim of the fuel-free output. Checked directly by `native_decide` over `ℚ` — the whole arc is
`[CField α]`-only, nothing noncomputable reaches the native compiler. -/

open RadElem CPolyG

/-- **The fuel-free Case-1 run** `radIntegrateCase1Wf cderivG V f g 3 C` on
`∫ 1/((x−1)³√x)` — the no-fuel companion of `sqrtxRun`. -/
def sqrtxRunWf : CPolyG ℚ × CPolyG ℚ :=
  radIntegrateCase1Wf cderivG sqrtxV sqrtxF sqrtxG 3 sqrtxC

/-- **The fuel-free Case-1 iterate reproduces `sqrtxRun`** (`native_decide`): the Wf descent on
`∫ 1/((x−1)³√x)` yields exactly the validated `(Crem, vNum)` of the original run. -/
theorem radIntegrateCase1Wf_eq_sqrtxRun :
    sqrtxRunWf = sqrtxRun := by native_decide

/-- The fuel-free rational part for `∫ 1/((x−1)³√x)` lifted to `RadElem (QFunNZG ℚ)`. -/
def sqrtxVliftWf : RadElem (QFunNZG ℚ) :=
  [CField.zero, CField.div (qxOfNum sqrtxRunWf.2) (qxOfNum (cmulG sqrtxV2 sqrtxF))]

/-- The fuel-free rational-part target for `∫ 1/((x−1)³√x)` lifted to `RadElem (QFunNZG ℚ)`. -/
def sqrtxRatLiftWf : RadElem (QFunNZG ℚ) :=
  [CField.zero,
    CField.sub (CField.div (qxOfNum sqrtxC) (qxOfNum (cmulG sqrtxV3 sqrtxF)))
      (CField.div (qxOfNum sqrtxRunWf.1) (qxOfNum (cmulG sqrtxV sqrtxF)))]

/-- **The fuel-free Case-1 driver integrates `∫ 1/((x−1)³√x)`** (`native_decide`): `radDeriv` of the Wf
rational part equals the rational part of the integrand after subtracting the `k = 1` residual. -/
theorem sqrtxDriverWf_integrates :
    radIsZero (radSub (radDeriv 2 sqrtxFqx sqrtxVliftWf) sqrtxRatLiftWf) = true := by native_decide

/-- **The fuel-free Case-1 run** on `∫ 1/((x−1)³√(x³+1))` — the no-fuel companion of `cubeRun`. -/
def cubeRunWf : CPolyG ℚ × CPolyG ℚ :=
  radIntegrateCase1Wf cderivG cubeV cubeF cubeG 3 cubeC

/-- **The fuel-free Case-1 iterate reproduces `cubeRun`** (`native_decide`): the Wf descent on the
headline radicand `y² = x³+1` yields exactly the validated `(Crem, vNum)` of the original run. -/
theorem radIntegrateCase1Wf_eq_cubeRun :
    cubeRunWf = cubeRun := by native_decide

/-- The fuel-free rational part for `∫ 1/((x−1)³√(x³+1))` lifted to `RadElem (QFunNZG ℚ)`. -/
def cubeVliftWf : RadElem (QFunNZG ℚ) :=
  [CField.zero, CField.div (qxOfNum cubeRunWf.2) (qxOfNum (cmulG (cpowG cubeV 2) cubeF))]

/-- The fuel-free rational-part target for `∫ 1/((x−1)³√(x³+1))` lifted to `RadElem (QFunNZG ℚ)`. -/
def cubeRatLiftWf : RadElem (QFunNZG ℚ) :=
  [CField.zero,
    CField.sub (CField.div (qxOfNum cubeC) (qxOfNum (cmulG (cpowG cubeV 3) cubeF)))
      (CField.div (qxOfNum cubeRunWf.1) (qxOfNum (cmulG cubeV cubeF)))]

/-- **The fuel-free Case-1 driver integrates `∫ 1/((x−1)³√(x³+1))`** (`native_decide`): `radDeriv` of the Wf
rational part equals the rational part of the integrand after subtracting the `k = 1` residual. -/
theorem cubeDriverWf_integrates :
    radIsZero (radSub (radDeriv 2 cubeFqx cubeVliftWf) cubeRatLiftWf) = true := by native_decide

/-- **The fuel-free Case-2 iterate reproduces the validated run** `radIntegrateCase2Wf W ρ 3 C =
radIntegrateCase2 W ρ 3 C` on `∫ 1/(x³·√(x³−x))` (`native_decide`). The fuel-free descent (recursing on the
multiplicity `k = 3 → 2 → 1`) yields exactly the `(Crem, vNum)` of `c2itRun`, so the `radDeriv`-validated
identity `c2itDriver_integrates` holds verbatim of the fuel-free output. -/
theorem radIntegrateCase2Wf_eq_c2itRun :
    radIntegrateCase2Wf c2itW c2itRho 3 c2itC = c2itRun := by native_decide

/-- **The fuel-free Case-3 iterate reproduces the validated run** `radIntegrateCase3Wf cderivG ρ g C =
radIntegrateCase3 cderivG ρ g C` on `∫ x⁴/√(x³+1)` (`native_decide`). The fuel-free degree-lowering yields
exactly the `(Crem, vNum)` of `c3itRun`, so `c3itDriver_integrates` holds verbatim of the fuel-free output. -/
theorem radIntegrateCase3Wf_eq_c3itRun :
    radIntegrateCase3Wf cderivG c3itRho c3itG c3itC = c3itRun := by native_decide

/-! ## Part 6 — the FLAT fuel-free top-level: `radIntegrateRationalWf` / `cIntegrateAlgebraicWf`

`radIntegrateRational` and `cIntegrateAlgebraic` have **no recursion of their own** (the descents are all in
the Part 1–3 iterates), so their fuel-free companions are pure **leaf substitution**: every fueled leaf is
swapped for its fuel-free counterpart, the flat structure is unchanged, and **no `termination_by` is needed**.
The Wf top-level is validated directly below by differentiating its output. -/

namespace CPolyG

variable {α : Type*} [CField α]

/-- **The fuel-free multi-case simple-radical rational-part driver** `radIntegrateRationalWf ρ R B` over
`y² = ρ`, denominator `B` monic, numerator `R` (proper): the fuel-free companion of `radIntegrateRational`,
by **pure leaf substitution** — `cSqfreeYunFFGWf` for the squarefree factorization (no fuel), `(cgcdWf · ·).1`
for every gcd, `cdivWf` for every exact division, `radPartialFractionCoprime` for the partial fraction, and
this file's `radReduceCase{1,2}IterateWf` for the Case-1 / Case-2 dispatch. Same flat structure as
`radIntegrateRational` (squarefree-decompose `B`, split each factor into its `V`-part / `W`-part, partial-
fraction `R`, classify and dispatch); returns the per-factor reductions `(isV, Bᵢ, eᵢ, Nᵢ, vNumᵢ, Cremᵢ)`.
**No fuel at runtime**; not self-recursive (no `termination_by`). Needs `[CField α] [CFracGcdCoreWf α]` (the
latter for the fuel-free squarefree factorization). -/
def radIntegrateRationalWf [CFracGcdCoreWf α] (ρ R B : CPolyG α) :
    List (Bool × CPolyG α × ℕ × CPolyG α × CPolyG α × CPolyG α) :=
  let g : CPolyG α := cscaleG (CField.div CField.one (cnatCastG 2)) (cderivG ρ)   -- `½·ρ'` (n = 2)
  let factored : List (CPolyG α × ℕ) :=
    (cSqfreeYunFFGWf B).zipIdx.filterMap (fun (Bi, i) =>
      if cdegG Bi = 0 then none else some (Bi, i + 1))
  let split : List (Bool × CPolyG α × ℕ) :=
    factored.flatMap (fun (Bi, e) =>
      let Wi := cmonicG (cgcdWf Bi ρ).1
      let Vi := cdivWf Bi Wi
      (if cdegG Vi = 0 then [] else [(true, Vi, e)]) ++
      (if cdegG Wi = 0 then [] else [(false, Wi, e)]))
  let primePowers : List (CPolyG α) := split.map (fun (_, fi, e) => cpowG fi e)
  let nums : List (CPolyG α) := radPartialFractionCoprime R primePowers
  (split.zip nums).map (fun ((isV, fi, e), Ni) =>
    if isV then
      let (Crem, vNum) := radReduceCase1IterateWf cderivG fi (cderivG fi) ρ g e e Ni []
      (true, fi, e, Ni, vNum, Crem)
    else
      let (Crem, vNum) := radReduceCase2IterateWf fi (cdivWf ρ fi) ρ e e Ni []
      (false, fi, e, Ni, vNum, Crem))

end CPolyG

/-! ### The fuel-free unified algebraic integrator `cIntegrateAlgebraicWf` (radical top-level)

`cIntegrateAlgebraic` is one flat composition over `radIntegrateRational` (rational part) + `radLogArgSolve`
(log part). `radLogArgSolve` is itself **non-recursive** (a matrix build `radLogMatrix`, a rational kernel
`ratKernelVector`, and a `List.foldl` — no fuel of its own), so the only fuel-free substitution one layer up
is `radIntegrateRationalWf` for `radIntegrateRational`. -/

/-- **The fuel-free unified algebraic integrator** `cIntegrateAlgebraicWf ρ R B residual c D degBound` over
`y² = ρ`: the fuel-free companion of `cIntegrateAlgebraic`, producing the full `∫ R/(B·y) dx = v + c·log u`
(principal case). Identical flat structure — computes the rational part `v` by the fuel-free multi-case
dispatch (`radIntegrateRationalWf` + `radAssembleRatPart`), then SOLVES the log argument on `residual`
(`radLogArgSolve ρ residual D degBound`, itself non-recursive / fuel-free); on `none` returns just the
rational part. **No fuel at runtime**; not self-recursive. Needs `[CFracGcdCoreWf (QFunNZG ℚ)]` (via the
tower's base `[CFracGcdCoreWf ℚ]`) for `radIntegrateRationalWf`'s squarefree factorization. -/
def cIntegrateAlgebraicWf (ρ : QFunNZG ℚ) (R B : CPolyG ℚ)
    (residual : RadElem (QFunNZG ℚ)) (c : QFunNZG ℚ) (D : CPolyG ℚ) (degBound : ℕ) :
    AlgIntegralResult :=
  let ρpoly : CPolyG ℚ := qxNum ρ
  let runs := CPolyG.radIntegrateRationalWf ρpoly R B
  let v := radAssembleRatPart ρ runs
  match radLogArgSolve ρ residual D degBound with
  | none => ⟨v, []⟩
  | some N =>
    let Dq : QFunNZG ℚ := qxOfNum D
    let u : RadElem (QFunNZG ℚ) := N.map (fun z => CField.div z Dq)
    ⟨v, [(c, u)]⟩

/-! ## Part 7 — ★ top-level `native_decide` validations: the radical integrator is fuel-free end-to-end

The fuel-free top-level is checked directly with the radical derivation, so the `D(∫f) = f` validation holds
of the **fuel-free** output. The three round-trips from `ComputableRadicalIntegrateFull` are replayed through
`cIntegrateAlgebraicWf`: rational-only, log-only, and the combined rational + log case. -/

open RadElem CPolyG

/-! ### Rational-only round-trip -/

/-- **The fuel-free recovered rational-only result** for `∫ 1/((x−1)²√(x²+1))`: the rational part is
reconstructed by `radIntegrateRationalWf`, and the non-principal residual gives an empty log list. -/
def rtRatRecoveredWf : AlgIntegralResult :=
  cIntegrateAlgebraicWf rtRatRho rtRatR rtRatB rtRatNonPrincipalResidual CField.one [0, 0, 1] 1

/-- **★ The FUEL-FREE radical integrator integrates `∫ 1/((x−1)²√(x²+1))`: `algDeriv F' = integrand`**
(`native_decide`). The fuel-free `cIntegrateAlgebraicWf` reconstructs the rational antiderivative `F'` from
`(R, B) = (1, (x−1)²)` (the multi-case dispatch run fuel-free), with an empty log list (the non-principal
residual ⇒ `radLogArgSolve = none`); the **actual** algebraic derivation `algDeriv` of `F'` equals the
integrand `radDeriv rtRatV`. The radical integrator now integrates end-to-end **with no `ℕ`-fuel** — the
rational part reconstructed by the fuel-free dispatch, validated by the real radical derivation. Checked by
`radIsZero` over `ℚ(x)`. -/
theorem cIntegrateAlgebraicWf_rtRat_integrates :
    radIsZero (radSub (algDeriv rtRatRho rtRatRecoveredWf) rtRatIntegrand) = true := by native_decide

/-- **The fuel-free rational-only result has nonzero rational part and empty log list** (`native_decide`):
the structural signature of a pure rational integral `∫ = v`. -/
theorem cIntegrateAlgebraicWf_rtRat_shape :
    (radIsZero rtRatRecoveredWf.ratPart, rtRatRecoveredWf.logTerms.length) = (false, 0) := by
  native_decide

/-! ### Log-only round-trip -/

/-- **The fuel-free recovered log-only result** for `∫ dx/(x√(x²+1))`: empty rational part and one computed
principal log term. -/
def rtLogRecoveredWf : AlgIntegralResult :=
  cIntegrateAlgebraicWf rtLogRho [1] [1] rtLogIntegrand CField.one rtLogD 0

/-- **★ The FUEL-FREE radical integrator integrates the log-only example** `∫ dx/(x√(x²+1))`
(`native_decide`): the Wf driver computes the same principal log derivative, with no top-level fuel. -/
theorem cIntegrateAlgebraicWf_rtLog_integrates :
    radIsZero (radSub (algDeriv rtLogRho rtLogRecoveredWf) rtLogIntegrand) = true := by native_decide

/-- **The fuel-free log-only result has empty rational part and one log term** (`native_decide`): the
structural signature of a pure logarithmic integral. -/
theorem cIntegrateAlgebraicWf_rtLog_shape :
    (radIsZero rtLogRecoveredWf.ratPart, rtLogRecoveredWf.logTerms.length) = (true, 1) := by
  native_decide

/-! ### Combined rational + log round-trip -/

/-- **The fuel-free recovered combined result** for `F = v + log(x + y)`: both the rational part and the log
argument are reconstructed by `cIntegrateAlgebraicWf`. -/
def rtCombRecoveredWf : AlgIntegralResult :=
  cIntegrateAlgebraicWf rtCombRho rtCombR rtCombB rtCombLogResidual CField.one [1] 1

/-- **★★ The FUEL-FREE radical integrator integrates the combined rational + log example**
(`native_decide`): `algDeriv` of the Wf output equals the mixed integrand `radDeriv v + radLogDeriv u`. -/
theorem cIntegrateAlgebraicWf_rtComb_integrates :
    radIsZero (radSub (algDeriv rtCombRho rtCombRecoveredWf) rtCombIntegrand) = true := by native_decide

/-- **The fuel-free combined result has nonzero rational part and one log term** (`native_decide`): the
structural signature of a genuine combined algebraic integral `∫ = v + c·log u`. -/
theorem cIntegrateAlgebraicWf_rtComb_shape :
    (radIsZero rtCombRecoveredWf.ratPart, rtCombRecoveredWf.logTerms.length) = (false, 1) := by
  native_decide

/-! ## ★ STRETCH note — the LOG part and the `afIntegrateAlgebraicWf` general-curve layer

* **The log part is already fuel-free.** `radLogArgSolve` (and hence the `c·log u` half) is **non-recursive**
  — it builds the linear system `radLogMatrix`, solves it with the rational kernel `ratKernelVector`
  (Gauss / `ratRref`, non-recursive over the row list), and assembles `a₀, a₁` by a `List.foldl`. It carries
  no `ℕ`-fuel and needs no `…Wf` companion: `cIntegrateAlgebraicWf` shares it verbatim. So the FULL radical
  integral `v + c·log u` is fuel-free.
* **General curve layer — `afIntegrateAlgebraicWf` (`ComputableGeneralWellFounded`).** The general
  non-radical algebraic curve path is fuel-free through the same leaf-substitution strategy: rational and log
  parts are finite integral-basis linear solves, and the resultants bottom at the fuel-free `cresultantWf`. -/

/-! ### `#print axioms` — the fuel-free algebraic-integration validations

The well-founded `…Wf` defs are TOTAL via well-founded recursion (the measure `k` / `cdegG C`), **not** via
fuel. The remaining validation theorems are `native_decide` checks over the Wf outputs, **no `sorryAx`**. -/

-- ★ The fuel-free iterates reproduce the `radDeriv`-validated runs (native_decide):
#print axioms radIntegrateCase1Wf_eq_sqrtxRun
#print axioms sqrtxDriverWf_integrates
#print axioms radIntegrateCase1Wf_eq_cubeRun
#print axioms cubeDriverWf_integrates
#print axioms radIntegrateCase2Wf_eq_c2itRun
#print axioms radIntegrateCase3Wf_eq_c3itRun

-- ★★ The FUEL-FREE radical integrator integrates end-to-end (`D(∫f) = f`, native_decide):
#print axioms cIntegrateAlgebraicWf_rtRat_integrates
#print axioms cIntegrateAlgebraicWf_rtRat_shape
#print axioms cIntegrateAlgebraicWf_rtLog_integrates
#print axioms cIntegrateAlgebraicWf_rtLog_shape
#print axioms cIntegrateAlgebraicWf_rtComb_integrates
#print axioms cIntegrateAlgebraicWf_rtComb_shape

end DeepWiki.SymbolicIntegration
