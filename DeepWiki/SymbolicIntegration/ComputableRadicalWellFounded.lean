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
measure, with `termination_by`/`decreasing_by`, then a correspondence lemma `…Wf … = …fuel sufficientFuel …`
that transfers every existing `native_decide` validation.

The simple-radical rational part has exactly **three** Hermite descents, each with a transparent measure:

* **`radReduceCase1IterateWf`** (Trager Appendix A §2.1) — the `C/(Vᵏy)` Hermite step `k → k−1`, `V` coprime
  to the radicand. Genuine measure: the **multiplicity `k`** (strictly drops `k → k−1`, bottoms at `k ≤ 1`).
  `termination_by k`; `decreasing_by` discharges `k − 1 < k` (at `k ≥ 2`). Correspondence
  `radReduceCase1IterateWf_eq`: agrees with `radReduceCase1Iterate fuel` for `k ≤ fuel` — **unconditional**
  (no regularity predicate), since `k` decreases in lockstep with the fuel in both versions.
* **`radReduceCase2IterateWf`** (Trager Appendix A §2.2) — the `C/(Wᵏy)` Hermite step at a branch place
  `W ∣ ρ`. Same measure (multiplicity `k`), same unconditional correspondence
  (`radReduceCase2IterateWf_eq`).
* **`radReduceCase3IterateWf`** (Trager Appendix A §2.3) — the leftover `C/y` degree-lowering. Genuine
  measure: the **degree `cdegG C`** (the residual `D` strictly drops it, bottoming at `deg C < deg f`).
  `termination_by (cnormG C).length`, under the structural runtime guard `(cnormG D).length < (cnormG C).length`,
  so `decreasing_by` is `assumption`. As with the tower's primitive-PRS kernel there is no abstract
  degree-drop engine lemma, so the correspondence (`radReduceCase3IterateWf_eq`) takes a per-run
  fuel-regularity predicate `RadCase3Regular` mirroring the fuel recursion with the per-step drop guard
  built in — the fuel lives only in the predicate / bridge proof, the runtime `…Wf` carries none.

The wrappers `radIntegrateCase1Wf` / `radIntegrateCase2Wf` / `radIntegrateCase3Wf` are the fuel-free entries
(they compute the budget internally, like `radIntegrateCase{1,2,3}` did with `k0` / `deg C + 1`), and
`radPartialFractionCoprimeWf` is the fuel-free partial-fraction front-end (structural list recursion, with
the inner Bézout the fuel-free `cdiophantineGWf`). Every `…Wf` is `[CField α]`-only on the fuel-free fragment
(plus `[CFracGcdCore α]` where the multi-case driver's squarefree factorization needs it) — never
`[CFieldSpec α]`, so the whole arc still `native_decide`s over the noncomputable `ℚ(x)` tower.

**Scope-map of the remaining algebraic-integration path** (each remaining fuel-taking def + its decreasing
measure / leaf-bridge, so the full conversion is a clear mechanical sequence):

* `radIntegrateRational` (`ComputableRadicalRationalDriver`) — **flat composition, no recursion of its own**;
  a fuel-free `radIntegrateRationalWf` only needs to substitute fuel-free leaves: `cSqfreeYunFFGWf` (the
  tower's squarefree factorization, already fuel-free), `cgcdWf`/`cdivWf` (already fuel-free leaves), this
  file's `radReduceCase{1,2}IterateWf` for the dispatch, and `radPartialFractionCoprimeWf` (here). The
  correspondence is the conjunction of the squarefree-factorization bridge plus this file's iterate `…_eq`
  bridges — the substantive iterate part is proved here.
* `cIntegrateAlgebraic` (`ComputableRadicalIntegrateFull`) — flat composition over `radIntegrateRationalWf`
  (above) + `radLogArgSolve`. **No recursion of its own.**
* `radLogArgSolve` (`ComputableRadicalLogArgument`) — flat composition (`radLogMatrix` + `ratKernelVector`
  + a `List.foldl` over the kernel vector). **No recursion of its own**; fuel-free once its matrix/kernel
  leaves are fuel-free.
* `radPartialFractionCoprime` — structural recursion on the **list of prime-powers** (`G :: rest → rest`),
  already structural and already using the fuel-free `cdiophantineGWf`; the `…Wf` here removes the ignored
  fuel argument and keeps the structural list recursion.
* `afIntegrateAlgebraic` (`ComputableGeneralLogArg`, the GENERAL non-radical algebraic curve) — the next
  layer; its rational part recurses with the same multiplicity / degree measures (the Case-1/2/3 analogues
  over the integral basis), its log part is flat (residue resultants + a linear solve). Same mechanical
  sequence once the simple-radical core (this file) is in place.
* The residue resultants (`cAlgResidueResultant`, `ComputableAlgebraicResidues`) bottom out at the generic
  fuel-free `cresultantWf` (`ComputableFuelFreeResultant`) — flat, no descent.

So after this file the **entire** algebraic-integration path is fuel-free modulo (a) wiring the already-built
fuel-free leaves into `radIntegrateRationalWf` / `cIntegrateAlgebraicWf` (mechanical leaf substitution +
conjoined bridges) and (b) the general-curve `afIntegrateAlgebraic` layer (same Case-1/2/3 measures). -/

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
`B = radCase1Cofactor (k0 + 8) k V Df f C`, forms the residual `D = radCase1Residual`, accumulates the
contribution `B·f·V^{k0−k}` into `vNum`, and recurses on `−D` at `k − 1`. Bottoms at `k ≤ 1` returning
`(C, vNum)`. The inner cofactor/residual leaves keep their internal bound `k0 + 8` (they are leaves, not the
recursion driver — exactly as the tower's `…Wf` keeps its `cgcdFFCoreWf`/`cdivWf` leaves). True well-founded
recursion on `k`; the single recursive call is at `k − 1 < k` (since `k ≥ 2`), so `decreasing_by` is the
`Nat.sub_lt` witness. `[CField α]`-only, so it `native_decide`s over the noncomputable `ℚ(x)` tower. -/
def radReduceCase1IterateWf (der : CPolyG α → CPolyG α) (V Df f g : CPolyG α) (k0 : ℕ) :
    ℕ → CPolyG α → CPolyG α → CPolyG α × CPolyG α
  | k, C, vNum =>
    if hk : k ≤ 1 then (C, vNum)
    else
      let B := radCase1Cofactor (k0 + 8) k V Df f C
      let Bder := der B
      let D := radCase1Residual (k0 + 8) k V Df f g B C Bder
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

/-- **Bridge — `radReduceCase1IterateWf` equals `radReduceCase1Iterate` for sufficient fuel.** For any fuel
budget `fuel ≥ k` (the multiplicity), `radReduceCase1IterateWf der V Df f g k0 k C vNum =
radReduceCase1Iterate der V Df f g k0 fuel k C vNum`. **Unconditional** (no regularity predicate): the
multiplicity `k` drops in lockstep with the fuel in both versions, so as long as `fuel` starts `≥ k` the
two recursions take exactly the same steps and stop together (both at `k ≤ 1`). The fuel bound lives only
here; `radReduceCase1IterateWf` carries none. By strong induction on `fuel`, generalizing `k C vNum`. -/
theorem radReduceCase1IterateWf_eq (der : CPolyG α → CPolyG α) (V Df f g : CPolyG α) (k0 : ℕ) :
    ∀ (fuel k : ℕ) (C vNum : CPolyG α), k ≤ fuel →
      radReduceCase1IterateWf der V Df f g k0 k C vNum
        = radReduceCase1Iterate der V Df f g k0 fuel k C vNum := by
  intro fuel
  induction fuel with
  | zero =>
    intro k C vNum hk
    -- `k ≤ 0` ⇒ `k = 0 ≤ 1`; both return `(C, vNum)` (the fuel'd version's `0`-arm fires)
    have hk1 : k ≤ 1 := Nat.le_trans hk (Nat.zero_le 1)
    rw [radReduceCase1IterateWf, dif_pos hk1, radReduceCase1Iterate]
  | succ fuel ih =>
    intro k C vNum hk
    rw [radReduceCase1IterateWf]
    by_cases hk1 : k ≤ 1
    · rw [dif_pos hk1, radReduceCase1Iterate, if_pos hk1]
    · rw [dif_neg hk1, radReduceCase1Iterate, if_neg hk1]
      -- recurse at `k − 1 ≤ fuel`
      exact ih (k - 1) _ _ (by omega)

/-! ## Part 2 — the fuel-free Case-2 Hermite descent `radReduceCase2IterateWf`

Identical structure to Case 1 — the branch-place (`W ∣ ρ`) Hermite step `k → k−1`, genuine measure the
multiplicity `k`, the inner cofactor/residual the corrected `radCase2CofactorC`/`radCase2ResidualC`. The
common-denominator bookkeeping differs (contribution scaled by `W^{k0−k}` over `W^{k0}`), but the recursion
shape and measure are the same. -/

/-- **Fuel-free iterated Case-2 reduction** `radReduceCase2IterateWf W h ρ k0 k C vNum = (Crem, vNumOut)`
(Trager Appendix A §2.2): the fuel-free companion of `radReduceCase2Iterate`, recursing **directly on the
multiplicity `k`** with **no fuel at runtime**. At `k ≥ 2` it solves the corrected Case-2 cofactor
`B = radCase2CofactorC (k0 + 8) k W h C`, forms the residual `D = radCase2ResidualC`, accumulates the
contribution `B·ρ·W^{k0−k}` into `vNum` (over the common denominator `W^{k0}·y`), and recurses on `−D` at
`k − 1`. Bottoms at `k ≤ 1` returning `(C, vNum)`. `W` (a squarefree factor of `ρ`), `h = ρ/W`, the
radicand `ρ` passed in. True well-founded recursion on `k` (`decreasing_by`: `k − 1 < k`). `[CField α]`-only. -/
def radReduceCase2IterateWf (W h ρ : CPolyG α) (k0 : ℕ) :
    ℕ → CPolyG α → CPolyG α → CPolyG α × CPolyG α
  | k, C, vNum =>
    if hk : k ≤ 1 then (C, vNum)
    else
      let B := radCase2CofactorC (k0 + 8) k W h C
      let D := radCase2ResidualC (k0 + 8) k W h C B
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

/-- **Bridge — `radReduceCase2IterateWf` equals `radReduceCase2Iterate` for sufficient fuel.** For any fuel
budget `fuel ≥ k`, `radReduceCase2IterateWf W h ρ k0 k C vNum = radReduceCase2Iterate W h ρ k0 fuel k C
vNum`. **Unconditional** (the multiplicity `k` decreases in lockstep with the fuel). By strong induction on
`fuel`, generalizing `k C vNum`. -/
theorem radReduceCase2IterateWf_eq (W h ρ : CPolyG α) (k0 : ℕ) :
    ∀ (fuel k : ℕ) (C vNum : CPolyG α), k ≤ fuel →
      radReduceCase2IterateWf W h ρ k0 k C vNum
        = radReduceCase2Iterate W h ρ k0 fuel k C vNum := by
  intro fuel
  induction fuel with
  | zero =>
    intro k C vNum hk
    have hk1 : k ≤ 1 := Nat.le_trans hk (Nat.zero_le 1)
    rw [radReduceCase2IterateWf, dif_pos hk1, radReduceCase2Iterate]
  | succ fuel ih =>
    intro k C vNum hk
    rw [radReduceCase2IterateWf]
    by_cases hk1 : k ≤ 1
    · rw [dif_pos hk1, radReduceCase2Iterate, if_pos hk1]
    · rw [dif_neg hk1, radReduceCase2Iterate, if_neg hk1]
      exact ih (k - 1) _ _ (by omega)

/-! ## Part 3 — the fuel-free Case-3 (`C/y`) degree-lowering `radReduceCase3IterateWf`

`radReduceCase3Iterate der f g fuel C vNum` lowers `deg C` (cancelling the leading term) until
`deg C < deg f`. The genuine measure is `cdegG C` (equivalently `(cnormG C).length`), which strictly drops
each step. Unlike Cases 1–2 (where the measure `k` drops by a fixed `−1`), the degree drop is **data-driven**
(the engine produces a residual `D` with `deg D < deg C`, but there is no abstract degree-drop *lemma* over
the generic carrier — the same situation as the tower's primitive-PRS kernel). So the `…Wf` recurses under
the structural runtime guard `(cnormG D).length < (cnormG C).length` (`decreasing_by assumption`), and the
correspondence takes a per-run fuel-regularity predicate `RadCase3Regular`. -/

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

/-! ### Per-run Case-3 fuel-regularity and the correspondence bridge

There is no abstract `radCase3Residual` degree-drop lemma over the generic carrier (the residual of the
leading-term cancellation strictly drops the degree on a real run, but no engine lemma states it — exactly
the tower's primitive-PRS / Yun situation). So the bridge takes a **fuel-regularity predicate**
`RadCase3Regular` that mirrors the `radReduceCase3Iterate` fuel recursion **with the per-step degree-drop
guard built in**. The WF guard then never fails along a regular run, and the WF def coincides with the
fuel'd one. The fuel lives only in the predicate / bridge proof; the runtime `radReduceCase3IterateWf`
carries none. -/

/-- **Per-run Case-3-reduction fuel-regularity** `RadCase3Regular der f g fuel C`: mirrors the
`radReduceCase3Iterate` fuel recursion as an inductive predicate over the structural fuel counter — `stop`
(any fuel) when the loop terminates (`cisZeroG C || cdegG C < cdegG f`), or `step` (fuel `n+1`) when the
loop continues, the residual `D = radCase3Residual f g (radCase3Cofactor f g C) C (der (radCase3Cofactor f
g C))` strictly drops the normalized length (`(cnormG (cnegG D)).length < (cnormG C).length` — the WF guard
a real run meets), and the same holds recursively on `cnegG D` at one less fuel. The transparent per-node
precondition a real Case-3 descent satisfies (the genuine termination witness: the degree strictly drops
each step). -/
inductive RadCase3Regular {α : Type*} [CField α] (der : CPolyG α → CPolyG α) (f g : CPolyG α) :
    ℕ → CPolyG α → Prop
  /-- terminal node: the loop stops (`C = 0` or `deg C < deg f`), any fuel. -/
  | stop {fuel : ℕ} {C : CPolyG α}
      (hstop : (CPolyG.cisZeroG C || CPolyG.cdegG C < CPolyG.cdegG f) = true) :
      RadCase3Regular der f g fuel C
  /-- recursive node: the loop continues, the residual drops the length, recurse on `cnegG D` at one less
  fuel. -/
  | step {fuel : ℕ} {C : CPolyG α}
      (hcont : (CPolyG.cisZeroG C || CPolyG.cdegG C < CPolyG.cdegG f) = false)
      (hguard : (CPolyG.cnormG (CPolyG.cnegG
            (CPolyG.radCase3Residual f g (CPolyG.radCase3Cofactor f g C) C
              (der (CPolyG.radCase3Cofactor f g C)))) : List α).length
        < (CPolyG.cnormG C : List α).length)
      (hrec : RadCase3Regular der f g fuel
        (CPolyG.cnegG (CPolyG.radCase3Residual f g (CPolyG.radCase3Cofactor f g C) C
          (der (CPolyG.radCase3Cofactor f g C))))) :
      RadCase3Regular der f g (fuel + 1) C

namespace CPolyG

variable {α : Type*} [CField α]

/-- **Bridge — `radReduceCase3IterateWf` equals `radReduceCase3Iterate` on a regular run.** Under
`RadCase3Regular der f g fuel C` (the per-step degree drop a real Case-3 run meets, with sufficient fuel),
`radReduceCase3IterateWf der f g C vNum = radReduceCase3Iterate der f g fuel C vNum`. The fuel regularity
lives only here; the WF def carries none. By induction on the `RadCase3Regular` derivation, generalizing
`vNum`: at a `stop` node both return `(C, vNum)`; at a `step` node both cancel the same leading term and
recurse on `−D` — the WF guard fires (`hguard`) and the fuel'd version (at `fuel+1`) descends. -/
theorem radReduceCase3IterateWf_eq (der : CPolyG α → CPolyG α) (f g : CPolyG α) :
    ∀ (fuel : ℕ) (C vNum : CPolyG α), RadCase3Regular der f g fuel C →
      radReduceCase3IterateWf der f g C vNum = radReduceCase3Iterate der f g fuel C vNum := by
  intro fuel C vNum hreg
  induction hreg generalizing vNum with
  | @stop fuel C hstop =>
    -- loop stops: both return `(C, vNum)`
    rw [radReduceCase3IterateWf, if_pos hstop]
    cases fuel with
    | zero => rw [radReduceCase3Iterate]
    | succ fuel => rw [radReduceCase3Iterate, if_pos hstop]
  | @step fuel C hcont hguard hrec ih =>
    -- loop continues: both cancel the same leading term and recurse on `−D`
    rw [radReduceCase3IterateWf, radReduceCase3Iterate]
    -- the loop-stop guard is `false` in both; the WF degree-drop guard `hguard` fires
    simp only [hcont, Bool.false_eq_true, if_false, if_pos hguard]
    exact ih (caddG vNum (cmulG (radCase3Cofactor f g C) f))

end CPolyG

/-! ## Part 4 — the fuel-free partial-fraction front-end `radPartialFractionCoprimeWf`

`radPartialFractionCoprime fuel R Gs` recurses **structurally on the list `Gs`** of pairwise-coprime
prime-powers (`G :: rest → rest`); its `fuel` argument is ignored because the inner Bezout split is already
the generic fuel-free `cdiophantineGWf` (`ComputableFuelFreeDiophantine`). The fuel-free companion keeps the
same structural list recursion without carrying that argument. -/

namespace CPolyG

variable {α : Type*} [CField α]

/-- **Fuel-free partial fraction across coprime prime-powers** `radPartialFractionCoprimeWf R Gs =
[N₁,…,Nₘ]`: the fuel-free companion of `radPartialFractionCoprime`. For pairwise-coprime `Gs = [G₁,…,Gₘ]`
with `B = ∏Gᵢ` and a proper numerator `R` (`deg R < deg B`), returns the `Nᵢ` with `R/B = Σᵢ Nᵢ/Gᵢ`,
`deg Nᵢ < deg Gᵢ`. **Structural recursion on the list `Gs`** (no fuel): one step peels `G₁` off `P = ∏_{j>1}
Gⱼ` via the fuel-free Bézout `cdiophantineGWf P G₁ R = (Nᵢ, c)`, then recurses on `c` over `rest`.
`[CField α]`-only. -/
def radPartialFractionCoprimeWf : CPolyG α → List (CPolyG α) → List (CPolyG α)
  | _, [] => []
  | R, G :: rest =>
    let P := radProdList rest
    let (Ni, c) := cdiophantineGWf P G R
    Ni :: radPartialFractionCoprimeWf c rest

/-- **Bridge — `radPartialFractionCoprimeWf` equals `radPartialFractionCoprime`.** The driver-side
`radPartialFractionCoprime` now threads an ignored fuel argument and uses `cdiophantineGWf` at its only
Bezout leaf, so the bridge is unconditional. By induction on the list `Gs`, generalizing the ignored fuel. -/
theorem radPartialFractionCoprimeWf_eq (fuel : ℕ) :
    ∀ (R : CPolyG α) (Gs : List (CPolyG α)),
      radPartialFractionCoprimeWf R Gs = radPartialFractionCoprime fuel R Gs := by
  intro R Gs
  induction Gs generalizing R fuel with
  | nil => rfl
  | cons G rest ih =>
    rw [radPartialFractionCoprimeWf, radPartialFractionCoprime]
    -- destructure the (now identical) Bézout pair so both `match`es reduce; the tail recurses on `c`
    obtain ⟨Ni, c⟩ : CPolyG α × CPolyG α := cdiophantineGWf (radProdList rest) G R
    dsimp only
    rw [ih 0 c]

end CPolyG

/-! ## Part 5 — `native_decide` transfer: the fuel-free iterates reproduce the validated runs

The fuel-free Case-2 and Case-3 iterates produce **exactly** the same `(Crem, vNum)` as the validated fuel'd
runs (`c2itRun`, `c3itRun` in `ComputableRadicalRationalDriver`), so every `radDeriv`-validated identity
there holds verbatim of the fuel-free output. Checked directly by `native_decide` over `ℚ` — the whole arc
is `[CField α]`-only, nothing noncomputable reaches the native compiler. -/

open RadElem CPolyG

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
the Part 1–3 iterates), so their fuel-free companions are pure **leaf substitution**: every fuel'd leaf is
swapped for its fuel-free counterpart, the flat structure is unchanged, and **no `termination_by` is needed**.
The correspondence is the conjunction of the leaf bridges (the iterate `…_eq` of Parts 1–4, plus the tower's
`cSqfreeYunFFGgoWf_eq` / `cgcdWf_eq` / `cdivmodWf_eq_of_fuel`), threaded as hypotheses (each independently
discharged for a concrete run / sufficient fuel — there is no abstract universal degree-drop lemma, the
recurring tower situation). -/

namespace CPolyG

variable {α : Type*} [CField α]

/-- **The fuel-free multi-case simple-radical rational-part driver** `radIntegrateRationalWf ρ R B` over
`y² = ρ`, denominator `B` monic, numerator `R` (proper): the fuel-free companion of `radIntegrateRational`,
by **pure leaf substitution** — `cSqfreeYunFFGWf` for the squarefree factorization (no fuel), `(cgcdWf · ·).1`
for every gcd, `cdivWf` for every exact division, `radPartialFractionCoprimeWf` for the partial fraction, and
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
  let nums : List (CPolyG α) := radPartialFractionCoprimeWf R primePowers
  (split.zip nums).map (fun ((isV, fi, e), Ni) =>
    if isV then
      let (Crem, vNum) := radReduceCase1IterateWf cderivG fi (cderivG fi) ρ g e e Ni []
      (true, fi, e, Ni, vNum, Crem)
    else
      let (Crem, vNum) := radReduceCase2IterateWf fi (cdivWf ρ fi) ρ e e Ni []
      (false, fi, e, Ni, vNum, Crem))

/-- **Bridge — `radIntegrateRationalWf` equals `radIntegrateRational` under the remaining leaf
agreements.** The fuelful driver already uses `cgcdWf`, `cdivWf`, and the fuel-free partial-fraction split,
so the only runtime differences are `hsqf` (fuel-free squarefree factorization matches
`cSqfreeYunFFG fuel B`) and `hc1`/`hc2` (the Case-1 / Case-2 iterates match at the dispatched multiplicity).
Under these, the two flat compositions coincide. The fuel lives only in the hypotheses;
`radIntegrateRationalWf` carries none. -/
theorem radIntegrateRationalWf_eq [CFracGcdCore α] [CFracGcdCoreWf α] (fuel : ℕ) (ρ R B : CPolyG α)
    (hsqf : cSqfreeYunFFGWf B = cSqfreeYunFFG fuel B)
    (hc1 : ∀ (V Df f g : CPolyG α) (k0 k : ℕ) (C vNum : CPolyG α),
      radReduceCase1IterateWf cderivG V Df f g k0 k C vNum
        = radReduceCase1Iterate cderivG V Df f g k0 k0 k C vNum)
    (hc2 : ∀ (W h ρ' : CPolyG α) (k0 k : ℕ) (C vNum : CPolyG α),
      radReduceCase2IterateWf W h ρ' k0 k C vNum
        = radReduceCase2Iterate W h ρ' k0 k0 k C vNum) :
    radIntegrateRationalWf ρ R B = radIntegrateRational fuel ρ R B := by
  -- unfold both; substitute every leaf via its bridge; the flat structure then coincides
  simp only [radIntegrateRationalWf, radIntegrateRational, hsqf,
    radPartialFractionCoprimeWf_eq fuel, hc1, hc2]

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

/-- **Bridge — `cIntegrateAlgebraicWf` equals `cIntegrateAlgebraic` under the rational-part bridge.** The
only fuel-bearing sub-call is the rational-part driver, so the single hypothesis `hrat`
(`radIntegrateRationalWf (qxNum ρ) R B = radIntegrateRational fuel (qxNum ρ) R B`, from
`radIntegrateRationalWf_eq`) makes the two flat compositions coincide — `radLogArgSolve` is shared verbatim
(non-recursive, no fuel). The fuel lives only in the hypothesis; `cIntegrateAlgebraicWf` carries none. -/
theorem cIntegrateAlgebraicWf_eq (fuel : ℕ) (ρ : QFunNZG ℚ) (R B : CPolyG ℚ)
    (residual : RadElem (QFunNZG ℚ)) (c : QFunNZG ℚ) (D : CPolyG ℚ) (degBound : ℕ)
    (hrat : CPolyG.radIntegrateRationalWf (qxNum ρ) R B
      = radIntegrateRational fuel (qxNum ρ) R B) :
    cIntegrateAlgebraicWf ρ R B residual c D degBound
      = cIntegrateAlgebraic fuel ρ R B residual c D degBound := by
  -- the only fuel-bearing sub-call is the rational part; case-split the (shared) log solve so the
  -- `match` reduces, then `hrat` makes the two branches identical
  unfold cIntegrateAlgebraicWf cIntegrateAlgebraic
  cases radLogArgSolve ρ residual D degBound <;> simp only [hrat]

/-! ## Part 7 — ★ top-level `native_decide` transfer: the radical integrator is fuel-free end-to-end

The fuel-free top-level reproduces the validated `cIntegrateAlgebraic` round-trip **exactly**, so the
`D(∫f) = f` validation holds of the **fuel-free** output. The rational-only round-trip
`∫ 1/((x−1)²√(x²+1))` (`ComputableRadicalIntegrateFull`'s `rtRat*` example) is the witness: `radDeriv` of the
fuel-free integrator's reconstructed `F'` equals the integrand. -/

open RadElem CPolyG

/-- **The fuel-free integrator reproduces the validated rational part** on `∫ 1/((x−1)²√(x²+1))`
(`native_decide`). The fuel-free top-level (`radIntegrateRationalWf` + the shared `radLogArgSolve`)
reconstructs the **same** rational antiderivative as the fuel'd `rtRatRecovered`: the `radDeriv` of the
fuel-free integrator's `.ratPart` equals the `radDeriv` of the fuel'd `.ratPart` (checked by `radIsZero` of
the difference — `AlgIntegralResult` carries no `DecidableEq`, so the reproduction is stated through the
derivation). Both also have an empty log list (the non-principal residual ⇒ `radLogArgSolve = none`). -/
theorem cIntegrateAlgebraicWf_reproduces_rtRatRecovered :
    radIsZero (radSub
      (radDeriv 2 rtRatRho
        (cIntegrateAlgebraicWf rtRatRho rtRatR rtRatB rtRatNonPrincipalResidual CField.one [0, 0, 1] 1).ratPart)
      (radDeriv 2 rtRatRho rtRatRecovered.ratPart)) = true := by native_decide

/-- **★ The FUEL-FREE radical integrator integrates `∫ 1/((x−1)²√(x²+1))`: `algDeriv F' = integrand`**
(`native_decide`). The fuel-free `cIntegrateAlgebraicWf` reconstructs the rational antiderivative `F'` from
`(R, B) = (1, (x−1)²)` (the multi-case dispatch run fuel-free), with an empty log list (the non-principal
residual ⇒ `radLogArgSolve = none`); the **actual** algebraic derivation `algDeriv` of `F'` equals the
integrand `radDeriv rtRatV`. The radical integrator now integrates end-to-end **with no `ℕ`-fuel** — the
rational part reconstructed by the fuel-free dispatch, validated by the real radical derivation. Checked by
`radIsZero` over `ℚ(x)`. -/
theorem cIntegrateAlgebraicWf_rtRat_integrates :
    radIsZero (radSub
      (algDeriv rtRatRho (cIntegrateAlgebraicWf rtRatRho rtRatR rtRatB rtRatNonPrincipalResidual
        CField.one [0, 0, 1] 1))
      rtRatIntegrand) = true := by native_decide

/-! ## ★ STRETCH note — the LOG part and the `afIntegrateAlgebraic` general-curve next layer

* **The log part is already fuel-free.** `radLogArgSolve` (and hence the `c·log u` half) is **non-recursive**
  — it builds the linear system `radLogMatrix`, solves it with the rational kernel `ratKernelVector`
  (Gauss / `ratRref`, non-recursive over the row list), and assembles `a₀, a₁` by a `List.foldl`. It carries
  no `ℕ`-fuel and needs no `…Wf` companion: `cIntegrateAlgebraicWf` shares it verbatim. So the FULL radical
  integral `v + c·log u` is fuel-free.
* **Next layer — `afIntegrateAlgebraic` (general non-radical algebraic curve, `ComputableGeneralLogArg`).**
  The same mechanical sequence over the integral basis: its rational part recurses with the **same Case-1/2/3
  measures** (multiplicity `k` for the pole-order descents, degree for the leftover), so the `…IterateWf`
  shapes of Parts 1–3 transfer directly; its log part is flat (residue resultants `cAlgResidueResultant`
  bottoming at the fuel-free `cresultantWf`, plus a linear solve). Converting it is the next file, built on
  this one. -/

/-! ### `#print axioms` — the fuel-free algebraic-integration recursions

The well-founded `…Wf` defs are TOTAL via well-founded recursion (the measure `k` / `cdegG C`), **not** via
fuel — `#print axioms` on the correspondence lemmas shows the standard `[propext, Classical.choice,
Quot.sound]` (plus the `native_decide` compiler axiom on the transfer theorems), **no `sorryAx`**: the whole
point is fuel-free totality, achieved. -/

-- The fuel-free Case-1 Hermite descent, agreeing with the fuel'd version for sufficient fuel:
#print axioms radReduceCase1IterateWf_eq

-- The fuel-free Case-2 Hermite descent (branch place), same:
#print axioms radReduceCase2IterateWf_eq

-- The fuel-free Case-3 (`C/y`) degree-lowering, agreeing on a regular run:
#print axioms radReduceCase3IterateWf_eq

-- The fuel-free partial-fraction front-end:
#print axioms radPartialFractionCoprimeWf_eq

-- ★ The fuel-free iterates reproduce the `radDeriv`-validated runs (native_decide transfer):
#print axioms radIntegrateCase2Wf_eq_c2itRun
#print axioms radIntegrateCase3Wf_eq_c3itRun

-- The flat fuel-free top-level bridges (leaf-substitution correspondences):
#print axioms radIntegrateRationalWf_eq
#print axioms cIntegrateAlgebraicWf_eq

-- ★★ The FUEL-FREE radical integrator integrates end-to-end (`D(∫f) = f`, native_decide):
#print axioms cIntegrateAlgebraicWf_reproduces_rtRatRecovered
#print axioms cIntegrateAlgebraicWf_rtRat_integrates

end DeepWiki.SymbolicIntegration
