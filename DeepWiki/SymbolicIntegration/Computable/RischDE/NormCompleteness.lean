import DeepWiki.SymbolicIntegration.Computable.RischDE.Completeness
import DeepWiki.SymbolicIntegration.Computable.Tower.RischDEWellFounded

/-! # §6.2 RDE completeness — the fuel-free normal-denominator step preserves solvability (`hnorm`)

`RischDEInnerCompletenessWf` (`ComputableRischDECompleteness`) decomposes the deep §6 inner-solve
completeness into three converse clauses, `hnorm` / `hbound` / `hsolve`. `hbound` is produced (modulo a
precise cancellation residual) by `ComputableRischDEDegreeBound`; this file pursues `hnorm`.

**What `hnorm` says.** `hnorm` is the SOLVABILITY-PRESERVATION of Bronstein §6.2's `RdeNormalDenominator`,
stated against the fuel-free engine: *if the input RDE has a polynomial solution then the §6.2 reduction
does not return `none`* — `(∃ ynum yden, IsCRischDEGPolySol …) → (cRdeNormalDenominatorGWf …).isSome =
true`.

**The §6.2 transformation, made precise.** `cRdeNormalDenominatorGWf Dt fnum fden gnum gden`
(`ComputableTowerRischDEWellFounded`) splits the denominators into normal parts `dₙ = (cSplitFactorFastGWf
Dt fden).1`, `eₙ = (cSplitFactorFastGWf Dt gden).1`, forms `h = gcd(eₙ, eₙ')/gcd(p, p')`
(`p = gcd(dₙ, eₙ)`), and returns `some (a, b, c, h)` **iff the single guard `cdvdGWf eₙ (dₙ·h·h)`
holds** — otherwise `none`. So the §6.2 step loses a solution **only** through that one divisibility gate,
and `hnorm` is **exactly**:

  a polynomial solution `⟹ cdvdGWf eₙ (dₙ·h·h) = true`   (equivalently `(…).isSome = true`).

**The two-layer structure of `hnorm` (this file's contribution).**

* **The Wf engine layer is fully reachable** and is closed here, axiom-clean (NO `native_decide`/`sorry`):
  - `cRdeNormalDenominatorGWf_isSome_iff` — the §6.2 step's `isSome` is *exactly* its `cdvdGWf` guard
    (`(…).isSome = true ↔ cdvdGWf eₙ (dₙ·h·h) = true`), the precise control-flow reading.
  - `cdvdGWf_of_dvd` — the **converse of `dvd_of_cdvdGWf`**: a *mathematical* divisibility
    `toPolyG eₙ ∣ toPolyG (dₙ·h·h)` (with `eₙ ≠ 0`) forces the engine check `cdvdGWf = true`, with no fuel
    bound.
  - `cRdeNormalDenominatorGWf_isSome_of_dvd` — composing the two: the *mathematical* §6.2 divisibility
    `eₙ ∣ dₙh²` makes the §6.2 step return `some`. This collapses `hnorm` to a single divisibility fact.

* **The mathematical divisibility is the irreducible §6.2 residual** (precisely isolated, NEVER `sorry`).
  That a *polynomial solution forces* `eₙ ∣ dₙh²` is **Bronstein Theorem 6.1.2** — the necessity of the
  normal-denominator divisibility, a valuation-theoretic fact at the normal poles that the engine does not
  self-certify (the soundness arc only ever *reads off* `eₙ ∣ dₙh²` from a successful `cdvdGWf`, never
  *derives* it from a solution). It is bundled as `RdeNormalDivisibilityResidualWf`, and `hnorm` is produced
  modulo it (`hnormWf_of_divisibilityResidualWf`).

So `hnorm` reduces — through a fully proven Wf engine layer — to the single mathematical divisibility
`solution ⟹ eₙ ∣ dₙh²` (Bronstein Thm 6.1.2), which is the precise §6.2 frontier. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG


/-! ## The fuel-free engine layer: `isSome` is exactly the `cdvdGWf` guard

`cRdeNormalDenominatorGWf`'s body is `if cdvdGWf eₙ (dₙ·h·h) then some (…) else none`. Its divisibility
check is the semantic `cdvdGWf`, so the `dvd ⟹ guard ⟹ some` bridge needs no fuel bound. -/

section WfEngineLayer

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CFracGcdCoreWf α]

/-- **The Wf §6.2 normal part `eₙ` of the `g`-denominator**. -/
def rdeNormEnWf (Dt : CPolyG α) (gden : CPolyG α) : CPolyG α :=
  (CPolyG.cSplitFactorFastGWf Dt gden).1

/-- **The Wf §6.2 normal part `dₙ` of the `f`-denominator**. -/
def rdeNormDnWf (Dt : CPolyG α) (fden : CPolyG α) : CPolyG α :=
  (CPolyG.cSplitFactorFastGWf Dt fden).1

/-- **The Wf §6.2 multiplicity factor `h = gcd(eₙ,eₙ')/gcd(p,p')`. -/
def rdeNormHWf (Dt : CPolyG α) (fden gden : CPolyG α) : CPolyG α :=
  CPolyG.cdivWf
    (CFracGcdCoreWf.cgcdFFCoreWf (rdeNormEnWf Dt gden) (CPolyG.cderivG (rdeNormEnWf Dt gden)))
    (CFracGcdCoreWf.cgcdFFCoreWf
      (CFracGcdCoreWf.cgcdFFCoreWf (rdeNormDnWf Dt fden) (rdeNormEnWf Dt gden))
      (CPolyG.cderivG (CFracGcdCoreWf.cgcdFFCoreWf
        (rdeNormDnWf Dt fden) (rdeNormEnWf Dt gden))))

/-- **The Wf §6.2 dividend `dₙ·h²`. -/
def rdeNormDnh2Wf (Dt : CPolyG α) (fden gden : CPolyG α) : CPolyG α :=
  CPolyG.cmulG (CPolyG.cmulG (rdeNormDnWf Dt fden) (rdeNormHWf Dt fden gden))
    (rdeNormHWf Dt fden gden)

omit [CFieldSpec α] in
/-- **The Wf §6.2 step's `isSome` is exactly its `cdvdGWf` guard**. -/
theorem cRdeNormalDenominatorGWf_isSome_iff (Dt : CPolyG α) (fnum fden gnum gden : CPolyG α) :
    (CPolyG.cRdeNormalDenominatorGWf Dt fnum fden gnum gden).isSome = true ↔
      CPolyG.cdvdGWf (rdeNormEnWf Dt gden) (rdeNormDnh2Wf Dt fden gden) = true := by
  rw [CPolyG.cRdeNormalDenominatorGWf]
  simp only [rdeNormDnh2Wf, rdeNormHWf, rdeNormDnWf, rdeNormEnWf]
  split <;> simp_all

omit [CDiffField α] [CFracGcdCoreWf α] in
/-- **The converse of `dvd_of_cdvdGWf`: mathematical divisibility forces the Wf engine check**. -/
theorem cdvdGWf_of_dvd (q p : CPolyG α) (hq0 : CPolyG.cnormG q ≠ [])
    (hdvd : toPolyG q ∣ toPolyG p) :
    CPolyG.cdvdGWf q p = true := by
  by_cases h : CPolyG.cdvdGWf q p = true
  · exact h
  · have hfalse : CPolyG.cdvdGWf q p = false := Bool.eq_false_iff.mpr h
    exact False.elim ((CPolyG.not_dvd_of_cdvdGWf_false q p hq0 hfalse) hdvd)

/-- **The Wf §6.2 step returns `some` from the mathematical §6.2 divisibility**. -/
theorem cRdeNormalDenominatorGWf_isSome_of_dvd (Dt : CPolyG α)
    (fnum fden gnum gden : CPolyG α)
    (hen0 : CPolyG.cnormG (rdeNormEnWf Dt gden) ≠ [])
    (hdvd : toPolyG (rdeNormEnWf Dt gden) ∣ toPolyG (rdeNormDnh2Wf Dt fden gden)) :
    (CPolyG.cRdeNormalDenominatorGWf Dt fnum fden gnum gden).isSome = true :=
  (cRdeNormalDenominatorGWf_isSome_iff Dt fnum fden gnum gden).mpr
    (cdvdGWf_of_dvd _ _ hen0 hdvd)

end WfEngineLayer


/-! ## ★ The Wf §6.2 divisibility residual and `hnorm`

The Wf normal-denominator bridge above lets the same valuation-theoretic residual discharge the
fuel-free `RischDEInnerCompletenessWf.hnorm` clause directly. Unlike the fueled residual, the Wf bundle
does not carry a fuel-length side condition: the semantic `cdvdGWf` bridge is `dvd ⟹ cdvdGWf` outright. -/

section DivisibilityResidualWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- **The precise Wf §6.2 divisibility residual**: a polynomial solution forces the mathematical Wf
normal-denominator divisibility, and the Wf normal part `eₙ` is nonzero. No fuel side condition is present. -/
structure RdeNormalDivisibilityResidualWf (Dt fnum fden gnum gden : CPolyG α) : Prop where
  /-- Bronstein Thm 6.1.2, Wf form: a polynomial solution forces `eₙ ∣ dₙh²`. -/
  hdvd : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    toPolyG (rdeNormEnWf Dt gden) ∣ toPolyG (rdeNormDnh2Wf Dt fden gden)
  /-- The Wf §6.2 normal part `eₙ` of `gden` is nonzero. -/
  hen0 : CPolyG.cnormG (rdeNormEnWf Dt gden) ≠ []

omit [CRischField α] in
/-- **`hnorm` from the Wf §6.2 divisibility residual**: the fuel-free normal-denominator step preserves
solvability, with no fuel side condition. -/
theorem hnormWf_of_divisibilityResidualWf (Dt fnum fden gnum gden : CPolyG α)
    (hres : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominatorGWf Dt fnum fden gnum gden).isSome = true := by
  intro hsol
  exact cRdeNormalDenominatorGWf_isSome_of_dvd Dt fnum fden gnum gden
    hres.hen0 (hres.hdvd hsol)

omit [CDiffFieldSpec α] [CRischField α] in
/-- **`eₙ ∣ dₙ` makes the Wf §6.2 divisibility free**. -/
theorem dvd_dnh2Wf_of_en_dvd_dn (Dt : CPolyG α) (fden gden : CPolyG α)
    (hdvd : toPolyG (rdeNormEnWf Dt gden) ∣ toPolyG (rdeNormDnWf Dt fden)) :
    toPolyG (rdeNormEnWf Dt gden) ∣ toPolyG (rdeNormDnh2Wf Dt fden gden) := by
  rw [rdeNormDnh2Wf, CPolyG.toPolyG_cmulG, CPolyG.toPolyG_cmulG]
  exact (hdvd.mul_right _).mul_right _

omit [CRischField α] in
/-- **The Wf `hdvd` clause is free when `eₙ ∣ dₙ`**. -/
theorem hdvdWf_free_of_en_dvd_dn (Dt fnum fden gnum gden : CPolyG α)
    (hdvd : toPolyG (rdeNormEnWf Dt gden) ∣ toPolyG (rdeNormDnWf Dt fden)) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      toPolyG (rdeNormEnWf Dt gden) ∣ toPolyG (rdeNormDnh2Wf Dt fden gden) :=
  fun _ => dvd_dnh2Wf_of_en_dvd_dn Dt fden gden hdvd

end DivisibilityResidualWf


/-! ## Wf assembly from the Wf normal-denominator residual

`RischDEInnerCompletenessWf` is assembled by discharging `hnorm` from `RdeNormalDivisibilityResidualWf`
through `hnormWf_of_divisibilityResidualWf`; the remaining `hbound`/`hsolve` clauses use the Wf §6
functions. -/

section AssembleWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- **`RischDEInnerCompletenessWf` with `hnorm` discharged from the Wf §6.2 residual**. -/
theorem rischDEInnerCompletenessWf_of_norm_bound_solve (Dt fnum fden gnum gden : CPolyG α)
    (hnormRes : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden)
    (hbound : ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorGWf Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      ∀ q : CPolyG α,
        IsReducedRdeSol Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1 q →
        cdegG q ≤ cRdeBoundDegreeG Dt
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1)
    (hsolve : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRischDEGWf Dt fnum fden gnum gden).isSome = true) :
    RischDEInnerCompletenessWf Dt fnum fden gnum gden where
  hnorm := hnormWf_of_divisibilityResidualWf Dt fnum fden gnum gden hnormRes
  hbound := hbound
  hsolve := hsolve

end AssembleWf

/-! ### Restatement against `RischDEInnerCompletenessWf.hnorm`'s field type (anonymous `example`) -/

-- The Wf engine bridge: mathematical divisibility forces the Wf normal-denominator step to succeed.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CFracGcdCoreWf α]
    (Dt fnum fden gnum gden : CPolyG α)
    (hen0 : CPolyG.cnormG (rdeNormEnWf Dt gden) ≠ [])
    (hdvd : toPolyG (rdeNormEnWf Dt gden) ∣ toPolyG (rdeNormDnh2Wf Dt fden gden)) :
    (cRdeNormalDenominatorGWf Dt fnum fden gnum gden).isSome = true :=
  cRdeNormalDenominatorGWf_isSome_of_dvd Dt fnum fden gnum gden hen0 hdvd

-- The Wf residual produces exactly the `RischDEInnerCompletenessWf.hnorm` field shape.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
    [CRischField α] (Dt fnum fden gnum gden : CPolyG α)
    (hres : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominatorGWf Dt fnum fden gnum gden).isSome = true :=
  hnormWf_of_divisibilityResidualWf Dt fnum fden gnum gden hres

/-! ### Final verdict (stated precisely)

**Is `hnorm` discharged?** **YES — modulo a single, precisely isolated deep divisibility (Bronstein Thm
6.1.2).** `hnormWf_of_divisibilityResidualWf` produces the **exact** `hnorm` clause of
`RischDEInnerCompletenessWf` from `RdeNormalDivisibilityResidualWf` (confirmed by the field-type
`example`). The §6.2 transformation loses a solution **only** through its one `cdvdGWf` divisibility gate,
and `hnorm` is that gate's completeness.

**What is closed unconditionally (the fully-proven Wf engine layer; NO `native_decide`/`sorry`):**
* `cRdeNormalDenominatorGWf_isSome_iff` — the §6.2 Wf step's `isSome` is *exactly* its `cdvdGWf` guard
  `eₙ ∣ dₙh²` (definitional control-flow reading);
* `cdvdGWf_of_dvd` — the **converse of `dvd_of_cdvdGWf`**: mathematical `toPolyG q ∣ toPolyG p` (+ `q ≠ 0`)
  forces the engine check `cdvdGWf = true` — so the §6.2 guard is honest in **both** directions, with no
  fuel bound;
* `cRdeNormalDenominatorGWf_isSome_of_dvd` — composing them: the *mathematical* §6.2 divisibility
  `eₙ ∣ dₙh²` makes the Wf §6.2 step return `some`, collapsing `hnorm` to that single divisibility.
The Wf residual `RdeNormalDivisibilityResidualWf` and assembly
`rischDEInnerCompletenessWf_of_norm_bound_solve` feed this bridge directly into
`RischDEInnerCompletenessWf`.

**The single deep residual** (`RdeNormalDivisibilityResidualWf`, NEVER `sorry`): `hdvd` — a polynomial
solution forces `eₙ ∣ dₙh²` (**Bronstein Thm 6.1.2**, the valuation-theoretic necessity at the normal
poles), plus the **benign** engine side-condition `hen0` (`eₙ ≠ 0`, free for weakly-normalized
`gden ≠ 0`). The deep `hdvd` is the one genuinely irreducible piece — it is *not* derivable from the
cleared identity `IsCRischDEGPolySol` by elementary algebra (the identity lives in the polynomial ring, the
divisibility is about the denominator's normal-pole structure).

**`hdvd` is reachable in the structural cases, and the deep case has a concrete Mathlib route.**
`dvd_dnh2Wf_of_en_dvd_dn` / `hdvdWf_free_of_en_dvd_dn` discharge `hdvd` **unconditionally** when `eₙ ∣ dₙ`
(so it is non-vacuous, not a hidden `sorry`). The full deep case (arbitrary normal poles) reduces to the
per-pole order-drop `Polynomial.derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors` (Mathlib has
it) lifted through `cValuationG` over the tower — a complete Thm 6.1.2 development, the actionable
frontier for closing `hdvd` outright.

**What `RischDEInnerCompletenessWf` now reduces to.** With `hnorm` produced here
(`rischDEInnerCompletenessWf_of_norm_bound_solve`), `RischDEInnerCompletenessWf` reduces to: `hbound`
(`ComputableRischDEDegreeBound`, modulo a cancellation residual) + `hsolve` (the §6.4–6.6 SPDE/poly-RDE
exhaustiveness, `ComputableRischDESolveExhaustiveness`) + the deep §6.2 divisibility (Bronstein Thm 6.1.2,
`RdeNormalDivisibilityResidualWf.hdvd`). The §6.2 normal-denominator completeness clause is discharged down
to its single valuation-theoretic keystone, through a fully proven engine layer. -/

/-! ### Axiom audit (the Wf engine layer + the modular assembly are axiom-clean; NO `native_decide`,
NO `sorry`) -/

#print axioms cRdeNormalDenominatorGWf_isSome_iff
#print axioms cdvdGWf_of_dvd
#print axioms cRdeNormalDenominatorGWf_isSome_of_dvd
#print axioms hnormWf_of_divisibilityResidualWf
#print axioms rischDEInnerCompletenessWf_of_norm_bound_solve

end DeepWiki.SymbolicIntegration
