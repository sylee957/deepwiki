import DeepWiki.SymbolicIntegration.ComputableIntegrateTowerCorrectG

/-! # One-shot (checker-free) algorithm soundness for the integrator's polynomial branch

The integrator's other soundness route is **check-based**: the bridge `field_identity_of_checkIdentityG`
(`ComputableIntegrateTowerCorrectG`) takes the driver `cIntegrateGFull`'s output, asks the runtime
Boolean `checkIdentityG`, and proves `checkIdentityG = true ⟹ D(∫f) = f`. The genuine soundness wanted is
**one-shot**: the algorithm output is provably correct *with the runtime check redundant* — not "check
passes implies correct" but "the algorithm always passes its own check, so `D(res) = integrand`
directly".

This file delivers that one-shot for the **reachable polynomial branch** (Bronstein §5.4 / §6, the
`b = 0` primitive-integration arm of `cPolyRischDEG`, `Dt = 1` over a constant base — the regime
`cIntegrateGFull` runs the polynomial part `∫ fₚ` in). The spine:

* **`derivative_toPolyG_cIntegratePolyG`** — the *abstract algorithm-correctness atom*, UNCONDITIONAL
  (mod characteristic zero, needed to divide by `i+1`): the engine's term-by-term antiderivative
  `cIntegratePolyG c` has formal derivative exactly `c`, `D(toPolyG (cIntegratePolyG c)) = toPolyG c`.
  No runtime check. (`derivative_Xpow_mul_toPolyG_integrateTail` is its inductive heart.)
* **`toPolyG_cmonomialDeriv_cIntegratePolyG_const`** — the same under the engine derivation
  `cmonomialDeriv [1] = κ_D + d/dt = mapCoeffs + derivative`, over a constant base (`mapCoeffs = 0`).
* **`checkIdentityG_cIntegratePolyG_const`** — ★ THE CRUX (the task's missing link): the
  polynomial-branch output *passes* `checkIdentityG` abstractly (`= true`, no check executed). The
  `algorithm-output ⟹ check-passes` direction, proven.
* **`field_identity_cIntegratePolyG_const` / `field_identity_of_cPolyRischDEG`** — composing the crux
  with the bridge `field_identity_of_checkIdentityG` gives the checker-free one-shot `D(∫f) = f`; the
  latter keyed on the genuine algorithm `cPolyRischDEG [1] fuel [] c n = some q`. Specialized to the
  level-1 carrier `ℚ(x) = QFunNZG ℚ` as **`field_identity_of_cPolyRischDEG_qfunNZG`** — the deliverable
  (no checker, no `native_decide`, axiom-clean `[propext, choice, Quot.sound]`).

## Precise scope of the FULL transcendental one-shot (`cIntegrateGFull = some res ⟹ D(res) = integrand`)

The campaign from here is a clear lemma sequence, not a fog. The full transcendental crux
`cIntegrateGFull = some res ⟹ checkIdentityG = true` decomposes by `cIntegrateGFull`'s structure
(canonical split via `canonicalRepresentationFastG` ⟹ special-part `cisZeroG b` test ⟹ normal part
`cIntegrateReducedG` plus poly part `cPolyRischDEG`):

* **Poly part (`cPolyRischDEG`, `b = 0`)** — DONE here (`checkIdentityG_cIntegratePolyG_const`), the atom
  `derivative_toPolyG_cIntegratePolyG`. EXISTS, abstract, axiom-clean.
* **Normal part (`cIntegrateReducedG` = `cHermiteReduceTowerG` + `cLogPartG`)** — NOT yet abstract: the
  Hermite reduction identity `D(g) + h = a/d` and the Rothstein–Trager residue-log correctness are only
  `native_decide`-validated today (no abstract `cHermiteReduceTowerG`-spec). NEEDS: an abstract
  `cHermiteReduceTowerG` correctness (the per-squarefree-factor Hermite step, telescoped — the
  generic-curve analogue `generalReduceRationalTelescope` in `ComputableGeneralIntegralSoundness` is the
  template) and a `cLogPartG` residue-sum correctness. This is the genuinely hard, high-value piece.
* **Canonical split** (`canonicalRepresentationFastG` reconstructs `f = fₚ + b/dₛ + cₙ/dₙ`) — EXISTS
  abstract at `α = QFunNZG ℚ` (`canonicalRepresentationFastG_reconstructs_qfunNZG`,
  `ComputableSplitFactorTowerCorrectG`); needs threading into the assembly.
* **Special part** (`b = 0` required by `cIntegrateGFull`) — degenerate over a primitive extension
  (`dₛ = 1`); the genuine hyperexp / hypertangent special part is the documented continuation.
* **Constant-base discharge** — the `hconst : mapCoeffs (…) = 0` hypothesis here is the "coefficients are
  differential constants" regime; lifting it from a hypothesis to a derived fact (the tower's base
  derivation) is a small transport, NOT hard.
* **Algebraic driver** (the separate algebraic integrators `cIntegrateAlgebraicWf` / `afIntegrateAlgebraicWf`)
  — its `hsplit` round-trip self-discharge is already abstract (`isGeneralRationalIntegral_of_roundtrip`,
  `toPolyG_afDeriv_eq_of_roundtrip`, `ComputableGeneralIntegralSoundness`); its standalone soundness is
  `cIntegrateAlgebraicWf_sound` (`ComputableAlgebraicWfSoundness`).

So: the poly-branch one-shot is proven (this file); the canonical-split and algebraic-round-trip pieces
EXIST abstract; the single genuinely-hard remaining piece is an **abstract `cHermiteReduceTowerG` plus
`cLogPartG` correctness** (the normal part). Once that lands, the assembly
`cIntegrateGFull = some res ⟹ checkIdentityG = true` (then `⟹ D = integrand` via the bridge) is
mechanical. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **`toK (cnatCastG k) = (k : K)`**: the `k`-fold `CField.one` sum reads as the genuine natural cast
in `K = CFieldSpec.K α` (`cnatCastG` is the engine's `ℕ`-cast). A 4-line `toK`-homomorphism induction,
inlined here so this file's only import is `ComputableIntegrateTowerCorrectG`. -/
theorem toK_cnatCastG_oneShot (k : ℕ) :
    CFieldSpec.toK (CPolyG.cnatCastG k : α) = (k : CFieldSpec.K α) := by
  induction k with
  | zero => rw [CPolyG.cnatCastG, CFieldSpec.toK_zero, Nat.cast_zero]
  | succ n ih => rw [CPolyG.cnatCastG, CFieldSpec.toK_add, CFieldSpec.toK_one, ih, Nat.cast_succ,
      add_comm]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Shifted antiderivative-tail derivative law** (the inductive heart): for the index-`k`-started
integration tail `L_k = (c.zipIdx k).map (fun (a,i) => a/(i+1))`,
`D(X^{k+1} · toPolyG L_k) = X^k · toPolyG c`. By induction on `c` peeling `C(a/(k+1))·X^{k+1}`, whose
derivative `(k+1)·C(a/(k+1))·X^k = C(toK a)·X^k` recovers the term (`(k+1)·(a/(k+1)) = a` over the field). -/
theorem derivative_Xpow_mul_toPolyG_integrateTail [CharZero (CFieldSpec.K α)] (c : CPolyG α) :
    ∀ k : ℕ, Polynomial.derivative
        (X ^ (k + 1) *
          toPolyG ((c.zipIdx k).map (fun ai => CField.div ai.1 (cnatCastG (ai.2 + 1)))))
      = X ^ k * toPolyG c := by
  induction c with
  | nil => intro k; simp
  | cons a as ih =>
    intro k
    -- `(a :: as).zipIdx k = (a, k) :: as.zipIdx (k+1)`; map and read `toPolyG`
    simp only [List.zipIdx_cons, List.map_cons, toPolyG_cons]
    -- `X^{k+1} · (C(toK (a/(k+1))) + X · toPolyG(tail)) = C(..)·X^{k+1} + X^{k+2}·toPolyG(tail)`
    rw [mul_add, derivative_add]
    -- the head term: `D(C(toK (a/(k+1)))·X^{k+1}) = (k+1)·C(toK (a/(k+1)))·X^k`
    have hhead : Polynomial.derivative
        (X ^ (k + 1) * Polynomial.C (CFieldSpec.toK (CField.div a (cnatCastG (k + 1)))))
        = Polynomial.C (CFieldSpec.toK a) * X ^ k := by
      rw [mul_comm, derivative_C_mul, derivative_X_pow, add_tsub_cancel_right, ← mul_assoc, ← C_mul]
      congr 1
      -- `(toK (a/(k+1))) · (k+1 : K) = toK a`, since `toK (cnatCast (k+1)) = (k+1 : K)`
      rw [CFieldSpec.toK_div, toK_cnatCastG_oneShot]
      have hk1 : ((k : CFieldSpec.K α) + 1) ≠ 0 := by
        have : ((k : CFieldSpec.K α) + 1) = ((k + 1 : ℕ) : CFieldSpec.K α) := by push_cast; ring
        rw [this, Nat.cast_ne_zero]; omega
      push_cast
      field_simp
    -- the tail term: regroup `X^{k+1}·(X·toPolyG tail) = X^{(k+1)+1}·toPolyG tail`, apply IH at `k+1`
    have htail : Polynomial.derivative
        (X ^ (k + 1) * (X * toPolyG
          ((as.zipIdx (k + 1)).map (fun ai => CField.div ai.1 (cnatCastG (ai.2 + 1))))))
        = X ^ (k + 1) * toPolyG as := by
      have hrw : X ^ (k + 1) * (X * toPolyG
            ((as.zipIdx (k + 1)).map (fun ai => CField.div ai.1 (cnatCastG (ai.2 + 1)))))
          = X ^ ((k + 1) + 1) * toPolyG
            ((as.zipIdx (k + 1)).map (fun ai => CField.div ai.1 (cnatCastG (ai.2 + 1)))) := by
        rw [pow_succ]; ring
      rw [hrw, ih (k + 1)]
    rw [hhead, htail, mul_add]
    ring

/-! ### The `cIntegratePolyG` formal-derivative correctness (unconditional, abstract)

`cIntegratePolyG c = 0 :: (c.zipIdx.map (fun (a,i) => a/(i+1)))` is the engine's term-by-term
antiderivative `∫ Σ cᵢtⁱ = Σ (cᵢ/(i+1)) t^{i+1}` (the `b = 0` primitive branch of `cPolyRischDEG`).
Its **formal** derivative `cderivG` (`= Polynomial.derivative` under `toPolyG`) inverts it exactly — the
`k = 0` instance of the shifted law, with `X^1 = X`, `X^0 = 1`. This is the genuine
*algorithm-correctness atom*: the antiderivative is right, with **no runtime check**. Needs only
characteristic zero (to divide by `i+1`), nothing about the derivation. -/

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **★ `cIntegratePolyG` is correct (formal-derivative form), checker-free**:
`D(toPolyG (cIntegratePolyG c)) = toPolyG c` over `(CFieldSpec.K α)[X]`, where `D = Polynomial.derivative`.
The engine's term-by-term antiderivative differentiates back to its integrand — proven, no `checkIdentityG`.
Immediate from `derivative_Xpow_mul_toPolyG_integrateTail` at `k = 0`. -/
theorem derivative_toPolyG_cIntegratePolyG [CharZero (CFieldSpec.K α)] (c : CPolyG α) :
    Polynomial.derivative (toPolyG (CPolyG.cIntegratePolyG c)) = toPolyG c := by
  have h := derivative_Xpow_mul_toPolyG_integrateTail c 0
  simpa only [CPolyG.cIntegratePolyG, toPolyG_cons, CFieldSpec.toK_zero, map_zero, zero_add,
    pow_zero, pow_one, one_mul, List.zipIdx] using h

/-! ### The `cmonomialDeriv [1]` (monomial-derivation) form over a constant base

The engine's actual derivation is `cmonomialDeriv Dt = κ_D + Dt·d/dt` (`= implicitDeriv (toPolyG Dt)`
under `toPolyG`). For the **canonical primitive monomial** `Dt = [CField.one]` (`D(t) = 1`),
`toPolyG [CField.one] = 1`, so `implicitDeriv 1 = mapCoeffs + derivative`: the formal `t`-derivative
*plus* the coefficientwise base derivation `κ_D`. The term-by-term antiderivative `cIntegratePolyG c`
therefore differentiates back to `c` exactly when the coefficient-derivation term `mapCoeffs` vanishes
— i.e. over a **constant base** (`κ_D = 0` on the coefficients), the regime `cIntegrateGFull` runs the
polynomial part in (Bronstein §5.4, primitive case). We carry that as the explicit hypothesis
`hconst : mapCoeffs (toPolyG (cIntegratePolyG c)) = 0` (which holds whenever every coefficient is a
differential constant). This is the genuine `D(∫ fₚ) = fₚ` for the polynomial part — checker-free. -/

/-- **★ `cIntegratePolyG` differentiates back under the primitive monomial derivation** (`Dt = 1`),
checker-free: if the coefficientwise-derivation term vanishes (`mapCoeffs (toPolyG (cIntegratePolyG c))
= 0`, the constant-base regime), then `toPolyG (cmonomialDeriv [CField.one] (cIntegratePolyG c)) =
toPolyG c` over `(CFieldSpec.K α)[X]`. Routes the engine derivation through
`toPolyG_cmonomialDeriv` (`= implicitDeriv (toPolyG [1]) = implicitDeriv 1 = mapCoeffs + derivative`),
kills `mapCoeffs` by `hconst`, and finishes with the formal-derivative atom
`derivative_toPolyG_cIntegratePolyG`. The polynomial-part `D(∫ fₚ) = fₚ`, abstract. -/
theorem toPolyG_cmonomialDeriv_cIntegratePolyG_const [CharZero (CFieldSpec.K α)] (c : CPolyG α)
    (hconst : Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) = 0) :
    toPolyG (CPolyG.cmonomialDeriv ([CField.one] : CPolyG α) (CPolyG.cIntegratePolyG c))
      = toPolyG c := by
  rw [toPolyG_cmonomialDeriv]
  -- `toPolyG [CField.one] = 1`, so `implicitDeriv 1 = mapCoeffs + derivative`
  have hDt : toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, map_one, mul_zero, add_zero]
  rw [hDt, Differential.implicitDeriv, Derivation.add_apply, hconst, zero_add]
  -- the `v • derivative'` part is `1 • derivative = derivative`
  rw [Derivation.smul_apply, one_smul, Derivation.restrictScalars_apply]
  exact derivative_toPolyG_cIntegratePolyG c

/-! ### ★ The checker-free FIELD identity `D(∫ fₚ) = fₚ` for the polynomial part

We now assemble the genuine one-shot for the polynomial branch — **no `checkIdentityG`**. The full
driver `cIntegrateGFull` integrates a polynomial part `fₚ` (a `b = 0` primitive Risch-DE) by
`cIntegratePolyG`, recombining it into the rational part with denominator `1`. The resulting
antiderivative `g = amG(toPolyG (cIntegratePolyG c)) / amG 1` satisfies the field-level identity
`towerFractionFieldDerivG [1] g = amG(toPolyG c) / amG 1` directly: the tower derivation on a
polynomial image is the image of the monomial derivation (`extendDeriv_algebraMap`), which the
abstract atom `toPolyG_cmonomialDeriv_cIntegratePolyG_const` sends to `toPolyG c`. The `checkIdentityG`
guard is **redundant** here — the algorithm output is provably correct without it. -/

/-- **★★ Checker-free field one-shot `D(∫ fₚ) = fₚ` (polynomial part, primitive monomial)**: over a
constant base (`hconst : mapCoeffs (toPolyG (cIntegratePolyG c)) = 0`), the tower fraction-field
derivation sends the antiderivative `amG(toPolyG (cIntegratePolyG c))` to `amG(toPolyG c)` exactly:
`towerFractionFieldDerivG [CField.one] (amG (toPolyG (cIntegratePolyG c))) = amG (toPolyG c)` over
`RatFunc (CFieldSpec.K α)`. **No `checkIdentityG`** — `extendDeriv_algebraMap` pushes the field
derivation onto the polynomial image, and the abstract monomial-derivation atom finishes it. This is
the genuine `D(∫f) = f` for the polynomial part, with the runtime check provably redundant. -/
theorem towerFractionFieldDerivG_amG_cIntegratePolyG_const [CharZero (CFieldSpec.K α)]
    [Algebra ℚ (CFieldSpec.K α)] (c : CPolyG α)
    (hconst : Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) = 0) :
    towerFractionFieldDerivG ([CField.one] : CPolyG α)
        (amG α (toPolyG (CPolyG.cIntegratePolyG c)))
      = amG α (toPolyG c) := by
  -- the tower field derivation on a polynomial image is the image of the monomial derivation
  rw [towerFractionFieldDerivG, extendDeriv_algebraMap, ← toPolyG_cmonomialDeriv]
  -- which the abstract atom identifies with `toPolyG c`
  rw [toPolyG_cmonomialDeriv_cIntegratePolyG_const c hconst]

/-! ### ★ THE CRUX: the polynomial-branch output PASSES `checkIdentityG` (algorithm self-discharge)

The task's missing link, for the reachable polynomial branch: the engine **always passes its own
check** here, so the runtime guard is redundant. We show the directly-built pure-polynomial result
`⟨(cIntegratePolyG c, [CField.one]), []⟩` — the shape `cPolyRischDEG`'s `b = 0` integration branch
emits (recombined over denominator `1`, no logs) — satisfies `checkIdentityG [CField.one] · c
[CField.one] = true` **without any check being run**: the abstract atoms compute the cleared identity
directly. `checkIdentityG` clears denominators and tests `cisZeroG`; with `gden = aden = 1` and no logs
this collapses (`cisZeroG_iff`) to the polynomial identity `D(cIntegratePolyG c) = c`, which is the atom
`toPolyG_cmonomialDeriv_cIntegratePolyG_const`. Composing with `field_identity_of_checkIdentityG` then
gives `D(∫f) = f` checker-free — the `checkIdentityG` guard is provably never needed on this
branch. -/

/-- `toPolyG (cmonomialDeriv [CField.one] [CField.one]) = 0`: the primitive monomial derivation
annihilates the constant `1` (`D(1) = 0`). Both the coefficient-derivation part (`mapCoeffs 1 =
C(D 1) = 0`) and the formal-`t`-derivative part (`derivative 1 = 0`) vanish. -/
theorem toPolyG_cmonomialDeriv_one : toPolyG
    (CPolyG.cmonomialDeriv ([CField.one] : CPolyG α) ([CField.one] : CPolyG α)) = 0 := by
  rw [toPolyG_cmonomialDeriv]
  have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, map_one, mul_zero, add_zero]
  rw [hone]
  exact Derivation.map_one_eq_zero _

/-- **★★ THE CRUX (polynomial branch): the integration output passes `checkIdentityG` abstractly**,
checker-free. Over a constant base (`hconst`), the pure-polynomial result
`⟨(cIntegratePolyG c, [CField.one]), []⟩` satisfies `checkIdentityG [CField.one] · c [CField.one] =
true` — proven by the abstract atoms, with **no runtime check executed**. This is the missing link
`algorithm-output ⟹ check-passes`: the engine's `b = 0` integration branch *always* validates, so the
`checkIdentityG` guard is redundant on it. Reduce `checkIdentityG` to `cisZeroG (csubG …)`, clear via
`cisZeroG_iff` (denominators `gden = aden = 1`, empty-log fold seed `0/1`), and finish with
`toPolyG_cmonomialDeriv_cIntegratePolyG_const` (`D q = c`) and `toPolyG_cmonomialDeriv_one` (`D 1 = 0`). -/
theorem checkIdentityG_cIntegratePolyG_const [CharZero (CFieldSpec.K α)] (c : CPolyG α)
    (hconst : Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) = 0) :
    CPolyG.checkIdentityG ([CField.one] : CPolyG α)
        ⟨(CPolyG.cIntegratePolyG c, ([CField.one] : CPolyG α)), []⟩ c ([CField.one] : CPolyG α)
      = true := by
  -- unfold the check; the empty-log fold is just the seed `([0], [1])`
  rw [CPolyG.checkIdentityG]
  simp only [List.foldl_nil]
  -- the check is `cisZeroG (csubG lhs rhs)`; clear to the polynomial identity `toPolyG lhs = toPolyG rhs`
  rw [cisZeroG_iff, toPolyG_csubG, sub_eq_zero]
  -- push `toPolyG` through everything
  have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, map_one, mul_zero, add_zero]
  have hzero : toPolyG ([CField.zero] : CPolyG α) = 0 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_zero, map_zero, mul_zero, add_zero]
  simp only [toPolyG_cmulG, toPolyG_caddG, toPolyG_csubG, hone, hzero]
  -- the rational-part numerator derivative `D(q)·1 − q·D(1)`, with `D(1) = 0`
  rw [toPolyG_cmonomialDeriv_one,
    toPolyG_cmonomialDeriv_cIntegratePolyG_const c hconst]
  ring

/-! ### ★★★ THE ONE-SHOT (checker-free): compose the crux with the field bridge

Composing `checkIdentityG_cIntegratePolyG_const` (the algorithm self-discharges its check) with
`field_identity_of_checkIdentityG` (check ⟹ field identity) yields the genuine one-shot the campaign
targets: the polynomial-branch antiderivative satisfies `D(∫f) = f` **with the runtime check provably
redundant**. The `checkIdentityG = true` fact is supplied by the abstract atom — it is *never executed*.
This is exactly the `algorithm = some res → D(res) = integrand` (no checker) for the reachable
polynomial branch. -/

/-- **★★★ Checker-free one-shot `D(∫ fₚ) = fₚ` via the field bridge** (polynomial branch). Over a
constant base (`hconst`), the pure-polynomial antiderivative `g = amG(toPolyG (cIntegratePolyG c))/amG 1`
satisfies the field-level identity `towerFractionFieldDerivG [1] g + logResidueSumG [1] [] = amG(toPolyG
c)/amG 1` over `RatFunc (CFieldSpec.K α)` — obtained by feeding the *abstractly-proven*
`checkIdentityG = true` (the crux `checkIdentityG_cIntegratePolyG_const`) into the bridge
`field_identity_of_checkIdentityG`. The `checkIdentityG` guard is **never run**: the algorithm output is
proven correct. The genuine one-shot algorithm-soundness for the polynomial branch, routed through the
existing bridge to show it is redundant with the check. -/
theorem field_identity_cIntegratePolyG_const [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)]
    (c : CPolyG α) (hconst : Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) = 0) :
    towerFractionFieldDerivG ([CField.one] : CPolyG α)
        (amG α (toPolyG (CPolyG.cIntegratePolyG c)) / amG α (toPolyG ([CField.one] : CPolyG α)))
        + logResidueSumG ([CField.one] : CPolyG α)
            (⟨(CPolyG.cIntegratePolyG c, ([CField.one] : CPolyG α)), []⟩ : IntegralResultG α).logs
      = amG α (toPolyG c) / amG α (toPolyG ([CField.one] : CPolyG α)) := by
  have hone_ne : toPolyG ([CField.one] : CPolyG α) ≠ 0 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, map_one, mul_zero, add_zero]; exact one_ne_zero
  exact field_identity_of_checkIdentityG ([CField.one] : CPolyG α)
    ⟨(CPolyG.cIntegratePolyG c, ([CField.one] : CPolyG α)), []⟩ c ([CField.one] : CPolyG α)
    hone_ne hone_ne (by simp) (checkIdentityG_cIntegratePolyG_const c hconst)

/-! ### ★ Keyed on the actual algorithm function `cPolyRischDEG`

The result above is for the directly-built pure-polynomial result; here we key it on the genuine
algorithm `cPolyRischDEG [CField.one] fuel [] c n` (the `b = 0` integration branch of the Poly-Risch-DE
dispatcher), which — when the degree budget admits (`deg c + 1 ≤ n`, the branch condition) — returns
exactly `some (cIntegratePolyG c)`. So the field identity holds for whatever the algorithm emits, with no
check executed. -/

omit [CDiffFieldSpec α] in
/-- **`cPolyRischDEG` `b = 0` branch returns `cIntegratePolyG c`** (for nonzero `c` within the degree
budget). When `cisZeroG c = false` and `deg c + 1 ≤ n`, `cPolyRischDEG Dt fuel [] c n = some
(cIntegratePolyG c)`: the pure-integration arm of the dispatcher. Pins the algorithm's output shape. -/
theorem cPolyRischDEG_nil_eq [CFracGcdCore α] [CRischField α] (Dt : CPolyG α) (fuel : ℕ)
    (c : CPolyG α) (n : ℤ)
    (hc : CPolyG.cisZeroG c = false) (hdeg : (CPolyG.cdegG c : ℤ) + 1 ≤ n) :
    CPolyG.cPolyRischDEG Dt fuel ([] : CPolyG α) c n = some (CPolyG.cIntegratePolyG c) := by
  have hb : CPolyG.cisZeroG ([] : CPolyG α) = true := by rw [cisZeroG_iff, toPolyG_nil]
  simp only [CPolyG.cPolyRischDEG, hb, if_true, hc, Bool.false_eq_true, if_false]
  rw [if_neg (by omega : ¬ (CPolyG.cdegG c : ℤ) + 1 > n)]

/-- **★★★ Checker-free one-shot keyed on `cPolyRischDEG`**: if the Poly-Risch-DE dispatcher's `b = 0`
integration branch returns `some q` (`cPolyRischDEG [CField.one] fuel [] c n = some q`, nonzero `c`
within the degree budget, constant base), then the field-level antiderivative identity
`towerFractionFieldDerivG [1] (amG(toPolyG q)/amG 1) + … = amG(toPolyG c)/amG 1` holds — **no
`checkIdentityG` executed**. The genuine `algorithm = some res → D(res) = integrand` for the polynomial
branch: the runtime guard is provably redundant. (`q = cIntegratePolyG c` by `cPolyRischDEG_nil_eq`,
then `field_identity_cIntegratePolyG_const`.) -/
theorem field_identity_of_cPolyRischDEG [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)]
    [CFracGcdCore α] [CRischField α]
    (fuel : ℕ) (c q : CPolyG α) (n : ℤ)
    (hc : CPolyG.cisZeroG c = false) (hdeg : (CPolyG.cdegG c : ℤ) + 1 ≤ n)
    (hsome : CPolyG.cPolyRischDEG ([CField.one] : CPolyG α) fuel ([] : CPolyG α) c n = some q)
    (hconst : Differential.mapCoeffs (toPolyG q) = 0) :
    towerFractionFieldDerivG ([CField.one] : CPolyG α)
        (amG α (toPolyG q) / amG α (toPolyG ([CField.one] : CPolyG α)))
      = amG α (toPolyG c) / amG α (toPolyG ([CField.one] : CPolyG α)) := by
  -- the algorithm output is exactly `cIntegratePolyG c`
  have hq : q = CPolyG.cIntegratePolyG c := by
    rw [cPolyRischDEG_nil_eq ([CField.one] : CPolyG α) fuel c n hc hdeg] at hsome
    exact (Option.some.injEq _ _ ▸ hsome).symm
  subst hq
  -- empty logs ⇒ `logResidueSumG … [] = 0`, so the field-identity is exactly the bridge output
  have h := field_identity_cIntegratePolyG_const (α := α) c hconst
  rwa [logResidueSumG_nil, add_zero] at h

/-! ### ★ Discharging the constant-base hypothesis: `mapCoeffs` is inherited from integrand to antiderivative

`field_identity_of_cPolyRischDEG` carries `hconst : mapCoeffs (toPolyG q) = 0` on the algorithm *output*.
That output-side hypothesis is **not** automatic, but it *is* implied by the corresponding *input*-side
fact `mapCoeffs (toPolyG c) = 0` (the integrand's coefficients being differential constants): the
antiderivative's degree-`i+1` coefficient is `cᵢ/(i+1)`, whose base derivative `(cᵢ)′/(i+1)` vanishes
exactly when `(cᵢ)′` does. So the constant-base condition transports from integrand to antiderivative
(`cIntegratePolyG_const_coeff`), letting the poly-RDE soundness be keyed on the *input* (the natural
form). The conduit is the commutation of the two polynomial derivations `mapCoeffs` and `derivative`. -/

/-- **`mapCoeffs` and `derivative` commute on `(CFieldSpec.K α)[X]`**:
`mapCoeffs (derivative r) = derivative (mapCoeffs r)`. Both are derivations; the coefficientwise check
(`coeff_mapCoeffs`, `coeff_derivative`) reduces to `(x·(n+1))′ = x′·(n+1)`, true since the nat-cast
`(n+1 : K)` is a differential constant (`map_natCast`). The conduit for transporting the constant-base
condition through the antiderivative `cIntegratePolyG`. -/
theorem mapCoeffs_derivative_commute (r : (CFieldSpec.K α)[X]) :
    Differential.mapCoeffs (Polynomial.derivative r) =
      Polynomial.derivative (Differential.mapCoeffs r) := by
  ext n
  rw [Differential.coeff_mapCoeffs, coeff_derivative, coeff_derivative,
    Differential.coeff_mapCoeffs, Derivation.leibniz]
  have hc : ((↑n + 1 : (CFieldSpec.K α)))′ = 0 := by
    rw [show ((↑n + 1 : (CFieldSpec.K α))) = ((n + 1 : ℕ) : (CFieldSpec.K α)) by push_cast; ring,
      Derivation.map_natCast]
  rw [hc, smul_zero, zero_add, smul_eq_mul, mul_comm]

/-- **★ Constant-base condition transports through `cIntegratePolyG`** (conditional, *not*
unconditional): if the integrand's coefficients are differential constants
(`mapCoeffs (toPolyG c) = 0`), then so are the antiderivative's
(`mapCoeffs (toPolyG (cIntegratePolyG c)) = 0`). NOT free: the converse-style reading shows the output
condition is *equivalent* to the input one (each output coefficient `cᵢ/(i+1)` is constant iff `cᵢ` is),
so the hypothesis is genuinely needed. Proof: `Q := mapCoeffs (toPolyG (cIntegratePolyG c))` has
`derivative Q = mapCoeffs (derivative (toPolyG (cIntegratePolyG c))) = mapCoeffs (toPolyG c) = 0`
(commute + the atom `derivative_toPolyG_cIntegratePolyG` + hypothesis) and zero constant term
(`cIntegratePolyG` starts `0 :: …`), so `Q = 0` (`derivative_eq_zero` ⟹ `natDegree 0` ⟹ `C (coeff 0)`). -/
theorem cIntegratePolyG_const_coeff [CharZero (CFieldSpec.K α)] (c : CPolyG α)
    (hc : Differential.mapCoeffs (toPolyG c) = 0) :
    Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) = 0 := by
  set Q := Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) with hQ
  -- `derivative Q = 0` by commuting `mapCoeffs`/`derivative` and the formal-derivative atom
  have hderiv : Polynomial.derivative Q = 0 := by
    rw [hQ, ← mapCoeffs_derivative_commute, derivative_toPolyG_cIntegratePolyG, hc]
  -- `coeff Q 0 = 0`: `cIntegratePolyG` has zero constant term (`0 :: …`)
  have hcoeff0 : Q.coeff 0 = 0 := by
    rw [hQ, Differential.coeff_mapCoeffs]
    have : (toPolyG (CPolyG.cIntegratePolyG c)).coeff 0 = 0 := by
      rw [CPolyG.cIntegratePolyG, toPolyG_cons, coeff_add, coeff_C_zero, CFieldSpec.toK_zero,
        coeff_X_mul_zero, add_zero]
    rw [this, map_zero]
  -- `derivative Q = 0` ⟹ `natDegree Q = 0` ⟹ `Q = C (coeff Q 0) = 0`
  have hdeg : Q.natDegree = 0 := Polynomial.derivative_eq_zero.mp hderiv
  rw [eq_C_of_natDegree_eq_zero hdeg, hcoeff0, map_zero]

/-- **★★★ Poly-RDE soundness on the `b = 0` branch, keyed on the integrand** (the honest strongest
form): if `cPolyRischDEG [CField.one] fuel [] c n = some q` (nonzero `c` within the degree budget,
primitive base `Dt = 1`) and the integrand is over a **constant base** (`mapCoeffs (toPolyG c) = 0`),
then the field-level antiderivative identity `towerFractionFieldDerivG [1] (amG(toPolyG q)/amG 1)
= amG(toPolyG c)/amG 1` holds — **no `checkIdentityG`, no `native_decide`**. Strengthens
`field_identity_of_cPolyRischDEG` by replacing its *output*-side `mapCoeffs (toPolyG q) = 0` with the
natural *input*-side `mapCoeffs (toPolyG c) = 0` (via `cIntegratePolyG_const_coeff`). **Regime
boundary**: `Dt = [CField.one]` is required — the `b = []` branch integrates by the term-by-term
`cIntegratePolyG`, which inverts the monomial derivation `D(tⁱ) = i·tⁱ⁻¹` only when `D(t) = 1`; for a
general monomial `D(tⁱ) = i·tⁱ⁻¹·Dt`, so term-by-term integration is no longer the inverse and this
branch is unreachable (the dispatcher routes `b = 0` here only in the primitive case `δ = 0`). -/
theorem cPolyRischDEG_nil_field_identity [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)]
    [CFracGcdCore α] [CRischField α]
    (fuel : ℕ) (c q : CPolyG α) (n : ℤ)
    (hc : CPolyG.cisZeroG c = false) (hdeg : (CPolyG.cdegG c : ℤ) + 1 ≤ n)
    (hsome : CPolyG.cPolyRischDEG ([CField.one] : CPolyG α) fuel ([] : CPolyG α) c n = some q)
    (hconst : Differential.mapCoeffs (toPolyG c) = 0) :
    towerFractionFieldDerivG ([CField.one] : CPolyG α)
        (amG α (toPolyG q) / amG α (toPolyG ([CField.one] : CPolyG α)))
      = amG α (toPolyG c) / amG α (toPolyG ([CField.one] : CPolyG α)) := by
  -- `q = cIntegratePolyG c`, so the output-side `mapCoeffs` follows from the input-side via the transport
  have hq : q = CPolyG.cIntegratePolyG c := by
    rw [cPolyRischDEG_nil_eq ([CField.one] : CPolyG α) fuel c n hc hdeg] at hsome
    exact (Option.some.injEq _ _ ▸ hsome).symm
  subst hq
  exact field_identity_of_cPolyRischDEG fuel c (CPolyG.cIntegratePolyG c) n hc hdeg
    (cPolyRischDEG_nil_eq ([CField.one] : CPolyG α) fuel c n hc hdeg)
    (cIntegratePolyG_const_coeff c hconst)

/-! ### ★ THE DELIVERABLE at the level-1 carrier `α = QFunNZG ℚ = ℚ(x)`

Instantiating the checker-free polynomial-branch one-shot at the generic level-1 carrier
`α = QFunNZG ℚ`, where `CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ` (genuine `Algebra ℚ` and `CharZero`).
This is the concrete `cPolyRischDEG = some res → D(res) = integrand` (no checker, no `native_decide`)
for the polynomial branch over `ℚ(x)(t)`. The two local instances bridge the carrier abbreviation to
`RatFunc ℚ`, the standard carrier-specialization pattern for the generic `field_identity_of_checkIdentityG`
bridge at `α = QFunNZG ℚ`. -/

/-- `CharZero (CFieldSpec.K (QFunNZG ℚ)) = CharZero (RatFunc ℚ)`: re-declared locally so the deliverable
synthesizes the `CharZero` the polynomial-branch one-shot needs over the carrier abbreviation. -/
noncomputable local instance : CharZero (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (CharZero (RatFunc ℚ))

/-- The engine carrier `CFieldSpec.K (QFunNZG ℚ)` is `RatFunc ℚ`, a `ℚ`-algebra. Local instance so the
deliverable synthesizes the **same** `Algebra ℚ` the bridge `towerFractionFieldDerivG` uses. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- **★★★ Checker-free one-shot at `α = QFunNZG ℚ`** — the deliverable: if the Poly-Risch-DE
dispatcher's `b = 0` integration branch returns `some q` over the level-1 carrier `ℚ(x) = QFunNZG ℚ`
(`cPolyRischDEG [CField.one] fuel [] c n = some q`, nonzero `c` within the degree budget, constant
base), then the field-level antiderivative identity `towerFractionFieldDerivG [1] (amG(toPolyG q)/amG 1)
= amG(toPolyG c)/amG 1` holds over `RatFunc ℚ` — with **no `checkIdentityG` executed**, no
`native_decide`. The genuine `algorithm = some res → D(res) = integrand` for the polynomial branch at
ℚ(x): the runtime guard is provably redundant. The `QFunNZG ℚ` instance of
`field_identity_of_cPolyRischDEG`. -/
theorem field_identity_of_cPolyRischDEG_qfunNZG (fuel : ℕ) (c q : CPolyG (QFunNZG ℚ)) (n : ℤ)
    (hc : CPolyG.cisZeroG c = false) (hdeg : (CPolyG.cdegG c : ℤ) + 1 ≤ n)
    (hsome : CPolyG.cPolyRischDEG ([CField.one] : CPolyG (QFunNZG ℚ)) fuel
        ([] : CPolyG (QFunNZG ℚ)) c n = some q)
    (hconst : Differential.mapCoeffs (toPolyG q) = 0) :
    towerFractionFieldDerivG ([CField.one] : CPolyG (QFunNZG ℚ))
        (amG (QFunNZG ℚ) (toPolyG q) / amG (QFunNZG ℚ) (toPolyG ([CField.one] : CPolyG (QFunNZG ℚ))))
      = amG (QFunNZG ℚ) (toPolyG c)
          / amG (QFunNZG ℚ) (toPolyG ([CField.one] : CPolyG (QFunNZG ℚ))) :=
  field_identity_of_cPolyRischDEG fuel c q n hc hdeg hsome hconst

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- ★ THE FORMAL-DERIVATIVE ATOM (UNCONDITIONAL, abstract, checker-free): the engine's term-by-term
-- antiderivative `cIntegratePolyG` differentiates back to its integrand, `D(toPolyG (cIntegratePolyG c))
-- = toPolyG c` over `(CFieldSpec.K α)[X]` — proven, no runtime check.
example [CharZero (CFieldSpec.K α)] (c : CPolyG α) :
    Polynomial.derivative (toPolyG (CPolyG.cIntegratePolyG c)) = toPolyG c :=
  derivative_toPolyG_cIntegratePolyG c

-- ★ THE CRUX (checker self-discharge): the polynomial-branch output PASSES `checkIdentityG` abstractly
-- (no check executed) — the missing link `algorithm-output ⟹ check-passes` for the reachable branch.
example [CharZero (CFieldSpec.K α)] (c : CPolyG α)
    (hconst : Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) = 0) :
    CPolyG.checkIdentityG ([CField.one] : CPolyG α)
        ⟨(CPolyG.cIntegratePolyG c, ([CField.one] : CPolyG α)), []⟩ c ([CField.one] : CPolyG α)
      = true :=
  checkIdentityG_cIntegratePolyG_const c hconst

-- ★ THE DELIVERABLE at `α = QFunNZG ℚ`: `cPolyRischDEG = some q ⟹ D(res) = integrand` over `RatFunc ℚ`,
-- checker-free (the `checkIdentityG` guard is never run; no native_decide).
example (fuel : ℕ) (c q : CPolyG (QFunNZG ℚ)) (n : ℤ)
    (hc : CPolyG.cisZeroG c = false) (hdeg : (CPolyG.cdegG c : ℤ) + 1 ≤ n)
    (hsome : CPolyG.cPolyRischDEG ([CField.one] : CPolyG (QFunNZG ℚ)) fuel
        ([] : CPolyG (QFunNZG ℚ)) c n = some q)
    (hconst : Differential.mapCoeffs (toPolyG q) = 0) :
    towerFractionFieldDerivG ([CField.one] : CPolyG (QFunNZG ℚ))
        (amG (QFunNZG ℚ) (toPolyG q) / amG (QFunNZG ℚ) (toPolyG ([CField.one] : CPolyG (QFunNZG ℚ))))
      = amG (QFunNZG ℚ) (toPolyG c)
          / amG (QFunNZG ℚ) (toPolyG ([CField.one] : CPolyG (QFunNZG ℚ))) :=
  field_identity_of_cPolyRischDEG_qfunNZG fuel c q n hc hdeg hsome hconst

-- ★ CONSTANT-BASE TRANSPORT (conditional): integrand coefficients differential-constant ⟹ antiderivative
-- coefficients differential-constant (`mapCoeffs (toPolyG c) = 0 → mapCoeffs (toPolyG (cIntegratePolyG c))
-- = 0`) — the hypothesis is genuinely needed (the two conditions are equivalent).
example [CharZero (CFieldSpec.K α)] (c : CPolyG α)
    (hc : Differential.mapCoeffs (toPolyG c) = 0) :
    Differential.mapCoeffs (toPolyG (CPolyG.cIntegratePolyG c)) = 0 :=
  cIntegratePolyG_const_coeff c hc

-- ★ POLY-RDE SOUNDNESS keyed on the INTEGRAND (`b = 0` branch, primitive base): `cPolyRischDEG = some q`
-- with `mapCoeffs (toPolyG c) = 0` ⟹ `D(amG q/amG 1) = amG c/amG 1`, checker-free.
example [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCore α] [CRischField α]
    (fuel : ℕ) (c q : CPolyG α) (n : ℤ)
    (hc : CPolyG.cisZeroG c = false) (hdeg : (CPolyG.cdegG c : ℤ) + 1 ≤ n)
    (hsome : CPolyG.cPolyRischDEG ([CField.one] : CPolyG α) fuel ([] : CPolyG α) c n = some q)
    (hconst : Differential.mapCoeffs (toPolyG c) = 0) :
    towerFractionFieldDerivG ([CField.one] : CPolyG α)
        (amG α (toPolyG q) / amG α (toPolyG ([CField.one] : CPolyG α)))
      = amG α (toPolyG c) / amG α (toPolyG ([CField.one] : CPolyG α)) :=
  cPolyRischDEG_nil_field_identity fuel c q n hc hdeg hsome hconst

/-! ## ★★ The §6.6 CANCELLATION-case soundness (the broader poly-RDE, `b ≠ 0`, `deg b = 0`)

The `b = []` arc above is the *non-cancellation* `b = 0` pure-integration branch. The genuinely harder
reachable arms of `cPolyRischDEG` are the §6.6 **cancellation** cases (Bronstein p.212/213): when `deg(b) = 0`
(a degree-0 `t`-polynomial `b ∈ α*`) the leading terms of `Dq` and `b·q` cancel, so the solve recurses
degree-by-degree into the base RDE `crischDESolve b₀ (lc c)` (eq. 6.23, primitive) /
`crischDESolve (b₀ + m·η) (lc c)` (eq. 6.24, hyperexponential). These are `cPolyRischDECancelPrimG` /
`cPolyRischDECancelExpG`, which the dispatcher routes the primitive (`δ = 0`) / hyperexponential (`δ = 1`)
regimes into — the full-Risch poly-RDE beyond the `cIntegrateGFull` driver (which only hits `b = []`).

★ **The soundness needs NO base-oracle correctness.** The base solve `crischDESolve b₀ (lc c) = some s`
returns *some* `s`; the algorithm then subtracts `c ← c − b·(s·tᵐ) − D(s·tᵐ)` and recurses. Whatever `s`
is, this per-step subtraction makes the assembled `Dq + b·q = c` **telescope exactly** — the base solve's
correctness (the abstract `CRischFieldSpec.crischDESolve_spec`) only governs *whether* the recursion makes
progress (termination/completeness), not the soundness of the identity it returns. So the cancellation-case
soundness is a clean fuel induction over `toPolyG`, NO `[CRischFieldSpec α]` hypothesis needed — the base
solve enters as an opaque `some s`. This is the same shape as `derivative_toPolyG_cIntegratePolyG` (an
unconditional algorithm-correctness atom), now for the cancellation recursion. -/

section Cancellation

variable [CRischField α]

/-- **★ Primitive cancellation poly-RDE is sound** (`toPolyG_cmonomialDeriv_cPolyRischDECancelPrim`),
checker-free and base-oracle-free: if `cPolyRischDECancelPrimG Dt fuel b c n = some q` then the assembled
`q` solves `Dq + b·q = c` at the polynomial level — `toPolyG (cmonomialDeriv Dt q) + toPolyG b · toPolyG q
= toPolyG c` over `(CFieldSpec.K α)[X]`. Fuel induction: the base (`cisZeroG c`, `q = []`) gives
`0 = toPolyG c` (`cisZeroG_iff`); the step assembles `q = s·tᵐ + q'` with the IH `Dq' + b·q' = c'` and
`c' = c − b·(s·tᵐ) − D(s·tᵐ)`, telescoping to `Dq + b·q = c` by `linear_combination` (the derivation
`cmonomialDeriv = implicitDeriv` is additive). The base solve `crischDESolve b₀ (lc c) = some s` enters as
an OPAQUE witness — its correctness is irrelevant to the identity (only to termination), so NO
`[CRischFieldSpec α]`. -/
theorem toPolyG_cmonomialDeriv_cPolyRischDECancelPrim (Dt b : CPolyG α) :
    ∀ (fuel : ℕ) (c : CPolyG α) (n : ℤ) (q : CPolyG α),
      CPolyG.cPolyRischDECancelPrimG Dt fuel b c n = some q →
      toPolyG (CPolyG.cmonomialDeriv Dt q) + toPolyG b * toPolyG q = toPolyG c := by
  intro fuel
  induction fuel with
  | zero =>
    intro c n q hsolve
    rw [CPolyG.cPolyRischDECancelPrimG] at hsolve
    exact absurd hsolve (by simp)
  | succ fuel ih =>
    intro c n q hsolve
    rw [CPolyG.cPolyRischDECancelPrimG] at hsolve
    simp only at hsolve
    by_cases hc : CPolyG.cisZeroG c = true
    · rw [if_pos hc, Option.some.injEq] at hsolve
      subst hsolve
      rw [(cisZeroG_iff c).mp hc, toPolyG_cmonomialDeriv, toPolyG_nil, map_zero, mul_zero, add_zero]
    · rw [if_neg hc] at hsolve
      by_cases hn : n < (CPolyG.cdegG c : ℤ)
      · rw [if_pos hn] at hsolve; exact absurd hsolve (by simp)
      · rw [if_neg hn] at hsolve
        split at hsolve
        · exact absurd hsolve (by simp)
        · rename_i s _hbase
          split at hsolve
          · exact absurd hsolve (by simp)
          · rename_i q' hrec
            rw [Option.some.injEq] at hsolve
            subst hsolve
            have hih := ih _ _ q' hrec
            simp only [toPolyG_cmonomialDeriv, toPolyG_caddG, toPolyG_csubG, toPolyG_cmulG,
              map_add] at hih ⊢
            linear_combination hih

/-- **★ Hyperexponential cancellation poly-RDE is sound** (`toPolyG_cmonomialDeriv_cPolyRischDECancelExp`),
checker-free and base-oracle-free: if `cPolyRischDECancelExpG Dt fuel b c n = some q` then `Dq + b·q = c`
at the polynomial level — `toPolyG (cmonomialDeriv Dt q) + toPolyG b · toPolyG q = toPolyG c` over
`(CFieldSpec.K α)[X]`. Identical telescoping fuel induction to the primitive case
(`toPolyG_cmonomialDeriv_cPolyRischDECancelPrim`); the only algorithmic difference is the base RDE's shifted
coefficient `b₀ + m·η` (eq. 6.24), but the returned `s` again enters opaquely, so the per-step subtraction
`c ← c − b·(s·tᵐ) − D(s·tᵐ)` telescopes the same way. NO `[CRischFieldSpec α]` hypothesis. -/
theorem toPolyG_cmonomialDeriv_cPolyRischDECancelExp (Dt b : CPolyG α) :
    ∀ (fuel : ℕ) (c : CPolyG α) (n : ℤ) (q : CPolyG α),
      CPolyG.cPolyRischDECancelExpG Dt fuel b c n = some q →
      toPolyG (CPolyG.cmonomialDeriv Dt q) + toPolyG b * toPolyG q = toPolyG c := by
  intro fuel
  induction fuel with
  | zero =>
    intro c n q hsolve
    rw [CPolyG.cPolyRischDECancelExpG] at hsolve
    exact absurd hsolve (by simp)
  | succ fuel ih =>
    intro c n q hsolve
    rw [CPolyG.cPolyRischDECancelExpG] at hsolve
    simp only at hsolve
    by_cases hc : CPolyG.cisZeroG c = true
    · rw [if_pos hc, Option.some.injEq] at hsolve
      subst hsolve
      rw [(cisZeroG_iff c).mp hc, toPolyG_cmonomialDeriv, toPolyG_nil, map_zero, mul_zero, add_zero]
    · rw [if_neg hc] at hsolve
      by_cases hn : n < (CPolyG.cdegG c : ℤ)
      · rw [if_pos hn] at hsolve; exact absurd hsolve (by simp)
      · rw [if_neg hn] at hsolve
        split at hsolve
        · exact absurd hsolve (by simp)
        · rename_i s _hbase
          split at hsolve
          · exact absurd hsolve (by simp)
          · rename_i q' hrec
            rw [Option.some.injEq] at hsolve
            subst hsolve
            have hih := ih _ _ q' hrec
            simp only [toPolyG_cmonomialDeriv, toPolyG_caddG, toPolyG_csubG, toPolyG_cmulG,
              map_add] at hih ⊢
            linear_combination hih

/-! ### The dispatcher routes the cancellation regimes (Lemma 6.5.1)

`cPolyRischDEG` routes by `δ = deg(Dt)` and `deg(b)`. With `b ≠ 0` of degree `0`: the primitive regime
(`δ = 0`) goes to `cPolyRischDECancelPrimG`, the hyperexponential regime (`δ = 1`) to
`cPolyRischDECancelExpG`. These pin the dispatcher to the cancellation solvers (the cancellation analogue of
`cPolyRischDEG_eq_noCancel_of_primitive`, `ComputableRischDEStructural`). -/

omit [CFieldSpec α] [CDiffFieldSpec α] in
/-- **The §6.5/§6.6 dispatcher reduces to the primitive cancellation solve** in the primitive regime with
`deg(b) = 0`, `b ≠ 0`: if `cdegG Dt = 0`, `cdegG b = 0`, `cisZeroG b = false` then
`cPolyRischDEG Dt fuel b c m = cPolyRischDECancelPrimG Dt fuel b c m`. The `δ = 0 ∧ deg(b) = 0` routing arm
of Lemma 6.5.1. -/
theorem cPolyRischDEG_eq_cancelPrim (Dt : CPolyG α) (fuel : ℕ) (b c : CPolyG α) (m : ℤ)
    (hδ : CPolyG.cdegG Dt = 0) (hdb : CPolyG.cdegG b = 0) (hb : CPolyG.cisZeroG b = false) :
    CPolyG.cPolyRischDEG Dt fuel b c m = CPolyG.cPolyRischDECancelPrimG Dt fuel b c m := by
  rw [CPolyG.cPolyRischDEG]
  simp only [hb, Bool.false_eq_true, if_false, hδ, hdb, Nat.cast_zero]
  rw [if_neg (by norm_num), if_pos ⟨trivial, trivial⟩]

omit [CFieldSpec α] [CDiffFieldSpec α] in
/-- **The §6.5/§6.6 dispatcher reduces to the hyperexponential cancellation solve** in the
hyperexponential regime with `deg(b) = 0`, `b ≠ 0`: if `cdegG Dt = 1`, `cdegG b = 0`, `cisZeroG b = false`
then `cPolyRischDEG Dt fuel b c m = cPolyRischDECancelExpG Dt fuel b c m`. The `δ = 1 ∧ deg(b) = 0` routing
arm of Lemma 6.5.1. -/
theorem cPolyRischDEG_eq_cancelExp (Dt : CPolyG α) (fuel : ℕ) (b c : CPolyG α) (m : ℤ)
    (hδ : CPolyG.cdegG Dt = 1) (hdb : CPolyG.cdegG b = 0) (hb : CPolyG.cisZeroG b = false) :
    CPolyG.cPolyRischDEG Dt fuel b c m = CPolyG.cPolyRischDECancelExpG Dt fuel b c m := by
  rw [CPolyG.cPolyRischDEG]
  simp only [hb, Bool.false_eq_true, if_false, hδ, hdb, Nat.cast_zero, Nat.cast_one]
  rw [if_neg (by norm_num), if_neg (by norm_num), if_pos ⟨trivial, trivial⟩]

/-- **★ Dispatcher-keyed primitive-cancellation soundness** (`cPolyRischDEG_cancelPrim_sound`): in the
primitive regime (`cdegG Dt = 0`, `deg(b) = 0`, `b ≠ 0`), a dispatcher success
`cPolyRischDEG Dt fuel b c m = some q` solves `Dq + b·q = c` at the polynomial level. Composes the routing
`cPolyRischDEG_eq_cancelPrim` with the cancellation soundness
`toPolyG_cmonomialDeriv_cPolyRischDECancelPrim`. -/
theorem cPolyRischDEG_cancelPrim_sound (Dt b c q : CPolyG α) (fuel : ℕ) (m : ℤ)
    (hδ : CPolyG.cdegG Dt = 0) (hdb : CPolyG.cdegG b = 0) (hb : CPolyG.cisZeroG b = false)
    (hsome : CPolyG.cPolyRischDEG Dt fuel b c m = some q) :
    toPolyG (CPolyG.cmonomialDeriv Dt q) + toPolyG b * toPolyG q = toPolyG c := by
  rw [cPolyRischDEG_eq_cancelPrim Dt fuel b c m hδ hdb hb] at hsome
  exact toPolyG_cmonomialDeriv_cPolyRischDECancelPrim Dt b fuel c m q hsome

/-- **★ Dispatcher-keyed hyperexponential-cancellation soundness** (`cPolyRischDEG_cancelExp_sound`): in
the hyperexponential regime (`cdegG Dt = 1`, `deg(b) = 0`, `b ≠ 0`), a dispatcher success
`cPolyRischDEG Dt fuel b c m = some q` solves `Dq + b·q = c` at the polynomial level. Composes the routing
`cPolyRischDEG_eq_cancelExp` with `toPolyG_cmonomialDeriv_cPolyRischDECancelExp`. -/
theorem cPolyRischDEG_cancelExp_sound (Dt b c q : CPolyG α) (fuel : ℕ) (m : ℤ)
    (hδ : CPolyG.cdegG Dt = 1) (hdb : CPolyG.cdegG b = 0) (hb : CPolyG.cisZeroG b = false)
    (hsome : CPolyG.cPolyRischDEG Dt fuel b c m = some q) :
    toPolyG (CPolyG.cmonomialDeriv Dt q) + toPolyG b * toPolyG q = toPolyG c := by
  rw [cPolyRischDEG_eq_cancelExp Dt fuel b c m hδ hdb hb] at hsome
  exact toPolyG_cmonomialDeriv_cPolyRischDECancelExp Dt b fuel c m q hsome

/-! ### ★ The field-level lift of the cancellation soundness

The polynomial identity `Dq + b·q = c` over `(CFieldSpec.K α)[X]` lifts to the tower fraction field
`RatFunc (CFieldSpec.K α)` by pushing `towerFractionFieldDerivG` onto the polynomial image
(`extendDeriv_algebraMap`) and using that `amG` is a ring hom. This mirrors
`towerFractionFieldDerivG_amG_cIntegratePolyG_const` for the `b = []` branch — but with the genuine
`b ≠ 0` term carried through. -/

variable [Algebra ℚ (CFieldSpec.K α)]

omit [CRischField α] in
/-- **★ Field-level lift of a polynomial Risch-DE identity**
(`towerFractionFieldDerivG_amG_of_polyIdentity`): from `Dq + b·q = c` over `(CFieldSpec.K α)[X]` (the
`cmonomialDeriv`/`toPolyG` form), the tower fraction-field identity `towerFractionFieldDerivG Dt (amG q)
+ amG b · amG q = amG c` over `RatFunc (CFieldSpec.K α)`. `extendDeriv_algebraMap` pushes the field
derivation onto the polynomial image (`= amG (cmonomialDeriv Dt q)`), and `amG`'s ring-hom
`map_add`/`map_mul` collapse the cleared identity. The generic bridge under which both cancellation
soundnesses become field-level `D(q) + b·q = c`. -/
theorem towerFractionFieldDerivG_amG_of_polyIdentity (Dt b c q : CPolyG α)
    (hpoly : toPolyG (CPolyG.cmonomialDeriv Dt q) + toPolyG b * toPolyG q = toPolyG c) :
    towerFractionFieldDerivG Dt (amG α (toPolyG q))
        + amG α (toPolyG b) * amG α (toPolyG q)
      = amG α (toPolyG c) := by
  rw [towerFractionFieldDerivG, extendDeriv_algebraMap, ← toPolyG_cmonomialDeriv,
    ← map_mul, ← map_add, hpoly]

/-- **★★ Field-level primitive-cancellation soundness** (`cPolyRischDEG_cancelPrim_field`): the headline
cancellation-case deliverable. In the primitive regime (`cdegG Dt = 0`, `deg(b) = 0`, `b ≠ 0`), a
dispatcher success `cPolyRischDEG Dt fuel b c m = some q` solves the field-level Risch DE
`towerFractionFieldDerivG Dt (amG q) + amG b · amG q = amG c` over `RatFunc (CFieldSpec.K α)` — **no
`checkIdentityG`, no `native_decide`, no base-oracle correctness `[CRischFieldSpec α]`**. Composes
`cPolyRischDEG_cancelPrim_sound` (polynomial soundness) with `towerFractionFieldDerivG_amG_of_polyIdentity`
(field lift). The §6.6 primitive cancellation case bridged to the field level, base-oracle-free. -/
theorem cPolyRischDEG_cancelPrim_field (Dt b c q : CPolyG α) (fuel : ℕ) (m : ℤ)
    (hδ : CPolyG.cdegG Dt = 0) (hdb : CPolyG.cdegG b = 0) (hb : CPolyG.cisZeroG b = false)
    (hsome : CPolyG.cPolyRischDEG Dt fuel b c m = some q) :
    towerFractionFieldDerivG Dt (amG α (toPolyG q))
        + amG α (toPolyG b) * amG α (toPolyG q)
      = amG α (toPolyG c) :=
  towerFractionFieldDerivG_amG_of_polyIdentity Dt b c q
    (cPolyRischDEG_cancelPrim_sound Dt b c q fuel m hδ hdb hb hsome)

/-- **★★ Field-level hyperexponential-cancellation soundness** (`cPolyRischDEG_cancelExp_field`): in the
hyperexponential regime (`cdegG Dt = 1`, `deg(b) = 0`, `b ≠ 0`), a dispatcher success
`cPolyRischDEG Dt fuel b c m = some q` solves the field-level Risch DE `towerFractionFieldDerivG Dt (amG q)
+ amG b · amG q = amG c` over `RatFunc (CFieldSpec.K α)` — no `checkIdentityG`, no `native_decide`, no
`[CRischFieldSpec α]`. Composes `cPolyRischDEG_cancelExp_sound` with
`towerFractionFieldDerivG_amG_of_polyIdentity`. The §6.6 hyperexponential cancellation case at the field
level, base-oracle-free. -/
theorem cPolyRischDEG_cancelExp_field (Dt b c q : CPolyG α) (fuel : ℕ) (m : ℤ)
    (hδ : CPolyG.cdegG Dt = 1) (hdb : CPolyG.cdegG b = 0) (hb : CPolyG.cisZeroG b = false)
    (hsome : CPolyG.cPolyRischDEG Dt fuel b c m = some q) :
    towerFractionFieldDerivG Dt (amG α (toPolyG q))
        + amG α (toPolyG b) * amG α (toPolyG q)
      = amG α (toPolyG c) :=
  towerFractionFieldDerivG_amG_of_polyIdentity Dt b c q
    (cPolyRischDEG_cancelExp_sound Dt b c q fuel m hδ hdb hb hsome)

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- ★ Primitive cancellation poly-RDE soundness, checker-free and base-oracle-free: `cPolyRischDECancelPrimG
-- = some q ⟹ Dq + b·q = c` over `(CFieldSpec.K α)[X]`, NO `[CRischFieldSpec α]`.
example (Dt b : CPolyG α) (fuel : ℕ) (c : CPolyG α) (n : ℤ) (q : CPolyG α)
    (h : CPolyG.cPolyRischDECancelPrimG Dt fuel b c n = some q) :
    toPolyG (CPolyG.cmonomialDeriv Dt q) + toPolyG b * toPolyG q = toPolyG c :=
  toPolyG_cmonomialDeriv_cPolyRischDECancelPrim Dt b fuel c n q h

-- ★★ Field-level primitive-cancellation soundness via the dispatcher (the broader full-Risch poly-RDE),
-- checker-free, base-oracle-free: `cPolyRischDEG = some q` ⟹ `D(amG q) + amG b · amG q = amG c`.
example (Dt b c q : CPolyG α) (fuel : ℕ) (m : ℤ)
    (hδ : CPolyG.cdegG Dt = 0) (hdb : CPolyG.cdegG b = 0) (hb : CPolyG.cisZeroG b = false)
    (hsome : CPolyG.cPolyRischDEG Dt fuel b c m = some q) :
    towerFractionFieldDerivG Dt (amG α (toPolyG q))
        + amG α (toPolyG b) * amG α (toPolyG q)
      = amG α (toPolyG c) :=
  cPolyRischDEG_cancelPrim_field Dt b c q fuel m hδ hdb hb hsome

end Cancellation

/-! ### Axiom audit — the one-shot rests only on the standard kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`); no `native_decide`, no `sorry`. -/

#print axioms derivative_toPolyG_cIntegratePolyG
#print axioms toPolyG_cmonomialDeriv_cIntegratePolyG_const
#print axioms towerFractionFieldDerivG_amG_cIntegratePolyG_const
#print axioms checkIdentityG_cIntegratePolyG_const
#print axioms field_identity_cIntegratePolyG_const
#print axioms field_identity_of_cPolyRischDEG
#print axioms field_identity_of_cPolyRischDEG_qfunNZG
#print axioms mapCoeffs_derivative_commute
#print axioms cIntegratePolyG_const_coeff
#print axioms cPolyRischDEG_nil_field_identity
#print axioms toPolyG_cmonomialDeriv_cPolyRischDECancelPrim
#print axioms toPolyG_cmonomialDeriv_cPolyRischDECancelExp
#print axioms cPolyRischDEG_cancelPrim_field
#print axioms cPolyRischDEG_cancelExp_field

end DeepWiki.SymbolicIntegration
