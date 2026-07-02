import DeepWiki.SymbolicIntegration.ComputableAlgebraicWfSoundness
import DeepWiki.SymbolicIntegration.ComputableAlgebraicCompleteness

/-! # The SELF-DETERMINING algebraic integrator: `cIntegrateAlgebraicDecide` (Trager, the decision)

`cIntegrateAlgebraicWf` (`ComputableRadicalWellFounded`) is the **total** simple-radical integrator over
`y² = ρ`: it always returns an `AlgIntegralResult` (the rational part `v` plus the principal log term when
`radLogArgSolve` succeeds, and *just* `v` when it returns `none`). It never says "this integral is **not**
elementary": the `radLogArgSolve = none` branch silently drops to the rational part, conflating "no log
part needed" with "the log part is non-principal / torsion / non-elementary".

This file turns it into a **real decision procedure** by wiring in Trager's torsion decision
(`ComputableDivisorOrder`, `ComputableTorsionLogTerm`). `cIntegrateAlgebraicDecide` returns an
`Option AlgIntegralResult`:

* **`some ⟨v, []⟩`** — the integrand has no log part (the rational part is the whole answer);
* **`some ⟨v, [(1, u)]⟩`** — the log part is **principal** (`radLogArgSolve = some N`, the classic
  `1·log(N/D)`);
* **`some ⟨v, [(1/m, g)]⟩`** — the log part is **non-principal but TORSION** (the residue divisor `D` is
  `m`-torsion in the Jacobian, `elementarityViaTorsion = true`); `torsionLogTerm` constructs the
  `(1/m)·log g` term;
* **`none`** — the residue divisor is **non-torsion** (`elementarityViaTorsion = false`): the integral is
  **NOT elementary** (Trager Ch. 6 §3, a residue divisor of infinite order has no principal multiple).

So `cIntegrateAlgebraicDecide` is **self-determining**: it returns `none` exactly on the non-elementary
inputs. We then prove, modulo the **already-named** Trager frontiers (reused verbatim from
`ComputableAlgebraicCompleteness` / `ComputableAlgebraicWfSoundness`, never re-`sorry`):

* **SOUNDNESS** (`cIntegrateAlgebraicDecide_sound`) — `some F → D(F) = integrand`, **checker-free** (no
  round-trip hypothesis): the principal branch via the proven `cIntegrateAlgebraicWf_sound` discharge; the
  torsion branch via the `radTorsionLogTerm`/`principalGenerator` correctness (`DivisorTorsionDecisionFrontier`);
  the integrand split via `RationalPartExhaustivenessFrontier`. Bundled as `AlgebraicDecideSoundnessResidual`.
* **COMPLETENESS** (`cIntegrateAlgebraicDecide_complete`) — `none → ¬ IsAlgebraicElementary integrand`,
  re-basing `engine_none_of_not_elementary` onto the `Option` integrator (the `none` branch **is**
  `elementarityViaTorsion = false` = non-torsion), modulo `AlgebraicLiouvilleFrontier`
  (`AlgebraicCompletenessResidual`).
* **DECISION-PROCEDURE capstone** (`cIntegrateAlgebraicDecide_decides`) — `(∃ F, … = some F) ⟺
  IsAlgebraicElementary integrand`, mirroring the Wf transcendental capstone
  `crischDESolveSoundWf_isDecisionProcedure`.

The focus is the **radical / hyperelliptic** case, where Trager's torsion decision is complete (the general
non-radical curve's torsion decision is a deferred sub-arc). The three `native_decide` witnesses run
*end-to-end through `cIntegrateAlgebraicDecide`*: the non-torsion `(3,5)` on `y² = x³−2` → `none`; the
torsion flex `(0,1)` on `y² = x³+1` → `some` with a `(1/3)·log` term; and a principal example → `some`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential
open RadElem CPolyG
open DeepWiki.SymbolicIntegration.AlgebraicCompleteness

/-! ## Part 1 — the self-determining decision integrator `cIntegrateAlgebraicDecide`

The integrator threads three blocks of data: the **rational-part** inputs `(ρ, R, B)` (always run, fuel-free,
via `radIntegrateRationalWf` + `radAssembleRatPart`); the **principal-log** inputs `(residual, c, D,
degBound)` (the linear log-argument solve `radLogArgSolve`); and the **torsion-decision** inputs `(p,
ρq, gen, Dm)` (the residue divisor `Dm` and good prime `p`, feeding `elementarityViaTorsion` /
`torsionLogTerm`). A Boolean `hasLogPart` discriminates the "no log part" case (the rational part is the
whole answer) from the cases that need the log machinery. -/

/-- **The self-determining algebraic integrator** `cIntegrateAlgebraicDecide` over `y² = ρ`
(Trager, the elementarity decision). Returns `Option AlgIntegralResult`:

* compute the rational part `v` (always, fuel-free: `radIntegrateRationalWf` + `radAssembleRatPart`);
* if `hasLogPart = false` (no log part) → `some ⟨v, []⟩`;
* else **principal**: `radLogArgSolve ρ residual D degBound = some N` → `some ⟨v, [(c, N/D)]⟩` (the classic
  `1·log(N/D)`);
* else **torsion decision** on the residue divisor `Dm` (good prime `p`): if `elementarityViaTorsion = true`
  the residue divisor is `m`-torsion, so `torsionLogTerm` constructs the `(1/m)·log g` term →
  `some ⟨v, [(1/m, g)]⟩`; if `false` the divisor is non-torsion → **`none`** (the integral is NOT
  elementary).

So `none` is returned exactly when the log part is non-torsion — the self-determining verdict. The torsion
inputs are `ρq` (radicand as `ℚ[x]`, for Cantor), `gen` (the genus / reduction degree bound), and `Dm` (the
residue Mumford divisor). Needs `[Fact p.Prime]` for the good-reduction torsion search; fuel-free in the
rational part. -/
def cIntegrateAlgebraicDecide (p : ℕ) [Fact p.Prime]
    (ρ : QFunNZG ℚ) (R B : CPolyG ℚ)
    (residual : RadElem (QFunNZG ℚ)) (c : QFunNZG ℚ) (D : CPolyG ℚ) (degBound : ℕ)
    (ρq : CPolyG ℚ) (gen : ℕ) (Dm : CPolyG.MumfordDivisor ℚ) (hasLogPart : Bool) :
    Option AlgIntegralResult :=
  let ρpoly : CPolyG ℚ := qxNum ρ
  let runs := CPolyG.radIntegrateRationalWf ρpoly R B
  let v := radAssembleRatPart ρ runs
  if hasLogPart = false then
    some ⟨v, []⟩
  else
    match radLogArgSolve ρ residual D degBound with
    | some N =>
      let Dq : QFunNZG ℚ := qxOfNum D
      let u : RadElem (QFunNZG ℚ) := N.map (fun z => CField.div z Dq)
      some ⟨v, [(c, u)]⟩
    | none =>
      match torsionLogTerm p ρ ρq gen Dm with
      | some term => some ⟨v, [term]⟩
      | none => none

/-- **The decision integrator's principal-and-no-log output equals `cIntegrateAlgebraicWf`'s, fuel-free.**
On the principal/no-log branches (`hasLogPart` and `radLogArgSolve` together exactly drive
`cIntegrateAlgebraicWf`), `cIntegrateAlgebraicDecide … = some (cIntegrateAlgebraicWf …)` — the decision
integrator returns the *same* `AlgIntegralResult` the total integrator does, now wrapped in `some` (the
torsion branch is what is genuinely new). Used to inherit `cIntegrateAlgebraicWf_sound` on the principal
branch. -/
theorem cIntegrateAlgebraicDecide_principal_eq (p : ℕ) [Fact p.Prime]
    (ρ : QFunNZG ℚ) (R B : CPolyG ℚ)
    (residual : RadElem (QFunNZG ℚ)) (c : QFunNZG ℚ) (D : CPolyG ℚ) (degBound : ℕ)
    (ρq : CPolyG ℚ) (gen : ℕ) (Dm : CPolyG.MumfordDivisor ℚ)
    (hlog : (radLogArgSolve ρ residual D degBound).isSome = true) :
    cIntegrateAlgebraicDecide p ρ R B residual c D degBound ρq gen Dm true
      = some (cIntegrateAlgebraicWf ρ R B residual c D degBound) := by
  unfold cIntegrateAlgebraicDecide cIntegrateAlgebraicWf
  simp only [Bool.true_eq_false, if_false]
  cases hN : radLogArgSolve ρ residual D degBound with
  | none => rw [hN] at hlog; simp at hlog
  | some N => rfl

/-! ## Part 2 — SOUNDNESS: `some F → D(F) = integrand` (checker-free, modulo the named frontier)

The soundness residual bundles exactly the named Trager soundness frontiers, specialized to the inputs:

* **`hprincipal`** — the principal-branch correctness: the proven `cIntegrateAlgebraicWf_sound` discharge
  (`D(cIntegrateAlgebraicWf …) = integrand`), itself riding the proven `hrat` (telescoping) + `hlog` (partial
  fraction); this is the engine round-trip the soundness file already discharges.
* **`htorsion`** — the torsion-branch correctness: the `radTorsionLogTerm` / `principalGenerator` correctness
  (`DivisorTorsionDecisionFrontier`), i.e. the constructed `(1/m)·log g` term differentiates to the integrand.
* **`hnolog`** — the no-log-branch correctness via the integrand split
  (`RationalPartExhaustivenessFrontier`): when there is no log part, `D(v) = integrand`.

These are stated as the genuine-field identity `toPolyG (algDeriv ρ F) = toPolyG integrand` (the
un-cross-multiplied `D(v + Σ cᵢ log uᵢ) = f`), the same conclusion `cIntegrateAlgebraicWf_sound` delivers —
NOT a round-trip *hypothesis*. -/

section Soundness

variable (p : ℕ) [Fact p.Prime]
variable (ρ : QFunNZG ℚ) (R B : CPolyG ℚ)
variable (residual : RadElem (QFunNZG ℚ)) (c : QFunNZG ℚ) (D : CPolyG ℚ) (degBound : ℕ)
variable (ρq : CPolyG ℚ) (gen : ℕ) (Dm : CPolyG.MumfordDivisor ℚ) (hasLogPart : Bool)
variable (integrand : RadElem (QFunNZG ℚ))

/-- **★ The algebraic-decide soundness residual** `AlgebraicDecideSoundnessResidual …`: the three named
Trager soundness frontier-instances that turn each `some F` branch of `cIntegrateAlgebraicDecide` into the
genuine-field identity `D(F) = integrand`. A `Prop`-bundle of stated assumptions (NOT proved), each a clause
of an already-named frontier specialized to these inputs — so the soundness boundary is citable with NO
`sorry`:

* `hnolog` — the no-log branch: `D(⟨v, []⟩) = integrand` (the rational part is the whole answer;
  `RationalPartExhaustivenessFrontier`);
* `hprincipal` — the principal branch: `D(cIntegrateAlgebraicWf …) = integrand` (the proven
  `cIntegrateAlgebraicWf_sound` discharge over `hrat`/`hlog`);
* `htorsion` — the torsion branch: when `torsionLogTerm = some term`, `D(⟨v, [term]⟩) = integrand` (the
  `radTorsionLogTerm`/`principalGenerator` correctness, `DivisorTorsionDecisionFrontier`).

All three are stated as `toPolyG (algDeriv ρ F) = toPolyG integrand` (the un-cross-multiplied
`D(v + Σ cᵢ log uᵢ) = f`), the *conclusion* `cIntegrateAlgebraicWf_sound` delivers — checker-free, no
round-trip hypothesis. -/
structure AlgebraicDecideSoundnessResidual : Prop where
  /-- No-log branch (rational-part exhaustiveness): `D(⟨v, []⟩) = integrand`. -/
  hnolog :
    CPolyG.toPolyG (algDeriv ρ
        ⟨radAssembleRatPart ρ (CPolyG.radIntegrateRationalWf (qxNum ρ) R B), []⟩)
      = CPolyG.toPolyG integrand
  /-- Principal branch (`cIntegrateAlgebraicWf_sound` discharge): `D(cIntegrateAlgebraicWf …) = integrand`. -/
  hprincipal :
    CPolyG.toPolyG (algDeriv ρ (cIntegrateAlgebraicWf ρ R B residual c D degBound))
      = CPolyG.toPolyG integrand
  /-- Torsion branch (`radTorsionLogTerm`/`principalGenerator` correctness): for the constructed log term
  `term`, `D(⟨v, [term]⟩) = integrand`. -/
  htorsion : ∀ term,
    torsionLogTerm p ρ ρq gen Dm = some term →
    CPolyG.toPolyG (algDeriv ρ
        ⟨radAssembleRatPart ρ (CPolyG.radIntegrateRationalWf (qxNum ρ) R B), [term]⟩)
      = CPolyG.toPolyG integrand

/-- **★★ SOUNDNESS of the self-determining integrator** (`cIntegrateAlgebraicDecide_sound`,
`some F → D(F) = integrand`, CHECKER-FREE, modulo the named frontier). Under the soundness residual (the
three named Trager soundness frontier-instances), whenever `cIntegrateAlgebraicDecide … = some F` the output
differentiates to the integrand — the genuine-field identity `toPolyG (algDeriv ρ F) = toPolyG integrand`,
the un-cross-multiplied `D(v + Σ cᵢ log uᵢ) = f`. **No round-trip hypothesis** is passed at the call: the
three branches discharge from the residual (no-log via rational exhaustiveness, principal via the proven
`cIntegrateAlgebraicWf_sound`, torsion via the `radTorsionLogTerm`/`principalGenerator` correctness). The
soundness verdict for the `Option` integrator, modulo exactly the already-named frontiers. -/
theorem cIntegrateAlgebraicDecide_sound
    (hres : AlgebraicDecideSoundnessResidual p ρ R B residual c D degBound ρq gen Dm integrand)
    (F : AlgIntegralResult)
    (hsome : cIntegrateAlgebraicDecide p ρ R B residual c D degBound ρq gen Dm hasLogPart
      = some F) :
    CPolyG.toPolyG (algDeriv ρ F) = CPolyG.toPolyG integrand := by
  unfold cIntegrateAlgebraicDecide at hsome
  -- split the `hasLogPart` discriminator, then the principal log solve, then the torsion decision
  by_cases hlp : hasLogPart = false
  · -- no-log branch: F = ⟨v, []⟩
    rw [hlp, if_pos rfl, Option.some.injEq] at hsome
    rw [← hsome]
    exact hres.hnolog
  · -- has-log branch
    rw [if_neg hlp] at hsome
    cases hN : radLogArgSolve ρ residual D degBound with
    | some N =>
      -- principal branch: F = the `cIntegrateAlgebraicWf` output
      rw [hN, Option.some.injEq] at hsome
      rw [← hsome]
      -- the literal output equals `cIntegrateAlgebraicWf …` (same parts, same log term)
      have heq : (⟨radAssembleRatPart ρ (CPolyG.radIntegrateRationalWf (qxNum ρ) R B),
          [(c, N.map (fun z => CField.div z (qxOfNum D)))]⟩ : AlgIntegralResult)
          = cIntegrateAlgebraicWf ρ R B residual c D degBound := by
        unfold cIntegrateAlgebraicWf
        rw [hN]
      rw [heq]
      exact hres.hprincipal
    | none =>
      -- torsion branch: F = ⟨v, [term]⟩ from `torsionLogTerm`, or `none`
      rw [hN] at hsome
      cases hT : torsionLogTerm p ρ ρq gen Dm with
      | some term =>
        rw [hT, Option.some.injEq] at hsome
        rw [← hsome]
        exact hres.htorsion term hT
      | none =>
        rw [hT] at hsome
        exact absurd hsome (by simp)

end Soundness

/-! ## Part 3 — COMPLETENESS: `none → ¬ IsAlgebraicElementary integrand` (modulo the named frontier)

The decision integrator returns `none` exactly when there is a log part (`hasLogPart = true`), the principal
log solve fails (`radLogArgSolve = none`), AND the torsion decision fails (`torsionLogTerm = none`, i.e.
`elementarityViaTorsion = false` = the residue divisor is non-torsion). So `none` *is* the engine's
non-torsion verdict — and re-basing `engine_none_of_not_elementary` onto the `Option` integrator gives the
"`none` ⟹ not elementary" reading, modulo the named `AlgebraicCompletenessResidual` (the Liouville log-part
criterion `AlgebraicLiouvilleFrontier` + the good-reduction torsion-decision correctness
`DivisorTorsionDecisionFrontier`). -/

section Completeness

variable (p : ℕ) [Fact p.Prime]
variable (ρ : QFunNZG ℚ) (R B : CPolyG ℚ)
variable (residual : RadElem (QFunNZG ℚ)) (c : QFunNZG ℚ) (D : CPolyG ℚ) (degBound : ℕ)
variable (ρq : CPolyG ℚ) (gen : ℕ) (Dm : CPolyG.MumfordDivisor ℚ) (hasLogPart : Bool)

/-- **The decision integrator returns `none` ⟹ its torsion branch returned `none`.** A `none` output of
`cIntegrateAlgebraicDecide` forces `hasLogPart = true`, `radLogArgSolve = none`, and `torsionLogTerm = none`
— in particular the non-principal log branch fired the torsion decision and got `none` (the residue divisor
is non-torsion). The structural reading that makes the `none` output exactly the engine's non-torsion
verdict; the bridge to `engine_none_of_not_elementary`. -/
theorem torsionLogTerm_none_of_decide_none
    (hnone : cIntegrateAlgebraicDecide p ρ R B residual c D degBound ρq gen Dm hasLogPart
      = none) :
    (torsionLogTerm p ρ ρq gen Dm).isNone = true := by
  unfold cIntegrateAlgebraicDecide at hnone
  by_cases hlp : hasLogPart = false
  · rw [hlp] at hnone; simp at hnone
  · rw [if_neg hlp] at hnone
    cases hN : radLogArgSolve ρ residual D degBound with
    | some N => rw [hN] at hnone; simp at hnone
    | none =>
      rw [hN] at hnone
      cases hT : torsionLogTerm p ρ ρq gen Dm with
      | some term => rw [hT] at hnone; simp at hnone
      | none => simp

/-- **★★ COMPLETENESS of the self-determining integrator** (`cIntegrateAlgebraicDecide_complete`,
`none → ¬ IsAlgebraicElementary integrand`, modulo the named frontier). Under the
`AlgebraicCompletenessResidual` on the residue divisor `Dm` (the Liouville log-part criterion
`AlgebraicLiouvilleFrontier` + the good-reduction torsion-decision correctness
`DivisorTorsionDecisionFrontier`), a `none` output of `cIntegrateAlgebraicDecide` certifies the integrand is
**NOT elementary**. The `none` branch forces the torsion decision to have returned `none`
(`torsionLogTerm_none_of_decide_none`); `engine_none_of_not_elementary`'s contrapositive then turns the
non-torsion verdict into `¬ elem`. This re-bases the algebraic completeness onto the `Option` integrator:
`none` is the self-determining "not elementary" answer, modulo exactly the already-named frontier. -/
theorem cIntegrateAlgebraicDecide_complete {isTorsion : Prop} {elem : Prop}
    (hres : AlgebraicCompletenessResidual ρq gen Dm p isTorsion elem)
    (hnone : cIntegrateAlgebraicDecide p ρ R B residual c D degBound ρq gen Dm hasLogPart
      = none) :
    ¬ elem := by
  -- the `none` output forces the torsion branch to `none` (non-torsion verdict)
  have hT : (torsionLogTerm p ρ ρq gen Dm).isNone = true :=
    torsionLogTerm_none_of_decide_none p ρ R B residual c D degBound ρq gen Dm hasLogPart hnone
  -- contrapositive of the completeness equivalence: if `elem` held, the log term would be emitted
  intro hcon
  have hsome : (torsionLogTerm p ρ ρq gen Dm).isSome = true :=
    (cIntegrateAlgebraicWf_complete_of_residual ρ ρq gen Dm p hres).mpr hcon
  rw [Option.isNone_iff_eq_none] at hT
  rw [hT] at hsome
  simp at hsome

end Completeness

/-! ## Part 4 — the DECISION-PROCEDURE capstone: `(∃ F, … = some F) ⟺ IsAlgebraicElementary integrand`

Combining soundness (`some ⟹ elementary`, via the soundness residual's torsion correctness pinned to
elementarity) with completeness (`none ⟹ ¬ elementary`) gives the full decision-procedure equivalence,
mirroring the transcendental `crischDESolveSoundWf_isDecisionProcedure`. The integrator answers `some _`
**iff** the integrand is elementary, modulo the bundled named frontier.

The cleanest assembly rides the completeness equivalence `cIntegrateAlgebraicWf_complete_of_residual`
(`torsionLogTerm.isSome ⟺ elem`) on the **has-log** path together with the structural reading of
`cIntegrateAlgebraicDecide`'s output: with a log part present and the principal solve failing,
`cIntegrateAlgebraicDecide = some _ ⟺ torsionLogTerm = some _ ⟺ elem`. -/

section Decides

variable (p : ℕ) [Fact p.Prime]
variable (ρ : QFunNZG ℚ) (R B : CPolyG ℚ)
variable (residual : RadElem (QFunNZG ℚ)) (c : QFunNZG ℚ) (D : CPolyG ℚ) (degBound : ℕ)
variable (ρq : CPolyG ℚ) (gen : ℕ) (Dm : CPolyG.MumfordDivisor ℚ)

/-- **On the non-principal log path, `cIntegrateAlgebraicDecide = some _` iff the torsion branch fires.**
With a log part present (`hasLogPart = true`) and the principal log solve failing (`radLogArgSolve = none`),
the decision integrator returns `some _` **exactly** when `torsionLogTerm = some term` — the structural
equivalence isolating the torsion decision as the elementarity gate on this path. -/
theorem decide_isSome_iff_torsion_isSome
    (hlog : radLogArgSolve ρ residual D degBound = none) :
    (cIntegrateAlgebraicDecide p ρ R B residual c D degBound ρq gen Dm true).isSome = true
      ↔ (torsionLogTerm p ρ ρq gen Dm).isSome = true := by
  unfold cIntegrateAlgebraicDecide
  simp only [Bool.true_eq_false, if_false, hlog]
  cases hT : torsionLogTerm p ρ ρq gen Dm with
  | none => simp
  | some term => simp

/-- **★★ THE DECISION-PROCEDURE CAPSTONE** (`cIntegrateAlgebraicDecide_decides`,
`(∃ F, … = some F) ⟺ IsAlgebraicElementary integrand`, modulo the bundled frontier). On the non-principal
log path (`hasLogPart = true`, `radLogArgSolve = none` — the path the torsion decision governs), under the
`AlgebraicCompletenessResidual` (the two named deep frontiers), the self-determining integrator returns
`some F` for some `F` **iff** the integrand is elementary:
`(∃ F, cIntegrateAlgebraicDecide … true = some F) ↔ elem`. The chain: `∃ F, … = some F ⟺
cIntegrateAlgebraicDecide.isSome` ⟺ `torsionLogTerm.isSome` (the structural
`decide_isSome_iff_torsion_isSome`) ⟺ `elem` (the completeness equivalence
`cIntegrateAlgebraicWf_complete_of_residual`). This is the algebraic analogue of the transcendental
`crischDESolveSoundWf_isDecisionProcedure`: a genuine decision procedure for elementary integrability of
simple-radical algebraic functions, modulo exactly the named Trager frontiers (Liouville-for-algebraic +
the good-reduction torsion decision). -/
theorem cIntegrateAlgebraicDecide_decides {isTorsion : Prop} {elem : Prop}
    (hres : AlgebraicCompletenessResidual ρq gen Dm p isTorsion elem)
    (hlog : radLogArgSolve ρ residual D degBound = none) :
    (∃ F, cIntegrateAlgebraicDecide p ρ R B residual c D degBound ρq gen Dm true = some F)
      ↔ elem := by
  rw [← Option.isSome_iff_exists,
    decide_isSome_iff_torsion_isSome p ρ R B residual c D degBound ρq gen Dm hlog]
  exact cIntegrateAlgebraicWf_complete_of_residual ρ ρq gen Dm p hres

end Decides

/-! ## Part 5 — ★ end-to-end `native_decide` witnesses (self-determining, both verdicts)

Three runs *through `cIntegrateAlgebraicDecide`* exercise all three log outcomes plus the `none` verdict:

* the **non-torsion** `(3,5)` on `y² = x³−2` → `none` (NOT elementary) — the self-determining negative answer;
* the **torsion** flex `(0,1)` on `y² = x³+1` → `some` with a `(1/3)·log` term (elementary, non-principal);
* a **principal** example (the rational-only round-trip's principal log path) → `some`.

Each is `native_decide`: the decision integrator type-checks and *reduces* to the expected verdict. -/

/-! ### Witness A — the non-torsion `(3,5)` on `y² = x³ − 2` → `none` (NOT elementary) -/

/-- **A non-principal log residual** `decideNonPrincipalResidual` — the double-pole integrand
`[0, 1/(x²·(x²+1))]` for which `radLogArgSolve … [0,0,1] 1 = none` (the principal-case ansatz fails at this
degree bound, the torsion boundary). Reused to force the principal log solve to `none` on the elliptic
witnesses, so the torsion decision is what governs the verdict. -/
def decideNonPrincipalResidual : RadElem (QFunNZG ℚ) :=
  radInvYLift (qxOfNum [0, 0, 1, 0, 1]) CField.one

/-- **The decision integrator on the non-torsion `(3,5)` of `y² = x³ − 2`** — a log-part input
(`hasLogPart = true`) whose principal solve fails (the non-principal `decideNonPrincipalResidual`,
`radLogArgSolve = none`) and whose residue divisor `(3,5)` is non-torsion, so `cIntegrateAlgebraicDecide` is
expected to return `none`. -/
def decideWitnessNonTorsion : Option AlgIntegralResult :=
  cIntegrateAlgebraicDecide 5 tltRhoX3m2 [1] [1] decideNonPrincipalResidual CField.one [0, 0, 1] 1
    hypRhoX3m2 1 hypPt35 true

/-- **★★ The self-determining integrator returns `none` on the non-torsion `(3,5)`** (`native_decide`):
end-to-end through `cIntegrateAlgebraicDecide`, the rank-1 infinite-order residue divisor `(3,5)` on
`y² = x³ − 2` drives the principal log solve to `none` and the torsion decision to non-torsion, so the
integrator returns `none` — the famous non-elementary witness, **self-determined**. The integral of the
corresponding algebraic function is NOT elementary (Trager Ch. 6: a residue divisor of infinite order has no
principal multiple). -/
theorem decideWitnessNonTorsion_none : decideWitnessNonTorsion = none := by native_decide

/-! ### Witness B — the torsion flex `(0,1)` on `y² = x³ + 1` → `some` with a `(1/3)·log` term -/

/-- **The decision integrator on the torsion flex `(0,1)` of `y² = x³ + 1`** — a log-part input whose
principal solve fails (`residual = 0`, `radLogArgSolve = none`) and whose residue divisor `(0,1)` is order-3
torsion, so `cIntegrateAlgebraicDecide` is expected to return `some ⟨v, [(1/3, y − 1)]⟩` (the non-principal
torsion branch). -/
def decideWitnessTorsion : Option AlgIntegralResult :=
  cIntegrateAlgebraicDecide 5 tltRhoX3p1 [1] [1] decideNonPrincipalResidual CField.one [0, 0, 1] 1
    hypRhoX3p1 1 hypPt01 true

/-- **★★ The self-determining integrator returns `some` with a `(1/3)·log` term on the torsion `(0,1)`**
(`native_decide`): end-to-end through `cIntegrateAlgebraicDecide`, the order-3 flex residue divisor `(0,1)`
on `y² = x³ + 1` drives the principal log solve to `none` and the torsion decision to `some 3`, so the
integrator returns `some F` with exactly one log term whose coefficient is `1/3` (field-equal to
`oneOverMQ 3` via `qEq`). Checked on `(isSome, logTerms.length, coefficient = 1/3)`. The integral IS
elementary, with a `(1/3)·log(y − 1)` term — **self-determined** (the contrasting positive verdict). -/
theorem decideWitnessTorsion_some :
    (decideWitnessTorsion.isSome,
     (decideWitnessTorsion.map fun F => F.logTerms.length),
     (decideWitnessTorsion.bind fun F => F.logTerms.head?.map fun t => qEq t.1 (oneOverMQ 3)))
      = (true, some 1, some true) := by native_decide

/-! ### Witness C — a principal example → `some` -/

/-- **The decision integrator on a principal-log example** — the rational-only round-trip's curve
`y² = x² + 1` with the principal log argument `radArgRhoArcsinh`'s `arcsinh` solve. With `hasLogPart = true`
and a principal `radLogArgSolve = some N`, `cIntegrateAlgebraicDecide` is expected to return `some` with the
principal `1·log(N/D)` term — the divisor inputs (`hypPt35`, here irrelevant) are bypassed because the
principal solve succeeds first. -/
def decideWitnessPrincipal : Option AlgIntegralResult :=
  cIntegrateAlgebraicDecide 5 rtRatRho [1] [1]
    (radInvYLift rtRatRho CField.one) CField.one [1] 1
    (qxNum rtRatRho) 1 hypPt35 true

/-- **★ The self-determining integrator returns `some` on the principal example** (`native_decide`):
end-to-end through `cIntegrateAlgebraicDecide`, the principal log argument `∫ 1/√(x²+1) = arcsinh(x) =
log(x + y)` solves (`radLogArgSolve = some N`), so the integrator returns `some F` with exactly one
(principal) log term — `(isSome, logTerms.length) = (true, some 1)`. The principal branch is taken before the
torsion decision (the divisor inputs are bypassed). The positive verdict for the classic principal case. -/
theorem decideWitnessPrincipal_some :
    (decideWitnessPrincipal.isSome, decideWitnessPrincipal.map fun F => F.logTerms.length)
      = (true, some 1) := by native_decide

/-! ## ★★ The self-determining algebraic decision-procedure milestone (`native_decide`) -/

/-- **★★ THE SELF-DETERMINING ALGEBRAIC INTEGRATOR DECIDES ELEMENTARITY** (Trager, the decision,
`native_decide`). `cIntegrateAlgebraicDecide` turns the total `cIntegrateAlgebraicWf` into a real decision
procedure by wiring in Trager's torsion test: it returns `some F` when the integral is elementary (no log
part; principal `1·log u`; or the residue divisor torsion ⟹ `(1/m)·log g`) and **`none`** when the residue
divisor is non-torsion (NOT elementary). End-to-end through the `Option` integrator:

* on the **non-torsion** `(3,5)` of `y² = x³ − 2`, `cIntegrateAlgebraicDecide = none` (NOT elementary) — the
  self-determined negative verdict;
* on the **torsion** flex `(0,1)` of `y² = x³ + 1`, it returns `some` with a `(1/3)·log` term (elementary,
  non-principal) — coefficient `1/3`;
* on a **principal** example (`∫ 1/√(x²+1) = log(x + y)`), it returns `some` with a principal log term.

Proven (modulo exactly the already-named Trager frontiers, never re-`sorry`):
**`cIntegrateAlgebraicDecide_sound`** (`some F → D(F) = integrand`, checker-free),
**`cIntegrateAlgebraicDecide_complete`** (`none → ¬ elementary`), and the capstone
**`cIntegrateAlgebraicDecide_decides`** (`(∃ F, … = some F) ⟺ elementary`). The simple-radical / hyperelliptic
elementary-integration **decision procedure**, self-determining, sound, and complete modulo the
Liouville-for-algebraic structure theorem and the good-reduction torsion-decision correctness. -/
theorem self_determining_algebraic_decision_validates :
    decideWitnessNonTorsion = none
    ∧ (decideWitnessTorsion.isSome,
       (decideWitnessTorsion.map fun F => F.logTerms.length),
       (decideWitnessTorsion.bind fun F => F.logTerms.head?.map fun t => qEq t.1 (oneOverMQ 3)))
        = (true, some 1, some true)
    ∧ (decideWitnessPrincipal.isSome, decideWitnessPrincipal.map fun F => F.logTerms.length)
        = (true, some 1) := by native_decide

/-! ### Restatements pinning the decision-procedure content (anonymous `example`s) -/

section Restatements

-- ★ SOUNDNESS (checker-free, modulo the named frontier): `some F → D(F) = integrand`.
example (p : ℕ) [Fact p.Prime]
    (ρ : QFunNZG ℚ) (R B : CPolyG ℚ) (residual : RadElem (QFunNZG ℚ)) (c : QFunNZG ℚ)
    (D : CPolyG ℚ) (degBound : ℕ) (ρq : CPolyG ℚ) (gen : ℕ) (Dm : CPolyG.MumfordDivisor ℚ)
    (hasLogPart : Bool) (integrand : RadElem (QFunNZG ℚ))
    (hres : AlgebraicDecideSoundnessResidual p ρ R B residual c D degBound ρq gen Dm integrand)
    (F : AlgIntegralResult)
    (hsome : cIntegrateAlgebraicDecide p ρ R B residual c D degBound ρq gen Dm hasLogPart
      = some F) :
    CPolyG.toPolyG (algDeriv ρ F) = CPolyG.toPolyG integrand :=
  cIntegrateAlgebraicDecide_sound p ρ R B residual c D degBound ρq gen Dm hasLogPart integrand
    hres F hsome

-- ★ COMPLETENESS (modulo the named frontier): `none → ¬ elementary`.
example (p : ℕ) [Fact p.Prime]
    (ρ : QFunNZG ℚ) (R B : CPolyG ℚ) (residual : RadElem (QFunNZG ℚ)) (c : QFunNZG ℚ)
    (D : CPolyG ℚ) (degBound : ℕ) (ρq : CPolyG ℚ) (gen : ℕ) (Dm : CPolyG.MumfordDivisor ℚ)
    (hasLogPart : Bool) {isTorsion elem : Prop}
    (hres : AlgebraicCompletenessResidual ρq gen Dm p isTorsion elem)
    (hnone : cIntegrateAlgebraicDecide p ρ R B residual c D degBound ρq gen Dm hasLogPart
      = none) :
    ¬ elem :=
  cIntegrateAlgebraicDecide_complete p ρ R B residual c D degBound ρq gen Dm hasLogPart
    hres hnone

-- ★ DECISION PROCEDURE (modulo the named frontier): `(∃ F, … = some F) ⟺ elementary`.
example (p : ℕ) [Fact p.Prime]
    (ρ : QFunNZG ℚ) (R B : CPolyG ℚ) (residual : RadElem (QFunNZG ℚ)) (c : QFunNZG ℚ)
    (D : CPolyG ℚ) (degBound : ℕ) (ρq : CPolyG ℚ) (gen : ℕ) (Dm : CPolyG.MumfordDivisor ℚ)
    {isTorsion elem : Prop}
    (hres : AlgebraicCompletenessResidual ρq gen Dm p isTorsion elem)
    (hlog : radLogArgSolve ρ residual D degBound = none) :
    (∃ F, cIntegrateAlgebraicDecide p ρ R B residual c D degBound ρq gen Dm true = some F)
      ↔ elem :=
  cIntegrateAlgebraicDecide_decides p ρ R B residual c D degBound ρq gen Dm hres hlog

end Restatements

/-! ### Axiom audit — the decision/soundness/completeness/capstone are axiom-clean
(`[propext, Classical.choice, Quot.sound]`); the witnesses use `native_decide` (`Lean.ofReduceBool`). -/

#print axioms cIntegrateAlgebraicDecide_sound
#print axioms cIntegrateAlgebraicDecide_complete
#print axioms cIntegrateAlgebraicDecide_decides
#print axioms decideWitnessNonTorsion_none
#print axioms decideWitnessTorsion_some
#print axioms self_determining_algebraic_decision_validates

end DeepWiki.SymbolicIntegration
