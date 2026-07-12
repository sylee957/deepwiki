# Ultimate goal — a sound AND complete transcendental Risch algorithm

**North star.** Make the transcendental Risch integrator (Bronstein, *Symbolic Integration I:
Transcendental Functions*, DOI 10.1007/b138171 — the book's core, §5–§7) **provably sound and
complete** as an *abstract* theorem, not merely `native_decide`-validated:

> The integrator returns a correct elementary antiderivative exactly when the integrand has one —
> `some ⟹ D(∫f) = f` (soundness) and `some ⟺ f is elementary` (completeness) — resting only on the
> genuinely necessary **new-monomial side-conditions** the book itself requires, each named and
> justified, never hidden.

This is the standing north star of [[feedback-prove-algorithm-invariants]]: replace "computable +
native_decide" with abstract invariant proofs.

## What the book's ultimate algorithm IS (from the `Sources/Doi_10_1007_b138171/` catalog)

The core transcendental Risch algorithm integrates over a single transcendental monomial extension,
recursing up a tower:

- **§5 integration** — Hermite reduction (§5.3, Thm 5.3.1), polynomial reduction (§5.4, Thm 5.4.1/2),
  residue criterion / logarithmic part (§5.6, Thm 5.6.1), integration of reduced functions (§5.7,
  Thm 5.7.1/2), the primitive case (§5.8, Thm 5.8.1), the hyperexponential case (§5.9, Thm 5.9.1),
  the hypertangent case (§5.10, Thm 5.10.1/2), the nonlinear-no-specials case (§5.11), in-field
  integration (§5.12).
- **§5.5 Liouville's theorem** — the structure theorem (Thm 5.5.1 log / exp instance / Thm 5.5.2–3
  general): every elementary antiderivative is `g + Σ cᵢ log uᵢ`. This is what turns soundness of the
  reductions into *completeness* (no such form ⟹ not elementary).
- **§6 the Risch Differential Equation** (RDE) — normal/special denominator (§6.1–6.2), degree bounds
  (§6.3), SPDE (§6.4, Thm 6.4.1), non-cancellation (§6.5) and cancellation (§6.6) cases. The RDE is
  what §5.8–5.10 call to integrate coefficients.
- **§7 parametric RDE / limited integration** (§7.1–7.3) — the parametric generalization §5.8's
  coefficient antiderivatives need.

## Current status (verified 2026-07-12, live code)

The **entire pipeline is computable + native_decide-validated end-to-end** (`cIntegrate` etc.). The
**systematic gap is the abstract correctness theorems.** Every chapter's `## NOT YET FORMALIZED`
block says the same: *"the algorithm is computable + native_decide-validated; the abstract correctness
theorem (Thm 5.3.1 / 5.4.1 / 5.6.1 / 5.8.1 / 6.4.1 / …) is NOT proved."*

A large **abstract layer already exists** and is the scaffold to finish onto:
- **Soundness** — the a-priori `D(∫f)=f` arc (`Engine/Tower/*`, the checker-free "north star" of
  [[leanproofs-symbolic-integration-soundness-arc]]): base-regime normal-part soundness proven; the
  full LRT solver; genuine-integral notions. Substantially done, resting on genuine Bronstein
  conditions.
- **Completeness** — `Engine/IntegratorCompleteness.lean`: `logExtension_completeness`,
  `logAlgebraic_tower_completeness`, non-elementarity propagation — all PROVEN, resting on
  `NondegenerateLog` (the new-monomial condition). Two of three named frontier `def`s discharged
  (`TowerExhaustivenessFrontier`, `BaseObstructionFrontier` are theorems); **`ExpCaseLiouvilleFrontier`
  is the one undischarged frontier here** — but the exp keystone
  `isLiouville_expExtension_uncond` IS proven in `Engine/LiouvilleExpBridge.lean` (likely a wiring
  job, not new math — verify first).
- **Liouville keystones** — `isLiouville_logExtension_uncond` (LiouvilleLog) +
  `isLiouville_expExtension_uncond` (LiouvilleExpBridge), both proven, axiom-clean, the transcendental
  `IsLiouville` instances Mathlib lacked ([[leanproofs-risch-completeness-assessment]]).
- **RDE completeness tower-induction** — `crischFieldComplete_step` / base ℚ, structurally complete
  modulo the honest per-level `RischDEStepFrontier`.

So the work is **assembly + discharging honest conditions**, not from-scratch. The pieces that ARE
genuine irreducible frontiers (must remain hypotheses): the new-monomial nondegeneracy
(`NondegenerateLog`/`NondegenerateExp`/`hη`/`IsRdeNormalPoleBounded` — all the SAME Risch new-monomial
condition; these are what makes an extension a genuine new transcendental, correctly a hypothesis) +
the §5.12/§7.3 parametric-log-derivative-of-a-radical recognizer's deferred witness. Everything else
is provable.

## Definition of done

1. **Soundness (abstract, unconditional-modulo-side-conditions).** A top-level theorem: a successful
   run of the transcendental integrator yields a genuine antiderivative — the reduction correctness
   theorems (§5.3/5.4/5.6/5.7/5.8) proved abstractly and composed through the RDE (§6) soundness, so
   `some result ⟹ D(result) = integrand` with NO round-trip re-check.
2. **Completeness (abstract).** `some ⟺ f is elementary` at every tower level, assembled from the
   Liouville structure theorem (§5.5) + the RDE decision procedure (`crischDESolveSound_isDecisionProcedure`)
   + the tower-induction, resting only on the named new-monomial conditions. `ExpCaseLiouvilleFrontier`
   discharged (wire the exp keystone); the §5.5 general structure theorem (Thm 5.5.2/3) either proved
   or reduced to a single named, justified frontier.
3. **Assembly.** One capstone statement in the engine that pins both, with an `#print axioms` audit
   showing `[propext, Classical.choice, Quot.sound]` only (no `sorry`, no `native_decide` in the
   abstract theorems). `example`s restating it against the book's wording.
4. **Catalog.** As each abstract correctness theorem lands, delete its `[research]`/"abstract
   correctness … NOT proved" note from the relevant `Sources/Doi_10_1007_b138171/Chapter*.lean`
   `## NOT YET FORMALIZED` block (subtractive, [[feedback-subtractive-missing-markers]]). Status lives
   in the catalog, not memory.

## Status — SUBSTANTIVELY COMPLETE (2026-07-13)

The transcendental Risch integrator is **proved sound and complete for every transcendental monomial
case, both per level and at every tower depth**, all axiom-clean (`[propext, Classical.choice,
Quot.sound]`, no `sorry`, no `native_decide`), all cataloged, all merged to main. 12 gate-green phases:

- **Per-level sound-and-complete** (`some ⟺ genuinely elementary-integrable`, genuine antiderivative on
  success): primitive (`lrtSolver_soundAndComplete_on_tower`, `thm_5_5_1_soundAndComplete`),
  hyperexponential §5.9 (`hyperexpRischLevel_succeeds_iff_integrable`, `thm_5_9_1_soundAndComplete`),
  hypertangent §5.10 (`tangentRischLevel_succeeds_iff_integrable`, `thm_5_10_soundAndComplete`), via the
  generic `rischLevel_succeeds_iff_integrable`.
- **At every tower depth** `DenseFracTower n`: `hyperexpRischLevel_succeeds_iff_integrable_tower`,
  `denseTangentTower_soundAndComplete` (`thm_5_9_1/5_10_soundAndComplete_tower`).
- **Genuine soundness** (true antiderivative, not the formal residue-constant identity):
  `soundGenuineLrt`/`soundGenuineLrt_of_guard`.
- **Grounded on the necessary condition, not an axiom**: `primitiveFrontierLrt_of_genuineData` proves the
  frontier IS the necessary new-monomial condition (`GenuinePrimitiveMonomialLrt`, "η is not a
  derivative").
- **Tower-exhaustiveness kernel** (Thm 5.5.2/5.5.3): `not_elementary_tower_of_not_elementary_base`
  (`thm_5_5_2_tower_exhaustiveness`).
- **Both transcendental Liouville keystones** proved: `liouville_logExtension`/`liouville_expExtension`.

Everything rests on exactly the **necessary Risch new-monomial conditions** (`NondegenerateLog`/`Exp`,
`GenuinePrimitiveMonomialLrt`) + the field-RDE completeness recursion hypothesis
(`CRischFieldComplete (DenseFracTower n)`).

### The honest remaining boundary (research/refactor, NOT autonomously forceable — rigorously assessed)

- **Whole-tower *unconditionality*** (discharging `CRischFieldComplete` up the tower): requires a
  **design refactor** — the `CRischField (DenseFrac β)` instance solver is normalization-free, so its
  completeness is false as stated; the fix is rebasing it onto the weak-normalizing `crischDESolveSoundWf`
  (the never-completed `docs/rischde-wf-migration.md` task), after which the RDE frontier
  `RischDEStepFrontierWf` (6 genuine Bronstein-completeness clauses) still remains — genuine math, a
  necessary hypothesis, not bookkeeping. Left as the explicit `CRischFieldComplete` hypothesis, which is
  the mathematically honest compositional form.
- **The fully general structure theorem** (Thm 5.5.2/5.5.3 inductive form): needs an abstract
  `IsElementary` / elementary-tower predicate Mathlib lacks. The transitivity kernel + the per-monomial
  conditioned instances are the assemblable core; the full induction is the `[research]` boundary.

## Execution

Autonomous, self-paced, commit-per-gate-green-phase ([[feedback-merge-after-proving]],
[[feedback-no-blocking-taskoutput]]). Each phase: prove one abstract correctness theorem (or wire one
frontier), gate with `scripts/check.sh`, restate as an `example` against the book, update the catalog,
commit. Verify against live code before trusting any 3-day-old memory claim — the frontier map in
[[leanproofs-risch-completeness-assessment]] is the guide but many "walls" already fell.

### Phase order (dependency-first; refine as each lands)

- **P0** — map: enumerate the abstract-correctness theorems still open (grep the catalog's "NOT proved"
  notes + the `def … Frontier` Props with no discharging theorem); confirm which keystones are already
  proven-but-unwired. Write the confirmed backlog here.
- **P1** — discharge `ExpCaseLiouvilleFrontier` by wiring `isLiouville_expExtension_uncond` (fast win,
  verify it's really just wiring).
- **P2** — §5 reduction correctness: Thm 5.3.1 (Hermite), 5.4.1 (poly), 5.6.1 (residue), 5.8.1
  (primitive) abstractly — the memory says the abstract spines exist (`hermiteReducePower_spec`,
  RT-resultant lemmas); assemble them onto the engine's reductions.
- **P3** — §6 RDE abstract soundness/decision: compose the discharged residuals (#1 mechanical, #2/#3
  reduced) into `crischDESolve` per-level correctness; assemble the tower-induction.
- **P4** — §5.5 structure theorem (Thm 5.5.2/3): the tower-exhaustiveness "no Liouville form ⟹ not
  elementary" — prove or reduce to one named frontier.
- **P5** — capstone: assemble soundness + completeness into one top-level theorem + axiom audit +
  book-wording `example`s; subtract the catalog notes.

The genuine research floor (which STAYS a named hypothesis, not a gap): the new-monomial nondegeneracy
conditions. Document, don't grind.
