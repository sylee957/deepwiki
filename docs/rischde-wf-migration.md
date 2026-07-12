# Migration plan: switch the tower Risch-DE oracle to the fuel-free `cRischDEG`

Self-contained instructions for retiring the fuel-threaded `cRischDEG` Risch-DE solver in
favour of the well-founded `cRischDEG`, at the level that matters: the
`CRischField (CFracG β)` **instance**. Written to be executed by an agent without prior
conversation context. Read this whole file before touching anything.

**One-line goal.** Make the tower Risch-DE recursion *actually* fuel-free by rebasing the
`CRischField (CFracG β)` instance's `crischDESolve` from `cRischDEG […] towerRischDEFuel`
onto `cRischDEG`, then retire the orphaned fuel'd solver + its soundness track.

**Status when this plan was written (2026-07-02).** Assessed only — no code changed. Two
reversible spikes established the scope (a naïve instance def-swap hit a module-layering wall
and was reverted; the tree is green). This is a **multi-session, high-blast-radius** effort;
do it phased and gate-green per phase, or not at all.

---

## 1. Why this migration (the payoff)

The transcendental engine already has a full fuel-free layer: `cRischDEG`
(`Computable/Tower/RischDEWellFounded.lean:430`), `cIntegrateGFullWf`
(`Computable/UnifiedFuelFree.lean`), and axiom-clean Wf soundness
(`field_identity_of_cIntegrateGFullWf_of_checkIdentityG`, `crischDESolveSoundWf_field`). So the
top of the pipeline *looks* fuel-free.

**But the tower recursion re-introduces fuel at every level.** The base solve of the tower is
the typeclass method `CRischField.crischDESolve`. Its only non-trivial instance,
`instCRischFieldCFracG : CRischField (CFracG β)` (`Computable/Tower/RischDE.lean:465`), is
defined as

```
crischDESolve f g :=
  if cdenomNormalGateG f then
    match CPolyG.cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2 with
    | none => none | some (ynum, yden) => if h : cisZeroG yden = false then some ⟨(ynum,yden),h⟩ else none
  else none
```

i.e. it runs the **fuel'd** `cRischDEG` with a fixed `towerRischDEFuel := 60`
(`Computable/Tower/RischDE.lean:431`). Because `cRischDEG` recurses into `[CRischField β]`
for its own base solves, running `cRischDEG` at level `n+1` calls this instance at level `n`
— which is `cRischDEG`. So today's "Wf tower" still bottoms through fuel'd `cRischDEG` at every
recursion step, and the fixed fuel `60` is a latent incompleteness (deep towers can exhaust
it). Only rebasing the **instance** onto `cRischDEG` makes the whole tower genuinely
fuel-free and fuel-budget-free.

`cRischDEG` currently has ~17 consumers (this instance + the fuel'd soundness development that
proves `crischDESolve`'s headline correctness). Retiring it means rebasing the instance and
porting that soundness.

## 2. The four entangled layers (why it is not a def-swap)

1. **Module layering.** `cRischDEG` is defined in `Tower/RischDEWellFounded.lean`, which
   `import`s `Tower/RischDE.lean` — the file that holds the instance *and* defines `cRischDEG`.
   The instance (lower layer) cannot forward-reference `cRischDEG`. The instance + its two
   `rfl`-reduction lemmas must **move** to a module that comes *after* `cRischDEG`.

2. **Typeclass swap `CFracGcdCore β` → `CFracGcdCoreWf β`.** The fuel'd instance's `variable`
   block is `{β} [CField β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β] [CRischField β]`
   (`Computable/Tower/RischDE.lean:454`). But `cRischDEG`'s block is
   `[CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]`
   (`Computable/Tower/RischDEWellFounded.lean:418`) — a **different** gcd class. The rebased
   instance, every one of its consumers, and the whole tower recursion must therefore carry
   `CFracGcdCoreWf`. Feasible: the recursion instances exist —
   `instCFracGcdCoreWfCFracG : CFracGcdCoreWf (CFracG β)` (`Computable/Tower/WellFounded.lean:151`),
   `CFracGcdCoreWf ℚ` (`…:139`), `CFracGcdCoreWf RadX3` (`Computable/MixedTowerIntegrate.lean:96`).

3. **Soundness re-wiring (~9 files).** The fuel'd soundness development reasons symbolically
   about `cRischDEG [1] towerRischDEFuel` and unfolds the instance to it by `rfl` via
   `crischDESolve_eq_solve_of_normal` (`Computable/Tower/RischDE.lean:478`) and
   `cdenomNormalGateG_of_crischDESolve_isSome` (`…:496`). There is **no `cRischDEG = cRischDEG`
   bridge** (they are parallel implementations; a fixed `towerRischDEFuel` cannot equal the
   well-founded result in general), so the soundness cannot transfer by rewrite — it must be
   re-established proof-by-proof against the existing Wf development
   (`cRischDEG_some_imp_stages`, `Computable/Tower/RischDEWellFounded.lean:449`;
   `crischDESolveSoundWf_field`, `Computable/RischDE/SolveSoundWf.lean:174`). The headline to
   port is `crischDESolve_field_of_witness_residual` (`Computable/SoundnessCapstone.lean:294`).

4. **Open-problem entanglement.** There is deliberately **no** `CRischFieldSpec (CFracG β)`
   instance — it is a known-open goal (`Computable/SoundnessCapstone.lean:476`,
   `Computable/RischDE/SolveNorm.lean:493`). The fuel'd `SoundnessCapstone` is *partial progress
   toward it*. The migration must **port** that partial progress onto `cRischDEG`, not discard
   it; it may not be *completable*, only relocated. Treat this as the residual research frontier,
   not a blocker for the mechanical parts (layers 1–2).

**No gate-green intermediate for the pure switch.** Rebasing the instance immediately breaks the
`rfl`-reduction lemmas and everything downstream of them, so layers 1–3 must land in one
gate-green push (per Phase). Do not expect to commit "the switch" alone.

## 3. Current-state inventory (verify before editing — cite live line numbers)

Fuel'd side (to retire):
- `cRischDEG` def + `towerRischDEFuel := 60` + the instance + reduction lemmas + the fuel'd
  special-denominator cluster `cRdeSpecialDenominatorG` / `cValuationG` / `cSpecialPolyG` /
  `cRdeNormalDenominatorG` / `cWeakNormalizerG` — all in `Computable/Tower/RischDE.lean`.
- Fuel'd soundness: `Computable/SoundnessCapstone.lean` and
  `Computable/RischDE/{Structural,TowerCorrectG,NormalCorrect,ExpPrimCancellation,SolveNorm,
  SolveNormCanon,SolveSound,DegreeBoundCancellation}.lean`, `Computable/WeakNormalizerCorrect.lean`.

Wf side (to build on — already exists):
- `cRischDEG` + `cRischDEG_some_imp_stages` (`Computable/Tower/RischDEWellFounded.lean`).
- Wf stages `cRdeNormalDenominatorG` / `cRdeSpecialDenominatorG` / `cValuationG` /
  `cSPDEG` / `cPolyRischDEG` (`…WellFounded.lean`, `…RischDEWellFounded.lean`).
- Standalone Wf solver + soundness `crischDESolveSoundWf` / `crischDESolveSoundWf_field`
  (`Computable/RischDE/SolveSoundWf.lean`); `cWeakNormalizerG`, `cdiophantineG`, etc.
- `CFracGcdCoreWf` recursion instances (§2.2).

Instance consumers (import chains to update): `SoundnessCapstone`, `MixedTowerIntegrate`,
`TranscendentalOverAlgebraic`, `RischDE/SolveSound`, `RischDE/SolveNorm`, `RischDE/SolveNormCanon`,
`Hyperexp/NormalSoundness`, `Tower/GcdFF`, and the catalog `Sources/Doi_10_1007_b138171/Chapter6.lean`
(`alg_6_6_rischDEBase` / `alg_6_6_rationalRDE` route through `CRischField.crischDESolve`; the
`native_decide` examples must still evaluate to the same results).

Build/gate: `export PATH="$HOME/.elan/bin:$PATH"` on every `Bash`; gate is
`scripts/check.sh [module]` (exit 0 = `GATE: PASS`, treats warnings/`sorry` as failure). Run bare
as the final gate. Every new `Sources/*` module must be imported into `Sources.lean` (no globs).

## 4. Phased plan (each phase gate-green, one commit)

### P0 — Preconditions
1. `git status` clean. Finish or park the leaf-level fuel work first if in flight.
2. Confirm the §3 line numbers against live code; the counts/anchors will have drifted.
3. Decide the new home for the instance (Phase P2). Recommended: a new module
   `Computable/Tower/RischDEInstance.lean` importing `Tower.RischDEWellFounded` (which transitively
   has `Tower.RischDE`), so it sees both `cRischDEG` and `CFracG`/`cdenomNormalGateG`.

> **P1 FEASIBILITY VERDICT (2026-07-02): GREEN — mechanical mirror-port, not blocked on the open
> spec.** The fuel'd headline `crischDESolve_field_of_witness_residual`
> (`Computable/SoundnessCapstone.lean:294`) *derives* the field identity as: gate-reduction →
> `rdeCleared_of_success_and_residual` (`RischDE/Structural.lean:294`) → `rischDE_field_of_cleared`
> (`RischFieldSpec.lean:116`, fuel-agnostic — REUSE). The cleared derivation is
> `cRischDEG_rdeCleared_gen` (`RischDE/TowerCorrectG.lean:769`) fed by the derivable-stages lemma
> `cRischDEG_some_imp_noCancel_of_primitive` + the residual `RischDEStructuralResidual`. To Wf-ify:
> the Wf stages (`cRdeNormalDenominatorG`, `cRdeSpecialDenominatorG`, `cSPDEG`,
> `cPolyRischDENoCancelG`) are **structural mirrors** of the fuel'd stages (identical `let`/`if`
> shape and output formulas; only the split/gcd/dvd sub-ops swap `…G fuel → …G`), so the three
> capstone sub-lemmas port near-verbatim: `cRdeSpecialDenominatorG_primitive_eq`
> (`RischDEWellFounded.lean:294`) ALREADY EXISTS; `cRischDEG_some_imp_stages`
> (`RischDEWellFounded.lean:449`) + `…_structural` (`Structural.lean:123`) ALREADY EXIST. So P1 needs
> only: (a) a Wf `cRdeNormalDenominatorG_cleared_lift`, (b) a Wf
> `cSPDEG_polyRischDENoCancel_cleared_at_boundDegree`, (c) `cPolyRischDEG_eq_noCancel_of_primitive`,
> (d) assemble `cRischDEG_rdeCleared_gen` + `RischDEStructuralResidualWf` +
> `cRischDEG_some_imp_noCancel_of_primitive` + the headline. The `hin`/`CSPDEGClearedInputsGen`
> (open-spec kernel) stays a *hypothesis* in both — P1 does NOT try to close it. Bounded proof-porting,
> not research.

> **P1 PROGRESS (2026-07-02).** Landed gate-green in `RischDE/Structural.lean`:
> `cPolyRischDEG_eq_noCancel_of_primitive` + `cRischDEG_some_imp_noCancel_of_primitive` (verbatim
> ports) AND `cPolyRischDENoCancelG_cleared_identity` (checklist item 1 — the hardest, a WF-induction
> proof). ★ METHOD PROVEN: the WF sub-lemmas port via **`fun_induction cFooWf … generalizing q with`**
> (NOT `.induct` — that mis-binds the `let`-values; `fun_induction` matches the sibling pattern at
> `OneShotSoundness.lean:528` for `cPolyRischDECancelPrimG`). Recursive case closes with
> `simp only [c', p, denote, map_add] at hih ⊢; linear_combination hih`. So the remaining sub-lemmas are
> de-risked bounded ports. Sizes (fuel'd templates in `TowerCorrectG.lean`): `cSPDEG_cleared_lifting_gen`
> (:165, 106 lines, WF on `(n+1).toNat` → `fun_induction cSPDEG`), `cSPDEGCleared_of_inputs_gen`
> (:301, 58 lines), `cRdeNormalDenominatorG_cleared_lift_gen` (:649, 48 lines — NON-recursive straight-line
> def, so a plain unfold+algebra port, no induction). Remaining P1 sub-lemmas (each a
> mirror-port of the named fuel'd template in `RischDE/TowerCorrectG.lean`; no Wf version or `_eq` bridge
> exists yet, so port proof-by-proof):
> 1. `cPolyRischDENoCancelG_cleared_identity` ← `cPolyRischDENoCancelG_cleared_identity_gen`
>    (`cPolyRischDENoCancelG` in `Tower/WellFounded.lean:410` mirrors `cPolyRischDENoCancelG`). The MATH
>    mirrors verbatim (base `c=0`; recursive `q = caddG p qrec`, `linear_combination ihrec` after
>    `toPolyG_c'` expansion). The ONLY friction is the `.induct` plumbing: the fuel'd proof is
>    `induction fuel`; the Wf one needs `cPolyRischDENoCancelG.induct` which generates **5 cases** and
>    — because the `else` branch has a `let m : ℤ` — binds that `m` among the case hypotheses, so
>    positional `rename_i` counts differ per case. RECOMMEND: use `fun_induction` (Lean 4.31) or first
>    `#check @cPolyRischDENoCancelG.induct` to read the exact case arities before writing `rename_i`;
>    unfold each branch with `cPolyRischDENoCancelG.eq_def` + `if_pos`/`if_neg` (pattern:
>    `FuelFreeGcd.lean:115` `toPolyG_cdivmodWf` via `cdivmodWf.induct`).
> 2. `cSPDEG_cleared_lifting_of_inputs` + `cSPDEG_polyRischDENoCancel_cleared_at_boundDegree`
>    ← `cSPDEG_cleared_lifting_of_inputs_gen` (`TowerCorrectG:…`) + `…_at_boundDegree_gen`
>    (`TowerCorrectG:434`). Uses (1) + the `CSPDEGClearedInputsGen` hypothesis (open-spec kernel — stays
>    a hypothesis). `toPolyG_cdivWf_exact_mul_gen` (`TowerCorrectG:451`) already exists.
> 3. `cRdeNormalDenominatorG_cleared_lift` ← `cRdeNormalDenominatorG_cleared_lift_gen`
>    (`TowerCorrectG:649`, ~48 lines; unfolds the normal-denom def — `cRdeNormalDenominatorG`
>    (`Tower/WellFounded.lean:242`) mirrors it exactly).
> 4. Assemble `cRischDEG_rdeCleared_gen` ← `cRischDEG_rdeCleared_gen` (`TowerCorrectG:769`) using (1)(2)(3)
>    + `cRdeSpecialDenominatorG_primitive_eq` (already exists, `RischDEWellFounded:294`).
> 5. `RischDEStructuralResidualWf` (mirror `RischDEStructuralResidual`, `Structural:252`, with the Wf-stage
>    references) + `rdeClearedWf_of_success_and_residual` (mirror `rdeCleared_of_success_and_residual`,
>    `Structural:294`, using (4) + `cRischDEG_some_imp_noCancel_of_primitive` [DONE]).
> 6. The headline `crischDESolveWf_field_of_residual` for the gated oracle
>    `fun f g => if cdenomNormalGateG f then (match cRischDEG [1] … with …) else none` — mirror
>    `crischDESolve_field_of_witness_residual` (`SoundnessCapstone:294`), using (5) +
>    `rischDE_field_of_cleared` (`RischFieldSpec:116`, REUSE, fuel-agnostic) + the new instance's two
>    `rfl`-reduction lemmas (built in P2).
>
> **★★ P1 DONE (2026-07-02).** All 6 checklist items landed gate-green in `RischDE/Structural.lean`
> (6 commits, bare `lake build` PASS at the end): items 1-3 as above; item 4 assembled as
> `rdeClearedIdentityWf_of_polyRDEIdentity` (takes the bare poly-RDE identity directly rather than the
> solver-success form, via three thin composition wrappers `cSPDEG_cleared_lifting_of_inputs` /
> `_polyRischDENoCancel_cleared_of_inputs` / `_at_boundDegree`); item 5 as `RischDEStructuralResidualWf` +
> `rdeClearedWf_of_success_and_residual`; item 6 as `crischDEWf_field_of_success_and_residual` — the
> carrier-generic field-level headline (no tower-gcd witness, no fuel, no `native_decide`), proved by
> composing (5) with the already fuel-agnostic `rischDE_field_of_cleared`. **The research-gate question is
> answered YES**: the fuel-free `cRischDEG` track supports the *exact same* field-level Risch-DE
> soundness as the fuel'd track, with no dependency on the open tower-spec (`CSPDEGClearedInputsGenWf`
> stays a hypothesis throughout, same as the fuel'd `CSPDEGClearedInputsGen`). **P2 (relocate + rebase the
> tower instance) is unblocked** — the target shape it must produce (`crischDESolveWf` + a
> `cdenomNormalGateG`-gated wrapper matching `crischDEWf_field_of_success_and_residual`'s hypotheses) now
> exists and is proven.

### P1 — Prove the Wf instance soundness *standalone* (no switch yet; low-risk, independent commit)
Before moving anything, make sure the target soundness exists on `cRischDEG`. Establish (or
confirm) a lemma of the exact shape the rebased instance will need — the analogue of
`crischDESolve_field_of_witness_residual` but for the gated `cRischDEG` oracle
`fun f g => if cdenomNormalGateG f then (match cRischDEG [1] … with …) else none`. Route it
through `cRischDEG_some_imp_stages` + `crischDESolveSoundWf_field` + the Wf stage soundness.
Keep it in a Wf-side file. Gate, commit. This de-risks Phase P2: if this soundness cannot be
built, STOP — the migration is blocked on the open tower-spec frontier (§2.4) and needs research,
not refactoring.

### P2 — Relocate + rebase the instance (the atomic switch; the big commit)
1. Create `Computable/Tower/RischDEInstance.lean` (imports `Tower.RischDEWellFounded`). Define
   `instCRischFieldCFracG : CRischField (CFracG β)` with `variable {β} [CField β] [CDiffField β]
   [CFieldDomain β] [CFracGcdCoreWf β] [CRischField β]` (note `CFracGcdCoreWf`), body identical to
   the fuel'd one but calling `cRischDEG ([CField.one] : CPolyG β) f.1.1 f.1.2 g.1.1 g.1.2`
   (no fuel). Move the two reduction lemmas here, restated over `cRischDEG`; their proofs stay
   `if_pos`/`if_neg`-on-the-gate + `rfl`.
2. Delete the old instance + reduction lemmas from `Tower/RischDE.lean`. (Leave `cRischDEG` and
   the fuel'd cluster for now — Phase P4 deletes them once orphaned.)
3. Add `Tower.RischDEInstance` to the `Computable` aggregator and to the import chain of every
   §3 consumer that referenced the instance through `Tower.RischDE`.
4. Re-wire the fuel'd soundness that broke: each theorem that used
   `crischDESolve_eq_solve_of_normal`/`cdenomNormalGateG_of_crischDESolve_isSome` to reach
   `cRischDEG` now reaches `cRischDEG`; repoint its downstream to the Phase-P1 Wf soundness and
   the Wf stage lemmas. This is the ~9-file bulk. Work one consumer file at a time; keep the
   overall build red only within this phase, green at its end.
5. Propagate `CFracGcdCore` → `CFracGcdCoreWf` wherever a consumer's signature or `variable` block
   now needs it (the instance's new requirement flows outward). The recursion instances (§2.2)
   discharge it automatically at concrete tower levels.
6. Gate bare → PASS. Verify the `Sources/…/Chapter6.lean` `native_decide` examples still evaluate
   (same results — `cRischDEG` computes the same solutions `cRischDEG` did within budget, and
   more beyond it). Commit.

> **P2-PREP DONE (2026-07-02).** The standalone soundness the switch needs is built gate-green in a
> **fuel-independent** file `RischDE/RawSolveField.lean`: `crischDERawSolveWf_field_of_residual` proves the
> field-level Risch-DE identity for the fuel-free raw solver `crischDERawSolveWf` (= the exact `match
> cRischDEG [1] … with …` runtime shape the rebased instance body will use) from a bare success + the
> residual `RawSolveResidualWf`, composing the Phase-P1 headline `crischDEWf_field_of_success_and_residual`.
> No fuel, no tower-gcd witness, no `native_decide`; axiom-clean. So step-4's "repoint downstream to the
> Phase-P1 Wf soundness" now has a concrete, proven target to point at.
>
> **★ P2 BLAST-RADIUS INVENTORY (empirical, 2026-07-02 — start the P2 session from here):**
> - **Reduction-lemma consumers = exactly 3 files** (`grep -rln
>   'crischDESolve_eq_solve_of_normal\|cdenomNormalGateG_of_crischDESolve_isSome'`): `Tower/RischDE.lean`
>   (self — the defining file), `SoundnessCapstone.lean`, `RischDE/NormalCorrect.lean`. These are the ONLY
>   files that *unfold the instance body via the reduction lemmas* and so break on the switch; each must
>   repoint to the Wf reduction lemmas + `crischDERawSolveWf_field_of_residual` (SoundnessCapstone's
>   `crischDESolve_field_of_witness_residual`) / the Wf raw-solve soundness.
> - **`CRischField.crischDESolve` on CFracG appears in ~24 files** but the vast majority are *runtime
>   `def` call sites* (they compute a solve; they do NOT reason about the fuel'd body), so they survive the
>   switch untouched — the body is still `Option (CFracG β)`-valued, just fuel-free. Do NOT touch these.
> - **`[CFracGcdCore β]` (fuel'd, non-Wf) = 48 occurrences across 9 files**, but this cuts across TWO
>   concerns: (a) the fuel'd **gcd** machinery `cgcdFFCore` (`Tower/GcdFFCore.lean`, `Tower/GcdFFCorrect.lean`,
>   `WeakNormalizerCorrect.lean`) — genuinely needs `[CFracGcdCore β]`, NOT touched by the RDE switch
>   (the Wf gcd `cgcdFFCoreWf` is a parallel track); vs (b) the RDE-**instance**-driven requirements in
>   `Tower/RischDE.lean` / `SoundnessCapstone.lean` / the `RischDE/Solve*.lean` chain — these flip to
>   `[CFracGcdCoreWf β]`. So the §2.2 propagation is narrower than 48; scope it by "does this signature need
>   the RDE instance or the fuel'd gcd?" per occurrence.
> - **The atomic character is real**: the new instance and the old cannot coexist (ambiguous
>   `CRischField (CFracG β)` resolution — §5 hard constraint), and `Tower/RischDEWellFounded.lean` (home of
>   `cRischDEG`) already imports `Tower/RischDE.lean` (home of the old instance), so the new instance file
>   must sit ABOVE `RischDEWellFounded` in the import DAG and the old instance deleted in the same commit.
>   The tree is red from the delete until all 3 reduction-consumers + the instance-driven `[CFracGcdCoreWf]`
>   signatures are repointed — a single focused session, not an end-of-session add-on.

### P3 — Point the catalog + public surface at the Wf oracle
Update `Sources/Doi_10_1007_b138171/Chapter6.lean` docstrings/aliases so `alg_6_6_*` describe the
now-fuel-free `crischDESolve`; ensure `IntegrationFunctionsCatalog` still `#check`s resolve. Gate,
commit.

### P4 — Retire the orphaned fuel'd solver + cluster
Now that nothing live uses them: delete `cRischDEG`, `towerRischDEFuel`, the fuel'd special-denom
cluster (`cRdeSpecialDenominatorG`, `cValuationG`, `cSpecialPolyG`, `cRdeNormalDenominatorG`,
`cWeakNormalizerG`), the fuel'd `cIntegrateGFull` if it too is now orphaned, and the fuel'd
`SoundnessCapstone`/RischDE-soundness lemmas that only certified them (keep any ported to Wf in
P1/P2). Delete the whole-file only when a `grep` for each name across `DeepWiki`+`Sources` is
empty; otherwise excise per-decl. Gate bare → PASS. Commit.

### P5 — Sweep + audit
`grep -rn '\bcRischDEG\b' DeepWiki Sources --include='*.lean'` empty (only `cRischDEG` remains);
`grep -rn 'towerRischDEFuel'` empty; Sources orphan audit clean; bare gate PASS; restate a couple
of the moved soundness theorems as `example`s to confirm they say the right thing. Update the
fuel-retirement memory and CLAUDE.md if any convention shifted.

## 5. Hard constraints (do NOT)
- **Do not** keep two `CRischField (CFracG β)` instances — instance resolution will go ambiguous.
  The switch is atomic (old out, new in) within P2.
- **Do not** introduce a `cRischDEG = cRischDEG` axiom/`sorry` bridge to shortcut P2.4 — there is
  no true such equation (fixed fuel ≠ well-founded result).
- **Do not** delete the fuel'd `SoundnessCapstone` partial-progress content in P4 without first
  porting whatever it proves onto `cRischDEG` in P1/P2 — it is progress toward the open tower
  spec, not dead code.
- **Do not** widen or weaken `crischDESolve`'s behaviour: the gated-oracle shape
  (`cdenomNormalGateG` then solve then `cisZeroG` guard) is a soundness gate; preserve it.
- Commit/push only when asked; one commit per phase; each gate-green.

## 6. Risk & the open-problem contingency
The mechanical layers (1 relocation, 2 typeclass swap) are bounded and low-risk. Layer 3
(soundness re-wiring) is the bulk and the main effort. Layer 4 (the open tower `CRischFieldSpec`)
is the genuine risk: **Phase P1 is the gate** — if the standalone Wf instance soundness cannot be
proved from the existing Wf development, the migration is blocked on research and should stop with
P1's findings recorded, leaving the fuel'd oracle in place. In that case, the fallback is to keep
`cRischDEG` solely as the tower base-solve and pursue the fuel-freeness elsewhere. Expect the full
migration to span multiple sessions; do not start P2 without P1 green.

## 7. Acceptance criteria (migration done)
- [ ] `grep -rn '\bcRischDEG\b'` over `*.lean` empty; `towerRischDEFuel` gone.
- [ ] `instCRischFieldCFracG.crischDESolve` runs `cRischDEG`; the tower is fuel-free end to end.
- [ ] The instance soundness (`crischDESolve`'s field identity) holds on the Wf oracle.
- [ ] `Sources/…/Chapter6.lean` `native_decide` examples pass unchanged; catalog `#check`s resolve.
- [ ] Bare `scripts/check.sh` → `GATE: PASS`; Sources orphan audit clean.
- [ ] One gate-green commit per phase; no `sorry`/axiom bridge introduced.

## P2-EXEC — the atomic switch execution plan (2026-07-03, take-the-risk run)

Grinding the full switch to green across loop turns (broken tree persists between turns; commit only when
the whole `lake build` passes). Steps 1–4 verified green twice already:

1. **Relocate instance** → `Tower/RischDEInstance.lean` (fuel-free, `cRischDEG` + `cdenomNormalGateG`,
   `[CFracGcdCoreWf β]`) + its two reduction lemmas `crischDESolveWf_eq_solve_of_normal` /
   `cdenomNormalGateG_of_crischDESolve_isSome`. ✓
2. **Delete old instance** from `Tower/RischDE.lean`; **relocate** the `cRischDEG` native_decide
   validations from `Tower/RischDEWellFounded.lean` up to the instance file; **wire 7 imports**
   (aggregator `Tower.lean` + the 6 synth-failure files: Hyperexp/Special, Tower/Reduce, Chapter6,
   OneShotSoundness, UnifiedFuelFree, TranscendentalOverAlgebraic). ✓
3. **Port `SoundnessCapstone`** — `RischDESuccessResidual`→`RischDESuccessResidualWf` (Wf stage-fns, drop
   `hyden`/`CTowerGcdWitness`), capstone `crischDESolveWf_field_of_witness_residual` via the P1 headline
   `crischDEWf_field_of_success_and_residual`; add `[CFracGcdCoreWf β]` to the section block. ✓
4. **Port `NormalCorrect`** — `crischDESolveWf_yden_ne_zero`, `RischDESuccessResidualCrux`→Wf,
   `residual_of_crux`→builds `RischDESuccessResidualWf` (using `cdegG_cSpecialPolyG_one_eq_zero`,
   from `TowerGcdUnit` and `hdvdB_of_dvd_wf`, `hdvdC_of_dvd_wf` from `NormCompleteness`),
   `crischDESolve_field_of_crux`→Wf. ✓
5. **Port `SolveNorm`** — add `[CFracGcdCoreWf β]` to Solver/Normality/Bridges/Capstone blocks; port the
   Normality section (`IsWeaklyNormalizedNorm`→Wf via `cSplitFactorFastG`, `isWeaklyNormalizedNorm_dvdB`→
   `dvd_dn_h_of_normal_wf`) and the Capstone that builds the now-Wf crux.
6. **Port `SolveNormCanon`** (4 `crischDESolve`/crux refs).
7. **Port `WeakNormalizerCorrect`** (instance-synth `[CFracGcdCoreWf β]` fixes; it reasons about functions).
8. **Port `NormCompleteness`** (instance-synth fixes).
9. Gate bare → PASS; commit. Then P4 (delete the orphaned fuel'd `cRischDEG`/`towerRischDEFuel`/special-denom
   cluster + fuel'd `SoundnessCapstone` residual) once `grep cRischDEG` is empty.
