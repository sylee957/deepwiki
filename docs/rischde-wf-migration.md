# Migration plan: switch the tower Risch-DE oracle to the fuel-free `cRischDEGWf`

Self-contained instructions for retiring the fuel-threaded `cRischDEG` Risch-DE solver in
favour of the well-founded `cRischDEGWf`, at the level that matters: the
`CRischField (QFunNZG β)` **instance**. Written to be executed by an agent without prior
conversation context. Read this whole file before touching anything.

**One-line goal.** Make the tower Risch-DE recursion *actually* fuel-free by rebasing the
`CRischField (QFunNZG β)` instance's `crischDESolve` from `cRischDEG […] towerRischDEFuel`
onto `cRischDEGWf`, then retire the orphaned fuel'd solver + its soundness track.

**Status when this plan was written (2026-07-02).** Assessed only — no code changed. Two
reversible spikes established the scope (a naïve instance def-swap hit a module-layering wall
and was reverted; the tree is green). This is a **multi-session, high-blast-radius** effort;
do it phased and gate-green per phase, or not at all.

---

## 1. Why this migration (the payoff)

The transcendental engine already has a full fuel-free layer: `cRischDEGWf`
(`Computable/Tower/RischDEWellFounded.lean:430`), `cIntegrateGFullWf`
(`Computable/UnifiedFuelFree.lean`), and axiom-clean Wf soundness
(`field_identity_of_cIntegrateGFullWf_of_checkIdentityG`, `crischDESolveSoundWf_field`). So the
top of the pipeline *looks* fuel-free.

**But the tower recursion re-introduces fuel at every level.** The base solve of the tower is
the typeclass method `CRischField.crischDESolve`. Its only non-trivial instance,
`instCRischFieldQFunNZG : CRischField (QFunNZG β)` (`Computable/Tower/RischDE.lean:465`), is
defined as

```
crischDESolve f g :=
  if cdenomNormalGateG f then
    match CPolyG.cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2 with
    | none => none | some (ynum, yden) => if h : cisZeroG yden = false then some ⟨(ynum,yden),h⟩ else none
  else none
```

i.e. it runs the **fuel'd** `cRischDEG` with a fixed `towerRischDEFuel := 60`
(`Computable/Tower/RischDE.lean:431`). Because `cRischDEGWf` recurses into `[CRischField β]`
for its own base solves, running `cRischDEGWf` at level `n+1` calls this instance at level `n`
— which is `cRischDEG`. So today's "Wf tower" still bottoms through fuel'd `cRischDEG` at every
recursion step, and the fixed fuel `60` is a latent incompleteness (deep towers can exhaust
it). Only rebasing the **instance** onto `cRischDEGWf` makes the whole tower genuinely
fuel-free and fuel-budget-free.

`cRischDEG` currently has ~17 consumers (this instance + the fuel'd soundness development that
proves `crischDESolve`'s headline correctness). Retiring it means rebasing the instance and
porting that soundness.

## 2. The four entangled layers (why it is not a def-swap)

1. **Module layering.** `cRischDEGWf` is defined in `Tower/RischDEWellFounded.lean`, which
   `import`s `Tower/RischDE.lean` — the file that holds the instance *and* defines `cRischDEG`.
   The instance (lower layer) cannot forward-reference `cRischDEGWf`. The instance + its two
   `rfl`-reduction lemmas must **move** to a module that comes *after* `cRischDEGWf`.

2. **Typeclass swap `CFracGcdCore β` → `CFracGcdCoreWf β`.** The fuel'd instance's `variable`
   block is `{β} [CField β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β] [CRischField β]`
   (`Computable/Tower/RischDE.lean:454`). But `cRischDEGWf`'s block is
   `[CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]`
   (`Computable/Tower/RischDEWellFounded.lean:418`) — a **different** gcd class. The rebased
   instance, every one of its consumers, and the whole tower recursion must therefore carry
   `CFracGcdCoreWf`. Feasible: the recursion instances exist —
   `instCFracGcdCoreWfQFunNZG : CFracGcdCoreWf (QFunNZG β)` (`Computable/Tower/WellFounded.lean:151`),
   `CFracGcdCoreWf ℚ` (`…:139`), `CFracGcdCoreWf RadX3` (`Computable/MixedTowerIntegrate.lean:96`).

3. **Soundness re-wiring (~9 files).** The fuel'd soundness development reasons symbolically
   about `cRischDEG [1] towerRischDEFuel` and unfolds the instance to it by `rfl` via
   `crischDESolve_eq_solve_of_normal` (`Computable/Tower/RischDE.lean:478`) and
   `cdenomNormalGateG_of_crischDESolve_isSome` (`…:496`). There is **no `cRischDEG = cRischDEGWf`
   bridge** (they are parallel implementations; a fixed `towerRischDEFuel` cannot equal the
   well-founded result in general), so the soundness cannot transfer by rewrite — it must be
   re-established proof-by-proof against the existing Wf development
   (`cRischDEGWf_some_imp_stages`, `Computable/Tower/RischDEWellFounded.lean:449`;
   `crischDESolveSoundWf_field`, `Computable/RischDE/SolveSoundWf.lean:174`). The headline to
   port is `crischDESolve_field_of_witness_residual` (`Computable/SoundnessCapstone.lean:294`).

4. **Open-problem entanglement.** There is deliberately **no** `CRischFieldSpec (QFunNZG β)`
   instance — it is a known-open goal (`Computable/SoundnessCapstone.lean:476`,
   `Computable/RischDE/SolveNorm.lean:493`). The fuel'd `SoundnessCapstone` is *partial progress
   toward it*. The migration must **port** that partial progress onto `cRischDEGWf`, not discard
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
- `cRischDEGWf` + `cRischDEGWf_some_imp_stages` (`Computable/Tower/RischDEWellFounded.lean`).
- Wf stages `cRdeNormalDenominatorGWf` / `cRdeSpecialDenominatorGWf` / `cValuationGWf` /
  `cSPDEGWf` / `cPolyRischDEGWf` (`…WellFounded.lean`, `…RischDEWellFounded.lean`).
- Standalone Wf solver + soundness `crischDESolveSoundWf` / `crischDESolveSoundWf_field`
  (`Computable/RischDE/SolveSoundWf.lean`); `cWeakNormalizerGWf`, `cdiophantineGWf`, etc.
- `CFracGcdCoreWf` recursion instances (§2.2).

Instance consumers (import chains to update): `SoundnessCapstone`, `MixedTowerIntegrate`,
`TranscendentalOverAlgebraic`, `RischDE/SolveSound`, `RischDE/SolveNorm`, `RischDE/SolveNormCanon`,
`Hyperexp/FullSoundness`, `Tower/GcdFF`, and the catalog `Sources/Doi_10_1007_b138171/Chapter6.lean`
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
   has `Tower.RischDE`), so it sees both `cRischDEGWf` and `QFunNZG`/`cdenomNormalGateG`.

### P1 — Prove the Wf instance soundness *standalone* (no switch yet; low-risk, independent commit)
Before moving anything, make sure the target soundness exists on `cRischDEGWf`. Establish (or
confirm) a lemma of the exact shape the rebased instance will need — the analogue of
`crischDESolve_field_of_witness_residual` but for the gated `cRischDEGWf` oracle
`fun f g => if cdenomNormalGateG f then (match cRischDEGWf [1] … with …) else none`. Route it
through `cRischDEGWf_some_imp_stages` + `crischDESolveSoundWf_field` + the Wf stage soundness.
Keep it in a Wf-side file. Gate, commit. This de-risks Phase P2: if this soundness cannot be
built, STOP — the migration is blocked on the open tower-spec frontier (§2.4) and needs research,
not refactoring.

### P2 — Relocate + rebase the instance (the atomic switch; the big commit)
1. Create `Computable/Tower/RischDEInstance.lean` (imports `Tower.RischDEWellFounded`). Define
   `instCRischFieldQFunNZG : CRischField (QFunNZG β)` with `variable {β} [CField β] [CDiffField β]
   [CFieldDomain β] [CFracGcdCoreWf β] [CRischField β]` (note `CFracGcdCoreWf`), body identical to
   the fuel'd one but calling `cRischDEGWf ([CField.one] : CPolyG β) f.1.1 f.1.2 g.1.1 g.1.2`
   (no fuel). Move the two reduction lemmas here, restated over `cRischDEGWf`; their proofs stay
   `if_pos`/`if_neg`-on-the-gate + `rfl`.
2. Delete the old instance + reduction lemmas from `Tower/RischDE.lean`. (Leave `cRischDEG` and
   the fuel'd cluster for now — Phase P4 deletes them once orphaned.)
3. Add `Tower.RischDEInstance` to the `Computable` aggregator and to the import chain of every
   §3 consumer that referenced the instance through `Tower.RischDE`.
4. Re-wire the fuel'd soundness that broke: each theorem that used
   `crischDESolve_eq_solve_of_normal`/`cdenomNormalGateG_of_crischDESolve_isSome` to reach
   `cRischDEG` now reaches `cRischDEGWf`; repoint its downstream to the Phase-P1 Wf soundness and
   the Wf stage lemmas. This is the ~9-file bulk. Work one consumer file at a time; keep the
   overall build red only within this phase, green at its end.
5. Propagate `CFracGcdCore` → `CFracGcdCoreWf` wherever a consumer's signature or `variable` block
   now needs it (the instance's new requirement flows outward). The recursion instances (§2.2)
   discharge it automatically at concrete tower levels.
6. Gate bare → PASS. Verify the `Sources/…/Chapter6.lean` `native_decide` examples still evaluate
   (same results — `cRischDEGWf` computes the same solutions `cRischDEG` did within budget, and
   more beyond it). Commit.

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
`grep -rn '\bcRischDEG\b' DeepWiki Sources --include='*.lean'` empty (only `cRischDEGWf` remains);
`grep -rn 'towerRischDEFuel'` empty; Sources orphan audit clean; bare gate PASS; restate a couple
of the moved soundness theorems as `example`s to confirm they say the right thing. Update the
fuel-retirement memory and CLAUDE.md if any convention shifted.

## 5. Hard constraints (do NOT)
- **Do not** keep two `CRischField (QFunNZG β)` instances — instance resolution will go ambiguous.
  The switch is atomic (old out, new in) within P2.
- **Do not** introduce a `cRischDEG = cRischDEGWf` axiom/`sorry` bridge to shortcut P2.4 — there is
  no true such equation (fixed fuel ≠ well-founded result).
- **Do not** delete the fuel'd `SoundnessCapstone` partial-progress content in P4 without first
  porting whatever it proves onto `cRischDEGWf` in P1/P2 — it is progress toward the open tower
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
- [ ] `instCRischFieldQFunNZG.crischDESolve` runs `cRischDEGWf`; the tower is fuel-free end to end.
- [ ] The instance soundness (`crischDESolve`'s field identity) holds on the Wf oracle.
- [ ] `Sources/…/Chapter6.lean` `native_decide` examples pass unchanged; catalog `#check`s resolve.
- [ ] Bare `scripts/check.sh` → `GATE: PASS`; Sources orphan audit clean.
- [ ] One gate-green commit per phase; no `sorry`/axiom bridge introduced.
