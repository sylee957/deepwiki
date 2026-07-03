# gcd-core fuel migration (full) — phased plan

Goal: delete the fuel'd Euclidean base (`cdivmodG`/`cmodG`/`cdivG`/`cdvdG`/`cgcdExtG` in
`GenericPolyEngine`, the fuel'd tower gcd `cgcdFFCore`→`cgcdExtG`, the fuel'd Tower API
`cSplitFactorFastG`/`canonicalRepresentationFastG`/`cResidueResultantTowerG`/`cLogArgTowerG`/
`cSqfreeYunFFG`/`cSplitSquarefreeFactorFastG`, the fuel'd resultant/bezout `cresultantG`/`cbezoutOne`,
and the fuel'd Algebraic residue machinery), migrating every consumer to the fuel-free `…Wf` twins.

## Wf twins (mostly exist)
- Base: `cdivmodG→cdivmodWf`, `cmodG→cmodWf`, `cdivG→cdivWf`, `cdvdG→cdvdGWf`, `cgcdExtG→cgcdWf`
  (FuelFreeGcd); `cbezoutOne→cbezoutOneWf` (FuelFreeDiophantine).
- Tower gcd: `cgcdFFCore→cgcdFFCoreWf` (Tower/WellFounded; its raw core uses `cgcdWf`, NOT `cgcdExtG`).
- Tower API: `cSplitFactorFastGWf`, `canonicalRepresentationFastGWf`, `cResidueResultantTowerGWf`,
  `cLogArgTowerGWf`, `cSqfreeYunFFGWf` (Tower/WellFounded).
- MISSING twins to build: `cSplitSquarefreeFactorFastGWf`, `cParallelIntegrateTowerWf`, and a fuel-free
  resultant if `cresultantG` has none reachable (check `cresultantGWf`).

## Pins keeping the fuel'd base alive (beyond runtime)
1. Cataloged native_decide examples (Sources): `ex_3_5_2` (cSplitSquarefreeFactorFastG),
   `alg_10_3` (cParallelIntegrateTower), Ch5 residue-resultant examples.
2. Wf **soundness proofs** written against fuel'd defs: `LogPartTowerSoundness` (cLogArgTowerG ×8),
   `GcdFFCorrect`/`SoundnessCapstone` (cgcdTerminatesG), RadicalLogSoundness/GeneralLogSoundness
   (cresultantG).
3. Algebraic Trager machinery: `cresultantG`→`cAlgResidueResultant`/`discResultant`/`genResidueResultant`/
   `resYAtNode`; `cbezoutOne`→`radInvN`.

## Phase order (delete consumers before the ops they use)
- **G1 (done-first, safe):** re-point the swell-demo benchmarks' `cgcdExtG` → `cgcdWf` (fuel-free naive
  Euclidean; preserves the swell demonstration). Clears `cgcdExtG`'s Bench/GcdFF runtime consumers.
- **G2:** build the two missing Wf twins (`cSplitSquarefreeFactorFastGWf`, `cParallelIntegrateTowerWf`)
  + `cresultantGWf` if absent; add `…Wf_eq`/native_decide equivalence at the cataloged inputs.
- **G3:** re-point runtime consumers of the fuel'd Tower API to the Wf twins (Tower/Integrate internal
  chain, MixedTowerIntegrate, Hyperexp); re-catalog the book examples to the Wf versions.
- **G4:** migrate the Wf soundness proofs off the fuel'd defs. REFINED (probed 2026-07-03): the
  Wf soundness lemmas ALREADY EXIST in `OneShotAssembly` (`cLogArgTowerGWf_eq_linear_factor`,
  `cIntegrateReducedGWf_logs_eq_per_root`). The fuel'd soundness lemmas in `LogPartTowerSoundness`
  (`cLogArgTowerG_eq_linear_factor`, `cLogArgTowerG_associated_linear_factor`,
  `roots_residueResultantTowerG_eq_residues[_qfunNZG]`) feed exactly ONE live theorem:
  `field_identity_of_cIntegrateReducedGWf_of_residueMatch_qfunNZG` (Wf-facing, but its *proof* routes
  through the fuel'd lemmas). So G4 = re-route that one theorem's proof through the OneShotAssembly Wf
  lemmas, then the fuel'd `LogPartTowerSoundness` soundness island (cLogArgTowerG/cResidueResultantTowerG
  fuel'd theorems) is orphaned and deletable. Bounded proof work, not from-scratch. Similarly probe
  `cgcdTerminatesG` (feeds GcdFFCorrect's `associated_toPolyG_cgcdFFCore` — check for a Wf twin lemma).
- **G5:** re-point the Algebraic Trager machinery (cresultantG/cbezoutOne consumers) to Wf.
- **G6:** now-orphaned: delete the fuel'd Tower API + `cresultantG`/`cbezoutOne` + `cgcdFFCore` +
  their fuel'd correctness files (FieldGcd/ResultantGenericCore/GenericBezout fuel'd theorems, GcdFFCorrect).
- **G7:** delete the fuel'd Euclidean base `cdivmodG`/`cmodG`/`cdivG`/`cdvdG`/`cgcdExtG` from
  GenericPolyEngine once all consumers are gone. Final grep `(fuel : ℕ)` in the gcd core empty.

Each phase: block-comment-aware consumer scan INCLUDING Sources/, gate-green per phase, commit per phase.

## Progress log
- **G1** ✅ benchmarks `cgcdExtG`→`cgcdWf`.
- **G2a** ✅ built `cSplitSquarefreeFactorFastGWf`. (Resultant twin `cresultantWf` already existed.)
- **G3a** ✅ `cIntegrateHyperexpG` made fully fuel-free (re-point to `canonicalRepresentationFastGWf` +
  drop `fuel`; 6 native_decide sites updated) — removed `canonicalRepresentationFastG`'s last runtime pin.
- **G3b** ✅ re-cataloged Ch3 (`ex_3_5_1/2`) + Ch5 (`alg_5_6_*`, `ex_5_6_2`) to the Wf Tower API.
- **G4** ✅ retired the fuel'd residue engine: the fuel'd `cLogArgTowerG` soundness was a DEAD LEAF island
  (`cLogArgTowerG_eq_linear_factor` only in `#print axioms`; superseded by `cLogArgTowerGWf_eq_linear_factor`
  in OneShotAssembly) — deleted the 2 theorems, orphaning + deleting `cLogArgTowerG` + `cResidueResultantTowerG`.
  Kept shared `cAmcDdG`.
- **G6a** ✅ deleted orphaned `cSplitSquarefreeFactorFastG`.
- **REMAINING — split-factor correctness (G6b):** `SplitFactorTowerCorrectG` (10 decls) + `Tower/Unify`
  (2 decls) are a DECL-DEAD island — NO other file uses any of their decls in code (the one apparent hit was
  a docstring). BUT they are **import waypoints**: deleting them breaks RadicalIntegralSoundness et al., which
  rely on *transitive* imports flowing through them (`SplitFactorTowerCorrectG`→`GcdFFCorrect`+`Unify`;
  `Unify`→`Integrate`+`CanonicalFieldIdentity` — the derivation/`toPolyG` lemmas). ★ A naive delete-and-remove-import
  attempt broke the build (RadicalIntegralSoundness:461 `radDeriv_radGen_sound_qx`, OneShotSoundness) and was
  reverted. CORRECT procedure: (1) for EACH importer of the two files, add DIRECT imports of what it used
  transitively (candidates: `Tower.GcdFFCorrect`, `Tower.Integrate`, `CanonicalFieldIdentity`) — verify by
  building each importer green with the waypoint import removed but the file still present; (2) once all
  importers are self-sufficient, delete `SplitFactorTowerCorrectG.lean` + `Tower/Unify.lean` + remove the
  now-safe imports; (3) that orphans `cSplitFactorFastG`+`canonicalRepresentationFastG` (Tower/Integrate) →
  delete. Then G5 (Algebraic `cSqfreeYunFFG`/`cresultantG`/`cbezoutOne`) and G7 (Euclidean base) remain.
