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
- **G6b** ✅ retired the fuel'd §5 split-factor/canonical-rep Tower layer: (G6b-1) slimmed SplitFactorTowerCorrectG
  to its live `CDiffFieldSpec` bridge (`baseDerivQ` + `instCDiffFieldSpecQFunNZG`), deleting the dead fuel'd
  correctness decls; (G6b-2) slimmed Tower/Unify to a thin re-export waypoint (2 dead probe theorems removed)
  and deleted the now-orphaned `cSplitFactorFastG` + `canonicalRepresentationFastG` from Tower/Integrate.
  Wf twins carry all runtime. Kept the Yun squarefree section (`cSqfreeYunFFG`, still used by G5).
- **cleanup** ✅ deleted dead legacy `cSplitFactor` (MonomialDeriv, 0 consumers).

## G5 Algebraic — cSqfreeYunFFG arc COMPLETE (G5a–e)
- **G5a** ✅ radical integral-basis family (`radSquarePart`…`radGenus`) made fuel-free (re-point to
  `cSqfreeYunFFGWf`, drop fuel; downstream CantorComposition/HyperellipticDivisor + ch2 docstrings fixed).
- **G5b** ✅ deleted the redundant fuel'd `cIntegrateAlgebraic` island (RadicalIntegrateFull, 15 decls,
  superseded by `cIntegrateAlgebraicWf` which the Hdl catalog already uses).
- **G5c** ✅ deleted the orphaned fuel'd `radIntegrateRational` + its mc-dispatch validation (redundant with
  `radIntegrateRationalWf`); kept shared `mcRho/mcR/mcB/mcRhoQx` (Sources AppendixA uses them — build cross-check
  caught a missed `mcRhoQx`).
- **G5d** ✅ made `badPrimes`/`round2Step` fuel-free (the PRODUCTION path `integralBasisLoop→round2Pass→
  badPrimesOrder` was ALREADY fuel-free — `badPrimesOrder` uses `cSqfreeYunFFGWf`, `integralBasisLoop`'s fuel is a
  STRUCTURAL iteration bound; only the standalone example versions still threaded gcd-fuel).
- **G5e** ✅ deleted the now-orphaned fuel'd `cSqfreeYunFFG` + `cSqfreeYunFFGgo`.
- ★★ KEY DISTINCTION: **GCD-fuel** (threads to `cSqfreeYunFFG`/`cgcdFFCore` — REMOVE) vs **STRUCTURAL fuel**
  (`integralBasisLoop`'s `deg(disc)+1` iteration bound, `radReduceCase*Iterate`'s multiplicity counter — KEEP;
  they're meaningful termination bounds, not the "fuel ran out" ugliness). Not all `(fuel : ℕ)` is gcd-fuel.

## G5 COMPLETE (G5a–i) — the whole Algebraic Trager machinery is fuel-free
- G5f `cbezoutOne`→`cbezoutOneWf` (radInvN re-point, then deleted).
- G5g `discResultant`→`cresultantWf` (native_decide, clean).
- G5h migrated the residue-resultant soundness onto `cresultantWf`: re-pointed cAlgResidueResultant/
  genResidueResultant/resYAtNode + fixed all native_decide sites + migrated the abstract leaf
  compute-bridge theorems (toPolyG_cAlgResidueResultant_eq_of_eval / toPolyG_genResidueResultant_eq_of_eval /
  toK_cresultantG_cAlgResidueNorm) — SIMPLER, since toPolyG_cresultantWf carries no fuel-adequacy hypothesis.
- G5i deleted the fuel'd `cresultantG` def + its orphaned correctness (cresultantG_cnormG/toPolyG_cresultantG_of_ge/
  toPolyG_cresultantG), keeping the LIVE interpolation lemmas.
- ★ These residue "compute-bridge" soundness theorems were LEAVES (only #print axioms) whose PROOFS used the
  fuel'd correctness — migrating them (swap toPolyG_cresultantG→toPolyG_cresultantWf, drop fuel/hfuel) was
  the one genuinely-proof-editing part, and it was mechanical once toPolyG_cresultantWf was found to have the
  IDENTICAL conclusion (= Polynomial.resultant …).

## G5 (OLD, superseded) — cresultantG + cbezoutOne (deeper: proof-migration, not mechanical)
- `cresultantG` → `cAlgResidueResultant`/`genResidueResultant`/`resYAtNode`/`discResultant` + a real CORRECTNESS
  layer (`toPolyG_cresultantG`, `toPolyG_cAlgResidueResultant_eq_of_eval`, the residue-soundness theorems in
  AlgebraicResidues/GeneralResidues/RadicalLogSoundness/GeneralLogSoundness). Wf correctness EXISTS
  (`toPolyG_cresultantWf`, FuelFreeResultant:115), so it's tractable, but re-pointing needs re-routing those
  soundness proofs through the Wf lemma — genuine proof-migration, do fresh.
- `cbezoutOne` → `radInvN` (RadicalGeneralN); `cbezoutOneWf` exists — check if a clean re-point.

## G7 STARTED — base layer
- **G7a** ✅ deleted the dead-leaf fuel'd `SoundnessCapstone` (9 decls, 16 `cgcdFFCore` uses, zero external
  code consumers, superseded by the fuel-free RDE soundness) — re-pointed NormalCorrect's waypoint import.
- After G7a, genuine `CFracGcdCore.cgcdFFCore` CODE uses are confined to the self-contained base cluster:
  `Tower/GcdFFCore` (the `CFracGcdCore` class + the fuel'd instances `instCFracGcdCoreQ`/`RadX3`/`Q`,
  `instCTowerGcdWitnessQ_of_terminates`), `Tower/GcdFFCorrect` (correctness). Tower/Integrate's remaining
  `cgcdFFCore` mentions are DOCSTRINGS.
- REMAINING `[CFracGcdCore α]` binder sites: SolveNorm(6)/SolveExhaustiveness(5)/Structural(4)/Completeness(1)/
  MixedTowerIntegrate(1). ★ Structural GENUINELY uses it in some decls (the `omit [CFracGcdCore α] in` pattern
  shows deliberate per-decl inclusion) — NOT all vestigial. Verify per-decl before dropping.
- G7 FINISH (fresh, delicate): (1) drop the truly-vestigial binders; (2) verify no LIVE code needs the fuel'd
  `CFracGcdCore` INSTANCE (instance resolution is invisible to name-scans — delete-and-build is the test);
  (3) delete the fuel'd instances + Euclidean base (`cdivmodG`/`cmodG`/`cdivG`/`cdvdG`/`cgcdExtG`/`cgcdFFCore`)
  + fuel'd correctness (`FieldGcd`/`ResultantGenericCore` cdivG/cmodG parts/`GenericBezout`/`GcdFFCore`/`GcdFFCorrect`),
  tracing each the dead-leaf way. The deepest layer; do with fresh focus (fatigue-errors surfaced here).

## G7 progress + the base-is-MIXED finding
- **G7a** deleted dead-leaf SoundnessCapstone. **G7b** deleted vestigial `instCFracGcdCoreRadX3` (last external
  cgcdExtG tie). **G7c** dropped all leftover abstract `[CFracGcdCore α]` binders (RDE files + Tower/Integrate)
  after EMPIRICALLY confirming (instance-neutralization test) that ONLY GcdFFCorrect demands the fuel'd instances.
- ★★ CRUCIAL: the fuel'd base is NOT wholesale-deletable — it's INTERLEAVED with critical LIVE infrastructure:
  - **FieldGcd** = fuel'd `cgcdExtG` correctness + LIVE `cderivG` (the formal derivative, 25+ consumers!),
    `associated_toPolyG_cmonicG`, `cleadG_cnormG`/`cdegG_cnormG`/`stepG_length_lt`/`length_cnormG_of_ne`
    (the Wf engine — FuelFreeGcd/FuelFreeResultant/WellFounded — depends on these).
  - **GcdFFCorrect** = fuel'd `cgcdFFCore` correctness + LIVE GBPoly/PRS correctness (`CgcdBCorrect`,
    `CPrimPRSGenAssocReg`, `toGBCoeffPoly*`, `gbnormCore*`) used by the Wf fraction-free gcd via PrimPRSRegular.
  - **GenericPolyEngine** = LIVE CPolyG/CField base + the fuel'd Euclidean ops.
  - **ResultantGenericCore** = LIVE interpolation lemmas + fuel'd cdivG/cmodG correctness.
- G7 FINISH = SURGICAL per-decl deletion within these mixed files: remove ONLY the fuel'd ops
  (`cdivmodG`/`cmodG`/`cdivG`/`cdvdG`/`cgcdExtG`/`cgcdFFCore` + fuel'd instances/class) and their fuel'd
  correctness THEOREMS, keeping the pervasive live infra. A slip breaks the whole engine (cderivG is
  load-bearing everywhere) — do with fresh focus + gate after every file. Order: delete the fuel'd correctness
  theorems first (they consume the ops), then the ops, then the class+instances last.

## G7 base-deletion ATTEMPT + entanglement finding (do NOT retry naively)
Attempted the surgical base-op-correctness deletion (Field re-point + delete the fuel'd correctness theorems
from TowerGlue/ResultantGenericCore/GcdFFCorrect/FieldGcd/GcdFF). It BUILT PARTIALLY then broke + was fully
reverted (tree green at HEAD). Two lessons:
1. **GcdFF benchmarks are a cluster** — deleting `cgcdFFGen`/`gBenchFFGcd` orphans `benchFFGcd2_lt_benchExtGcd2`
   etc.; the whole fuel'd FF-gcd + swell-benchmark cluster must go together (or none).
2. **The fuel'd correctness is an ENTANGLED WEB via HYPOTHESES** — `cgcdTerminatesG` (FieldGcd) is used as a
   `(hterm : cgcdTerminatesG …)` HYPOTHESIS in `GcdFFCorrect`:887 + referenced by `PrimPRSRegular` — invisible
   to an ops-reference scan. Deleting a fuel'd correctness lemma requires mapping its FULL transitive closure
   (everything using it as hypothesis or term), then deleting the whole closure coordinately.
- ★ CORRECT G7-finish approach (fresh session): (a) build the complete fuel'd-correctness dependency graph
  (nodes = decls in FieldGcd/GcdFFCorrect/ResultantGenericCore/GenericBezout/GcdFF that mention ANY of
  cdivmodG/cmodG/cdivG/cdvdG/cgcdExtG/cgcdFFCore/cgcdFFGen/cgcdTerminatesG/the fuel'd instances — via term OR
  hypothesis), close it transitively, VERIFY the closure has no live (Wf/soundness) consumer; (b) delete the
  whole closure + the GcdFF benchmark cluster + the ops + class/instances in ONE coordinated pass, gate.
- The base ops are now DEAD (no live runtime/soundness consumer — only their own entangled correctness web),
  so leaving them is harmless; the deletion is the "100%-fuel-free" completion, needing the closure approach.

## Status after G6b: CLEAN WINS EXHAUSTED (superseded — see G5 above; more clean wins were found + landed)
The entire fuel'd §5/§6 Tower API is retired (split-factor, canonical-rep, squarefree-split, residue engine,
hyperexp driver). A full 0-consumer scan finds NO remaining clean fuel'd deletions. The three remaining
phases are LARGE interdependent cataloged-API cascades — deliberate focused sessions, not autonomous nibbles:
- **G5 (Algebraic)** — the whole `radical*` family (`radSquarePart`/`radSquarefreePart`/`radIntegralBasis`/
  `radSplitExact`/`radBasisDiscriminant`/`radGenus`/…) threads fuel down to `cSqfreeYunFFG`; `radGenus` is used
  by CantorComposition/HyperellipticDivisor/GeneralPicard* — dropping fuel there has a huge blast radius and
  requires re-cataloging the algebraic-function book (`Sources/Hdl_1721_1_15391/Chapter2` `ch2_integralBasis`).
  Also `cresultantG`→`cAlgResidueResultant`/`discResultant`/`genResidueResultant` and `cbezoutOne`→`radInvN`.
  Wf twins (`cSqfreeYunFFGWf`/`cresultantWf`/`cbezoutOneWf`) all exist — the work is re-point + drop-fuel +
  re-catalog across the whole Algebraic arc. ★ SCOPE DECISION NEEDED: re-catalog ch2 to the Wf versions?
- **G2b (parallel)** — port `cParallelIntegrate`→`SystemQ`→`AnsatzQ`→`SquarefreeFactorsQ` to Wf; re-catalog `alg_10_3`.
- **G7 (Euclidean base)** — `cdivmodG`/`cmodG`/`cdivG`/`cdvdG`/`cgcdExtG`/`cgcdFFCore` are held alive by the
  fuel'd gcd INSTANCES (`instCFracGcdCoreQ`/`RadX3`/`Q`, `instCTowerGcdWitnessQ`) + the Algebraic arc +
  `cgcdTerminatesG` (feeds the Wf gcd correctness). Blocked on G5. Once the fuel'd Algebraic consumers +
  instances are gone, trace FieldGcd/ResultantGenericCore/GenericBezout the dead-leaf way and delete the base.
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

  ★★ CORRECTED (second probe): SplitFactorTowerCorrectG is NOT a dead island — it MIXES dead fuel'd
  correctness (`canonicalRepresentationFastG_reconstructs_qfunNZG`, `_simple_proper_qfunNZG`,
  `cSplitFactorFastG_isSplittingFactorizationGen_qfunNZG`, `cstepGQ`, `associated_toPolyG_cstepGQ`,
  `associated_toPolyG_cgcdFFCore_reg`, the `C*RegularQ` classes) with **LIVE infrastructure**: `baseDerivQ`
  (used by RadicalIntegralSoundness) and the INSTANCE `instCDiffFieldSpecQFunNZG` (load-bearing — instance
  usage is invisible to a name-scan; its absence is the "failed to synthesize CDiffFieldSpec" error).
  So G6b = SURGICAL SLIM: delete only the dead fuel'd correctness decls, KEEP `baseDerivQ` /
  `instCDiffFieldSpecQFunNZG` / `toPolyG_cone_qfunNZG` (and the file itself as import waypoint). Then delete
  Tower/Unify's 2 dead theorems (keep the file if it's still an import waypoint for Chapter5/6, else delete
  with direct-import fixes). ★ SCAN-BUG LESSON: the consumer-scan regex MUST allow `noncomputable `/`private `/
  `@[…] ` prefixes before def/theorem/instance — the naive `^\s*(def|theorem|…)` misses `noncomputable def`
  and instances, giving false "dead island" verdicts. Always cross-check a wholesale-delete with an actual
  `lake build` before trusting the scan.
