# Track-B consolidation of the symbolic-integration engine

Track A (the nested-directory reorg) landed 2026-07-02. Track B is the *semantic* consolidation
deferred from `docs/refactor-symbolic-integration.md` §7. It is three independent, incremental,
low-marginal-value-but-consistency-improving efforts. Each is gate-green per commit. Do **not**
treat these as one big-bang; land them lemma-batch by lemma-batch.

## Item 1 — the `@[denote]` simp-attr unification (IN PROGRESS)

**Goal.** Every *denotation-push homomorphism square* — `toPolyG (op a b …) = Op (toPolyG a) (toPolyG b) …`
or `toK (op …) = Op (toK …)` — carries `@[denote]` and lives in the file that defines `op`, so the one
`denote` simp set (`DeepWiki/Transfer/Denote.lean`, driving the `transfer` elaborator + every
`simp only [denote]`) is the single canonical push mechanism. Today the *core* engine ops
(`GenericPolyEngine`: caddG/cmulG/cnegG/cscaleG/cshiftG/cpowG/…) are tagged; the algorithm-specific
squares mostly are not (28 of 151 `toPolyG_*`/`toK_*` theorems tagged at start).

**Curation criterion (hard-won — automation is NOT sufficient).** A `toPolyG_*`/`toK_*` theorem is a
`@[denote]` candidate **iff all** hold:
- It is an **equation** (`=`), not `≠` / `∣` / `↔` / `<` / `≤`.
- Its **LHS is `toPolyG (op …)` or `toK (op …)`** — a denotation applied to a computable op — and the
  **RHS pushes the denotation inward** (abstract op over `toPolyG`/`toK` of the arguments). This excludes:
  - *multiply-back* identities (`toPolyG (num a) * toPolyG (gcd a) = toPolyG a.1.1`) — LHS is a product of
    denotations, not `toPolyG (op)`.
  - *reading* lemmas (`(toPolyG p).coeff i = …`, `.natDegree`, `.eval`, `_getD`) — LHS projects out of a
    denotation.
  - *expansion* lemmas (`toPolyG p = ∑ …`) — would loop with the structural cons/nil rules.
- It is **unconditional** — no hypothesis binder (`hconst`, `hsolve`, `_eq_of_*`, `_of_len_le_*`,
  `_eq_zero_of_*`). Conditional squares create side-goals in `simp [denote]`; keep them out of the set.
- Its op is **atomic w.r.t. the set** — not already decomposable by other `@[denote]` rules into a
  *different* normal form. Exclude composite convenience lemmas that overlap tagged decompositions
  (`toPolyG_termG` = cscaleG∘div∘foldl∘clagNumG, `toPolyG_zero_cons` = `[0,c]` overlapping `toPolyG_cons`).
  Redundant-but-agreeing overlap is harmless; *competing* normal forms are the risk.
- It is **reused across files** (foundational), not a one-off local soundness/example helper. A
  one-off square (e.g. `toK_radicandX3p1`, `toPolyG_radInv2`, the `qxOfNum`/`cLaurentShiftG` families)
  earns `@[denote]` only when a second consumer appears — same "earn your generality" rule as typeclass
  params. Tagging one-offs only adds global-set noise.

**Verification.** The gate (`lake build` = all `simp [denote]`/`transfer` sites + native_decide) is the
empirical confluence/looping check. A tagged lemma that breaks a downstream proof (wrong normal form or
loop) is reverted, not forced.

**Consumption-site rewrite is a SEPARATE, later sub-item.** Converting the 163 `rw [toPolyG_*]` chains
+ 30 `simp only [… toPolyG_* …]` sites to `simp [denote]` / `transfer` is higher-churn and riskier
(rw chains often need ordering simp won't replicate). Do it opportunistically per file, never as a sweep.

### Batches
- **Batch 1 (foundational atomic squares) — DONE:** toK_foldl_add, toK_foldl_csub_mul
  (GenericPolyEngine), toPolyG_cresultantWf (FuelFreeResultant), toPolyG_cSubresultantG
  (SubresultantSpec), toPolyG_liftGBPolyCoreG, toPolyG_foldl_cmulG (GcdFFCorrect),
  toPolyG_foldl_cmulG_plainList, toPolyG_cmonicG_eq_normalize (YunSquarefreeDecomposition),
  toPolyG_cAmcDdG (LogPartTowerSoundness), toPolyG_append (RadicalDerivationInvariant).
- **Batch 2 (determinant homomorphisms) — DONE:** toK_cDetGn, toK_cDetG (Subresultant) — the
  `toK (cDetGn n M) = listDetn n (map toK M)` cofactor-determinant push-squares underlying the
  resultant/subresultant/Bareiss layer. (`toK_cDetG_eq_det` stays untagged: conditional matrix bridge.)
- **Foundational layer now COMPLETE.** The ~20 remaining untagged unconditional squares are, by the
  curation criteria, deliberately *not* `@[denote]`: one-off local soundness/example helpers
  (`toK_radicandX3p1`, `toPolyG_radInv2`, `toK_cubeRadicand`, the `qxOfNum`/`cLaurentShiftG`/
  `cAlgResidueNorm` families, `toPolyG_scale_one`, `toPolyG_afBasisElem_one`, `toPolyG_radDeriv_logFold`),
  multiply-back identities (`toPolyG_reduceNum_mul`/`reduceDen_mul`), composite-redundant convenience
  lemmas (`toPolyG_termG`), and special-case overlaps (`toPolyG_radDeriv_{linear,radGen,zero_cons}`).
  Each earns `@[denote]` only if a second cross-file consumer appears. Item 1's *foundational* scope is
  closed; further tagging is by-exception, not a batch.

## Item 2 — denotation-square discipline (NOT STARTED)

Relocate each `@[denote]` square to the file that *defines* its op (satellite-in-def-file rule). Many
already are; the exceptions are squares stranded in `*Soundness`/`*Spec` files downstream of the def.
High churn (imports), low math value. Do file-by-file, git-history-preserving.

## Item 3 — drop dead name markers (NOT STARTED)

Retire implementation-history suffixes from names where they no longer disambiguate: `Wf`/`WellFounded`
(fuel retirement is complete — the `Wf` twin is now the only one), `Full`/`Fast`, and the `G`
generic-suffix where no non-`G` sibling remains. Pure `git mv`/rename, touches thousands of refs
(`toPolyG_cgcdWf`, `cIntegrateGFullWf`, …). Highest churn, cosmetic. Batch by op-family, one rename per
commit, `wiki rdeps` before each.
