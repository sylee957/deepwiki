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

## Item 2 — denotation-square discipline (SPIKED — mostly BLOCKED by the CField/CFieldSpec split)

Relocate each `@[denote]` square to the file that *defines* its op (satellite-in-def-file rule).

**Spike finding 2026-07-09 (why this has narrow scope):** the stranded squares are stranded for a
*structural* reason, not neglect. A computable op is defined in the **Prop-free `CField`/`CDiffField`
layer** (e.g. `cAmcDdG` in `Tower/Integrate.lean` under `[CField α] [CDiffField α]`, `cmonicG` in
`GenericPolyEngine`), but its denotation square `toPolyG (op …) = …` needs the **`CFieldSpec`/
`CDiffFieldSpec` bridge** (that's what `toPolyG`/`toK` *are*) — a heavier context the pure-def file
deliberately does not establish. So the square naturally lives in the first *downstream* file that has
the bridge instances in scope; moving it up to the def file forces the bridge (or, for `_eq_normalize`,
a `NormalizationMonoid` import) upstream into the lean core — exactly the coupling this layering avoids.
Two concrete attempts confirmed it: `toPolyG_cmonicG_eq_normalize` → GenericPolyEngine needs `normalize`
(NormalizationMonoid) it doesn't import (reverted); `toPolyG_cAmcDdG` → Integrate.lean would need
`CFieldSpec`/`CDiffFieldSpec` added to a Spec-free def context. **Verdict:** Item 2 is *not* a broad
relocation sweep — most squares are already in the correct (first-bridge-available) file. Only squares
stranded *below* their first-bridge-available file are real targets; treat this as by-exception, and
never at the cost of pulling a bridge/normalization import into the Prop-free core.

## Item 3 — drop dead name markers (GWf family DONE)

Retire implementation-history suffixes from names where they no longer disambiguate.

**`GWf → G` DONE 2026-07-09** (2600 occurrences, 72 `.lean` + 15 `.md` files, one atomic gate-green
commit). The fuel migration (`docs/gcd-core-fuel-migration.md`) is complete, so the fueled generic
`…G` twins are deleted and the fuel-free `…GWf` engine is the sole generic version — `Wf` on a `GWf`
name is a dead marker, and dropping it restores the natural generic `…G` name (`cHermiteReduceTowerGWf`
→ `cHermiteReduceTowerG`, `cRischDEGWf` → `cRischDEG`, …). **Collision analysis:** across *all* decl
kinds only `cIntegratePolyGWf` collided (with the abstract `cIntegratePolyG`) — and it was a byte-identical
`rfl`-duplicate, subsumed first (its own commit). So `GWf → G` is exception-free. `GWf` is never an
English word, so substring-replace is false-positive-safe even in prose/docstrings; line numbers are
stable, so the tutorial's `file#L` anchors are unaffected.

**Remaining Item-3 markers are BLOCKED / not-dead:**
- **Bare `Wf`** (e.g. `cgcdWf`, `cdivWf`, `cmodWf`, `cdivmodWf`, `cresultantWf`, the `radIntegrateCase*Wf`
  family): 15 collide with a live twin — the concrete `Compute` layer (`Compute.cdivmod`/`cmod`/`cdiv`,
  `RtResultant.cresultant`) or an abstract-spec twin. `Wf` there still disambiguates fuel-free-generic
  from the fueled-concrete/abstract sibling. Not a clean drop.
- **`G` alone:** disambiguates generic-engine ops from the concrete `Compute` ℚ ops (live twins). Keep.
- **`Full`:** semantic — the full end-to-end integrator (`cIntegrateGFullWf`→now `cIntegrateGFull`) vs the
  per-case integrators (`cIntegrateHyperexpG`, …). Keep.
- **`Fast`:** ambiguous (no slow generic twin, but possibly distinguishes from a concrete variant); low
  value, defer.
