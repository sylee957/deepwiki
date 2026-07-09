# Integral-function entanglement — reduction plan

Scope: the executable integrators under `DeepWiki/SymbolicIntegration/Computable/`. Goal: reduce
cross-arc coupling flagged by the call graph (23 `uses` edges over 21 functions). This doc records
the findings, the verdict on each, and the phased work.

## Call graph (arcs = lanes; cross-lane edges = coupling)

- **Transcendental main:** `cIntegrateGFullWf` → { `canonicalRepresentationFastG`,
  `cIntegrateReducedG`, `cPolyRischDEG` }.
- **Reduced core + residue logs:** `cIntegrateReducedG` → { `cHermiteReduceTowerG`, `cLogPartG` };
  `cLogPartG` → { `cRationalResiduesG` → `cResidueResultantTowerG`, `cLogArgTowerG` }.
- **Risch DE recursion:** `crischDESolve` → `cRischDEG` → `cPolyRischDEG` → `cIntegratePolyG`.
- **Hyperexponential:** `cIntegrateHyperexpFullG` → { `cIntegrateHyperexpNormalG`
  (→ `cIntegrateReducedG`, `crischDESolve`), `cIntegrateHyperexpLaurentG` }; plus the leaf
  `cIntegrateHyperexpG` (examples only).
- **Algebraic / radical** (`cIntegrateAlgebraicDecide → …Wf`, `cIntegrateElementaryG → radLogArgSolveG`)
  and **Parallel** (`cParallelIntegrateTower → cParallelIntegrate`): isolated, zero coupling to the core.

Shared hubs `canonicalRepresentationFastG` and `cIntegrateReducedG` are each called by three
drivers — the legitimate shared core and the entire main↔hyperexp coupling surface.

## Findings & verdicts

### B — retire `cIntegrateHyperexpG`  ·  DO NOT (it is a deliberate counterexample)

Initial read: `cIntegrateHyperexpG` (`Hyperexp/Special.lean`) is a leaf driver (no integrator calls it,
only `native_decide` examples) whose normal part routes through `cIntegrateReducedG` **without** the
base-RDE correction — so it **overshoots on a special+normal mix**, which `cIntegrateHyperexpFullG`
(`Hyperexp/NormalCore.lean`) fixes via `cIntegrateHyperexpNormalG` (`∫R = η·Σcᵢ` subtracted through
`crischDESolve`). Looked like a redundant fueled-era twin to delete.

Investigation refuted this. `Hyperexp/Normal.lean` carries a deliberate contrast pair on the *same*
integrand `f = (2t−1)/(t²−t)`:
- `nSpecNorm_specialOnly_overshoots` — `cIntegrateHyperexpG` gives `checkIdentityG = false`;
- `nSpecNorm_full_lands` — `cIntegrateHyperexpFullG` gives `checkIdentityG = true`.

So `cIntegrateHyperexpG` is a **retained weaker driver used as a counterexample** in the correctness
ladder (the CLAUDE.md "ship the negative theorem too" discipline). Deleting it destroys
`nSpecNorm_specialOnly_overshoots` — a documented "this is why the full driver exists" fact. **No deletion.**
Its coupling to the shared hubs is the cost of a genuine (if weaker) driver, not accidental duplication.

### C — "unify the two RDE entries"  ·  DROP (not a real coupling)

`cIntegrateGFullWf → cPolyRischDEG` integrates the **polynomial part** (`Dqₚ = fₚ`, primitive `b=0`
case, returns a polynomial). `crischDESolve` is the **base-field scalar RDE** (`Dy+f·y=g`, `y ∈ α`). These
are different operations that happen to bottom out at the same `cPolyRischDEG`; merging their entry
points would be semantically wrong. The apparent "double entry" in the graph is correct separation, not
entanglement. No action.

### D — stop threading `cands` through the pipeline  ·  DEFER [infra]

`cands : List α` is a parameter of `cIntegrateGFullWf`, `cIntegrateReducedG`, `cLogPartG`,
`cRationalResiduesG`, the hyperexp variants — and ~50 soundness theorem signatures
(`OneShotAssembly`, `FullSoundness`, `NormalPartSoundness`, `LogPartTowerSoundness`). It cannot be removed
without a large proof-surface change. The only safe move is **additive**: a concrete-ℚ residue enumerator
`cResidueCandidatesQ` + an auto wrapper `cIntegrateGFullAutoWf`, so ℚ call sites stop hand-building lists.
But enumerating ℚ residues from `R(z) ∈ ℚ(x)[z]` is non-trivial (not a plain rational-root theorem over
ℚ(x)), so this is an infra task, not a quick win. Deferred; the manual `cands` interface stays as the
proof-facing primitive.

## Verdict

After investigation, **none of the three graph-suggested reductions is a safe win** — and that is itself
the useful result. The call graph's "entanglement" is either legitimate shared core (the two hubs) or
deliberate (the counterexample driver). The Algebraic and Parallel arcs are already fully isolated. The
library is well-factored here; there is no accidental coupling to remove.

- B — **do not delete** `cIntegrateHyperexpG` (deliberate counterexample; deletion loses
  `nSpecNorm_specialOnly_overshoots`).
- C — dropped (the "two RDE entries" are semantically distinct — correct separation, not coupling).
- D — deferred [infra] (`cands` is woven through ~50 soundness signatures; only an additive ℚ-enumerator
  wrapper is safe, and correct enumeration over `ℚ(x)[z]` is non-trivial).

If a future pass wants to act, the only genuinely additive item is D's `cResidueCandidatesQ` +
`cIntegrateGFullAutoWf` convenience wrapper for concrete-ℚ call sites — new code, touching no existing
signature.
