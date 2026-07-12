# Project: bundle recurring hypothesis clusters into named structures

**Status:** in progress · **Owner:** Codex-executable · **Repo:** `deepwiki` (Lean 4, v4.31.0)

Self-contained; assumes no conversation context. Read top to bottom before editing.

## The problem & the rule

Many `SymbolicIntegration` theorems carry 5–7+ hypotheses, and the *same clusters* of hypotheses recur
across theorems (e.g. in `Computable/LaurentSoundness.lean`, `{hnz, hmpos, hc, hproper, hmono}` — "`ds`
is a proper degree-`m` monomial denominator" — appears on 3 theorems; `hDt : toPolyG Dt = C (toK η) * X`
appears 8×). Long, repeated hypothesis lists are hard to read, use, and maintain.

**The rule (apply exactly this):** a hypothesis cluster that (a) **recurs on ≥ 2–3 declarations** and
(b) **always travels together** becomes one named `structure`/`abbrev`. One-off hypotheses stay inline.
Do **not** over-bundle: a cluster used once, or hypotheses that appear in different combinations, stay as
separate binders.

This is the existing codebase pattern — see `LrtReducedGenuineData`, `LrtPoleNormalityData` in
`Computable/LrtSoundness.lean` / `LrtResidueResultantDischarge.lean` for precedent.

## The loop (per file)

Prepend `export PATH="$HOME/.elan/bin:$PATH"` to every shell call. One file at a time, worklist order.

1. **Find recurring clusters:** list hypothesis binder names and their multiplicity —
   `grep -rhoE "\(h[a-zA-Z0-9]+ :" <file> | sort | uniq -c | sort -rn`
   then read the top few signatures to see which names co-occur on the same declarations. A group of
   names that appears together on ≥2–3 theorems is a bundle candidate.
2. **Define the bundle** near the top of the file (or, if the cluster recurs across files, in the
   earliest file that defines its ingredients). Use `Prop`-valued structures (these are hypotheses, not
   data), named `Is<Concept>` (CLAUDE.md predicate convention), one field per bundled hypothesis:
   ```lean
   /-- `ds` is a proper degree-`m` monomial denominator (the hyperexp special-case setup). -/
   structure IsSpecialDenominator (ds : CPolyG α) : Prop where
     nz     : cisZeroG ds = false
     mpos   : 0 < cdegG ds
     clead  : CFieldSpec.toK (cleadG ds) ≠ 0
     proper : ∀ j, cdegG ds ≤ j → (ds : List α).getD j CField.zero = CField.zero
     mono   : toPolyG ds = C (CFieldSpec.toK (cleadG ds)) * X ^ cdegG ds
   ```
   A single-condition cluster uses `abbrev … : Prop := …` instead of a `structure`
   (e.g. `abbrev IsHyperexpMonomial (Dt : CPolyG α) (η : α) : Prop := toPolyG Dt = C (toK η) * X`).
3. **Thread it:** replace the cluster of binders with one `(hds : IsSpecialDenominator ds)`. Inside the
   proof, destructure via field access (`hds.nz`, `hds.mono`, …) where the old hypothesis names were
   used (or open with `obtain ⟨hnz, hmpos, hc, hproper, hmono⟩ := hds` to keep the body unchanged).
   At **call sites**, construct the bundle: `⟨hnz, hmpos, hc, hproper, hmono⟩` (or a named smart
   constructor if one is natural).
4. **Gate the module:** `scripts/check.sh <Module>` must print `GATE: PASS` (warnings are failures).
   Fix call sites the change touched. Use `scripts/wiki rdeps <theoremName>` to find external callers.
5. **Commit per file:** `refactor(bundle): <Concept> in <Module>`, ending the body with
   `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`. Update the worklist.

## Worklist (start with LaurentSoundness as the template)

- [x] `Computable/LaurentSoundness.lean` — define `IsProperSpecialPart` (the
      `{nz,mpos,clead,proper}` prefix, 3 theorems), `IsSpecialDenominator` (adds `mono`, 2 theorems),
      and `IsHyperexpMonomial` (the `hDt` condition, 8 sites). **Template.**
- [x] `Computable/LrtSoundness.lean` (162 binders) — audited beyond the existing `Lrt*Data`; bundled the
      repeated Yun input pair as `IsYunFactorizationInput`.
- [x] `Computable/NormalPartSoundness.lean` (121) — bundled the repeated Hermite factor
      nonzero/cofactor-proper pair as `IsHermiteInnerFactor` and `IsHermiteFactorData`.
- [x] `Computable/OneShotAssembly.lean` (264) — bundled repeated full-driver branch selectors as
      `IsPureNormalBranch` / `IsPolynomialBranch`; left residue-side variants explicit.
- [x] `HermiteCorrectness.lean` (314) — bundled the repeated Diophantine agreement input,
      Hermite-inner Bézout input, and residual-wrapper denominator input.
- [x] `GroebnerBasis.lean` (429) — bundled the repeated Lazard base hypotheses as
      `HasLazardBaseDvd` / `HasLazardBaseDegreeZero`; left structural `hB` basis witnesses explicit.
- [x] `SubresultantCorrectness.lean` (255), `LaurentCoefficients.lean` (162) — large; expect several
      clusters each. `SubresultantCorrectness.lean`: bundled the exact β-divided PRS step as
      `IsBdivCExactStep` and the `bprimitivePartX` content-exactness input as
      `IsPrimitivePartXInput`; bundled endpoint PRS-chain regularity as `IsSubresPRSChainInput`.
      `LaurentCoefficients.lean`: bundled regular root data as `IsLaurentRegularRoot`.
- [x] sweep: `for f in $(find DeepWiki/SymbolicIntegration -name '*.lean'); do n=$(grep -coE "\(h[a-zA-Z0-9]+ :" "$f"); [ "$n" -gt 40 ] && echo "$n $f"; done | sort -rn`
      was run after the listed bundles. The raw count still flags already-audited files plus future
      candidates such as `LiouvilleLog.lean`, `SubresultantPRS.lean`, `IntegratorCases.lean`,
      and `Hyperexp/NormalSoundness.lean`; those need a separate cluster audit before any bundling.

## Guardrails

- Bundle only genuinely-recurring, always-together clusters (≥2–3 uses). When unsure, leave inline.
- `Prop` structures only (hypotheses, not data); name `Is<Concept>`; one field per hypothesis; a
  concise one-line docstring on the structure and each field.
- No change to executable/`native_decide` code; warnings are errors; `-/` trap; library-not-catalog
  (no book/source refs in `DeepWiki/` docstrings); commit per gate-green file.
- Keep it behaviour-preserving: the theorem *statements* are equivalent (bundle ⇔ the old conjunction);
  only the *shape* changes. Restate one converted theorem as an `example` against the intended meaning
  if the bundling is subtle.
