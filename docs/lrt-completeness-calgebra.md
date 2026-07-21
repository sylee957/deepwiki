# Completeness of the bundled LRT stage (`lrtIntegrate`)

**Framing**: `lrtIntegrate` never fails (every rational function is elementary-integrable
— `denseFrac_isElementary`), so completeness means **canonicity**: nothing spurious is
produced, and nothing produced can be avoided by any correct answer. Compare
`hermiteReduce_complete` (an existence decision — within-field antiderivative ↔ log part
vanishes): Tier A completes that decision computably; Tier B is the uniqueness content
Hermite never needed; Tier C mirrors Hermite's exactness-of-the-stage.

## Tier A — detection completeness — DONE (2026-07-21)

(Homed in `Integrate/LogPartSpec.lean` (sound + complete); composed into the full-pipeline record: see
`Integrate/RatIntegrate.lean` + `RatIntegrateSpec.lean` — `ratIntegrate_sound` is
hypothesis-free `D(∫f) = f` (Tier A absorbs the zero log part), `ratIntegrate_complete`
is the record-level decision. Poly-part uniqueness: `polyIntegrate_complete` in
`Diff/Derivative.lean`.)

- `lrtIntegrate_complete (g) (hsf) (hprop) : (lrtIntegrate g).terms = [] ↔ g.num = 0`
  (`Integrate/LogPartSpec.lean`). Forward: a nonzero proper fraction with squarefree
  denominator has a pole (IsAlgClosed), its residue is a root of the RT resultant
  (`image_residue_eq_roots_rtResultant`, membership-ext through the classical instance),
  the covering decomposition factor is nonconstant, `mem_lrtLogTerms_of_index` produces a
  pair. Backward: coprimality forces `den = 1` (`DenseFrac.eq_zero_of_num_eq_zero`, new
  Frac/Basic satellite), `rtResultant 0 1 = 1` (via `DensePolyResultant.resultant_eq` +
  Mathlib `resultant_zero_right` at degrees `(0,0)`), so every factor divides a unit
  (`dvd_powProd_of_mem`, new Squarefree/Basic satellite) — no nonconstant factors.
- `hermiteReduce_lrt_complete (f) : (∃ G, G′ = toRatFunc f) ↔
  (lrtIntegrate (hermiteReduce f).logPart).terms = []` — the composable, computable
  rational-integrability decision: `hermiteReduce_complete` ∘ Tier A.

## Tier B — residue canonicity (Rothstein minimality) — OPEN

For ANY representation `toRatFunc g = ∑ i, c i * logDeriv (u i) + v′` (constants `c i`),
every produced residue lies in the ℤ-span of the `c i`:

```
theorem lrtIntegrate_residues_minimal (g …contract…) {ι} [Fintype ι]
    (c u : ι → RatFunc R) (hc : ∀ i, (c i)′ = 0) (v : RatFunc R)
    (hrep : DenseFrac.toRatFunc g = ∑ i, c i * logDeriv (u i) + v′) :
    ∀ a ∈ residueSet g,
      algebraMap _ (RatFunc R) (Polynomial.C a) ∈ AddSubgroup.closure (Set.range c)
```

— i.e. `ℚ(residues)` is the minimal constant field; LRT's output is *the* answer.
Keystones (all exist, `RationalIntegrationLiouville.lean`): `residueAt`,
`residueAt_derivative_eq_zero` (kills `v′`), `residueAt_logSum_eq_coeff` + the witness
machinery (reads coefficients off log sums). Missing bridge to prove first:
`residueAt α (toRatFunc g) = A(α)/D′(α)` at the contract inputs (identifies `residueSet`
with the analytic residues); then the ℤ-span bookkeeping over factorizations of the `u i`
(each pole's residue contribution is `cᵢ · multiplicity`).

## Tier C — argument canonicity — essentially done, packaging only

At each residue the produced argument is `IsSimilar` to `gcd(D, A − aD′)` with degree =
multiplicity (`lrtLogTerms_isSimilar_gcd`, `RtData.natDegree_eq`). Optional record-level
packaging lemma when a consumer wants it.

## Conventions

- Each tier gate-green + `#print axioms` (`propext`/`Classical.choice`/`Quot.sound`);
  finish + report, commit only after user review.
- The classical-vs-real `DecidableEq` boundary stays membership-ext (see the standing
  lesson); `residueAt` is classical-scoped — expect the same transports in Tier B.
