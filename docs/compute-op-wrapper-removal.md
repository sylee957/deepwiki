# Remove the `Compute` op-wrappers (use the generic `CPoly.*` engine directly)

`Compute.{cnorm,cadd,cneg,cscale,cshift,cmul,clead}` are pure `:= CPoly.X` passthrough wrappers — a
concrete `CPoly ℚ` API that predates the ring-generalized generic engine. Now that
`CPoly.<op>` specializes to `ℚ` identically, the wrappers are redundant (that redundancy is what the
`Engine/ConcreteCoherence.lean` `*G_eq_*` bridge lemmas prove). Remove the wrappers; the concrete layer
uses the generic ops directly.

## Approach chosen: one `export`, not 700 prefixes or 16+ per-file `open`s — DONE

`export CPoly (cnorm cadd cneg cscale cshift cmul clead)` inside `namespace Compute` (in `LogToAtan`,
replacing the 7 wrapper `def`s) makes `Compute.cnorm` a genuine **alias** of `CPoly.cnorm` — the *same
constant*, no separate definition. It **propagates through imports**, so every bare `cnorm` in a
Compute-namespace file AND every qualified `Compute.cnorm` resolves with **zero per-file churn**. This
beat both alternatives (700 explicit `CPoly.` prefixes = verbose; per-file `open` = ~16+ files and misses
qualified refs). Selective export (not the genuine ℚ-specific `csub`/`cisZero`/`cnsmul`/`cderiv`, which
stay defined).

Because `Compute.cadd` now *is* `CPoly.cadd` (one constant), the `Engine/ConcreteCoherence.lean` `*G_eq_*`
bridge lemmas became vacuous (`CPoly.cadd = CPoly.cadd`) and were **deleted** (0 consumers); only
`toPolyG_eq_toPoly`/`nsmulG_eq_natCast_mul`/`cderivG_eq_cderiv` (bridging the still-separate
`Compute.toPoly`/`cderiv`) remain.

**One caveat (the ℚ-pinning trade-off):** the deleted ℚ-specific `def cnorm : CPoly ℚ → CPoly ℚ` used to
*pin* `α = ℚ` from a bare list literal; the generic export does not, so a handful of isolated
`cnorm [0,2,0,1]` sites need an explicit `: CPoly ℚ` annotation (this is exactly the "type specialization"
the removal is about). Only `Sources/…/HermiteExample221.lean` hit this (2 sites).

## Ops classification

- **Remove (7 pure wrappers):** `cnorm cadd cneg cscale cshift cmul clead` (all `:= CPoly.X`).
- **Keep (genuine ℚ-specific, fuel-based, not in the generic engine):** `cdivmod cdiv cmod cdvd cgcdExt
  cresultant …`, and the composed `csub` (`cadd∘cneg`), `cisZero` (`cnorm ==[]`), plus `cnsmul`/`cderiv`
  and `Compute.toPoly` (a genuine separate `ℚ`-denotation). Their bodies use the removed ops → resolve via
  the `open`.

## Phases (each gate-green)

1. **LogToAtan** — delete the 7 wrapper defs; add the selective `open`. Fix in-file fallout (`cdivmod`,
   `cgcdExt`, the `csub`/`cisZero` bodies, `cnsmul`/`cderiv`).
2. **The other 15 Compute files** — add the selective `open` to each. Fix satellite lemmas
   (`cnorm_nil`/`cnorm_idem`/`cnorm_cons_eq`/`toPoly_cnorm` in `Correctness.lean`, etc.) that unfolded the
   old wrapper defs — re-prove via the generic `cnormG_*` squares (they now coincide).
3. **ConcreteCoherence** — delete the now-vacuous `*G_eq_*` lemmas for the 7 removed ops (0 consumers);
   the `toPolyG_eq_toPoly` / `cderivG_eq_cderiv` / `nsmulG_eq_natCast_mul` (about the kept `Compute.toPoly`/
   `cderiv`/`cnsmul`) stay.
4. **Sources sweep** — replace any `Compute.<op>` qualified refs in `Sources/` catalogs (renames must sweep
   `Sources/` too — see `feedbacks/rename-must-sweep-sources-not-just-deepwiki.md`).

## Risk

Bounded: 16 files + one bridge file, 0 external consumers of the coherence lemmas. The satellite
re-proving is the only real work (the concrete satellites duplicate the generic `cnormG_*` after the open).
