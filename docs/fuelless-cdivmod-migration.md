# Fuel-less `cdivmod` / `cgcd` / `cgcdExt` migration plan

**Status: DONE (2026-07-09).** Executed as planned via the self-fueled-wrapper approach — commits: Phase 1
rename `…Core` (`b7e3deef`), Phases 2–6 wrappers + hypothesis-free corollaries + showcases + consumers
(`a1752d60`), Phase 7 docs/memory. All gate-green; every `native_decide` showcase reduces unchanged; no
`termination_by`/`WellFounded`; `[CField]`-only signatures preserved. The plan below is retained as the
executed design record.

Scope: the representation-independent division/gcd layer in
`DeepWiki/ComputableAlgebra/PolyReprDivision.lean` + `PolyReprDivisionDegree.lean`. Goal: expose a
**fuel-less API** for Euclidean division, gcd, and extended gcd — dropping the explicit `fuel : ℕ`
argument and, with it, every `cdeg _ < fuel` side-hypothesis on the correctness theorems — **without
introducing well-founded recursion** (`termination_by`/`WellFounded.fix`).

## Why fuel-less

Today the three engines are fuel-threaded structural recursions:

```
def cdivmod  [CField α] : ℕ → P α → P α → P α × P α
def cgcd     [CField α] : ℕ → P α → P α → P α
def cgcdExt  [CField α] : ℕ → P α → P α → P α × P α × P α
```

The `fuel` is pure bookkeeping: it never appears in the *meaning*, only bounds the recursion depth. Its
cost shows up in two places:

1. **Correctness hypotheses.** The termination-flavoured theorems carry a fuel bound that the caller must
   discharge:
   - `cdivmod_remainder_reduced (fuel) … (cdeg p < fuel)`
   - `cdivmod_exact (fuel) … (cdeg p < fuel)`
   - `toPoly_mul_cdiv_of_dvd (fuel) … (cdeg p < fuel)`
   - `cgcd_dvd (fuel) … (cdeg b < fuel)`
   - `cgcd_isGCD (fuel) … (cdeg b < fuel)`
   - `cmonicGcd_isGCD (fuel) … (cdeg b < fuel)`
   (The *identity* theorems `toPoly_cdivmod`, `toPoly_cgcdExt`, `dvd_cgcd`, `dvd_cgcdExt`,
   `isCoprime_of_cgcdExt_isUnit`, `dvd_of_cisZero_cdivmod_snd` hold at **every** fuel and carry no bound —
   they are unaffected by the fuel value, only by its presence as a parameter.)

2. **Caller ceremony.** Every consumer already picks a sufficient fuel by hand:
   - `cgcd`'s inner division: `cdivmod (cdeg a + 1) a b`
   - `csquarefreeCofactor := cgcd (cdeg (cderiv p) + 1) p (cderiv p)`
   - `csquarefreePart := (cdivmod (cdeg p + 1) p _).1`
   - `cmonicGcd (fuel) := cmonic (cgcd fuel a b)`
   - the 8 `native_decide` showcases pass a literal `5` or `cdeg _ + 1`.

   Each of these is choosing `cdeg + 1` (the tight sufficient bound) and then, in the paired theorem,
   proving `cdeg _ < cdeg _ + 1` by `omega`. That is the ceremony we want to delete.

## The chosen approach: self-fueled wrappers (no `wf`)

Keep the existing fuel-threaded recursions **verbatim** but rename them to a `…Core` suffix, then expose
fuel-less wrappers that compute the *tight* sufficient fuel from the input degree:

```
def cdivmodCore [CField α] : ℕ → P α → P α → P α × P α   -- (was cdivmod)
def cgcdCore    [CField α] : ℕ → P α → P α → P α          -- (was cgcd)
def cgcdExtCore [CField α] : ℕ → P α → P α → P α × P α × P α -- (was cgcdExt)

/-- Fuel-less Euclidean division: `cdeg p + 1` steps always fully reduce. -/
def cdivmod [CField α] (p q : P α) : P α × P α := cdivmodCore (cdeg p + 1) p q
/-- Fuel-less gcd: `cdeg b + 1` bounds the Euclidean step count. -/
def cgcd    [CField α] (a b : P α) : P α := cgcdCore (cdeg b + 1) a b
/-- Fuel-less extended gcd. -/
def cgcdExt [CField α] (a b : P α) : P α × P α × P α := cgcdExtCore (cdeg b + 1) a b
```

**Why `cdeg + 1` is always enough.** Each `cdivmodCore` step strictly lowers the honest degree of the
running dividend (or zeroes it) — this is exactly `degree_reduce_step_lt` /
`cdivmod_remainder_reduced`. Starting from `cdeg p`, at most `cdeg p + 1` steps reach a base case, so the
remainder is fully reduced. Likewise each `cgcd`/`cgcdExt` step strictly lowers `cdeg` of the *second*
argument, so `cdeg b + 1` steps suffice.

**Why this satisfies "no `wf`".** The recursion is still the plain structural `fuel + 1 ↦ fuel` — no
`termination_by`, no `decreasing_by`, no `WellFounded.fix`. The fuel becomes a *computed internal
constant*, not a caller-visible parameter. `native_decide` is **unaffected**: `…Core` reduces by
structural recursion exactly as today, and `cdivmod p q = cdivmodCore (cdeg p + 1) p q` reduces through
the wrapper (it is a plain `def`, not a `WellFounded.fix` the compiler must special-case).

### Why NOT `termination_by cdeg p`

The "purist" fuel-free form `def cdivmod (p q) : … := … termination_by cdeg p decreasing_by …` is
rejected here for two concrete reasons:

- **It *is* well-founded recursion** — the equation compiler emits `WellFounded.fix`. That is precisely
  what this task excludes.
- **It would leak `[CFieldSpec]` into the definition's signature.** The `decreasing_by` obligation is
  `cdeg (csub p (mul t q)) < cdeg p`, whose only proof route is `degree_reduce_step_lt`, which needs
  `[CField α] [CFieldSpec α]` (the `toK` leading-coefficient-cancellation argument). Since
  `decreasing_by` runs during elaboration of the `def`, `cdivmod` would have to take `[CFieldSpec α]` —
  propagating that instance to `cgcd`, `cgcdExt`, `csquarefreePart`, `cResultant` callers, and every
  downstream signature. The self-fueled wrapper keeps `cdivmod`/`cgcd`/`cgcdExt` at `[CField α]` only;
  `[CFieldSpec]` stays confined to the *degree/termination theorems* where it already lives.

The one honest cost of the wrapper approach: the implementation is still fuel-threaded *internally*, so it
is "fuel-less **API**", not "fuel-free **implementation**". Given the constraints that is the right
trade — the fuel is invisible to every caller and theorem, and nothing regresses.

## Declaration inventory & the post-migration signatures

`…Core` = today's fuel-threaded def, kept private/internal. New public shape on the right.

### `PolyReprDivision.lean`

| today | after |
|---|---|
| `cdivmod (fuel) p q` | `cdivmodCore (fuel) p q` + `cdivmod p q := cdivmodCore (cdeg p + 1) p q` |
| `toPoly_cdivmod (fuel) p q` | `toPoly_cdivmodCore (fuel) p q` (∀ fuel, unchanged) **+** `toPoly_cdivmod p q` (fuel-less corollary) |
| `dvd_of_cisZero_cdivmod_snd (fuel) …` | drop `fuel`; state on `cdivmod` (uses `toPoly_cdivmod`) |
| `cgcd (fuel) a b` | `cgcdCore (fuel) …` + `cgcd a b := cgcdCore (cdeg b + 1) a b` |
| `dvd_cgcd (fuel) …` | `dvd_cgcdCore (fuel) …` (∀ fuel) **+** `dvd_cgcd a b d …` fuel-less |
| `cgcdExt (fuel) a b` | `cgcdExtCore (fuel) …` + `cgcdExt a b := cgcdExtCore (cdeg b + 1) a b` |
| `toPoly_cgcdExt (fuel) …` | `toPoly_cgcdExtCore (fuel)` (∀ fuel) **+** `toPoly_cgcdExt a b` fuel-less |
| `dvd_cgcdExt (fuel) …` | drop `fuel` (from `toPoly_cgcdExt`) |
| `isCoprime_of_cgcdExt_isUnit (fuel) …` | drop `fuel` |
| `exists_partialFraction`, `exists_crt` | **untouched** (no fuel) |

### `PolyReprDivisionDegree.lean`

| today | after |
|---|---|
| `cisZero_cdivmod_snd (fuel) …` | helper on `cdivmodCore` (still needs the fuel form for the reduced proof); keep as `…Core` lemma |
| `cdivmod_remainder_reduced (fuel) … (cdeg p < fuel)` | `cdivmodCore_remainder_reduced` (fuel form) **+** `cdivmod_remainder_reduced p q (hq)` — **hypothesis-free** (instantiate fuel `= cdeg p + 1`, discharge `cdeg p < cdeg p + 1` by `omega`) |
| `cgcd_of_cisZero_snd (fuel) …` | `…Core` helper |
| `cgcd_dvd (fuel) … (cdeg b < fuel)` | `cgcdCore_dvd` (fuel form) **+** `cgcd_dvd a b (h?)` hypothesis-free |
| `cgcd_isGCD (fuel) … (cdeg b < fuel)` | `cgcd_isGCD a b` hypothesis-free |
| `cdivmod_exact (fuel) … (cdeg p < fuel)` | `cdivmod_exact p q (hq) (hdvd)` hypothesis-free |
| `toPoly_mul_cdiv_of_dvd (fuel) … (cdeg p < fuel)` | `toPoly_mul_cdiv_of_dvd p q (hq) (hdvd)` hypothesis-free |
| `cmonicGcd (fuel) a b` | `cmonicGcd a b := cmonic (cgcd a b)` |
| `cmonicGcd_isGCD (fuel) … (cdeg b < fuel)` | `cmonicGcd_isGCD a b (hg)` hypothesis-free |
| `csquarefreeCofactor` | body `cgcd p (cderiv p)` (drop the explicit `cdeg (cderiv p) + 1`) |
| `csquarefreePart` | body `(cdivmod p (csquarefreeCofactor p)).1` (drop `cdeg p + 1`) |
| `csquarefreeCofactor_dvd`, `toPoly_squarefree_factor` | re-check (should simplify — the `cdeg b < fuel` obligations they discharge disappear) |
| `degree_reduce_step_lt`, `cmonic`, `cmonic_monic`, `cmonic_associated` | **untouched** (no fuel) |

Everything in `PolyReprResultant.lean` is independent of `cdivmod`/`cgcd` (the resultant goes through
`clistDetn`/`cSylvester`, not division) — **no changes there**.

## Phase order (leaf-first; each phase its own gate-green commit)

The dependency DAG is `cdivmodCore → cgcdCore, cgcdExtCore → {csquarefree*, cmonicGcd}`, with the degree
theorems layered on top. Migrate bottom-up so each phase compiles against already-migrated leaves.

- **Phase 1 — rename to `…Core`.** Pure `git`-level rename of `cdivmod`/`cgcd`/`cgcdExt` and their
  fuel-form theorems to `…Core`, zero behaviour change. Update the internal call sites
  (`cgcdCore` calls `cdivmodCore`, etc.) and the `…Core` theorems' cross-references. Gate green. This
  isolates the mechanical rename from the semantic wrapper step.
- **Phase 2 — `cdivmod` wrapper + fuel-less division corollaries.** Add `cdivmod p q := cdivmodCore
  (cdeg p + 1) p q`; derive `toPoly_cdivmod`, `dvd_of_cisZero_cdivmod_snd`, `cdivmod_remainder_reduced`,
  `cdivmod_exact`, `toPoly_mul_cdiv_of_dvd` in **hypothesis-free** form from their `…Core` versions by
  instantiating `fuel := cdeg p + 1` and discharging the bound with `omega`.
- **Phase 3 — `cgcd` wrapper + fuel-less gcd corollaries.** `cgcd a b := cgcdCore (cdeg b + 1) a b`;
  derive `dvd_cgcd`, `cgcd_dvd`, `cgcd_isGCD` hypothesis-free.
- **Phase 4 — `cgcdExt` wrapper + Bézout corollaries.** `cgcdExt a b := cgcdExtCore (cdeg b + 1) a b`;
  derive `toPoly_cgcdExt`, `dvd_cgcdExt`, `isCoprime_of_cgcdExt_isUnit` (these are ∀-fuel already, so the
  corollary is a one-line instantiation).
- **Phase 5 — consumers.** `cmonicGcd`, `cmonicGcd_isGCD`, `csquarefreeCofactor`, `csquarefreePart`,
  `csquarefreeCofactor_dvd`, `toPoly_squarefree_factor` switch to the fuel-less callees and shed their
  fuel arguments/hypotheses.
- **Phase 6 — `native_decide` showcases.** Drop the literal fuel from all 8 showcases
  (`cdivmod 5 …` → `cdivmod …`, `cgcd 5 …` → `cgcd …`, `cgcdExt 5 …` → `cgcdExt …`). Verify each still
  reduces (it must — see the native_decide note).
- **Phase 7 — docs + memory.** Update `docs/representation-independent-poly.md`
  (drop the "fuel"/"every fuel" language where it no longer applies; keep it for the `…Core` identity
  lemmas), the `leanproofs-representation-independent-poly` memory note, and mark this plan DONE.

Optionally collapse Phases 2–4 or 5–6, but keep Phase 1 (the rename) separate so a bisect can tell a
mechanical rename apart from a semantic change.

## `native_decide` — the load-bearing concern, and why it's safe

The library's whole validation strategy is `native_decide` on concrete `List`/`SparsePoly` inputs
(≈120 site-wide, 8 touching division/gcd). The migration must not break a single one.

- The `…Core` recursions are **unchanged structural recursion on `fuel`** — they reduce under
  `native_decide` exactly as today.
- The wrappers `cdivmod p q = cdivmodCore (cdeg p + 1) p q` are **plain `def`s** — `native_decide`
  compiles `cdeg p`, adds one, and calls the compiled `…Core`. No `WellFounded.fix`, so no compiled-code
  special-casing and no risk of a non-reducing `Acc.rec`.
- This is strictly *easier* than the engine's own fuel retirement (memory: the `…Wf` conversion, where
  `native_decide` survived a genuinely well-founded rewrite). Here we never leave structural recursion.

If a future maintainer *does* want the purist `termination_by` form, note that `native_decide` would
still work (compiled evaluator handles WF), but `decide`/kernel `rfl` would not — the library uses
`native_decide` throughout, so even that variant would be safe. It is excluded here only for the `wf` and
`[CFieldSpec]`-propagation reasons above, not for a reduction reason.

## Risks & mitigations

- **A `…Core` correctness lemma silently needs the *value* of the fuel, not just `> cdeg`.** Re-check
  each termination lemma: all six use only `cdeg _ < fuel` (a `>` bound), which `cdeg _ + 1` satisfies —
  none inspects the exact fuel. Low risk; verified against the current statements above.
- **`cgcdExt` completeness.** `cgcdExt`'s theorems (`toPoly_cgcdExt`, `dvd_cgcdExt`, coprimality) are all
  ∀-fuel (Bézout holds at every fuel), so `cdeg b + 1` is not *required* for them — it is chosen only so
  the returned `g` is the fully-reduced gcd, matching `cgcd`. No theorem regresses; if a future
  "`cgcdExt` gcd is complete" lemma is added it will want the same `cdeg b + 1` bound, already supplied.
- **Naming churn.** The `…Core` rename touches every internal cross-reference. Do it as the isolated
  Phase 1 and audit with `grep -n "cdivmod\|cgcd\|cgcdExt" DeepWiki/ComputableAlgebra/PolyReprDivision*.lean`
  before/after.
- **Doc/memory drift.** The design doc leans on "holds at *every* fuel" as an elegance point for the
  identity lemmas; keep that language on the `…Core` identity theorems and phrase the fuel-less wrappers
  as "the tight `cdeg + 1` fuel, hidden".

## Out of scope

- The existing *engine's* fuel API (`cdivmodWf` etc. under `SymbolicIntegration/`) — that is a separate,
  already-planned migration (`docs/gcd-core-fuel-migration.md` / the fuel-retirement memory). This plan is
  only the `ComputableAlgebra` representation-independent layer.
- No change to `clistDetn`/`cResultant` (fuel-free already) or to any non-division algorithm.
