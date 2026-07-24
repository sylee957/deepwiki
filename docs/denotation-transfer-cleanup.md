# Plan: a relational refinement layer for `SymbolicIntegration/Computable`

**Status:** core layer **BUILT & gate-green on `main`** (Phases 1–2 done); remaining frontier is a
parametricity *translation* (below) · **Owner:** autonomous agent (Codex-executable) · **Repo:**
`deepwiki` (Lean 4, toolchain `leanprover/lean4:v4.32.1`)

This document is self-contained. It assumes **no** prior conversation context. Read it top to
bottom before touching code. Each phase is an independent, gate-green commit.

---

## STATUS UPDATE (what is already realized on `main`)

The relational layer exists in [`Computable/RefinesPolyG.lean`](../DeepWiki/SymbolicIntegration/Computable/RefinesPolyG.lean):

- **`RefinesPolyG p q := toPolyG p = q`** (functional refinement, the CoqEAL relation).
- **CoqEAL parametricity layer (realized):** generic classes `DenoteHom₁`/`DenoteHom₂` (denotation
  square; abstract `op` an `outParam`, in [`Computable/DenoteHom.lean`](../DeepWiki/SymbolicIntegration/Computable/DenoteHom.lean)) + two generic respect lemmas
  `RefinesPolyG.hom₁`/`hom₂` that dispatch on the instance. The hand-written per-op respect lemmas were
  retired into this layer.
- **Parametricity *translation* (realized — the frontier below is now partly built):** the
  `derive_denote_hom sq` command (also in `Computable/DenoteHom.lean`) reads a denotation square
  `sq : ∀ …, toPolyG (cop …) = op (toPolyG …) …`, extracts `cop` (computable head) and `op` (abstract
  operation, by abstracting `toPolyG` of the polynomial args from the RHS), and **generates** the
  `DenoteHom` instance — including parameterized ops (`cscaleG c`, `cpowG · n`; the scalar becomes an
  instance binder). All **ten** instances
  (`caddG/csubG/cmulG/cnegG/cderivG/cscaleG/cshiftG/cpowG/cmapDeriv/cmonomialDeriv`) are generated; a NEW
  operation needs only its `@[denote]` square + one `derive_denote_hom` line, with `op` DERIVED not
  hand-written. This is the Lean slice of Coq's `param` translation.
- **`transfer` tactic:** `first | (simp_all [RefinesPolyG, denote]; done) | aesop (rule_sets := [Refines])`.
  Branch 1 is the fast path for explicit-RHS goals; branch 2 **synthesizes** the abstract polynomial
  (metavariable RHS) by aesop over the `Refines` rule set (the `hom₁/hom₂` + nullary + `refinesPolyG_self`
  atom-closer). The `Refines` aesop rule set is declared in `Computable/Denote.lean`.
- **Zero-test reflection:** `eq_of_csub_cisZero` / `ne_of_csub_cisZero_false` bridge a `native_decide`
  `cisZeroG (csubG p q)` check to semantic (in)equality of the refined polynomials.

**Honest findings that recalibrate the rest of this plan (do not re-discover these):**
1. **Per-site transport conversion is largely DONE and is a readability, not line-count, win.** The clean
   `from by simp only [toPolyG_*]` blocks were already converted (commit series `refactor(denote): …`);
   net deltas were ±a few lines. No large untapped conversion remains.
2. **Transport is a MINORITY of proof bulk** across the topic (measured: `CoupledDE/Assembly`,
   `HermiteValuationTower`, `LrtSoundness`). The dominant bulk is real mathematics — degree bounds,
   coefficient extensionality, `RatFunc`/linear-algebra arithmetic. So the layer will not "greatly"
   shrink proofs; that expectation was miscalibrated. Do **not** force `denote`/`transfer` into the
   remaining coefficient-bash proofs where curated `simp only` lists feed `linear_combination` — high
   risk (over-firing), low value.
3. **Synthesis has no `= _` term-hole consumer** (Lean elaborates the hole before the tactic). Synthesis
   only fires on genuine `∃`-goals; the practical transfer is explicit-RHS or whole-goal (matching Trocq's
   whole-goal-translation ceiling).

**Remaining frontier (partly built):** `derive_denote_hom` (above) is the *instance-generating* half of a
Lean **parametricity translation** — the Lean analog of Coq's `param` / Trocq, structurally like Mathlib's
`@[to_additive]`. Done: generating `DenoteHom` instances (the abstract `op`) from the squares. Not yet:
(a) generating the *square itself* from the computable definition (would need a syntactic derivation over
the op's `def`), and (b) a full whole-goal transfer that rewrites arbitrary goals through the relation
(Trocq's translation). The instance generator is `CPolyG`-specific; a separate denotation family
(e.g. `RadElem`/`radDeriv` in `Algebraic/`) would need its own classes + command. **No mature Lean port of
CoqEAL/Trocq exists** — this direction is novel. See §6 for references.

---

## 0. TL;DR for the executing agent

The `DeepWiki/SymbolicIntegration/Computable/` proofs mix two layers in every proof: an
**executable** layer (`CPolyG α := List α`, ops `cmulG`/`caddG`/`csubG`/`cnormG`/…) and a
**semantic** layer (`(CFieldSpec.K α)[X]`, i.e. Mathlib `Polynomial`). They are connected by a
denotation `toPolyG : CPolyG α → (CFieldSpec.K α)[X]`. Almost every soundness proof **crosses this
seam by hand**, re-applying ~162 bespoke commuting-square lemmas
(`toPolyG_cmulG : toPolyG (cmulG p q) = toPolyG p * toPolyG q`, …). That hand-crossing is the
dominant source of proof bulk.

**This plan builds a relational refinement layer** — a Lean hand-roll of Coq's CoqEAL
("Refinements for Free!"): a relation `RefinesPolyG : CPolyG α → (CFieldSpec.K α)[X] → Prop` that
the operations *respect*, plus a `transfer` tactic that discharges refinement goals by recursively
applying the respect lemmas. Downstream proofs are then stated and reasoned **on the `K[X]` side**,
and the seam is crossed once, mechanically, by the tactic — never by hand-listing `toPolyG_c*`.

Categorically: `toPolyG` is the catamorphism (unique F-algebra homomorphism) from the representation
to `K[X]`; the transport squares are one functorial fact; `RefinesPolyG` expresses that
homomorphism as *a relation the operations respect*, which is what tolerates the redundant `List`
representation (see §6).

**Hard constraint (do not violate):** the executable engine is validated by `native_decide`, and
**that depends on the engine being `Prop`-free and reducing**. Do **not** convert `CPolyG` to a
quotient, and do **not** put a `Prop`-carrying `Subtype` on the *executable* path — either can
freeze `native_decide`. All work here is on the **proof/transport** side only. The executable defs
in `GenericPolyEngine.lean` and the `c*` ops are left byte-for-byte unchanged.

**Gate (must pass after every phase, warning- and `sorry`-free):**
```bash
export PATH="$HOME/.elan/bin:$PATH"
scripts/check.sh                      # full build; exit 0 = "GATE: PASS"
# fast mid-iteration feedback on one module:
scripts/check.sh DeepWiki.SymbolicIntegration.Computable.RefinesPolyG
```
`scripts/check.sh` treats `warning:` / `error:` / `declaration uses 'sorry'` as failure even when
`lake` itself exits 0. Do not weaken it.

---

## 1. Measured baseline (re-run to confirm before starting)

Record these in the Phase-0 commit message; re-run after each phase to show movement.

```bash
export PATH="$HOME/.elan/bin:$PATH"
SI=DeepWiki/SymbolicIntegration

grep -rhoE "theorem (toPolyG_|toK_|radDeriv_)[A-Za-z0-9_]+" $SI | wc -l          # ~162 squares exist
grep -rn "@\[denote\]" $SI | wc -l                                              # ~40  tagged (the squares reused as respect-lemma proofs)
grep -rcE "simp only \[[^]]*(toPolyG|toK_)" $SI | awk -F: '{s+=$2} END{print s}' # ~61  hand-listed transport sites (TARGET: → 0-ish)
grep -rc  "from by" $SI | awk -F: '{s+=$2} END{print s}'                         # ~142 show-block scaffolding (TARGET: ↓↓)
grep -rc  "monic_separable_eq_nodal" $SI | awk -F: '{s+=$2} END{print s}'        # ~9   base-change clusters (Phase 5)
```

Established facts (do not re-litigate):
- `CPolyG α := List α` — [`Computable/GenericPolyEngine.lean:139`](../DeepWiki/SymbolicIntegration/Computable/GenericPolyEngine.lean). A **redundant, non-normalized** rep (`[a,b]` ≡ `[a,b,0]`) ⟹ **not** a `Semiring`, cannot carry a `RingHom`/`AlgHom` on the nose. This is *why* we use a **relation**, not a bundled morphism — a relation tolerates the redundancy (this is the CoqEAL insight).
- `toPolyG` is `noncomputable` — [`GenericPolyEngine.lean:204`](../DeepWiki/SymbolicIntegration/Computable/GenericPolyEngine.lean).
- The ~162 `toPolyG_c*`/`toK_c*` squares already exist and are proven; a simp attr `@[denote]` is registered ([`Computable/Denote.lean:7`](../DeepWiki/SymbolicIntegration/Computable/Denote.lean)). We **reuse** these squares as the proofs of the respect lemmas — we do not re-derive anything.

**Litmus site** (use throughout): the `hdvd` bullet of `hAD_degree_of_genuineMonomial` in
[`Computable/LrtResidueResultantDischarge.lean`](../DeepWiki/SymbolicIntegration/Computable/LrtResidueResultantDischarge.lean) (≈ lines 309–339) — a ~18-line
`rw [show … = … from by simp only [toPolyG_csubG, toPolyG_cmulG, toPolyG_cmonomialDeriv, hg1, hg2]]`
block that is pure seam-crossing. When `transfer` collapses it to ~2 lines, the layer works.

---

## 2. The design (build exactly this)

### 2.1 The relation
New file `DeepWiki/SymbolicIntegration/Computable/RefinesPolyG.lean`:
```lean
/-- `p` refines `q` when `p`'s denotation is `q`. -/
def RefinesPolyG {α} [CField α] [CFieldSpec α] (p : CPolyG α) (q : (CFieldSpec.K α)[X]) : Prop :=
  toPolyG p = q
```
Start with this **functional** relation (`toPolyG p = q`) — it is the simplest heterogeneous
relation that works and reuses the existing squares directly. Generalize to a genuinely
non-functional `R` only if a specific op later resists (record it; do not pre-generalize).

Ship its satellites in the same file (repo rule: every `def` ships its API): an intro/elim pair
(`RefinesPolyG.intro`, `RefinesPolyG.denote_eq`), and a `rfl`-style constructor
`refinesPolyG_self : RefinesPolyG p (toPolyG p)`.

### 2.2 The respect lemmas (the "parametricity" facts)
One per core operation, proved in one line each from the existing square. Tag them all with a
**new attribute** `@[refines]` (register via `register_label_attr refines` or reuse an aesop rule
set — see 2.3). Minimum set to start:
```lean
@[refines] theorem RefinesPolyG.add : RefinesPolyG p p' → RefinesPolyG q q' → RefinesPolyG (caddG p q) (p' + q')
@[refines] theorem RefinesPolyG.sub : RefinesPolyG p p' → RefinesPolyG q q' → RefinesPolyG (csubG p q) (p' - q')
@[refines] theorem RefinesPolyG.mul : RefinesPolyG p p' → RefinesPolyG q q' → RefinesPolyG (cmulG p q) (p' * q')
@[refines] theorem RefinesPolyG.pow : RefinesPolyG p p' → RefinesPolyG (cpowG p n) (p' ^ n)
@[refines] theorem RefinesPolyG.norm : RefinesPolyG (cnormG p) (toPolyG p)          -- normalization is denotation-invariant
```
Then extend to the ops the target files actually use: `cmonomialDeriv`, `cderivG`, `cdivWf`,
`cscaleG`, constants (`[CField.zero]`, `[CField.one]`, `cnatCastG`), `cnegG`. Prove each from its
existing `toPolyG_*` square. Where a square is missing for an op you need, add the square (with its
one-line docstring) next to that op's definition — **not** in `RefinesPolyG.lean` (repo rule:
satellites live in the defining file).

### 2.3 The `transfer` tactic (the mechanism that changes how proofs are written)
Lean has no automatic parametricity, so provide a tactic that discharges
`RefinesPolyG <compound term> ?q` by recursively applying the `@[refines]` set, synthesizing the
abstract `?q` as it descends to atoms (atoms close by `refinesPolyG_self`). Two acceptable
implementations — pick whichever is cleaner and gates green:
- **(preferred) an aesop rule set:** `declare_aesop_rule_sets [Refines]`, tag the respect lemmas
  `@[aesop safe apply (rule_sets := [Refines])]`, and define `macro "transfer" : tactic => `(tactic| aesop (rule_sets := [Refines]) ...)`.
- **or a small recursive elaborator** that `apply`s from the `@[refines]` set and recurses on premises.

The user-facing win: to prove a fact about `toPolyG (bigCompoundTerm)`, you write
`have : RefinesPolyG bigCompoundTerm _ := by transfer` and then reason on the synthesized `K[X]`
term — the `toPolyG_c*` pushing disappears.

### 2.4 The discipline (why the layer pays off, not just the tactic)
State intermediate soundness facts **via `RefinesPolyG` / on the `K[X]` side**, so downstream
lemmas compose refinements and **never mention `toPolyG` or `c*` ops**. The seam is crossed once,
at the boundary, by `transfer`. This is the behavioral change; the tactic alone is not enough.

---

## 3. Phases (dependency-ordered; one gate-green commit each)

> **Standing directive — unify & retire, every iteration.** This layer exists to make code
> *disappear*, not accumulate. At **every** phase/commit, before you finish, actively hunt for
> things the new layer has made subsumable or redundant, unify them, and **delete** them in the
> **same commit** (do not leave dead code, "kept for reference" blocks, or `-- old:` comments).
> Concretely, each iteration:
> 1. **Retire squares that `transfer` subsumed.** Once a `toPolyG_c*` square is only ever used
>    inside a `@[refines]` respect-lemma proof (and no longer at any hand-listed call site),
>    confirm zero external dependents with `scripts/wiki rdeps <name>` and **delete** it — or, if
>    still referenced, leave it and note why. Target: the ~162-square count *goes down* over time.
> 2. **Unify duplicated transport.** If two lemmas/helpers do the same seam-crossing for different
>    ops or files, collapse them into one respect lemma or one generic helper. If two respect
>    lemmas differ only by a constant/atom, generalize to one.
> 3. **Retire scaffolding call sites.** Every `from by simp only [toPolyG_*]` / `rw [show …]` block
>    that `transfer` replaces is **deleted**, not commented out. The §1 grep counts (61 hand-lists,
>    142 `from by`, ~162 squares) must monotonically *decrease*; if a commit doesn't move them, say
>    why in the message.
> 4. **Fold stray denotation helpers.** Bespoke one-off transport helpers scattered in proof files
>    that the relation now covers get removed; their single call site uses `transfer`.
>
> Rule of thumb: a phase is not done until you've asked "what did this make dead?" and acted on it.
> Use `scripts/wiki rdeps <name>` (not `grep`) to prove a declaration is orphaned before deleting.
> This mirrors the repo's subtractive-marker and gradual-improvement conventions: unification is
> part of the work, not a separate later cleanup.

### Phase 0 — Baseline & guardrail
1. Run the §1 greps; paste counts into the commit message.
2. Pick one existing `example … := by native_decide` in the topic; confirm it builds. Every later
   phase must keep it green.
3. Commit: `docs(refines): baseline census + native_decide guard`.

**Acceptance:** gate PASS; numbers recorded.

### Phase 1 — Foundation: relation + respect lemmas + `transfer` tactic
Build §2.1–2.3 for the core arithmetic ops + `cnormG` + `cmonomialDeriv` (the litmus site needs
these). Add missing squares next to their defs and tag `@[denote]` opportunistically.

**Acceptance:** gate PASS; `RefinesPolyG.lean` compiles; `transfer` discharges
`RefinesPolyG (cmulG (caddG a b) c) ?q` synthesizing `?q = (toPolyG a + toPolyG b) * toPolyG c`;
`native_decide` guard green. Commit: `feat(refines): RefinesPolyG relation + respect lemmas + transfer tactic`.

### Phase 2 — Prove the layer on the litmus site
Rewrite the `hdvd` block in `LrtResidueResultantDischarge.lean` (§1) using `transfer` instead of the
`from by simp only [toPolyG_*]` scaffolding. Confirm the ~18 lines collapse to ~2–3.

**Acceptance:** gate PASS on that module; the block is materially shorter; the theorem still states
the same thing (restate via an `example` with the expected type if the signature is subtle).
Commit: `refactor(refines): discharge LrtResidueResultantDischarge hdvd via transfer`.

### Phase 3 — Roll out across the transport-heavy files
Prioritize by plumbing density (`grep -c "toPolyG" <file>`): `LrtResidueResultantDischarge` (finish),
`NormalPartSoundness`, `LrtSoundness`, then the `Algebraic/Radical*` soundness cluster. One file per
commit, gate each. Replace hand-listed `simp only [toPolyG…]` and `from by` transport blocks with
`transfer` + `K[X]`-side reasoning. Where a site is a single trivial square, plain `simp [denote]` is
fine — don't force `transfer` where it adds nothing.

**Acceptance:** gate PASS per file; grep counts (61 hand-lists, 142 `from by`) trending down;
`maxHeartbeats` bumps reduced where possible.

### Phase 4 — Extend the relation to the other denotations
Add `RefinesK` (for `toK : CField α → CFieldSpec.K α`, ~33 squares) and `RefinesRad` (for `radDeriv`,
~8 squares) with the same pattern, sharing the `transfer` tactic (parameterize the rule set, or one
rule set with all three families). Adopt in the `toK_*`/`radDeriv_*` sites.

**Acceptance:** gate PASS; `toK`/`radDeriv` transport sites converted.

### Phase 5 — Two orthogonal wins (independent; anytime)
1. **Base-change bundle.** Package the ~9 algebraic-closure clusters (monic + separable + `≠ 0` +
   roots-split over `K̄ = AlgebraicClosure (CFieldSpec.K α)`) into one helper returning those facts
   from `monic + squarefree` at `K` level — see the six `have`s ≈ lines 180–195 of
   `LrtResidueResultantDischarge.lean` for the shape. New file `AlgClosureBaseChange.lean`; convert
   clusters file-by-file.
2. **`yun_index` macro.** The ~21 three-line `List.getElem?_eq_some_iff` +
   `List.mk_mem_zipIdx_iff_getElem?` destructures → one `macro`/`syntax` tactic yielding `⟨hidx, hget⟩`.

**Acceptance:** gate PASS; clusters/destructures collapse; behavior unchanged.

---

## 4. Guardrails / do-not list (load-bearing)

- **Never** touch executable defs to serve the proof layer. `CPolyG`, the `c*` ops, and anything on
  the `native_decide` path stay `Prop`-free and unchanged.
- **Never** convert `CPolyG` to a quotient or a proof-carrying subtype.
- Every named declaration gets a **concise one-line `/-- … -/` docstring** (API-style, Lean idents in
  backticks). Anonymous `example`s get none. Each file opens with a `/-! … -/` module docstring
  **after** the imports.
- **`-/` trap:** a `-/` substring inside a docstring closes it early (write "sub- and super-", not
  "sub-/super-"). Audit: `grep -n -- '-/' file.lean | grep -vE -- '-/\s*$'`.
- These are **library** files under `DeepWiki/` — **no** book/source references, section numbers,
  DOIs, or "not yet"/progress wording in docstrings (that belongs only under `Sources/`).
- Treat all linter warnings as errors; the gate does.
- Register new modules: `RefinesPolyG.lean` (and later files) must be `import`ed by whatever already
  reaches them in the build; the topic root imports area aggregators. Confirm they're in the build,
  not silently skipped.
- Commit per gate-green phase/file. Do **not** squash phases. Do **not** push unless asked.
- Use `scripts/wiki rdeps <name>` before changing/renaming a declaration; `scripts/wiki show <name>`
  for signature + docstring. Prefer it over `grep` for "what uses X".
- **Unify & retire every iteration** (see the standing directive under §3): each commit deletes what
  the new layer made dead — subsumed squares (confirmed orphaned via `scripts/wiki rdeps`), duplicated
  transport lemmas, and scaffolding call sites — in the same commit, never leaving dead/commented code.

## 5. Success metric (one sentence)

Soundness proofs in the transport-heavy files reason on the `K[X]` side and cross the seam once via
`transfer` (or `simp [denote]` for trivial single squares); the ~61 hand-listed `simp only
[toPolyG…]` sites and multi-line `from by` transport blocks are largely gone; the litmus `hdvd`
block is short; `native_decide` still validates the engine; and `scripts/check.sh` is `GATE: PASS`
throughout. The §1 grep counts (hand-lists, `from by`, total squares) **monotonically decrease** —
every iteration retires what the layer subsumed.

## 6. Background (external prior art)

This layer is the Lean hand-roll of Coq's **CoqEAL** ("Refinements for Free!", Cohen–Dénès–Mörtberg;
refines MathComp polynomials to lists via parametricity) and its 2024 successor **Trocq** (proof
transfer for free). `toPolyG` is the catamorphism (unique F-algebra homomorphism) from the
representation to `K[X]`, so the transport squares are one functorial fact; `RefinesPolyG` expresses
that homomorphism as *a relation the operations respect*, which is exactly what tolerates the
redundant `List` representation (a bundled `AlgHom` cannot, since `List` isn't a ring). No mature
Lean port of CoqEAL/Trocq exists — hence the hand-rolled relation + `transfer` tactic. It also
mirrors the existing `CField`/`CFieldSpec` keystone in this codebase, which is the same
computable-ops + denotation-companion split at the *scalar* layer; this plan brings it to the
*polynomial* layer.
