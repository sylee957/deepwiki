# Representation-independent computable polynomials (and fractions)

**Goal.** Today `CPoly α := List α` — the computable polynomial engine is hard-wired to a *dense
coefficient list*. Make it abstract over the **representation** `P` (dense `List`, sparse
`List (ℕ × α)` / hashmap, …) behind an interface, and express the computational ops + their correctness
generically, so a different representation is a drop-in instance. `CFrac` (num/den pairs) follows once
`CPoly` is abstract.

## Feasibility — VALIDATED by spike (2026-07-09)

A standalone spike proved the two make-or-break properties hold:
- **`native_decide` reduces** through the interface at the `List` instance
  (`padd [1,2,3] [10,20] = [11,22,3]` by `native_decide`).
- **Correctness is representation-generic**: `pco (padd p q) i = pco p i + pco q i` proven for *any*
  `[PolyRepr P]` from the interface spec alone.

## The interface (minimal core)

```
class CPolyRepr (P : Type* → Type*) where
  coeff    : {α} → [Zero α] → P α → ℕ → α          -- coefficient at degree i (0 past the end)
  degBound : {α} → P α → ℕ                          -- an UPPER bound: coeff p i = 0 for i ≥ degBound p
  ofFn     : {α} → ℕ → (ℕ → α) → P α                -- dense construction from length + coeff fn
  coeff_ofFn    : coeff (ofFn n f) i = if i < n then f i else 0
  coeff_ge      : degBound p ≤ i → coeff p i = 0
```

Keep the interface **minimal** — `coeff` / `degBound` / `ofFn` — so a new representation is cheap to add.
Everything else is **derived generically**:

- `cadd p q      := ofFn (max (degBound p) (degBound q)) (fun i => coeff p i + coeff q i)`
- `cneg p        := ofFn (degBound p) (fun i => - coeff p i)`
- `cscale c p    := ofFn (degBound p) (fun i => c * coeff p i)`
- `cshift k p    := ofFn (degBound p + k) (fun i => if k ≤ i then coeff p (i - k) else 0)`
- `cmul p q      := ofFn (degBound p + degBound q) (fun i => ∑ j ∈ range (i+1), coeff p j * coeff q (i-j))`
- `ceval p x`, `cderiv p`, … likewise by a `coeff` formula.

**Exact degree / normalization** (`cnorm`/`clead`/`cdeg`/`cisZero`) needs the *largest* `i < degBound`
with `coeff p i ≠ 0` — a decidable search over `[0, degBound)` requiring `[DecidableEq α]` (or the
engine's `CCommRing.isZero`). Derived generically from `coeff` + `degBound`; no interface addition needed.

**Fuel ops** (`cdivmod`/`cgcdExt`) are already written on `clead`/`cdeg`/`cshift`/`csub`, so they become
representation-generic for free once those are.

## Denotation & correctness

- `toPoly : P α → (CRingSpec.R α)[X] := ∑ i ∈ range (degBound p), C (toR (coeff p i)) * X^i`,
  stated via `coeff`. The homomorphism squares (`toPoly (cadd p q) = toPoly p + toPoly q`, …) prove
  from the generic `coeff (cadd p q) i = coeff p i + coeff q i` + `Polynomial.ext`/`coeff` — **no more
  `List` induction**, so they hold for every representation at once.
- `native_decide` examples stay: the `List` instance's `coeff`/`ofFn`/`degBound` reduce, so every derived
  op reduces.

## Interaction with the ring-generalization (already landed)

Composes cleanly: ops are `{P} [CPolyRepr P] {α} [CCommRing α]`, with `CRingSpec` for the denotation —
the coefficient stays a computable commutative ring (field a specialization). The keystone
`CCommRing (P α)` (a polynomial-over-a-ring is a ring coefficient) is stated on the interface.

## Phased plan — Steps 1–6 BUILT (each gate-green, additive)

1. **Foundation — DONE** (`PolyRepr.lean`, commits `b67959c2`+`068825a0`): the `CPolyRepr` class, the
   dense `List` instance, generic `add`/`neg`/`scale`/`mul` + `toR` coefficient squares + `native_decide`.
2. **Exact-degree layer — DONE** (`PolyReprDegree.lean`, commit `9dc182de`): generic `cisZero`/`cdeg`/
   `clead`/`cnorm` on the coefficient support; `cisZero_iff` correctness; `native_decide`.
3. **Denotation — DONE** (`PolyReprDenote.lean`, commit `9dc182de`): generic `toPoly` via `coeff`, the
   `coeff_toPoly` bridge, and the homomorphism squares `toPoly_add`/`neg`/`scale`/`mul` — all coefficient-
   wise, **no `List` induction**, so they hold for every representation.
4. **Migration bridge — DONE** (`PolyReprBridge.lean`, commit `5f19a3e8`): `toPoly_list_eq`
   (`CPolyRepr.toPoly = CPoly.toPoly` at `List`) + under-denotation op agreements (`add↔cadd`, …). This
   is the *enabler*: because every engine theorem is `toPoly`-stated, call sites can be re-pointed
   `CPoly.c* → CPolyRepr.*` with proofs preserved. **Remaining bulk (documented, not yet done):** the
   actual sweep of the ~hundreds of engine call sites + `toPolyG_*` proofs — mechanical but large, a
   dedicated multi-session migration on top of this foundation.
5. **Second representation — DONE** (`PolyReprSparse.lean`, commit `496c73f0`): a sparse `SparsePoly`
   (association-list) instance; the generic engine runs on it unchanged (`native_decide` on `cdeg`/`clead`
   of sparsely-stored polynomials). **This is the proof of representation-independence.**
6. **Fractions — DONE** (`PolyReprFrac.lean`, commit `9f8018bf`): `GFrac P α` (num/den over any
   `CPolyRepr`), fraction `mul`/`add`, `RatFunc` denotation + `toRatFunc_mul`; `native_decide` on **both**
   the dense and sparse carriers.

**Net:** the abstraction is complete and validated end-to-end — interface, arithmetic, exact-degree
(`cisZero_iff`, `cdeg_eq_natDegree`, `toR_clead_eq_leadingCoeff`, `toPoly_cnorm`), denotation +
correctness, a second (sparse) carrier proving independence, and fractions — all reducing under
`native_decide`. The engine-agreement bridge proves every engine op equals the interface op at `List`.

## ⚠ Step 4's engine call-site sweep is NOT a mechanical rename (evidence)

Re-pointing the ~168 engine files that use `CPoly.c*` onto the interface **cannot** be done as a
behaviour-preserving mechanical sweep, for two hard reasons established empirically:

1. **The interface ops ≠ the engine ops as raw lists, over generic `[CCommRing α]`.** The engine's
   `cadd` (list recursion) gives `cadd [1,2] [3] = [4,2]`; the coefficient relation `coeff (add p q) i =
   add (coeff p i) (coeff q i)` needs `CCommRing.add x 0 = x` — a *ring law* the Prop-free `CCommRing`
   does not have. `cmul` differs by a trailing zero even at `ℚ` (`[3,10,8]` vs `[3,10,8,0]`). The ops
   agree only **under the denotation** `toPoly` (that is exactly what the bridge proves), not as the raw
   representations the engine computes with. So swapping `cadd → CPolyRepr.add` changes what the generic
   engine *computes*.
2. **120 of the engine files carry `native_decide` examples** pinned to exact list outputs, and the
   engine's thousands of correctness proofs are **representation-specific** (`List` induction on `::`/`[]`,
   `getD`, `length`). Re-parametrising a declaration by `{P} [CPolyRepr P]` forces every one of its proofs
   to be re-done through the interface's denotation squares instead of list lemmas — i.e. **re-deriving
   the engine's correctness against the abstract interface**, which is the original engine-development
   effort, not a sweep.

## The `CPolyEngine` enabler — and why migration is connected-component-scale, not per-module

`PolyEngine.lean` adds the **fat** interface `CPolyEngine extends CPolyRepr`: the polynomial ops are
**class fields**, and the `List` instance supplies the *concrete engine ops* — `CPolyEngine.add (p :
List α) = CPoly.cadd p` **definitionally**. So a declaration re-parametrised over `[CPolyEngine P]`
computes *exactly* the engine's list output at `List`: **`native_decide` is preserved** and the ops need
no bridge. The `SparsePoly` instance supplies the generic `ofFn` ops, so a migrated declaration also runs
sparse. This is the enabler that removes the *op* mismatch (blocker #1 above).

**But there is a second, harder coupling — the denotation.** A generic declaration `foo {P} [CPolyEngine
P] (p : P α)` must state its correctness through the *generic* `CPolyRepr.toPoly` (the `List`-specific
`CPoly.toPoly` doesn't typecheck at generic `P`). And `CPolyRepr.toPoly = CPoly.toPoly` at `List` is a
*proven bridge* (`toPoly_list_eq`), **not** definitional. So the moment a module's `toPoly`-stated theorem
is migrated, every downstream consumer that pattern-matches on `CPoly.toPoly` must migrate too. Migration
therefore propagates along the `toPoly` dependency graph: it is **connected-component-scale**, not
one-isolated-module-at-a-time. Even the smallest correctness module (`ReductionRealization`, 1 decl) has a
downstream consumer.

**The two honest ways to finish it**, both large:
1. **Component-by-component** re-derivation: migrate a `toPoly`-closed set of modules together (module +
   all consumers of its `toPoly` statements), gated per component. Correct, safe, multi-week.
2. **Redefine the engine denotation** `CPoly.toPoly := CPolyRepr.toPoly` (make the bridge *definitional*),
   re-proving the ~50 `toPolyG_*` satellites in `Polynomial.lean`, after which per-module migration
   becomes transparent. Bounded to the core file but high-risk (it is imported by all 168 files).

The delivered foundation (`CPolyRepr` + `CPolyEngine` + full correctness + bridge, all gate-green) is
what makes *either* route safe. It does not make the aggregate small: the engine port is a genuine
re-derivation effort, correctly scoped here rather than faked by breaking the 120 `native_decide` suites.

## The bottom-up generic algorithm layer (the constructive route, in progress)

Since the *existing* engine can't be migrated isolated-module-at-a-time, the constructive path is to
**re-build the algorithm stack generically on the interface**, bottom-up — each layer a real, gated,
`native_decide`-validated (dense *and* sparse) unit. Landed so far (all in `PolyReprDenote.lean` /
`PolyReprDivision.lean`):

- **`cpow p n = pⁿ`** — `toPoly_cpow : toPoly (cpow p n) = (toPoly p)^n`, by induction on the
  multiplicative square.
- **`csub` / `cmonomial c k = c·Xᵏ` / `cshift k p = Xᵏ·p`** — each with its denotation square, the
  building blocks of a division step.
- **`cderiv`** (formal derivative) — `toPoly_cderiv : toPoly (cderiv p) = (toPoly p).derivative`, via a
  ring `ℕ`-multiple `natMul` (`CCommRing` has no `SMul ℕ`) and `toR_natMul`.
- **`cdivmod fuel p q = (Q, R)`** (Euclidean division over a computable field) — the **division
  identity** `toPoly p = toPoly q · toPoly Q + toPoly R` at *every* fuel, by pure algebra + induction (no
  degree/termination argument needed).
- **Termination** (`PolyReprDivisionDegree.lean`) — `degree_reduce_step_lt` (one cancellation step
  strictly lowers `degree`, via `Polynomial.degree_sub_lt` leading-coefficient cancellation), and
  `cdivmod_remainder_reduced` (with `fuel > cdeg p` the remainder is zero or of degree `< cdeg q` — the
  Euclidean remainder property).
- **`cgcd` — a genuine gcd, both directions proven**: `dvd_cgcd` (every common divisor of `a,b` divides
  `cgcd a b`, from the division identity) *and* `cgcd_dvd` (with `cdeg b < fuel`, `cgcd a b` divides both
  `a` and `b`, by fuel induction on the remainder-reduced measure). The inner division uses a `cdeg a + 1`
  fuel (always fully reduced), decoupled from the gcd-step fuel.

Each computable op reduces under `native_decide` on both the dense `List` and sparse `SparsePoly`
carriers — the same algorithm, two representations — and the algebraic correctness is a-priori (not merely
`native_decide`-validated). This is a complete, representation-independent Euclidean gcd theory built
bottom-up on the interface.

## Risks

- **Efficiency of `native_decide`.** The dense-list ops today use tight `List` recursion; the generic
  `ofFn (…) (fun i => …)` iterates `0..degBound`. For the small `native_decide` examples this is fine
  (validated), but the dense `List` instance can still provide *optimized* `cadd`/`cmul` overrides
  (interface = default, instance may specialize) if a benchmark regresses.
- **Exact-degree search** needs `[DecidableEq α]`/`isZero` — already available via `CCommRing.isZero`.
- **Scale.** Step 4 (migrating the whole engine + its ~hundreds of correctness lemmas) is the bulk and is
  genuinely multi-session; steps 1–3 are the foundation and can land first.
