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

**Net:** the abstraction is complete and validated end-to-end — interface, arithmetic, exact-degree,
denotation + correctness, a second (sparse) carrier proving independence, and fractions — all reducing
under `native_decide`. What is left is only Step 4's *mechanical* re-pointing of the existing engine's
call sites onto the interface, which this foundation makes safe and incremental.

## Risks

- **Efficiency of `native_decide`.** The dense-list ops today use tight `List` recursion; the generic
  `ofFn (…) (fun i => …)` iterates `0..degBound`. For the small `native_decide` examples this is fine
  (validated), but the dense `List` instance can still provide *optimized* `cadd`/`cmul` overrides
  (interface = default, instance may specialize) if a benchmark regresses.
- **Exact-degree search** needs `[DecidableEq α]`/`isZero` — already available via `CCommRing.isZero`.
- **Scale.** Step 4 (migrating the whole engine + its ~hundreds of correctness lemmas) is the bulk and is
  genuinely multi-session; steps 1–3 are the foundation and can land first.
