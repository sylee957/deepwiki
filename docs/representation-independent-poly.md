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

## Phased plan (each gate-green; this is a multi-session arc)

1. **Foundation (additive).** New file `DeepWiki/ComputableAlgebra/PolyRepr.lean`: the `CPolyRepr` class,
   the `List` (dense) instance, and the derived `cadd`/`cneg`/`cscale`/`cshift`/`cmul` + their generic
   `coeff_*` squares. Does not touch the existing engine. *(This doc's spike is the core of it.)*
2. **Exact-degree layer.** Generic `cnorm`/`clead`/`cdeg`/`cisZero` on the interface, with satellites.
3. **Denotation.** Generic `toPoly` via `coeff`; the homomorphism squares (replacing the ~150 List-induction
   `toPolyG_*` proofs with `coeff`-based ones).
4. **Migrate the engine.** Re-point `CPoly α := List α` to `P` = the dense instance and switch the ops to
   the generic ones; or (safer) prove `List`-engine op = generic op and swap call sites gradually. The
   Risch/tower/Hermite/subresultant code then runs on the interface.
5. **Second representation (proof of independence).** Add a sparse instance (`List (ℕ × α)` sorted, or a
   hashmap) and re-run the `native_decide` showcase on it — the payoff.
6. **Fractions.** `CFracRepr` (num/den over any `CPolyRepr`), same pattern; `CFrac` today is already
   defined over `CPoly`, so it inherits the abstraction.

## Risks

- **Efficiency of `native_decide`.** The dense-list ops today use tight `List` recursion; the generic
  `ofFn (…) (fun i => …)` iterates `0..degBound`. For the small `native_decide` examples this is fine
  (validated), but the dense `List` instance can still provide *optimized* `cadd`/`cmul` overrides
  (interface = default, instance may specialize) if a benchmark regresses.
- **Exact-degree search** needs `[DecidableEq α]`/`isZero` — already available via `CCommRing.isZero`.
- **Scale.** Step 4 (migrating the whole engine + its ~hundreds of correctness lemmas) is the bulk and is
  genuinely multi-session; steps 1–3 are the foundation and can land first.
