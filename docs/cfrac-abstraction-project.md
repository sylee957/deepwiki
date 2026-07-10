# Representation-independent computable fractions and algorithm dependencies

## Goal

Turn `CFrac` from the current dense-polynomial carrier into the fraction-representation interface,
parallel to `CPoly`. Rename the current specialization to `DenseFrac`, add `SparseFrac`, and make
SymbolicIntegration depend on abstract, lawful polynomial and linear-algebra algorithms instead of
calling dense gcd, resultant, subresultant, and solve implementations directly.

The intended stack is:

```text
CPoly P + CPolyEngine P + LawfulCPolyEngine P
                    |
              CFrac F P
               /       \
       DenseFrac       SparseFrac
```

`CFrac F P` associates a fraction carrier `F` with the polynomial representation `P` stored in its
numerator and denominator. `DenseFrac` uses `DensePoly`; `SparseFrac` uses `CPoly.SparsePoly`.
Fraction arithmetic is generic over the interface and selects the underlying polynomial engine through
`CPolyEngine P`, so the dense specialization retains the established computation while the sparse one
runs the same fraction algorithm.

## Phases

1. **Carrier/interface split — DONE.** Introduce `CFrac F P`, `PolyFrac P`, `DenseFrac`, and `SparseFrac` in
   symmetric representation modules. Migrate type occurrences from the old `CFrac α` carrier to
   `DenseFrac α`; keep `CFrac.*` as the generic API namespace, not a compatibility type alias.
2. **Raw fraction boundary — DONE.** Retire the duplicate legacy pair arithmetic. Valid field operations now
   use `DenseFrac`/`CFrac`; the only unchecked pair is the explicitly named `RawFrac` boundary for
   algorithms that have not discharged denominator certificates yet.
3. **Generic field engine — DONE.** Generalize denominator-domain evidence, constructors, add/mul/neg/inv,
   zero test, and the `CField` instance over `[CFrac F P] [CPolyEngine P]`. Preserve the Prop-free runtime
   path; correctness assumptions remain in companion lawful classes.
4. **Generic denotation — DONE.** State the bridge into `RatFunc` through `CPoly.toPoly`, prove the fraction
   homomorphism laws with `LawfulCPolyEngine`, and expose `CFieldSpec (F α)`. Validate both
   `DenseFrac` and `SparseFrac` with native computation and denotation examples.
5. **Tower rewiring.** Generalize fraction derivation and tower constructors over a fraction
   representation where their bodies only use the interface. Keep dense specialization only where an
   actual downstream polynomial algorithm is still dense.
6. **Abstract algorithm capabilities — IN PROGRESS.** Introduce Prop-free/lawful pairs for polynomial
   gcd/division, resultant/subresultant, and linear solve. The first slice is `CLinearSolve`/
   `LawfulCLinearSolve`, with the rational RREF implementation as its instance and the coupled-DE
   consumer now requesting the capability rather than `cConstSolveUniqueQ` directly. The second slice is
   `CPolyGcd`/`LawfulCPolyGcd` now selects gcd for raw-fraction reduction, while
   `CPolyEuclidean`/`LawfulCPolyEuclidean` selects division and extended Bézout: dense polynomials use the
   well-founded engine, sparse polynomials use the generic `CPoly` engine, and the rational-function
   exact-division bridge consumes only the capability. Concrete dense and generic implementations become instances;
   SymbolicIntegration consumers request the weakest capability they need.
7. **Consumer migration.** Rewire closed components in dependency order: rational reduction and tower
   gcd; residue/resultant and squarefree layers; linear systems and coupled DE; algebraic-function
   Bareiss/Hermite consumers. Remove parallel implementations when two bodies express the same algorithm;
   retain representation-selected optimized instances when their implementations intentionally differ.
8. **Completion audit.** Classify every remaining `DenseFrac`, `DensePoly.c*`, concrete subresultant,
   and concrete solver dependency as either an explicit specialization boundary or an unfinished
   migration. Run the full warning-/sorry-free gate and rebuild the dependency graph before completion.

## Checkpoint discipline

Land the phases in small gate-green commits. Each new representation-independent executable path gets a
`SparseFrac` or `SparsePoly` computation witness. A generic wrapper around a concrete dense algorithm does
not count as migration: the algorithm itself must be supplied through an abstract capability or remain
explicitly dense at the call site.
