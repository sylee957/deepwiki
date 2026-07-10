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
   path; correctness assumptions remain in companion lawful classes. `CFrac.ofFraction` requires explicit
   nonzero evidence, while `CFrac.ofFraction?` exposes the executable checked `Option` boundary.
4. **Generic denotation — DONE.** State the bridge into `RatFunc` through `CPoly.toPoly`, prove the fraction
   homomorphism laws with `LawfulCPolyEngine`, and expose `CFieldSpec (F α)`. Validate both
   `DenseFrac` and `SparseFrac` through their representation-independent denotation laws.
5. **Tower rewiring — IN PROGRESS.** Generalize fraction derivation and tower constructors over a fraction
   representation where their bodies only use the interface. `towerDerivCFracWith` and the iterated
   `CDiffField` instance now work for any `CFrac F P`, with a generic `RatFunc` commuting square and a
   `SparseFrac` computation witness. The lawful `CFieldSpec` instance is now generic over every `CFrac F P`,
   rather than duplicated for dense and sparse carriers; recursive `CharZero`, `Algebra ℚ`, and
   `CDiffFieldSpec` tower instances are representation-independent as well. The parallel tower coefficient
   guard now works over any inner `CFrac F Q`, selecting gcd and division through `CPolyGcd Q` and
   `CPolyEuclidean Q`; dense and sparse inner fractions both execute through the same wrapper. Keep dense
   specialization only where an actual downstream polynomial algorithm is still dense.
6. **Abstract algorithm capabilities — IN PROGRESS.** Introduce Prop-free/lawful pairs for polynomial
   gcd/division, resultant/subresultant, and linear solve. The first slice is `CLinearSolve`/
   `LawfulCLinearSolve`, with the rational RREF implementation as its instance and the coupled-DE
   consumer now requesting the capability rather than `cConstSolveUniqueQ` directly. In the second slice,
   `CPolyGcd`/`LawfulCPolyGcd` selects gcd for raw-fraction reduction, while
   `CPolyEuclidean`/`LawfulCPolyEuclidean` selects division and extended Bézout: dense polynomials use the
   well-founded engine, sparse polynomials use the generic `CPoly` engine, and the rational-function
   exact-division bridge consumes only the capability. Concrete dense and generic implementations become
   instances. The third slice adds `CPolyResultant`/`LawfulCPolyResultant`: dense polynomials select the
   well-founded PRS resultant, sparse polynomials select the generic Sylvester determinant, and tower,
   radical, general-curve, and discriminant consumers request the capability. The tower residue-resultant
   bridge now proves correctness from `LawfulCPolyResultant`. The fourth slice generalizes the
   Sylvester-submatrix algorithm itself over `CPoly` and introduces `CPolySubresultant`/
   `LawfulCPolySubresultant`; dense and sparse LRT paths share the implementation, with correctness proved
   once through `CPoly.toPoly`. SymbolicIntegration consumers request the weakest capability they need.
7. **Consumer migration.** Rewire closed components in dependency order: rational reduction and tower
   gcd; residue/resultant and squarefree layers; linear systems and coupled DE; algebraic-function
   Bareiss/Hermite consumers. Remove parallel implementations when two bodies express the same algorithm;
   retain representation-selected optimized instances when their implementations intentionally differ.
8. **Completion audit.** Classify every remaining `DenseFrac`, `DensePoly.c*`, concrete subresultant,
   and concrete solver dependency as either an explicit specialization boundary or an unfinished
   migration. Run the full warning-/sorry-free gate and rebuild the dependency graph before completion.

## Checkpoint discipline

Land the phases in small gate-green commits. Each new representation-independent executable path gets a
`SparseFrac` or `SparsePoly` consumer or correctness witness. `ComputableAlgebra` does not use
`native_decide` proofs or executable showcase examples. Small concrete evidence goals may use the local
`ccompute` tactic, which tries only `rfl` and kernel `decide`; unsupported computation must become an
explicit lemma or an `Option`-returning API rather than silently switching to native evaluation. A generic
wrapper around a concrete dense algorithm does
not count as migration: the algorithm itself must be supplied through an abstract capability or remain
explicitly dense at the call site.
