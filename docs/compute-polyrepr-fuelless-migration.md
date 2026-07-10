# Retire the concrete `Compute` division and gcd layer — DONE

## Goal

Remove the fuel-threaded `Compute.cdivmod` / `cdiv` / `cmod` / `cdvd` / `cgcdExt`
definitions from `Compute/LogToAtan.lean`. Use the representation-independent, fuel-less
`CPoly.cdivmod` / `CPoly.cgcdExt` operations where the algorithm is naturally stated on the
`CPoly` interface, and use the well-founded `DensePoly.cdivmodWf` / `cdivWf` / `cmodWf` /
`cdvd` / `cgcdWf` API in the remaining dense-only downstream engine.

The split is intentional:

- `CPoly` is the public representation-independent polynomial layer in
  `ComputableAlgebra/PolyReprDivision.lean`;
- the `DensePoly.*Wf` family preserves the established normalized-list computation while
  removing caller-visible fuel from dense-only algorithms and their proofs.

## Constraints

- Preserve every `native_decide` result. The generic `CPoly` arithmetic may carry trailing
  zeros, so concrete list-valued results must be normalized at the boundary when their exact
  representation is part of the API.
- Do not leave compatibility shims for the retired `Compute` operations.
- Keep fuel only where it controls an algorithm's own recursion; do not pass it through merely
  to divide polynomials or compute a gcd.
- Replace the old concrete correctness lemmas with the existing `CPoly` or `DensePoly.*Wf`
  theorems rather than restating another concrete family.

## Completed phases

1. Migrated `logToAtanCompute` to `CPoly.cdivmod` / `CPoly.cgcdExt`, normalized its concrete
   outputs, and retired the local `cdvd` helper.
2. Migrated dense executable consumers (`RtResultant`, `Squarefree`, `Subresultant`, `Hermite`,
   and rational-function normalization) to the `DensePoly.*Wf` API.
3. Migrated correctness modules and source certificates to the fuel-free theorem families,
   deleting fuel-bound hypotheses and the superseded concrete division/gcd theorem block.
4. Deleted the remaining concrete definitions from `LogToAtan.lean`, removed compatibility fuel
   arguments from downstream helpers, and switched resultant sampling directly to
   `DensePoly.cresultantWf`.

Completion is verified by declaration/reference searches, affected module gates, and the full
repository gate.
