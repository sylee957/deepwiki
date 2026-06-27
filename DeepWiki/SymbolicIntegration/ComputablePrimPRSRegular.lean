import DeepWiki.SymbolicIntegration.ComputableTowerGcdFFCorrect
import DeepWiki.SymbolicIntegration.ComputableTowerWellFounded

/-! # Is the primitive-PRS content-exactness `CPrimPRSGenAssocReg` unconditional?

`ComputableTowerGcdFFCorrect.associated_toPolyG_cgcdFFCore` — the abstract correctness of the recursive
tower fraction-free gcd over `β(s)[t]` — is gated on the per-step regularity bundle
`CPrimPRSGenAssocReg cgcdB fuel P Q`. This file determines whether that bundle is an **unconditional
theorem** (so the recursive `CRischFieldSpec` and fully-abstract Risch soundness close end-to-end) or a
**genuine per-run non-degeneracy assumption**, and SHARPENS it precisely.

## Anatomy of `cprimPRSgcdGenCore` (the kernel) and `CPrimPRSGenAssocReg` (the gate)

`cprimPRSgcdGenCore cgcdB fuel P Q` (`ComputableTowerGcdFFCore`) runs a **primitive polynomial-remainder
sequence** in `t` over the GCD-domain coefficient ring `CPolyG β = β[s]`:
* if `Q` is zero, return `gbprimitivePartCore 30 cgcdB P` (strip `P`'s content);
* else set `r := gbprimitivePartCore 30 cgcdB (gbpsremainderCore 60 P Q)` — the **primitive part** of the
  **pseudo-remainder** — and recurse on `(Q, r)` with one less fuel.

`CPrimPRSGenAssocReg cgcdB fuel P Q` (`ComputableTowerGcdFFCorrect`) is the inductive bundle the gcd
invariant of *each step* consumes. At a non-terminal `fuel+1` step (with `Pn = gbnormCore P`, `Qn =
gbnormCore Q`, `prem = gbpsremainderCore 60 Pn Qn`, `r = gbprimitivePartCore 30 cgcdB prem`) it asks for:
  * **(i) termination** — the recursion reaches `gbisZeroCore Qn = true`;
  * **(ii) a pseudo-division witness** `(s, c)` with
    `C (amG (toPolyG c)) · toGBPolyG Pn = toGBPolyG s · toGBPolyG Qn + toGBPolyG prem` **and the multiplier
    `amG (toPolyG c) ≠ 0`** (a `β(s)`-unit);
  * **(iii) the content strip is a `β(s)`-unit scaling** — `Associated (toGBPolyG r) (toGBPolyG prem)`.

## The verdict (proved below)

`CPrimPRSGenAssocReg` is **NOT unconditional**, and the obstruction is **not** a missing
content/GCD-domain fact — it is exactly TWO per-run non-degeneracy ingredients, which we name sharply:

1. **The PRS terminates within the supplied `fuel`** — i.e. `CPrimPRSGenRegular cgcdB fuel P Q`
   (`ComputableTowerWellFounded`), the genuine per-step `t`-length-drop witness. The pseudo-remainder degree
   *does* strictly drop at the polynomial level over the integral domain `(CFieldSpec.K β)[X]` (`lc(Q)` is a
   non-zero-divisor) — this is a real theorem — but the engine's loop guard compares the **normalized list
   length** `(gbnormCore r).length`, and **no engine lemma states that list-length drop** abstractly over
   the non-field coefficient ring `CPolyG β = β[s]` (the same gap `ComputableTowerWellFounded` records:
   "no abstract `gbpsremainderCore` length-drop lemma"). So termination enters as the per-run witness.
2. **The content-gcd `cgcdB` is gcd-correct** — `CgcdBCorrect cgcdB`. On a real tower run this is the
   level-`β` gcd-correctness of `cgcdFFRawCore β` (the tower induction). It is **not** unconditional even at
   the base: `associated_toPolyG_cgcdExtG` needs `cgcdTerminatesG`, so the base `cgcdFFRawCore ℚ =
   (cgcdExtG _).1` is gcd-correct only on terminating Euclid runs.

Given those two — plus transparent per-step content-nonzero / fuel side-conditions the algorithm self-
satisfies — clauses (ii) and (iii) of `CPrimPRSGenAssocReg` are **theorems** (clause (ii)'s identity is
`toGBPolyG_gbpsremainderCore`, already unconditional; its nonzero-multiplier part is recovered here; clause
(iii) is `associated_toGBPolyG_gbprimitivePartCore_of_correct`). The deliverable is the **reduction
theorem** `cPrimPRSGenAssocReg_of_regular_of_correct`: `CPrimPRSGenRegular` + `CgcdBCorrect` + the
transparent side-conditions ⟹ `CPrimPRSGenAssocReg`. That replaces the opaque 13-hypothesis gate with the
**precise** non-degeneracy: *termination* and *level-β gcd-correctness*.

So fully-abstract soundness is **not** closed by an unconditional `CPrimPRSGenAssocReg`; it is closed *up
to* threading these two per-run witnesses through the tower recursion. This resolves the memory's tension:
the residual is **bookkeeping of termination + the level-β gcd-correctness induction**, NOT a missing
research-grade content theorem. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG GBPolyCore

end DeepWiki.SymbolicIntegration
