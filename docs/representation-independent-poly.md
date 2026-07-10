# Representation-independent computable polynomials (and fractions)

**Goal.** Today `DensePoly α := List α` — the computable polynomial engine is hard-wired to a *dense
coefficient list*. Make it abstract over the **representation** `P` (dense `List`, sparse
`List (ℕ × α)` / hashmap, …) behind an interface, and express the computational ops + their correctness
generically, so a different representation is a drop-in instance. `CFrac` (num/den pairs) follows once
`DensePoly` is abstract.

## Feasibility — VALIDATED by spike (2026-07-09)

A standalone spike proved the two make-or-break properties hold:
- **`native_decide` reduces** through the interface at the `List` instance
  (`padd [1,2,3] [10,20] = [11,22,3]` by `native_decide`).
- **Correctness is representation-generic**: `pco (padd p q) i = pco p i + pco q i` proven for *any*
  `[PolyRepr P]` from the interface spec alone.

## The interface (minimal core)

```
class CPoly (P : Type* → Type*) where
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

Composes cleanly: ops are `{P} [CPoly P] {α} [CCommRing α]`, with `CRingSpec` for the denotation —
the coefficient stays a computable commutative ring (field a specialization). The keystone
`CCommRing (P α)` (a polynomial-over-a-ring is a ring coefficient) is stated on the interface.

## Phased plan — Steps 1–6 BUILT (each gate-green, additive)

1. **Foundation — DONE** (`PolyRepr.lean`, `PolyReprDense.lean`, commits
   `b67959c2`+`068825a0`): the representation-neutral `CPoly` class and generic
   `add`/`neg`/`scale`/`mul` + `toR` coefficient squares, plus the dense `DensePoly` instance and its
   `native_decide` checks in a concrete-representation module symmetric to `PolyReprSparse.lean`.
2. **Exact-degree layer — DONE** (`PolyReprDegree.lean`, commit `9dc182de`): generic `cisZero`/`cdeg`/
   `clead`/`cnorm` on the coefficient support; `cisZero_iff` correctness; `native_decide`.
3. **Denotation — DONE** (`PolyReprDenote.lean`, commit `9dc182de`): generic `toPoly` via `coeff`, the
   `coeff_toPoly` bridge, and the homomorphism squares `toPoly_add`/`neg`/`scale`/`mul` — all coefficient-
   wise, **no `List` induction**, so they hold for every representation.
4. **Migration bridge — DONE** (`PolyReprBridge.lean`, commit `5f19a3e8`): `toPoly_list_eq`
   (`CPoly.toPoly = DensePoly.toPoly` at `List`) + under-denotation op agreements (`add↔cadd`, …). This
   is the *enabler*: because every engine theorem is `toPoly`-stated, call sites can be re-pointed
   `DensePoly.c* → CPoly.*` with proofs preserved. **Remaining bulk (documented, not yet done):** the
   actual sweep of the ~hundreds of engine call sites + `toPolyG_*` proofs — mechanical but large, a
   dedicated multi-session migration on top of this foundation.
5. **Second representation — DONE** (`PolyReprSparse.lean`, commit `496c73f0`): a sparse `SparsePoly`
   (association-list) instance; the generic engine runs on it unchanged (`native_decide` on `cdeg`/`clead`
   of sparsely-stored polynomials). **This is the proof of representation-independence.**
6. **Fractions — DONE** (`PolyReprFrac.lean`, commit `9f8018bf`): `GFrac P α` (num/den over any
   `CPoly`), fraction `mul`/`add`, `RatFunc` denotation + `toRatFunc_mul`; `native_decide` on **both**
   the dense and sparse carriers.

**Net:** the abstraction is complete and validated end-to-end — interface, arithmetic, exact-degree
(`cisZero_iff`, `cdeg_eq_natDegree`, `toR_clead_eq_leadingCoeff`, `toPoly_cnorm`), denotation +
correctness, a second (sparse) carrier proving independence, and fractions — all reducing under
`native_decide`. The engine-agreement bridge proves every engine op equals the interface op at `List`.

## ⚠ Step 4's engine call-site sweep is NOT a mechanical rename (evidence)

Re-pointing the ~168 engine files that use `DensePoly.c*` onto the interface **cannot** be done as a
behaviour-preserving mechanical sweep, for two hard reasons established empirically:

1. **The interface ops ≠ the engine ops as raw lists, over generic `[CCommRing α]`.** The engine's
   `cadd` (list recursion) gives `cadd [1,2] [3] = [4,2]`; the coefficient relation `coeff (add p q) i =
   add (coeff p i) (coeff q i)` needs `CCommRing.add x 0 = x` — a *ring law* the Prop-free `CCommRing`
   does not have. `cmul` differs by a trailing zero even at `ℚ` (`[3,10,8]` vs `[3,10,8,0]`). The ops
   agree only **under the denotation** `toPoly` (that is exactly what the bridge proves), not as the raw
   representations the engine computes with. So swapping `cadd → CPoly.add` changes what the generic
   engine *computes*.
2. **120 of the engine files carry `native_decide` examples** pinned to exact list outputs, and the
   engine's thousands of correctness proofs are **representation-specific** (`List` induction on `::`/`[]`,
   `getD`, `length`). Re-parametrising a declaration by `{P} [CPoly P]` forces every one of its proofs
   to be re-done through the interface's denotation squares instead of list lemmas — i.e. **re-deriving
   the engine's correctness against the abstract interface**, which is the original engine-development
   effort, not a sweep.

## The `CPolyEngine` enabler — and why migration is connected-component-scale, not per-module

`PolyEngine.lean` adds the Prop-free operations interface `CPolyEngine`, paired with
`LawfulCPolyEngine` for its denotation laws. A migrated declaration takes `[CPoly P] [CPolyEngine P]`;
the `List` instances supply the *concrete engine ops* — `CPolyEngine.add (p :
List α) = DensePoly.cadd p` **definitionally**. So a declaration re-parametrised over
`[CPoly P] [CPolyEngine P]`
computes *exactly* the engine's list output at `List`: **`native_decide` is preserved** and the ops need
no bridge. The `SparsePoly` instance supplies the generic `ofFn` ops, so a migrated declaration also runs
sparse. This is the enabler that removes the *op* mismatch (blocker #1 above).

**But there is a second, harder coupling — the denotation.** A generic declaration `foo {P} [CPoly P]
[CPolyEngine P] [LawfulCPolyEngine P] (p : P α)` must state its correctness through the *generic*
`CPoly.toPoly` (the `List`-specific
`DensePoly.toPoly` doesn't typecheck at generic `P`). And `CPoly.toPoly = DensePoly.toPoly` at `List` is a
*proven bridge* (`toPoly_list_eq`), **not** definitional. So the moment a module's `toPoly`-stated theorem
is migrated, every downstream consumer that pattern-matches on `DensePoly.toPoly` must migrate too. Migration
therefore propagates along the `toPoly` dependency graph: it is **connected-component-scale**, not
one-isolated-module-at-a-time. Even the smallest correctness module (`ReductionRealization`, 1 decl) has a
downstream consumer.

**The two honest ways to finish it**, both large:
1. **Component-by-component** re-derivation: migrate a `toPoly`-closed set of modules together (module +
   all consumers of its `toPoly` statements), gated per component. Correct, safe, multi-week.
2. **Redefine the engine denotation** `DensePoly.toPoly := CPoly.toPoly` (make the bridge *definitional*),
   re-proving the ~50 `toPolyG_*` satellites in `PolyReprDense.lean`, after which per-module migration
   becomes transparent. Bounded to the core file but high-risk (it is imported by all 168 files).

The delivered foundation (`CPoly` + `CPolyEngine` + full correctness + bridge, all gate-green) is
what makes *either* route safe. It does not make the aggregate small: the engine port is a genuine
re-derivation effort, correctly scoped here rather than faked by breaking the 120 `native_decide` suites.

The first consumer migration has landed: `cCoupledDESystem` is generic over `[CPoly P]
[CPolyEngine P]`, preserves the dense-list computation definitionally, and runs the same worked solve
on `SparsePoly`. Its dense soundness proof crosses a named specialization lemma, so existing downstream
theorems remain unchanged while the executable solver itself is representation-independent.

The next component has also landed: `CPolyEngine` now exposes formal differentiation and derived
subtraction with their `LawfulCPolyEngine` denotation laws. `coupledClearedCheck` and its soundness theorem
are representation-generic (and execute on `SparsePoly`), while `cDerivMonomialQ` is the first generic
parallel-integration helper; both retain the original dense computation definitionally.

The parallel-result validation path is now generic as well: `CPolyEngine.prod` folds the representation's
own multiplication from the existing generic `CPoly.one`, while `cParallelResultDerivQ` and
`cParallelCheckQ` run unchanged on dense and sparse polynomials. The accumulator reuses `CPoly.czero`;
that constructor and its denotation theorem were moved from the division module into
`PolyReprDenote.lean` instead of introducing a duplicate engine-zero API.

The Risch-DE helper layer now uses representation-generic evaluation and degree queries.
`CPolyEngine.eval` retains the dense engine's Horner evaluator definitionally, supplies the generic
evaluator for `SparsePoly`, and carries the corresponding `Polynomial.eval` denotation law.
`cisRootNat`, `cPosIntRoots`, and `cRdeBoundDegree` are generic over the representation, with sparse
`native_decide` checks; the existing dense weak normalizer continues to infer the `List` instance.

The representation-independent coupled-DE surface now also includes the Gaussian-pair helpers used by
tangent cancellation: coefficient scaling, evaluation at `i`, pair multiplication/subtraction/zero-test,
and synthetic division by `t-i`. Dense reconstruction proofs cross explicit definitional-specialization
lemmas. The tangent derivation is generic too and has a sparse `native_decide` check; the recursive
`cCoupledDECancelTan` driver and its reconstruction theorem remain on the dense frontier.

Coefficientwise and monomial differentiation now cross the representation boundary as well.
`CPolyEngine.mapCoeffs` preserves the dense engine's exact `List.map` computation and has a lawful
coefficient square for zero-preserving maps; `cmapDeriv` and `cmonomialDeriv` use that operation and have
generic denotation theorems plus sparse execution coverage. The shared Rothstein–Trager numerator
`cAmcDd` is generic on top of them. The duplicate dense implementation `afFx` is now a semantic
abbreviation of `cmapDeriv`, and `afDerivWf` reuses the same canonical operation instead of re-spelling
the coefficient map.

The degree-raising primitive polynomial integrator is representation-independent too.
`CPolyEngine.monomial` selects the exact dense `replicate k 0 ++ [c]` implementation at `List` and the
generic `ofFn` construction at `SparsePoly`; these are intentional representation specializations, not
duplicate algorithms. Its lawful square is supported by the dense-local `toPolyG_cMonomial` satellite.
`cIntegratePrimPolyDegRaise` and its telescoping soundness theorem are generic, execute on sparse input,
and retain the existing dense worked output. The lawful engine laws are universe-polymorphic in their
denotation carrier, so the same generic soundness theorem applies at tower coefficients such as
`CFrac β`, whose denotation is `RatFunc (CFieldSpec.K β)`.

The earlier Chapter 5 polynomial-part recursions now use the same representation-independent layer.
`cPolyReduceTower` and `cPrimitivePolyIntegrate` normalize through the engine and state their former
dense-list stopping tests semantically as “zero or degree below the cutoff.” Their cancellation steps use
engine monomials, subtraction, monomial derivation, and addition. Both execute on `SparsePoly`; the
original dense `CFrac ℚ` examples and source-catalog aliases remain unchanged. There is one recursive
implementation of each algorithm rather than parallel dense and generic bodies.
The immediate LRT tower wrapper `towerPolyIntegrateLrt` and its soundness theorem are generic over the
polynomial representation as well; the dense special-part proof now crosses the single `toPoly_list_eq`
boundary where it consumes that theorem.
The hyperexponential residual fold no longer carries a false dense-polynomial dependency either:
`cHyperexpResidual` is generic in the log-argument payload and needs only `CCommRing` on its scalar field.
Negative Laurent-coefficient extraction is representation-independent as well:
`cHyperexpSpecialNeg` reads its numerator through `CPoly.coeff` and its special denominator through the
engine's zero, degree, and leading-coefficient operations. It executes on sparse inputs, while the existing
dense Laurent soundness proof crosses explicit dense-specialization lemmas. This replaces the last direct
`List.getD` assumption in the helper rather than adding a parallel sparse implementation.
The parallel tower wrapper now abstracts its outer polynomial representation too. The engine's
`coeffList`/`ofCoeffList` adapters are the identity at `DensePoly` and generic coefficient enumeration/
construction at `SparsePoly`; `cToRatCoeffsQ` and `cParallelIntegrateTower` use them to share the single
dense base-field solver. The wrapper therefore executes on sparse tower polynomials without duplicating
the Risch–Norman algorithm. The Chapter 10 catalog alias remains explicitly pinned to `DensePoly`.
The same adapters remove the list boundary from `cIntegrateHyperexpLaurent`: its positive coefficients
are enumerated through the engine, and its numerator and monomial denominator are reconstructed in the
caller’s representation. The recursive Laurent algorithm now executes on sparse polynomials while the
existing dense soundness theorems continue to specialize it definitionally.
The result boundary is representation-independent now as well. `IntegralResult α P` stores both its
rational fraction and log arguments in `P`, with `P := DensePoly` as the default so existing signatures
remain unchanged. `checkIdentity` is generic over `CPolyEngine`, preserves the dense computation through
the engine adapters, and validates sparse integral results directly; no parallel generic result structure
was introduced.
That result abstraction also removes a real duplicate. `cCorrectHyperexpNormal` is the single generic
implementation of scalar-residual integration and subtraction; both `cIntegrateHyperexpNormal` and
`hyperexpCase.reducedCorrect` now call it instead of carrying matching dense bodies. It executes on sparse
results while preserving the dense engine operations definitionally.
The special/normal recombination was duplicated too. `combineRationalParts` now owns the generic fraction
addition formula; representation-generic `combineSN` and `combineSNLrt` both reuse it. Sparse result
examples exercise the shared combiners, while the existing dense soundness proofs specialize the same
definitions.
The symbolic LRT result container now follows the same pattern: `LrtResult α P` stores its rational part,
residue polynomials, and parametric log arguments in `P`, defaulting to `DensePoly`. `combineSNLrt` is
representation-generic and has sparse execution coverage, while the established LRT integrator and
soundness predicates continue to use the default dense specialization.
The result-level residue-constancy check is generic too. `CPolyEngine.cmonic` derives monic normalization
from the representation's normalization, zero test, leading coefficient, and scaling operations; it is
definitionally the established dense `cmonic` and runs through the sparse engine. Consequently
`allResiduesConstantLrt` and `AllResiduesConstantLrt` inspect `LrtResult α P` directly, without a second
sparse guard implementation.
The radical-extension degree-lowering leaves are split at their real representation boundary. The Case-3
cofactor/residual, generalized log-monomial cofactor, and exponential constant cofactor are generic over
`CPolyEngine` and execute on sparse polynomials. Case 1/2 and the exponential residual remain dense because
they still consume the dense Euclidean/Diophantine algorithms; no generic wrapper hides that dependency.
The algebraic residue norm `(cD' − g₀)² − g₁²ρ` and its denotation theorem are representation-independent
as well, with sparse execution coverage. The surrounding resultant/interpolation and residue-division
checks remain dense at their actual solver dependencies instead of duplicating those algorithms.
Three more algebraic construction leaves now share the engine interface: `zDderMinus` injects the
node-dependent constant before the dense double-resultant stage, `afRatMonomials` scales a supplied basis,
and `radCase3CofactorTower` computes the leading cofactor through a representation-generic derivative
callback. Each runs sparsely; their downstream resultant, linear-solve, and recursive drivers stay dense.
The rational candidate sweep had no polynomial dependency at all: `cRat` and
`defaultResidueCandidates` now live in the symbolic-integration namespace instead of under `DensePoly`.
The misleading qualified declarations were removed rather than retained as compatibility duplicates.
The ordinary result-level residue-constancy predicate now mirrors the LRT one:
`AllResiduesConstant` accepts `IntegralResult α P` and checks only its scalar coefficients, with a sparse
result example. The dense semantic `IsIntegralResult` predicate remains dense because its field denotation
still consumes the dense tower implementation.

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
- **`cdivmod p q = (Q, R)`** — **fuel-less** Euclidean division over a computable field
  (`:= cdivmodCore (cdeg p + 1) p q`; the fuel-threaded core `cdivmodCore` is internal, no well-founded
  recursion — see `docs/fuelless-cdivmod-migration.md`). The **division identity**
  `toPoly p = toPoly q · toPoly Q + toPoly R` holds at *every* fuel on the core (pure algebra + induction,
  no degree argument) and specialises to `toPoly_cdivmod`.
- **Termination** (`PolyReprDivisionDegree.lean`) — `degree_reduce_step_lt` (one cancellation step
  strictly lowers `degree`, via `Polynomial.degree_sub_lt` leading-coefficient cancellation), and
  `cdivmod_remainder_reduced` (**hypothesis-free**: the `cdivmod` remainder is zero or of degree
  `< cdeg q` — the Euclidean remainder property; the `cdeg p + 1` fuel discharges the old `> cdeg p`
  bound internally).
- **`cgcd` — a genuine gcd, both directions proven, fuel-less**: `dvd_cgcd` (every common divisor of
  `a,b` divides `cgcd a b`, from the division identity) *and* `cgcd_dvd` (`cgcd a b` divides both `a` and
  `b`, by fuel induction on the remainder-reduced measure — hypothesis-free). `cgcd a b :=
  cgcdCore (cdeg b + 1) a b`.

- **Downstream of the gcd** (`PolyReprDivisionDegree.lean`): `cgcd_isGCD` (the greatest-common-divisor
  universal property, instance-free), `cdivmod_exact` (`q ∣ p ⇒` zero remainder), `toPoly_mul_cdiv_of_dvd`
  (`q ∣ p ⇒ p = q·(p/q)`, the cofactor factorization), `cmonic` monic normalization
  (`cmonic_monic`), the **squarefree part** `csquarefreePart p = p / gcd(p, p')` with its cofactor
  factorization `toPoly_squarefree_factor : p = gcd(p, p') · squarefreePart p` (the Risch/integration
  entry point; genuine squarefree-ness of the quotient is the remaining frontier), and the degree API
  `cdeg_cmul`/`cdeg_cpow`.
- **Extended Euclidean & coprimality** (`PolyReprDivision.lean`): fuel-less `cgcdExt a b = (g, s, t)`
  (`:= cgcdExtCore (cdeg b + 1) a b`) with the **Bézout identity** `toPoly_cgcdExt : s·a + t·b = g` (at
  every fuel on the core, from the division identity), and `isCoprime_of_cgcdExt_isUnit` (unit gcd ⇒
  Mathlib `IsCoprime`) — the partial-fractions entry point.
- **Adopting the fuel-less engine downstream** — new generic algorithms built *on* the fuel-less
  `cgcdExt`/`cdivmod`: `cdiophantine a b c` solves `s·a + t·b = c` when `gcd(a,b) ∣ c`
  (`toPoly_cdiophantine`, scaling the Bézout pair by the exact quotient `c/g`), and
  `GFrac.reduce` normalises a fraction to lowest terms (num/den ÷ their gcd) with
  `toRatFunc_reduce` (value-preserving). Both `native_decide`-validated, purely additive.
- **Evaluation** (`PolyReprDenote.lean`): `ceval` with `toR_ceval` (= Mathlib `eval`), the ring-hom
  squares `toR_ceval_add`/`toR_ceval_mul`, and the factor theorem `ceval_eq_zero_iff_dvd`.
- **Resultant** (`PolyReprResultant.lean`, COMPLETE): `clistDetn` (computable cofactor determinant over
  `CCommRing`) with the bridge `toR_clistDetn` (= Mathlib `listDetn`, hence `Matrix.det` via
  `ListDet.listDetn_eq_det`); the Sylvester matrix `cSylvester`, `cResultant` = its `clistDetn`, and
  `cResultantDeriv p = cResultant p p'` (repeated-factor detector), `native_decide`-validated
  (`res(x−1,x−2)=−1`, `res(x²−1,x−1)=0`). The **abstract bridge** `toR_cResultant : toR (cResultant p q) =
  Polynomial.resultant (toPoly p) (toPoly q) (cdeg p) (cdeg q)` is proven: `cResultant` → `toR_clistDetn`
  → `listDetn_eq_det` (well-formedness `cSylvester_length`/`_row_length`) → `matrixOfList_cSylvester` (a
  `Matrix.ext`: the `getD`-of-`range·map` chain reduces, then a `Fin.addCases` induction matches
  `cSylvester`'s two blocks to `Polynomial.sylvester`'s exactly — no permutation — via `coeff_toPoly` +
  `Set.Icc`↔`∧`) → `Polynomial.resultant`. So `cResultant` is native_decide-executable *and* a-priori
  correct against Mathlib. Linked to the gcd subsystem by `isCoprime_of_cResultant_ne_zero`
  (`PolyReprResultantCoprime.lean`): a nonzero computable resultant of not-both-zero `p, q` certifies
  `IsCoprime (toPoly p) (toPoly q)` (via the bridge + Mathlib `resultant_eq_zero_iff`).

Each computable op reduces under `native_decide` on both the dense `List` and sparse `SparsePoly`
carriers — the same algorithm, two representations — and the algebraic correctness is a-priori (not merely
`native_decide`-validated). This is a complete, representation-independent polynomial Euclidean-domain
theory (arithmetic · derivative · division · gcd · monic · squarefree part) built bottom-up on the
interface — the constructive answer to the engine-migration impasse.

## Risks

- **Efficiency of `native_decide`.** The dense-list ops today use tight `List` recursion; the generic
  `ofFn (…) (fun i => …)` iterates `0..degBound`. For the small `native_decide` examples this is fine
  (validated), but the dense `List` instance can still provide *optimized* `cadd`/`cmul` overrides
  (interface = default, instance may specialize) if a benchmark regresses.
- **Exact-degree search** needs `[DecidableEq α]`/`isZero` — already available via `CCommRing.isZero`.
- **Scale.** Step 4 (migrating the whole engine + its ~hundreds of correctness lemmas) is the bulk and is
  genuinely multi-session; steps 1–3 are the foundation and can land first.
