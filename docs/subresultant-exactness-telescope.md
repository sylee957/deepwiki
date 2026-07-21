# The subresultant exactness telescope

**GOAL**: discharge `ReducedExact 1 f g` unconditionally (∀ `f g` over any computable
Euclidean domain of coefficients), so `resultantPRSReduced` gets an unconditional
`resultant_eq` and registers as a `DensePolyResultant` instance — completing the
fraction-free resultant family with the theorem Brown–Traub state as *"the right hand side
of (34) is exactly divisible by βᵢ"*, and closing the frontier the old engine documented as
its "LRT grounding".

## Where everything lives (2026-07-21, post `511f0109`)

- `DeepWiki/CAlgebra/Resultant/Subresultant.lean` — `cleanReduced` (Collins' reduced PRS,
  verified against Brown–Traub (33)/(35): carried divisor `lc(right)^{δ+1}`, first step 1),
  `resultantPRSReduced`, **`ReducedExact`** (the WF-recursive target Prop; measure
  `f.size + 2·g.size`), `resultantPRSReduced_eq_of_exact` (projections; done),
  brick one **`subresultant_eq_pseudoMod`** (first pseudo-remainder `= (−1)^{δ+1}·S_{deg g−1}`,
  = BT Lemma 1 (15); done), `exact_div_of_toPolynomial_C_mul` (done).
- `DeepWiki/CAlgebra/Resultant/Euclidean.lean` — the state-threaded `resultantDescent` +
  `resultantDescent_eq_of_invariant` (guarded obligations; done), `pseudo_identity`,
  `pseudoDiv_natDegree_le` (public bridges).
- `DeepWiki/Algebra/SubresultantSpec.lean` — determinantal `subresultant A B n m j`;
  **the exact-constant one-step transfer lemmas** (= BT (21)–(24), generic
  `[CommRing R] [IsDomain R]`): `subresultant_prs_step` (j < c),
  `subresultant_prs_step_top` (j = b−1), `subresultant_prs_step_deg` (j = c),
  `subresultant_prs_step_gap` (vanishing), `subresultant_C_mul`/`prs_unscale` (scaling),
  `subresultant_padding`.
- `DeepWiki/Algebra/SubresultantPRS/{Telescope,Remainder,ClosedForms}.lean` — chain-level:
  `subresultant_eq_pseudoRem` (exact single step), `subresultant_prs_normal_eq` (normal-chain
  closed form — stated in EXACTLY the reduced normalization), `subresultant_prs_closed_top`
  (general closed form with α/β-products), `beta_fold`, `lc_collapse_defective`,
  `subresPRS_gamma_ne_zero` (defective-collapse machinery).
- Paper: Brown–Traub 1971 in `references/10.1145:321662.321665` (OCR-verified this arc);
  catalog `Sources/Doi_10_1145_321662_321665/`. Reduced PRS = Collins 1967
  (`references/collins.pdf`, catalog `Doi_10_1145_321371_321381`).

## Why no shortcut exists (established)

A two-step-local divisibility argument fails: `subresultant_prs_step` puts the carried
α-power against the *product* `C(lc f^{a−c})·C(α_prev^{δ+1})·S_j(f,g)`, and extracting the
factor needs cancellation knowledge that only materializes after telescoping to the
**original pair**, where BT §6's ρ-integrality (eq. 37) is visible by inspection: for the
reduced α/β-choice every exponent is `δ(δ−1) ≥ 0`. The discharge must run the telescope.

## The induction (BT §6, Lean shape)

Strong induction along the descent, carrying the chain-with-history invariant:

> after ℓ exact steps from the original pair `(A, B)`, each computed element equals
> `C ρ · S_j(tA, tB)` for a **tracked, integral** constant ρ (the eq.-37 product) at its
> own-degree index `j`, and the pending divisor α is the eq.-35 value;

then the next pseudo-remainder equals `C αₗ · (±S_{j'}(tA, tB))` by the closed form — an
integral polynomial times the exact carried divisor — so the division is exact and the
invariant extends.

## Phases (each gate-green; commit per phase after review)

1. **Chain-with-history invariant.** `SubresChainInv (A B : DensePoly S) (ℓ) (α f g)`:
   `tf = C ρ₁ · S_{deg f}(tA,tB)`, `tg = C ρ₂ · S_{deg g}(tA,tB)` (with the boundary cases
   `f = A`, `g = B` for ℓ = 0, 1), α the tracked eq.-35 divisor, plus the ρ-product ledger.
   Prove `ReducedExact`-entry reduction: `(∀ ℓ-invariant facts) → ReducedExact 1 A B` shape.
2. **Step transfer.** One descent step under the invariant: instantiate
   `subresultant_prs_step`/`_top`/`_deg` at the current relation
   `C(lc f^{δ+1})·tf = C α·tg' + tg·tQ`, telescope the constants, produce the next
   invariant. Normal steps only need `_top`; defective steps produce the gap/deg cases.
3. **Normal stratum.** All δ = 1: ρ = ±1 (`subresultant_prs_normal_eq` applies directly);
   complete `ReducedExact` for inputs whose descent is normal — checkpoint theorem.
4. **Defective collapse.** The general ρ-ledger via `beta_fold`/`lc_collapse_defective`:
   prove eq.-37 integrality (`ρ ∈ S` — nonneg exponents) and the extension step for δ ≥ 2,
   including the `S_j = 0` gap indices (`subresultant_prs_step_gap`).
5. **Discharge + instance.** `reducedExact_all : ∀ f g, ReducedExact 1 f g`;
   `resultantPRSReduced_eq` unconditional; register
   `instance (priority := 250) reducedDensePolyResultant` (between primitive 300 and
   Euclidean 200 — bench was 153ms/496ms/49.4s on the degree-8 bivariate pair; re-bench);
   cross-check Bronstein Ex 2.4.1 + LRT regressions; consider switching the old engine's
   conditional-hypothesis instantiations to consume the discharged facts.

## Gotchas already learned (do not relearn)

- `deg`-vs-`size` bridging: `natDegree_toPolynomial_eq_size_sub_one` (unconditional);
  `size_eq_natDegree_add_one` needs nonzero.
- The descent's mod steps are always size-ordered after the entry swap; `ReducedExact`'s
  swap clause fires at most once (measure `f.size + 2·g.size` covers it).
- WF-def unfolding in unification is the recurring timeout: pass lambdas explicitly, `set`
  mapped lists whose functions contain `EuclideanDomain.gcd`/WF-defs.
- Old-engine mirrors (`goStep`-layer) keep the state 4-tuple type `… × ℕ` with the slot as
  the first-step flag; keep `subresPRS.go` and `goStep` in definitional lockstep or
  `go_step_state`'s `rfl` breaks.
- The catalog worked examples (`SubresultantExample241`, `SubresultantExercise22`) pin
  `goState` spellings — update the `show`-lines when the state shape changes; native_decide
  re-adjudicates the mathematical facts.
