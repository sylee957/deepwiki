# The subresultant exactness discharge

**GOAL — DONE 2026-07-21**: `ReducedExact 1 f g` is discharged unconditionally (∀ `f g` over
any computable Euclidean domain of coefficients), so `resultantPRSReduced` has the
hypothesis-free `resultantPRSReduced_eq` and is registered as a `DensePolyResultant`
instance at priority 250 — completing the fraction-free resultant family with the theorem
Brown–Traub state as *"the right hand side of (34) is exactly divisible by βᵢ"*, and closing
the frontier the old engine documented as its "LRT grounding". Axiom-clean
(`propext`/`Classical.choice`/`Quot.sound`).

## How it was closed: the α-divisibility ledger (NOT the global telescope)

The originally planned proof was BT §6's global telescope (track every element back to the
original pair, where eq.-37 ρ-integrality is visible). That was never needed. The finding
"no two-step-local shortcut exists" was about extracting divisibility from the *single*
carried element; the fix is to strengthen the induction hypothesis instead — a **local
invariant carrying all lower-index subresultants of the current pair**:

> `SubresLedger α f g` : `α ≠ 0` and for every `j < deg g`,
> `C (α^{deg g − j})` factors out of the determinantal `S_j(tf, tg)`.

- **Entry** (`subresLedger_one`): trivial at `α = 1`.
- **Head** = `ReducedExact`'s exact division: ledger at `j = deg g − 1` + brick one
  `subresultant_eq_pseudoMod` (`S_{deg g−1} = (−1)^{δ+1} · prem`), sign squared away.
- **Swap** (`SubresLedger.swap`): `subresultant_swap`, splitting
  `α^{deg g−j} = α^{(deg f−j)} · α^{(deg g−deg f)}`.
- **Step** (`SubresLedger.step`): `subresultant_prs_step` at the bridged pseudo-division
  relation; cancel `C(α^{b−j})` then `C(lc^{a−c})` in the domain; the exponent identity
  `(a−b+1)(b−j) = (a−c) + [(a−b+1)(c−j) + (a−b)(b−c−1)]` is BT eq.-37 nonnegativity
  localized (the slack `(a−b)(b−c−1) ≥ 0` is exactly the ρ-integrality exponent). Proven by
  decomposing `j < c < b ≤ a` into `Nat.le.dest` witnesses (ℕ-subtraction leaves; `ring`).
- **Discharge** (`reducedExact_of_ledger`): WF-recursion on the descent's own measure
  `f.size + 2·g.size`; `reducedExact_all := reducedExact_of_ledger ∘ subresLedger_one`.

All in `DeepWiki/CAlgebra/Resultant/Subresultant.lean`; the step/swap lemmas consume the
migrated `DeepWiki/Algebra/SubresultantSpec.lean` one-step transfer lemmas
(`subresultant_prs_step`, `subresultant_swap` = BT (21)–(24)). The chain-level
`SubresultantPRS/{Telescope,Remainder,ClosedForms}` machinery was **not needed** for this
discharge (it remains the home of the closed forms and the old engine's chains).

## Final state (post-discharge)

- `resultantPRSReduced` (Collins' reduced PRS, verified against Brown–Traub (33)/(35)):
  unchecked coefficient-wise divisions, **proven exact**; `resultantPRSReduced_eq`
  hypothesis-free; instance `reducedDensePolyResultant` at priority 250.
- Bench (degree-8 bivariate LRT pair, 5 reps): primitive 148ms < reduced 460ms ≪ Euclidean
  ~49s — priorities 300/250/200 confirmed; dispatch still selects primitive.
- The hypothesis-carrying forms (`resultantPRSReduced_eq_of_invariant`, `…_of_exact`) remain
  as the generic descent API.

## Possible follow-ups (not scheduled)

- The TRUE subresultant-PRS β-variant (BT (38)–(41), old engine's `subresPRS.go`) needs
  Brown '78 ψ-integrality — a separate arc if ever wanted as a resultant instance.
- Switch old-engine conditional-hypothesis instantiations to consume `reducedExact_all`-style
  discharged facts where they still carry chain hypotheses.

## Gotchas learned (kept for reuse)

- `deg`-vs-`size` bridging: `natDegree_toPolynomial_eq_size_sub_one` (unconditional);
  `size_eq_natDegree_add_one` needs nonzero.
- ℕ exponent identities with products are out of omega's fragment: decompose the strict
  chain via `Nat.le.dest` (`obtain ⟨u, hu⟩`), rewrite each subtraction to a witness with
  per-equation `omega` haves, close with `ring`. (`subst` on `b + u = a` fails — not `x = t`
  shaped; the rewrite-list route avoids it.)
- WF-def unfolding in unification is the recurring timeout: pass lambdas explicitly, `set`
  mapped lists whose functions contain `EuclideanDomain.gcd`/WF-defs.
- Old-engine mirrors (`goStep`-layer) keep the state 4-tuple with the first-step flag; keep
  `subresPRS.go` and `goStep` in definitional lockstep or `go_step_state`'s `rfl` breaks.
- The catalog worked examples (`SubresultantExample241`, `SubresultantExercise22`) pin
  `goState` spellings — update the `show`-lines when the state shape changes.
