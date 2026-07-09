# Subsume the base-vs-tower primitive-case special-part soundness proofs

**Goal.** The primitive-case recursive LRT Risch solver has TWO parallel `LawfulRischLevelLrt` instances —
the base `instLawfulRischLevelLrtPrimitive` (`RischTowerLrt`) and the recursive step
`instLawfulRischLevelLrtTower` (`RischSolverTowerLrt`). Each supplies its `specialSound` via a base-vs-tower
*pair* of near-identical proofs. Subsume each pair into one generic lemma (objective: subsume special into
general). The rest of the tree (decision procedures `reducedDecides`/`not_isElementaryIntegrable_reduced` are
already thin wrappers over `primitiveLrtDecides_of_setup`; `soundFormalLrt`/`integrateRationalLrt_sound` are
single) needs no change.

## The two parallel pairs (RAG-mapped)

**Pair A — the special *identity*** (`towerFractionFieldDerivG Dt (fieldFrac qp [1]) = fieldFrac fp [1]`):
- `primitive_special_identity` (`PrimitiveGuarded`) — poly antiderivative from `cPolyRischDEGWf` (const-coeff),
  proven via `field_identity_Dt1` + an `fp = 0` case.
- `tower_special_identityLrt` (`RischSolverTowerLrt`) — poly antiderivative from `towerPolyIntegrateLrt`
  (coefficient recursion), proven via `towerFractionFieldDerivG_div` bridge + `rw [hbridge, hDt, hpoly]`.
- **Common core**: given `hDt1 : toPolyG Dt = 1` and `himpl : implicitDeriv (toPolyG Dt) (toPolyG qp) = toPolyG fp`,
  the identity follows by the `towerFractionFieldDerivG_div` bridge (`[1]' = 0`) + `rw himpl`.

**Pair B — the special *soundness*** (the `specialSound` field: `toPolyG sden ≠ 0 ∧ ∃ v, D(fieldFrac snum sden)
= v ∧ v + fieldFrac crNorm = fieldFrac a d`):
- `primitiveGuardedCase_specialSound` (`RischTowerPrimitive`) — 3-conjunct guard, `cPolyRischDEGWf`,
  identity via `primitive_special_identity`.
- `towerPrimitiveCaseLrt_specialSound` (`RischSolverTowerLrt`) — 2-conjunct guard, `towerPolyIntegrateLrt`,
  identity via `tower_special_identityLrt`.
- **Common core**: after each proof's guard-extraction + poly-integrate gives `snum = qp`, `sden = [1]`, `hb`
  (`crSpecNum = 0`) and the Pair-A identity `hid`, the conclusion is IDENTICAL:
  `refine ⟨one_ne_zero, fieldFrac (crPoly Dt a d) [1], hid, ?recon⟩` where `?recon` is
  `hvan (crSpec = 0 ⟹ fieldFrac = 0)` + `canonicalReconstruction_of_charZero`.

## Layering (RAG-verified)

`RischSolverTowerLrt` reaches `RischTowerPrimitive` reaches `PrimitiveGuarded` (all upstream), and none reach
back — so the generics live upstream and both callers use them:
- `special_identity_of_polyAntideriv` → **`PrimitiveGuarded`** (has `towerFractionFieldDerivG`,
  `implicitDeriv`, `amG`, `fieldFrac`; `tower_special_identityLrt` reaches it).
- `primitiveSpecialSoundCore` → **`RischTowerPrimitive`** (has `canonicalReconstruction_of_charZero`, the `cr*`
  helpers; `towerPrimitiveCaseLrt_specialSound` reaches it).

## Phases

1. **Pair A generic — REFUTED by spike (2026-07-09).** `cPolyRischDEGWf_nil_field_identity`
   (`OneShotSoundness`) hands the base the *field identity* DIRECTLY — there is no implicitDeriv-form
   soundness for `cPolyRischDEGWf`. So `primitive_special_identity` (field-identity-direct route) and
   `tower_special_identityLrt` (implicitDeriv + `towerFractionFieldDerivG_div` bridge) reach the same
   conclusion via genuinely different proofs; the only shared proof content (the div bridge) has a single
   caller (the tower). No clean subsumption — do NOT force it.
2. **Pair B generic — DO THIS.** Add `primitiveSpecialSoundCore (Dt a d qp) (hd0) (hb) (hid)` to
   `RischTowerPrimitive`. It takes the special identity `hid` as a *hypothesis*, so it is agnostic to how each
   caller proved it (side-stepping the Pair-A obstacle). Refactor both `_specialSound` proofs to end
   `exact primitiveSpecialSoundCore … hid` after their own guard-extraction + poly-integrate. Restate one
   touched theorem as an `example`; delete this plan when done.

## Discipline

- Spike each generic BEFORE committing (it must compile AND both callers must go through green).
- Do NOT weaken correctness — `PrimitiveFrontierLrt`/`GcdFFCorrect`/`LrtLiouvilleFrontier` frontiers untouched.
- The base guard has an extra `cmapDeriv fp = 0` conjunct (the const-coeff condition) — it stays in the base
  `_specialSound`; only the shared *core* after guard-extraction is subsumed.
