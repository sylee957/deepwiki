import DeepWiki.SymbolicIntegration.Engine.PrimPRSRegular.Content
import DeepWiki.SymbolicIntegration.Engine.PrimPRSRegular.Degree

/-! # Primitive PRS regularity assembly

The regularity gate follows from PRS termination, gcd correctness, and transparent fuel bookkeeping.
-/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open DensePoly GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

/-! ## The reduction theorem: regularity + correctness ⟹ `CPrimPRSGenAssocReg` -/

/-- **The reduction theorem** `CPrimPRSGenAssocReg` from PRS termination and gcd-correctness: given
`CPrimPRSGenRegular cgcdB fuel P Q` and `CgcdBCorrect cgcdB`, the per-step regularity bundle
`CPrimPRSGenAssocReg cgcdB fuel P Q` holds. Content stripping needs no artificial coefficient-size bound. -/
theorem cPrimPRSGenAssocReg_of_regular_of_correct (cgcdB : DensePoly β → DensePoly β → DensePoly β)
    (hcorr : CgcdBCorrect cgcdB) :
    ∀ (fuel : ℕ) (P Q : GBPolyCore β), CPrimPRSGenRegular cgcdB fuel P Q →
      CPrimPRSGenAssocReg cgcdB fuel P Q := by
  intro fuel
  induction fuel with
  | zero =>
    intro P Q hreg
    -- at fuel 0, CPrimPRSGenRegular must be a `stop` node (the `step` ctor needs `fuel+1`)
    rw [CPrimPRSGenAssocReg]
    refine ⟨?_, ?_⟩
    · -- clause (i): the `stop`-node gives `DensePoly.cisZero (gbnormCore Q) = true`; reduce to `DensePoly.cisZero Q`
      cases hreg with
      | stop hz => rwa [cisZero_gbnormCore] at hz
    · -- clause (iii) on `P` (terminal strip): total content scaling
      exact associated_toGBPolyG_gbprimitivePartCore_total cgcdB hcorr P
  | succ fuel ih =>
    intro P Q hreg
    rw [CPrimPRSGenAssocReg]
    cases hreg with
    | stop hz =>
      -- terminal: left disjunct (Q normalizes to zero) + clause (iii) on `gbnormCore P`
      refine Or.inl ⟨hz, ?_⟩
      have h := associated_toGBPolyG_gbprimitivePartCore_total cgcdB hcorr (gbnormCore P)
      rwa [toGBPolyG_gbnormCore] at h
    | step hz _ hrec =>
      -- recursive node: right disjunct
      refine Or.inr ⟨by rw [hz]; simp, ?_, ?_, ?_⟩
      · -- clause (ii): the nonzero-multiplier pseudo-division witness
        obtain ⟨s, c, hrel, hc0⟩ := toGBPolyG_gbpsremainderCore_ne_zero (gbnormCore P).length (gbnormCore P)
          (gbnormCore Q) (by rw [gbnormCore_idemp]; exact hz)
        exact ⟨s, c, hrel, hc0⟩
      · -- clause (iii): the total content strip on `prem`
        exact associated_toGBPolyG_gbprimitivePartCore_total cgcdB hcorr
          (gbpsremainderCore (gbnormCore P).length (gbnormCore P) (gbnormCore Q))
      · -- the tower recursion preserves regularity.
        exact ih (gbnormCore Q) _ hrec

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- The per-step regularity gate follows from PRS termination, level-β gcd-correctness, and transparent fuel.
example (cgcdB : DensePoly β → DensePoly β → DensePoly β) (hcorr : CgcdBCorrect cgcdB)
    (fuel : ℕ) (P Q : GBPolyCore β) (hreg : CPrimPRSGenRegular cgcdB fuel P Q) :
    CPrimPRSGenAssocReg cgcdB fuel P Q :=
  cPrimPRSGenAssocReg_of_regular_of_correct cgcdB hcorr fuel P Q hreg

-- The list-length WF guard is the polynomial `t`-degree.
example (p : GBPolyCore β) : DensePoly.cdeg p = (DensePoly.toPoly p).natDegree := DensePoly.cdegG_eq_natDegree p

-- Clause (ii) with the β(s)-unit multiplier is unconditional given the non-terminal loop guard.
example (fuel : ℕ) (p q : GBPolyCore β) (hq : DensePoly.cisZero (gbnormCore q) = false) :
    ∃ (s : GBPolyCore β) (c : DensePoly β),
      Polynomial.C (CFrac.am β (DensePoly.toPoly c)) * toGBPoly p
          = toGBPoly s * toGBPoly q + toGBPoly (gbpsremainderCore fuel p q)
        ∧ CFrac.am β (DensePoly.toPoly c) ≠ 0 :=
  toGBPolyG_gbpsremainderCore_ne_zero fuel p q hq

-- The single pseudo-division step strictly drops the `t`-degree by leading-term cancellation.
example (p q : GBPolyCore β) (hp : DensePoly.cisZero (gbnormCore p) = false)
    (hq : DensePoly.cisZero (gbnormCore q) = false)
    (hdeg : (DensePoly.toPoly q).natDegree ≤ (DensePoly.toPoly p).natDegree)
    (hstepne : DensePoly.toPoly (gbStepReduce p q) ≠ 0) :
    (DensePoly.toPoly (gbStepReduce p q)).natDegree < (DensePoly.toPoly p).natDegree :=
  natDegree_gbStepReduce_lt p q hp hq hdeg hstepne

-- The inner pseudo-division loop completes under the explicit fuel bound `deg_t p < fuel`.
example (q : GBPolyCore β) (hq : DensePoly.cisZero (gbnormCore q) = false)
    (fuel : ℕ) (p : GBPolyCore β) (hlt : (DensePoly.toPoly p).natDegree < fuel) :
    (DensePoly.toPoly (gbpsremainderCore fuel p q)).natDegree < (DensePoly.toPoly q).natDegree
      ∨ DensePoly.toPoly (gbpsremainderCore fuel p q) = 0 :=
  gbpsremainderCore_degree_lt q hq fuel p hlt

/-! ## Summary

`CPrimPRSGenAssocReg cgcdB fuel P Q` follows from two per-run witnesses: PRS termination
`CPrimPRSGenRegular` and level-`β` gcd-correctness `CgcdBCorrect`.
The degree-drop content of termination is a theorem (`natDegree_gbStepReduce_lt`,
`gbpsremainderCore_degree_lt`), leaving only a satisfiable numeric fuel bound. -/

end DeepWiki.SymbolicIntegration
