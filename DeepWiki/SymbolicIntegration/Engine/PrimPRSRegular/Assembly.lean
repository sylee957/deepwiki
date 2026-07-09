import DeepWiki.SymbolicIntegration.Engine.PrimPRSRegular.Content
import DeepWiki.SymbolicIntegration.Engine.PrimPRSRegular.Degree

/-! # Primitive PRS regularity assembly

The regularity gate follows from PRS termination, gcd correctness, and transparent fuel bookkeeping.
-/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open CPoly GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

/-! ## The reduction theorem: regularity + correctness + bookkeeping ⟹ `CPrimPRSGenAssocReg` -/

/-- **Per-step content-strip bookkeeping** `CPrimPRSGenFuelOk fuel P Q`: at each primitive-PRS node, every
`t`-coefficient entering `gbprimitivePartCore` has `cnorm`-length at most `30`, mirroring the
`cprimPRSgcdGenCore` recursion so it threads alongside `CPrimPRSGenRegular`. -/
def CPrimPRSGenFuelOk (cgcdB : CPoly β → CPoly β → CPoly β) :
    ℕ → GBPolyCore β → GBPolyCore β → Prop
  | 0, P, _ => ∀ a ∈ gbnormCore P, (CPoly.cnorm a : List β).length ≤ 30
  | fuel + 1, P, Q =>
    if gbisZeroCore (gbnormCore Q) = true then
      ∀ a ∈ gbnormCore (gbnormCore P), (CPoly.cnorm a : List β).length ≤ 30
    else
      (∀ a ∈ gbnormCore (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q)),
          (CPoly.cnorm a : List β).length ≤ 30)
        ∧ CPrimPRSGenFuelOk cgcdB fuel (gbnormCore Q)
            (gbprimitivePartCore cgcdB (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q)))

/-- **The reduction theorem** `CPrimPRSGenAssocReg` from PRS termination and gcd-correctness: given
`CPrimPRSGenRegular cgcdB fuel P Q`, `CgcdBCorrect cgcdB`, and `CPrimPRSGenFuelOk cgcdB fuel P Q`, the
per-step regularity bundle `CPrimPRSGenAssocReg cgcdB fuel P Q` holds. -/
theorem cPrimPRSGenAssocReg_of_regular_of_correct (cgcdB : CPoly β → CPoly β → CPoly β)
    (hcorr : CgcdBCorrect cgcdB) :
    ∀ (fuel : ℕ) (P Q : GBPolyCore β), CPrimPRSGenRegular cgcdB fuel P Q →
      CPrimPRSGenFuelOk cgcdB fuel P Q → CPrimPRSGenAssocReg cgcdB fuel P Q := by
  intro fuel
  induction fuel with
  | zero =>
    intro P Q hreg hfuel
    -- at fuel 0, CPrimPRSGenRegular must be a `stop` node (the `step` ctor needs `fuel+1`)
    rw [CPrimPRSGenAssocReg]
    refine ⟨?_, ?_⟩
    · -- clause (i): the `stop`-node gives `gbisZeroCore (gbnormCore Q) = true`; reduce to `gbisZeroCore Q`
      cases hreg with
      | stop hz => rw [gbisZeroCore, ← gbnormCore_idemp, ← gbisZeroCore]; exact hz
    · -- clause (iii) on `P` (terminal strip): total content scaling
      rw [CPrimPRSGenFuelOk] at hfuel
      exact associated_toGBPolyG_gbprimitivePartCore_total 30 cgcdB hcorr P hfuel
  | succ fuel ih =>
    intro P Q hreg hfuel
    rw [CPrimPRSGenAssocReg]
    cases hreg with
    | stop hz =>
      -- terminal: left disjunct (Q normalizes to zero) + clause (iii) on `gbnormCore P`
      refine Or.inl ⟨hz, ?_⟩
      rw [CPrimPRSGenFuelOk, if_pos hz] at hfuel
      have h := associated_toGBPolyG_gbprimitivePartCore_total 30 cgcdB hcorr (gbnormCore P) hfuel
      rwa [toGBPolyG_gbnormCore] at h
    | step hz hguard hrec =>
      -- recursive node: right disjunct
      rw [CPrimPRSGenFuelOk, if_neg (by rw [hz]; simp)] at hfuel
      obtain ⟨hfuelPrem, hfuelRec⟩ := hfuel
      refine Or.inr ⟨by rw [hz]; simp, ?_, ?_, ?_⟩
      · -- clause (ii): the nonzero-multiplier pseudo-division witness
        obtain ⟨s, c, hrel, hc0⟩ := toGBPolyG_gbpsremainderCore_ne_zero 60 (gbnormCore P)
          (gbnormCore Q) (by rw [gbnormCore_idemp]; exact hz)
        exact ⟨s, c, hrel, hc0⟩
      · -- clause (iii): the total content strip on `prem`
        exact associated_toGBPolyG_gbprimitivePartCore_total 30 cgcdB hcorr
          (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q)) hfuelPrem
      · -- the tower recursion: regularity ∧ fuel ⟹ AssocReg one level down
        exact ih (gbnormCore Q) _ hrec hfuelRec

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- The per-step regularity gate follows from PRS termination, level-β gcd-correctness, and transparent fuel.
example (cgcdB : CPoly β → CPoly β → CPoly β) (hcorr : CgcdBCorrect cgcdB)
    (fuel : ℕ) (P Q : GBPolyCore β) (hreg : CPrimPRSGenRegular cgcdB fuel P Q)
    (hfuel : CPrimPRSGenFuelOk cgcdB fuel P Q) : CPrimPRSGenAssocReg cgcdB fuel P Q :=
  cPrimPRSGenAssocReg_of_regular_of_correct cgcdB hcorr fuel P Q hreg hfuel

-- The list-length WF guard is the polynomial `t`-degree.
example (p : GBPolyCore β) : gbdegCore p = (toGBCoeffPoly p).natDegree := gbdegCore_eq_natDegree p

-- Clause (ii) with the β(s)-unit multiplier is unconditional given the non-terminal loop guard.
example (fuel : ℕ) (p q : GBPolyCore β) (hq : gbisZeroCore (gbnormCore q) = false) :
    ∃ (s : GBPolyCore β) (c : CPoly β),
      Polynomial.C (QFunNZG.amG β (CPoly.toPoly c)) * toGBPolyG p
          = toGBPolyG s * toGBPolyG q + toGBPolyG (gbpsremainderCore fuel p q)
        ∧ QFunNZG.amG β (CPoly.toPoly c) ≠ 0 :=
  toGBPolyG_gbpsremainderCore_ne_zero fuel p q hq

-- The single pseudo-division step strictly drops the `t`-degree by leading-term cancellation.
example (p q : GBPolyCore β) (hp : gbisZeroCore (gbnormCore p) = false)
    (hq : gbisZeroCore (gbnormCore q) = false)
    (hdeg : (toGBCoeffPoly q).natDegree ≤ (toGBCoeffPoly p).natDegree)
    (hstepne : toGBCoeffPoly (gbStepReduce p q) ≠ 0) :
    (toGBCoeffPoly (gbStepReduce p q)).natDegree < (toGBCoeffPoly p).natDegree :=
  natDegree_gbStepReduce_lt p q hp hq hdeg hstepne

-- The inner pseudo-division loop completes under the explicit fuel bound `deg_t p < fuel`.
example (q : GBPolyCore β) (hq : gbisZeroCore (gbnormCore q) = false)
    (fuel : ℕ) (p : GBPolyCore β) (hlt : (toGBCoeffPoly p).natDegree < fuel) :
    (toGBCoeffPoly (gbpsremainderCore fuel p q)).natDegree < (toGBCoeffPoly q).natDegree
      ∨ toGBCoeffPoly (gbpsremainderCore fuel p q) = 0 :=
  gbpsremainderCore_degree_lt q hq fuel p hlt

/-! ## Summary

`CPrimPRSGenAssocReg cgcdB fuel P Q` is equivalent (given the bookkeeping `CPrimPRSGenFuelOk`) to two
per-run witnesses: PRS termination `CPrimPRSGenRegular` and level-`β` gcd-correctness `CgcdBCorrect`.
The degree-drop content of termination is a theorem (`natDegree_gbStepReduce_lt`,
`gbpsremainderCore_degree_lt`), leaving only a satisfiable numeric fuel bound. -/

end DeepWiki.SymbolicIntegration
