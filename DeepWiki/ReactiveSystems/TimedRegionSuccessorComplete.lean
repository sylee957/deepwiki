import DeepWiki.ReactiveSystems.SymbolicModelCheckingExecutableFull
import DeepWiki.ReactiveSystems.TimedRegionSuccessorSound

/-! # Completeness of the constructive region time-successor (Alur–Dill §4.3)
The constructive Alur–Dill delay-successor enumerator `regionCodeDelaySucc` (the finite
elapse orbit) satisfies the **completeness** obligation `SuccComplete`: every region reachable
from a valuation by *some* delay is listed. This discharges the deep half of the region
construction; together with `SuccSound` it would make the conditional full executable model
checker `SymSatCodeFull` unconditional. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- **`regionCodeDelaySucc` is complete.** Every region a valuation reaches after a delay is
in the listed orbit — the `SuccComplete` obligation, discharged by the generic orbit
reachability theorem `fp_add_mem_regionCodeDelaySucc` (instantiated at the clock type
`C ⊕ D`). -/
theorem succComplete_regionCodeDelaySucc {C D : Type*} [Fintype C] [Fintype D]
    [DecidableEq C] [DecidableEq D] {cmax : C ⊕ D → ℕ} :
    SuccComplete (cmax := cmax) regionCodeDelaySucc :=
  fun w t => fp_add_mem_regionCodeDelaySucc w t

-- Faithfulness: `SuccComplete` unfolds to "every delayed region is enumerated".
example {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]
    {cmax : C ⊕ D → ℕ} (w : Valuation (C ⊕ D)) (t : ℝ≥0) :
    regionFingerprint cmax (w.add t) ∈ regionCodeDelaySucc (regionFingerprint cmax w) :=
  succComplete_regionCodeDelaySucc w t

/-- **`regionCodeDelaySucc` is sound.** Every region it lists for `⟦w⟧` is `fp (w + t)` for
some delay `t` — the `SuccSound` obligation, discharged by `mem_regionCodeDelaySucc_imp_add`. -/
theorem succSound_regionCodeDelaySucc {C D : Type*} [Fintype C] [Fintype D]
    [DecidableEq C] [DecidableEq D] {cmax : C ⊕ D → ℕ} :
    SuccSound (cmax := cmax) regionCodeDelaySucc :=
  fun w γ' h => mem_regionCodeDelaySucc_imp_add w γ' h

/-- **Unconditional executable full model checking (Alur–Dill).** For a finite timed automaton
`A` and *any* timed formula `F`, `A ⊨ F` iff the full Bool decision `SymSatCodeFull` — using the
constructive region successor `regionCodeDelaySucc` — is `true` on the initial region code. This
removes the soundness/completeness hypotheses of `satisfiesMt_iff_decideFull`: the Alur–Dill
delay-successor is now *proved* sound and complete, so the full timed logic has a genuine,
self-contained decision procedure. -/
theorem satisfiesMt_iff_decideFull_delaySucc {Loc Act C D : Type*}
    [DecidableEq Loc] [DecidableEq Act] [DecidableEq C] [DecidableEq D]
    [Fintype Loc] [Fintype C] [Fintype D]
    (A : FinAutomaton Loc Act C) (F : Mt Act D) :
    A.toTimedAutomaton.SatisfiesMt F
      ↔ SymSatCodeFull A (cmax := Sum.elim A.cmax F.formulaCmax) regionCodeDelaySucc
          A.initial (RegionCode.initial _) F = true :=
  satisfiesMt_iff_decideFull A F regionCodeDelaySucc
    (succSound_regionCodeDelaySucc (cmax := Sum.elim A.cmax F.formulaCmax))
    (succComplete_regionCodeDelaySucc (cmax := Sum.elim A.cmax F.formulaCmax))

end DeepWiki.ReactiveSystems
