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

end DeepWiki.ReactiveSystems
