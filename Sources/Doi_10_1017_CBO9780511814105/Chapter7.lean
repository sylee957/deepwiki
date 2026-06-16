import DeepWiki.ReactiveSystems.MutualExclusion
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 7: Modelling mutual exclusion algorithms
Book-numbered restatements for Chapter 7. §7.1 (specifying mutual exclusion in
HML) is discharged by the `DeepWiki.ReactiveSystems` library as an invariant
property; §7.2 (Peterson's algorithm in CCS) and §7.3 (testing) are concrete
modelling developments and are noted but not catalogued as single declarations. -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems
open DeepWiki.ReactiveSystems.LTS

variable {Proc Act : Type*}

/-! ## §7.1 Specifying mutual exclusion in HML -/

/-- **§7.1** (p.147). "Process `i` is in its critical section" is observed as the
exit action `eᵢ` being enabled. The library's `LTS.CanDo`. -/
abbrev canDo := @LTS.CanDo

/-- **§7.1** (p.147). The mutual-exclusion safety formula `[e₁]ff ∨ [e₂]ff`. The
library's `LTS.mutexFormula`. -/
abbrev mutexFormula := @LTS.mutexFormula

/-- **§7.1** (p.147). The mutual-exclusion property `Inv([e₁]ff ∨ [e₂]ff)`. The
library's `LTS.MutEx`. -/
abbrev mutEx := @LTS.MutEx

/-- **§7.1** (p.147). Mutual exclusion, specified as an invariant, is equivalent
to the reachability statement that no reachable state has both critical sections
available — the formal correctness criterion for the algorithms in this chapter.
(A direct application of Theorem 6.1.) -/
theorem mutex_spec (L : LTS Proc Act) (e1 e2 : Act) (p : Proc) :
    p ∈ LTS.MutEx L e1 e2 ↔ ∀ q, L.Reachable p q → ¬ (LTS.CanDo L e1 q ∧ LTS.CanDo L e2 q) :=
  LTS.mem_MutEx L e1 e2 p

/-- **§7.1** (p.147). A state with the mutual-exclusion property is itself safe:
the two processes are not both in their critical sections. -/
theorem mutex_safe (L : LTS Proc Act) {e1 e2 : Act} {p : Proc} (h : p ∈ LTS.MutEx L e1 e2) :
    ¬ (LTS.CanDo L e1 p ∧ LTS.CanDo L e2 p) := LTS.MutEx_safe L h

/-! **§7.2 Specifying mutual exclusion using CCS** (p.149) and **§7.3 Testing
mutual exclusion** (p.152) develop Peterson's algorithm as a concrete CCS process
(boolean-variable processes `B₁ⁱ`, `B₂ⁱ`, `Kⁱ` and the protocol `P₁`, `P₂`) and a
testing methodology. These are concrete model constructions over the `Ccs` /
`ServersBacklog`-style machinery rather than general theorems, and are not
catalogued here as single declarations. -/

end DeepWiki.Rs
