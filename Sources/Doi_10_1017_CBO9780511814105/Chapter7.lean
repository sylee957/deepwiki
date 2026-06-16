import DeepWiki.ReactiveSystems.MutualExclusion
import DeepWiki.ReactiveSystems.Peterson
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

/-! ## §7 Peterson's algorithm in CCS -/

/-- **§7** (pp.144–146). The defining environment for Peterson's algorithm:
boolean variables `b1`, `b2` and the integer `k` as register processes
(`B1f`/`B1t`, `B2f`/`B2t`, `K1`/`K2`), and the two protocol processes
(`P1`/`P11`/`P12`, `P2`/`P21`/`P22`). The library's `petDefn`. -/
abbrev petDefn := @DeepWiki.ReactiveSystems.petDefn

/-- **§7** (p.146). Peterson's algorithm as a CCS process,
`(P₁ | P₂ | B1f | B2f | K1) \ L` (with `k` initially `1`). The library's
`peterson`. -/
abbrev peterson := @DeepWiki.ReactiveSystems.peterson

/-- **§7.2** (7.1, p.149). The CCS specification of mutual exclusion,
`MutexSpec = enter₁.exit₁.MutexSpec + enter₂.exit₂.MutexSpec`. The library's
`mutexSpec`. (As §7.2 notes, `peterson` is *not* observationally equivalent to
`mutexSpec` — the right correctness statement is the §7.1 mutual-exclusion
invariant, checked externally with the CWB; the system has 69 states.) -/
abbrev def_7_1 := @DeepWiki.ReactiveSystems.mutexSpec

/-! **§7.3 Testing mutual exclusion** (p.152) develops a testing methodology over
the same `peterson` model; the testing equivalence is not catalogued here. -/

end DeepWiki.Rs
