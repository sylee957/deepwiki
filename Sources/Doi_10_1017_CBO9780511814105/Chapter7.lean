import DeepWiki.ReactiveSystems.MutualExclusion
import DeepWiki.ReactiveSystems.Peterson
import DeepWiki.ReactiveSystems.SimulationWeak
import DeepWiki.ReactiveSystems.CcsTesting
import DeepWiki.ReactiveSystems.CcsTestingSafety
import DeepWiki.ReactiveSystems.HymanMutualExclusion
import DeepWiki.ReactiveSystems.CcsMutexMonitor
import DeepWiki.ReactiveSystems.Chapter7Examples
import DeepWiki.ReactiveSystems.Chapter7WeakSimCongruence
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

/-- **Exercise 7.3** (§7, p.146). Hyman's (1966) 'mutual exclusion' algorithm as a
CCS process, over the same shared variables as Peterson: `(P₁ | P₂ | B1f | B2f |
K1) \ L`, each `Pᵢ` running `bᵢ:=true; while k≠j do {while bⱼ do skip; k:=i};
critical; bᵢ:=false`. The library's `hyman` (validated by `hyman_tau_writes_b1`).
(Hyman's algorithm is not correct — the safety analysis is Exercise 7.4.) -/
abbrev ex_7_3 := @DeepWiki.ReactiveSystems.hyman

/-- **§7.2** (eq. 7.1, p.149). The CCS specification of mutual exclusion,
`MutexSpec = enter₁.exit₁.MutexSpec + enter₂.exit₂.MutexSpec`. The library's
`mutexSpec`. (This is the displayed equation (7.1), *not* book Definition 7.1.
As §7.2 notes, `peterson` is *not* observationally equivalent to `mutexSpec` —
the right correctness statement is the §7.1 mutual-exclusion invariant, checked
externally with the CWB; the system has 69 states.) -/
abbrev ccsMutexSpec := @DeepWiki.ReactiveSystems.mutexSpec

/-! ## §7.3 Testing mutual exclusion: weak traces and weak simulation -/

/-- **Definition 7.1** (§7.3, p.151). A *weak trace* of a process: a sequence of
visible actions performed via weak transitions (silent steps absorbed). The
library's `LTS.WeakTraces`. -/
abbrev def_7_1 := @LTS.WeakTraces

/-- **Definition 7.1** (§7.3, p.151). *Weak trace equivalence*: equal weak-trace
sets. The library's `LTS.WeakTraceEquiv`. -/
abbrev def_7_1_equiv := @LTS.WeakTraceEquiv

/-- **Definition 7.2** (§7.3, p.152). A *weak simulation* `R`: every concrete move
`s₁ —α→ s₁'` (any `α`, including `τ`) is answered by a weak transition `s₂ =α⇒
s₂'` with `s₁' R s₂'`. The library's `LTS.IsWeakSimulation`. -/
abbrev def_7_2 := @LTS.IsWeakSimulation

/-- **Definition 7.2** (§7.3, p.152). `s'` *weakly simulates* `s`: some weak
simulation relates them. The library's `LTS.WeaklySimulates`. -/
abbrev def_7_2_simulates := @LTS.WeaklySimulates

/-- **Proposition 7.1** (§7.3, p.152). The weak-simulation preorder is reflexive
(1) and transitive (2), and weak simulation preserves weak traces (3): if `s'`
weakly simulates `s`, every weak trace of `s` is a weak trace of `s'`. -/
theorem prop_7_1 (L : LTS Proc Act) (tau : Act) :
    (∀ s, LTS.WeaklySimulates L tau s s) ∧
    (∀ s s' s'', LTS.WeaklySimulates L tau s'' s' → LTS.WeaklySimulates L tau s' s →
      LTS.WeaklySimulates L tau s'' s) ∧
    (∀ s s', LTS.WeaklySimulates L tau s' s →
      LTS.WeakTraces L tau s ⊆ LTS.WeakTraces L tau s') :=
  ⟨LTS.weaklySimulates_refl, fun _ _ _ h1 h2 => h1.trans h2,
   fun _ _ h => h.weakTraces_subset⟩

/-- **§7.3** (weak analogue of "bisimilarity refines trace equivalence").
Observationally equivalent (weakly bisimilar) states are weak trace equivalent:
each weakly simulates the other, so their weak-trace sets coincide. -/
theorem weaklyBisimilar_weakTraceEquiv (L : LTS Proc Act) (tau : Act) {p q : Proc}
    (h : p ≈[L, tau] q) : LTS.WeakTraceEquiv L tau p q :=
  LTS.WeaklyBisimilar.weakTraceEquiv h

/-! ## §7.3 Testing and testable formulae (Definitions 7.3–7.4, Proposition 7.3) -/

/-- **Definition 7.3 / 7.4** (§7.3, p.155). The interaction `(s ∣ T) ∖ L` of a
process with a test, hiding every observable channel except the reject channel
`bad` (a test is a regular CCS process over `Act ∪ {bad}`). The library's
`LTS.interact`. -/
abbrev def_7_3 := @LTS.interact

/-- **Definition 7.4** (§7.3, p.155). `s` *passes* test `T`: the composite cannot
weakly perform the reject action `bad̄`. The library's `LTS.Passes`. -/
abbrev def_7_4 := @LTS.Passes

/-- **§7.3** (p.151). Weak (observational) HML satisfaction `⊨w`, the satisfaction
relevant to testing (`[a]ff` holds of processes affording no weak `=a⇒`
transition, Example 7.1). The library's `LTS.WSat`. -/
abbrev wsat := @LTS.WSat

/-- **Definition 7.4** (§7.3, p.156). `T` *tests for* `F` (so `F` is *testable*):
*weakly* satisfying `F` coincides with passing `T`, for every process. The
library's `LTS.Tests` (over `LTS.WSat`). -/
abbrev def_7_4_tests := @LTS.Tests

/-- **Proposition 7.3(1)** (§7.3, p.157). The formula `⟨a⟩tt` is **not testable**:
no test tests for it (the testing preorder cannot observe existential branching).
Discharged by `LTS.dia_tt_not_testable`. -/
theorem prop_7_3_1 {Name K : Type*} (a bad : Name) (defn : K → CCS Name K)
    (test : CCS Name K)
    (h : LTS.Tests defn bad test (HML.dia (DeepWiki.ReactiveSystems.Act.name a) HML.tt)) :
    False :=
  LTS.dia_tt_not_testable a bad defn test h

/-- **Proposition 7.3(2)** (§7.3, p.157). For distinct actions `a ≠ b`, the
formula `[a]ff ∨ [b]ff` is **not testable** (the testing preorder cannot observe
disjunctive/branching refusal). Discharged by `LTS.boxff_or_not_testable`. -/
theorem prop_7_3_2 {Name K : Type*} (a b bad : Name) (hab : a ≠ b) (defn : K → CCS Name K)
    (test : CCS Name K)
    (h : LTS.Tests defn bad test
      (HML.or (HML.box (DeepWiki.ReactiveSystems.Act.name a) HML.ff)
        (HML.box (DeepWiki.ReactiveSystems.Act.name b) HML.ff))) : False :=
  LTS.boxff_or_not_testable a b bad hab defn test h

/-- **§7.3** (p.157). Recursion-free *safety HML* — `tt`, `ff`, `∧`, `[a]` (no
`∨`, no `⟨a⟩`, no recursion). The library's `LTS.SafetyF`. -/
abbrev safetyHML := @LTS.SafetyF

/-- **Exercise 7.15** (§7.3, p.157). The test built from a safety formula
(`tt ↦ 0`, `ff ↦ bad̄.0`, `∧ ↦ +`, `[a] ↦ ā.·`). The library's `LTS.testOf`. -/
abbrev safetyTestOf := @LTS.testOf

/-- **Theorem 7.1 / Exercise 7.15** (§7.3, p.155–158), recursion-free fragment.
Every recursion-free safety HML formula (with real, non-`bad` actions) is
**testable**: a bad-free process weakly satisfies `F` iff it passes the
constructed test `testOf bad F` — e.g. the test for `[a]ff` is `ā.bad̄.0`
(Example 7.1). Discharged by `LTS.testOf_correct`. (The book's full Theorem 7.1
adds `ν`-recursion and the converse "every testable HML property lies in safety
HML", from Aceto–Ingólfsdóttir 1999 — external.) -/
theorem thm_7_1 {Name K : Type*} (defn : K → CCS Name K) (bad : Name)
    (F : LTS.SafetyF Name) (hF : F.NoBadAction bad) (s : CCS Name K)
    (hbf : LTS.BadFree defn bad s) :
    LTS.WSat (ccsLTS defn) DeepWiki.ReactiveSystems.Act.tau s F.toHML ↔
      LTS.Passes defn bad s (LTS.testOf bad F) :=
  LTS.testOf_correct F hF s hbf

/-! ## §7.3 The mutual-exclusion monitor (Proposition 7.2) -/

/-- **§7.3** (p.153). The monitor process `MutexTest = enter₁.MutexTest₁ +
enter₂.MutexTest₂`, `MutexTestᵢ = exitᵢ.MutexTest + enterⱼ.bad.0`, that observes a
process and emits `bad` on two `enter`s without an intervening `exit`. The
library's `mtDefn`. -/
abbrev mutexTest := @DeepWiki.ReactiveSystems.mtDefn

/-- **§7.3** (p.153). The collection `(enter₁ exit₁ + enter₂ exit₂)*` of
well-matched action sequences. The library's `WellMatched`. -/
abbrev mutexWellMatched := @DeepWiki.ReactiveSystems.WellMatched

/-- **Proposition 7.2** (§7.3, p.153), soundness ("if") direction. If a process
`P` can, after a well-matched run `σ ∈ (enter₁ exit₁ + enter₂ exit₂)*`, perform two
`enter`s in a row (`enter₁` then `enter₂`, or `enter₂` then `enter₁`), then the
monitored system `(P ∣ MutexTest) ∖ L` can perform the reject action `bad`: the
monitor detects every mutual-exclusion violation. Discharged by the library's
`monitored_bad_of_wellMatched_violation`. (The converse — completeness — is the book's Exercise 7.12.) -/
theorem prop_7_2_if {σ : List (DeepWiki.ReactiveSystems.Act DeepWiki.ReactiveSystems.MtChan)}
    {P P₁ P₂ P₃ : CCS DeepWiki.ReactiveSystems.MtChan DeepWiki.ReactiveSystems.MtK}
    (hσ : DeepWiki.ReactiveSystems.WellMatched σ)
    (hpath : LTS.WeakPath (ccsLTS DeepWiki.ReactiveSystems.mtDefn)
      DeepWiki.ReactiveSystems.Act.tau P σ P₁)
    (hviol :
      ((ccsLTS DeepWiki.ReactiveSystems.mtDefn) ⊢ P₁
          =[DeepWiki.ReactiveSystems.Act.coname DeepWiki.ReactiveSystems.MtChan.enter1]⇒[
            DeepWiki.ReactiveSystems.Act.tau] P₂ ∧
        (ccsLTS DeepWiki.ReactiveSystems.mtDefn) ⊢ P₂
          =[DeepWiki.ReactiveSystems.Act.coname DeepWiki.ReactiveSystems.MtChan.enter2]⇒[
            DeepWiki.ReactiveSystems.Act.tau] P₃) ∨
      ((ccsLTS DeepWiki.ReactiveSystems.mtDefn) ⊢ P₁
          =[DeepWiki.ReactiveSystems.Act.coname DeepWiki.ReactiveSystems.MtChan.enter2]⇒[
            DeepWiki.ReactiveSystems.Act.tau] P₂ ∧
        (ccsLTS DeepWiki.ReactiveSystems.mtDefn) ⊢ P₂
          =[DeepWiki.ReactiveSystems.Act.coname DeepWiki.ReactiveSystems.MtChan.enter1]⇒[
            DeepWiki.ReactiveSystems.Act.tau] P₃)) :
    ∃ Q, (ccsLTS DeepWiki.ReactiveSystems.mtDefn) ⊢
      DeepWiki.ReactiveSystems.monitored P DeepWiki.ReactiveSystems.MtK.MutexTest
        =[DeepWiki.ReactiveSystems.Act.name DeepWiki.ReactiveSystems.MtChan.bad]⇒[
          DeepWiki.ReactiveSystems.Act.tau] Q :=
  DeepWiki.ReactiveSystems.monitored_bad_of_wellMatched_violation hσ hpath hviol

/-- **Exercise 7.10** (§7.3, p.152). The weak-simulation preorder is a choice
congruence: if `Q` weakly simulates `P`, then `Q + R` weakly simulates both `P`
and `P + R`, for every CCS process `R`. The library's `weaklySimulates_choiceL`
and `weaklySimulates_choiceLR`. -/
theorem ex_7_10 {Name K : Type*} {defn : K → CCS Name K} {P Q R : CCS Name K}
    (h : LTS.WeaklySimulates (ccsLTS defn) DeepWiki.ReactiveSystems.Act.tau Q P) :
    LTS.WeaklySimulates (ccsLTS defn) DeepWiki.ReactiveSystems.Act.tau (CCS.choice Q R) P ∧
    LTS.WeaklySimulates (ccsLTS defn) DeepWiki.ReactiveSystems.Act.tau
      (CCS.choice Q R) (CCS.choice P R) :=
  ⟨DeepWiki.ReactiveSystems.weaklySimulates_choiceL h,
   DeepWiki.ReactiveSystems.weaklySimulates_choiceLR h⟩

/-- **Exercise 7.13** (§7.2, p.156). On the LTS `p ↺b`, `q —b→ p`, `q —b→ r`,
`q —a→ s`, `r ↺b` (`s` dead), the set of states satisfying the recursive safety
property `F =ν [a]ff ∧ [b]F` is `{p, r, s}`; only `q` is excluded (it can perform
`a`). The companion test `X ≝ ā.bad.0 + b̄.X` is passed by the same states. The
library's `safeStates_L713_eq`. -/
theorem ex_7_13 :
    recMax DeepWiki.ReactiveSystems.L713 DeepWiki.ReactiveSystems.F713 =
      {DeepWiki.ReactiveSystems.S713.p, DeepWiki.ReactiveSystems.S713.r,
        DeepWiki.ReactiveSystems.S713.s} :=
  DeepWiki.ReactiveSystems.safeStates_L713_eq

end DeepWiki.Rs
