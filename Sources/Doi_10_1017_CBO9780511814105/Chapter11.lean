import DeepWiki.ReactiveSystems.TimedTransitionSystems
import DeepWiki.ReactiveSystems.TimedTraces
import DeepWiki.ReactiveSystems.TimedBisimulationUntimed
import DeepWiki.ReactiveSystems.TimedBisimulationUntimedStrict
import DeepWiki.ReactiveSystems.TimedBisimulationWeak
import DeepWiki.ReactiveSystems.TimedRegions
import DeepWiki.ReactiveSystems.TimedRegionsBisimulation
import DeepWiki.ReactiveSystems.TimedRegionGraph
import DeepWiki.ReactiveSystems.TimedZones
import DeepWiki.ReactiveSystems.TimedJobshopNetwork
import DeepWiki.ReactiveSystems.TimedLanguageExample
import DeepWiki.ReactiveSystems.TimedAutomatonBisimilarity
import DeepWiki.ReactiveSystems.FourTimedAutomataBisim
import DeepWiki.ReactiveSystems.TimedTracesBisimilarity
import DeepWiki.ReactiveSystems.TimedTracesBisimilarityStrict
import DeepWiki.ReactiveSystems.TimedBisimulationTimeAbstracted
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 11: Timed behavioural equivalences
Book-numbered restatements for §11.1 (timed/untimed trace equivalence), §11.2
(timed/untimed bisimilarity), §11.4 (the region construction) and §11.5 (zones and
reachability graphs), discharged by the `DeepWiki.ReactiveSystems` library. -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems
open scoped NNReal

variable {Proc Act : Type*} {C : Type*}

/-! ## §11.1 Timed and untimed trace equivalence -/

/-- **Definition 11.1** (§11.1, p.193). A timed trace records the absolute time of
each action along a delay/action run. The library's `TLTS.TimedTrace`. -/
abbrev def_11_1 := @TLTS.TimedTrace

/-- **Definition 11.2** (§11.1, p.194). The timed language `L(A)` — the set of
finite timed traces. The library's `TLTS.timedLang`. -/
abbrev def_11_2 := @TLTS.timedLang

/-- **Definition 11.3** (§11.1, p.194). An untimed trace: the action projection of
a timed trace. The library's `TLTS.UntimedTrace`. -/
abbrev def_11_3 := @TLTS.UntimedTrace

/-- **Definition 11.4** (§11.1, p.194). The untimed language `Lᵤ(A)`. The library's
`TLTS.untimedLang`. -/
abbrev def_11_4 := @TLTS.untimedLang

/-- **Theorem 11.1** (§11.1, p.194). Timed-language equivalence implies
untimed-language equivalence. -/
theorem thm_11_1 {T₁ T₂ : TLTS Proc Act} {s₁ s₂ : Proc}
    (h : T₁.timedLang s₁ = T₂.timedLang s₂) : T₁.untimedLang s₁ = T₂.untimedLang s₂ :=
  TLTS.timedLang_eq_untimedLang_eq h

/-! ## §11.2 Timed and untimed bisimilarity -/

/-- **Theorem 11.2** (§11.2, p.196). Timed bisimilar processes are untimed
bisimilar. The library's `TLTS.TimedBisimilar.untimedBisimilar`. -/
theorem thm_11_2 (T : TLTS Proc Act) {p q : Proc} (h : TLTS.TimedBisimilar T p q) :
    TLTS.UntimedBisimilar T p q := TLTS.TimedBisimilar.untimedBisimilar h

/-- **Definition 11.5** (§11.2, p.195). Timed bisimilarity: a timed bisimulation
matches both visible actions and time-delay steps. The library's
`TLTS.TimedBisimilar` (bisimilarity over the combined action/delay labels). -/
abbrev def_11_5 := @TLTS.TimedBisimilar

/-- **Definition 11.5** (§11.2, p.195), the transfer property: timed bisimilarity
matches both action transitions and time-delay transitions on each side. -/
theorem def_11_5_transfer (T : TLTS Proc Act) (p q : Proc) :
    TLTS.TimedBisimilar T p q ↔
      (∀ a p', T.act p a p' → ∃ q', T.act q a q' ∧ TLTS.TimedBisimilar T p' q') ∧
      (∀ a q', T.act q a q' → ∃ p', T.act p a p' ∧ TLTS.TimedBisimilar T p' q') ∧
      (∀ d p', T.delay p d p' → ∃ q', T.delay q d q' ∧ TLTS.TimedBisimilar T p' q') ∧
      (∀ d q', T.delay q d q' → ∃ p', T.delay p d p' ∧ TLTS.TimedBisimilar T p' q') :=
  TLTS.timedBisimilar_iff T p q

/-- **§11.2** (p.195). Timed bisimilarity is an equivalence relation. -/
theorem timedBisimilar_equivalence (T : TLTS Proc Act) :
    Equivalence (TLTS.TimedBisimilar T) := TLTS.timedBisimilar_equivalence T

/-- **Definition 11.7** (§11.2, p.197). Untimed (time-abstract) bisimilarity:
actions are matched exactly, delays by *some* delay of possibly different
duration. The library's `TLTS.UntimedBisimilar` (strong bisimilarity on the
untimed LTS). -/
abbrev def_11_7 := @TLTS.UntimedBisimilar

/-- **§11.2** (p.197). Untimed bisimilarity is an equivalence relation. -/
theorem untimedBisimilar_equivalence (T : TLTS Proc Act) :
    Equivalence (TLTS.UntimedBisimilar T) := TLTS.untimedBisimilar_equivalence T

/-- **Lemma 11.1 / Exercise 11.4** (§11.2, p.198). Two states are untimed bisimilar
(actions matched exactly, delays matched by *some* delay — the transfer form) iff
they are strongly bisimilar in the untimed LTS `Tε` (Definition 3.2), where each
time-delay step is relabelled `ε`. The library *defines* untimed bisimilarity as
strong bisimilarity on `Tε` (`TLTS.untimedLTS`), so this is the transfer
characterization `TLTS.untimedBisimilar_iff`. -/
theorem lemma_11_1 (T : TLTS Proc Act) (p q : Proc) :
    ((∀ a p', T.act p a p' → ∃ q', T.act q a q' ∧ T.UntimedBisimilar p' q') ∧
     (∀ a q', T.act q a q' → ∃ p', T.act p a p' ∧ T.UntimedBisimilar p' q') ∧
     (∀ d p', T.delay p d p' → ∃ d' q', T.delay q d' q' ∧ T.UntimedBisimilar p' q') ∧
     (∀ d q', T.delay q d q' → ∃ d' p', T.delay p d' p' ∧ T.UntimedBisimilar p' q'))
      ↔ LTS.Bisimilar T.untimedLTS p q :=
  (TLTS.untimedBisimilar_iff T p q).symm

/-- **§11.2** (p.197). Timed bisimilarity refines untimed bisimilarity:
timed-bisimilar states are untimed bisimilar (durations are forgotten, so the
converse fails). -/
theorem timedBisimilar_untimedBisimilar (T : TLTS Proc Act) {p q : Proc}
    (h : TLTS.TimedBisimilar T p q) : TLTS.UntimedBisimilar T p q :=
  TLTS.TimedBisimilar.untimedBisimilar h

/-- **§11.2** (p.197), strictness. The refinement is *strict*: there are
untimed-bisimilar states that are **not** timed bisimilar (durations matter).
Witnessed by a state idling for any delay versus one idling only for delays `≤ 1`
— the converse of `timedBisimilar_untimedBisimilar` fails. -/
theorem untimedBisimilar_not_imp_timedBisimilar :
    ∃ (Q : Type) (T : TLTS Q Unit) (p q : Q),
      T.UntimedBisimilar p q ∧ ¬ T.TimedBisimilar p q :=
  DeepWiki.ReactiveSystems.untimedBisimilar_not_imp_timedBisimilar

/-! ## §11.3 Weak timed bisimilarity -/

/-- **Definition 11.8** (§11.3, p.201). The weak action transition `s =a⇒ t`
(`τ*` for `a = τ`, `τ*·a·τ*` for visible `a`). The library's `TLTS.wact`. -/
abbrev def_11_8_wact := @TLTS.wact

/-- **Definition 11.8** (§11.3, p.201). The weak delay transition `s =d⇒ t`: a run
of `τ`-actions and delays summing to `d`. The library's `TLTS.wdelay`. -/
abbrev def_11_8_wdelay := @TLTS.wdelay

/-- **Definition 11.9** (§11.3, p.201). A *weak timed bisimulation*: each concrete
action/delay step is matched by a weak timed transition. The library's
`TLTS.IsWeakTimedBisimulation`. -/
abbrev def_11_9 := @TLTS.IsWeakTimedBisimulation

/-- **Definition 11.10** (§11.3, p.201). *Weak timed bisimilarity* `≈`: some weak
timed bisimulation relates the states. The library's `TLTS.WeaklyTimedBisimilar`. -/
abbrev def_11_10 := @TLTS.WeaklyTimedBisimilar

/-- **Exercise 11.8** (§11.3, p.202). Timed bisimilarity refines weak timed
bisimilarity: `s ~ s'` implies `s ≈ s'` (a concrete step is a one-step weak
transition). -/
theorem ex_11_8 (T : TLTS Proc Act) (tau : Act) {s s' : Proc}
    (h : TLTS.TimedBisimilar T s s') : TLTS.WeaklyTimedBisimilar T tau s s' :=
  TLTS.TimedBisimilar.weaklyTimedBisimilar h

/-! ## §11.4 The region construction -/

/-- **Definition 11.11** (§11.4, p.205). Integer part `⌊d⌋` of a clock value. -/
noncomputable abbrev intPart := @DeepWiki.ReactiveSystems.intPart

/-- **Definition 11.11** (§11.4, p.205). Fractional part `frac(d) = d − ⌊d⌋`. -/
noncomputable abbrev fracPart := @DeepWiki.ReactiveSystems.fracPart

/-- **Definition 11.12** (§11.4, p.207), verbatim. Two clock valuations are
equivalent when their integer parts agree up to `cₓ`, they agree on which clocks
have a zero fractional part, and the ordering of fractional parts agrees. The
library's `RegionEquiv`. -/
abbrev def_11_12 := @DeepWiki.ReactiveSystems.RegionEquiv

/-- **Definition 11.12** is **not** symmetric as literally stated (the asymmetric
guard `v x ≤ cₓ` only catches differing fractional parts at an integer boundary
in one direction); the genuine region equivalence underlying Theorem 11.3 uses
the clamped floor `RegionEq`. -/
theorem def_11_12_not_symmetric :
    ¬ Std.Symm (DeepWiki.ReactiveSystems.RegionEquiv (C := Unit) (fun _ => 0)) :=
  DeepWiki.ReactiveSystems.not_symmetric_regionEquiv

/-- **Theorem 11.3** (§11.4, p.209), equivalence-relation part. Region
equivalence partitions the clock valuations — here the corrected `RegionEq` is a
genuine `Equivalence`. -/
theorem thm_11_3_equivalence (cmax : C → ℕ) :
    Equivalence (DeepWiki.ReactiveSystems.RegionEq cmax) :=
  DeepWiki.ReactiveSystems.regionEq_equivalence cmax

/-- **Theorem 11.3** (§11.4, p.209), finite-index part. Over a finite clock set,
region equivalence has finitely many classes — the region quotient is finite. -/
theorem thm_11_3_finite [Finite C] (cmax : C → ℕ) :
    Finite (DeepWiki.ReactiveSystems.Region cmax) :=
  DeepWiki.ReactiveSystems.Region.finite cmax

/-- **Theorem 11.3** (§11.4, p.209), untimed-bisimilarity part (modular form). In
a well-formed timed automaton (guards/invariants bounded by `cmax`) with the
region time-successor property, region-equivalent configurations `(ℓ, v)`,
`(ℓ, v')` are **untimed** bisimilar (`def_11_7`) — note *untimed*, not timed:
equal delays do not preserve regions. Built from guard invariance
(`regionEq_satisfies`) and reset preservation (`RegionEq.reset`); the
time-successor hypothesis is discharged unconditionally for finite clock sets
(`thm_11_3_untimedBisimilar_fintype`). -/
theorem thm_11_3_untimedBisimilar {Loc : Type*} (A : TimedAutomaton Loc Act C)
    {cmax : C → ℕ} (wf : A.WellFormed cmax) (hts : DeepWiki.ReactiveSystems.TimeSuccessor cmax)
    {ℓ : Loc} {v v' : Valuation C} (h : DeepWiki.ReactiveSystems.RegionEq cmax v v') :
    A.tlts.UntimedBisimilar (ℓ, v) (ℓ, v') :=
  DeepWiki.ReactiveSystems.regionEq_untimedBisimilar A wf hts h

/-- **Theorem 11.3** for single-clock timed automata (unconditional): the region
time-successor property holds outright for a subsingleton clock set, so
region-equivalent configurations are untimed bisimilar with no extra hypothesis. -/
theorem thm_11_3_untimedBisimilar_single_clock {Loc : Type*} [Subsingleton C]
    (A : TimedAutomaton Loc Act C) {cmax : C → ℕ} (wf : A.WellFormed cmax)
    {ℓ : Loc} {v v' : Valuation C} (h : DeepWiki.ReactiveSystems.RegionEq cmax v v') :
    A.tlts.UntimedBisimilar (ℓ, v) (ℓ, v') :=
  DeepWiki.ReactiveSystems.regionEq_untimedBisimilar_of_subsingleton A wf h

/-- **Theorem 11.3** (untimed-bisimilarity part), **unconditional for finite clock
sets** (§11.4, p.209). Since a timed automaton has finitely many clocks, the
general region time-successor property holds (`timeSuccessor_of_fintype`), so
region-equivalent configurations `(ℓ, v)`, `(ℓ, v')` are untimed bisimilar with no
extra hypothesis. This closes the substantive half of Theorem 11.3. -/
theorem thm_11_3_untimedBisimilar_fintype {Loc : Type*} [Fintype C]
    (A : TimedAutomaton Loc Act C) {cmax : C → ℕ} (wf : A.WellFormed cmax)
    {ℓ : Loc} {v v' : Valuation C} (h : DeepWiki.ReactiveSystems.RegionEq cmax v v') :
    A.tlts.UntimedBisimilar (ℓ, v) (ℓ, v') :=
  DeepWiki.ReactiveSystems.regionEq_untimedBisimilar_of_fintype A wf h

/-- **Definition 11.13** (§11.4, p.209). A *region* is an `≡`-equivalence class
`[v]_≡` of clock valuations. The library's `Region`. -/
abbrev def_11_13 := @DeepWiki.ReactiveSystems.Region

/-- **Definition 11.14** (§11.4, p.212). The *region graph* `Tᵣ(A)`: the quotient
of the untimed transition system by region equivalence on configurations, with
action labels lifted and a single `ε`-label for "some delay". The library's
`TimedAutomaton.regionGraph` (`Tᵤ(A).quot (regionConfigSetoid cmax)`). -/
noncomputable abbrev def_11_14 := @DeepWiki.ReactiveSystems.TimedAutomaton.regionGraph

/-- **Theorem 11.4** (§11.4, p.213), finiteness part. The region graph of a timed
automaton (finitely many locations and clocks) has finitely many symbolic
states. -/
theorem thm_11_4_finite {Loc : Type*} [Finite Loc] [Finite C] (cmax : C → ℕ) :
    Finite (Quotient (DeepWiki.ReactiveSystems.regionConfigSetoid (Loc := Loc) cmax)) :=
  DeepWiki.ReactiveSystems.regionGraph_finite cmax

/-- **Theorem 11.4** (§11.4, p.213), bisimilarity part (unconditional for finite
clock sets). A configuration `(ℓ,v)` of the untimed transition system `Tᵤ(A)` is
strongly bisimilar to its symbolic state `(ℓ,[v]_≡)` in the region graph `Tᵣ(A)`. -/
theorem thm_11_4_bisimilar {Loc : Type*} [Fintype C] (A : TimedAutomaton Loc Act C)
    {cmax : C → ℕ} (wf : A.WellFormed cmax) (c : Loc × Valuation C) :
    LTS.CrossBisimilar A.tlts.untimedLTS (A.regionGraph cmax) c
      (DeepWiki.ReactiveSystems.symbolicState cmax c) :=
  A.regionGraph_crossBisimilar_fintype wf c

/-- **Corollary 11.1** (§11.4, p.213). Untimed bisimilarity is decidable: two
configurations are untimed bisimilar iff their symbolic states are strongly
bisimilar in the *finite* region graph. -/
theorem cor_11_1 {Loc : Type*} [Fintype C] (A : TimedAutomaton Loc Act C)
    {cmax : C → ℕ} (wf : A.WellFormed cmax) (c₁ c₂ : Loc × Valuation C) :
    A.tlts.UntimedBisimilar c₁ c₂ ↔
      LTS.Bisimilar (A.regionGraph cmax)
        (DeepWiki.ReactiveSystems.symbolicState cmax c₁)
        (DeepWiki.ReactiveSystems.symbolicState cmax c₂) :=
  A.untimedBisimilar_iff_regionGraph_fintype wf c₁ c₂

/-- **§11.4 (Hennessy–Milner via the region graph).** Composing Corollary 11.1 with
the Hennessy–Milner theorem on the *finite* (hence image-finite) region graph: two
configurations are untimed bisimilar iff their symbolic states satisfy the same HML
formulae over the region graph — reducing (untimed) timed equivalence to logical
equivalence on a finite system (the region-graph route to the timed Hennessy–Milner
characterization). Discharged by `untimedBisimilar_iff_regionGraph_hmlEquiv`. -/
theorem cor_11_1_hmlEquiv {Loc : Type*} [Finite Loc] [Fintype C]
    (A : TimedAutomaton Loc Act C) {cmax : C → ℕ} (wf : A.WellFormed cmax)
    (c₁ c₂ : Loc × Valuation C) :
    A.tlts.UntimedBisimilar c₁ c₂ ↔
      LTS.HMLEquiv (A.regionGraph cmax)
        (DeepWiki.ReactiveSystems.symbolicState cmax c₁)
        (DeepWiki.ReactiveSystems.symbolicState cmax c₂) :=
  A.untimedBisimilar_iff_regionGraph_hmlEquiv wf c₁ c₂

/-- **Lemma 11.2 / Corollary 11.2** (§11.4, p.214). The reachability problem is
decidable: a symbolic state `t` is reachable in the region graph from `⟦c₀⟧` iff
`A` reaches some configuration in the class `t`, reducing reachability in the
infinite timed system to reachability in the finite region graph. -/
theorem lemma_11_2 {Loc : Type*} [Fintype C] (A : TimedAutomaton Loc Act C)
    {cmax : C → ℕ} (wf : A.WellFormed cmax) (c₀ : Loc × Valuation C)
    (t : Quotient (DeepWiki.ReactiveSystems.regionConfigSetoid cmax)) :
    (A.regionGraph cmax).Reachable (DeepWiki.ReactiveSystems.symbolicState cmax c₀) t ↔
      ∃ c, DeepWiki.ReactiveSystems.symbolicState cmax c = t ∧
        A.tlts.untimedLTS.Reachable c₀ c :=
  A.reachable_iff_regionGraph_fintype wf c₀ t

/-! ## §11.5 Zones and reachability graphs -/

/-- **Definition 11.15** (§11.5, p.215). The *future* `Z↑ = {v + d | v ∈ Z,
d ≥ 0}` of a zone. The library's `zoneUp`. -/
abbrev def_11_15_up := @DeepWiki.ReactiveSystems.zoneUp

/-- **Definition 11.15** (§11.5, p.215). The *reset* `Z[r] = {v[r] | v ∈ Z}` of a
zone. The library's `zoneReset`. -/
abbrev def_11_15_reset := @DeepWiki.ReactiveSystems.zoneReset

/-- **Definition 11.16** (§11.5, p.216). The symbolic transition relation `⤳` over
symbolic states `(ℓ, Z)`: a delay step `(ℓ,Z) ⤳ (ℓ, Z↑ ∧ I(ℓ))` and an action
step `(ℓ,Z) ⤳ (ℓ', (Z ∧ g)[r] ∧ I(ℓ'))` per edge `ℓ —g,a,r→ ℓ'`. The library's
`SymStep` (curried in the symbolic-state components). -/
abbrev def_11_16 := @DeepWiki.ReactiveSystems.SymStep

/-- **Theorem 11.5** (§11.5, p.216), soundness. Every valuation in the target of a
symbolic transition `(ℓ,Z) ⤳ (ℓ',Z')` is reached by a concrete transition from
some valuation of `Z` (the delay case needs `Z` to respect the invariant of `ℓ`,
which holds for all reachable symbolic states). -/
theorem thm_11_5_sound {Loc : Type*} (A : TimedAutomaton Loc Act C) {ℓ ℓ' : Loc}
    {Z Z' : Set (Valuation C)} (hstep : DeepWiki.ReactiveSystems.SymStep A ℓ Z ℓ' Z')
    (hZinv : Z ⊆ DeepWiki.ReactiveSystems.zoneGuard (A.inv ℓ)) {v' : Valuation C}
    (hv' : v' ∈ Z') : ∃ v ∈ Z, ∃ lab, A.tlts.untimedLTS.step (ℓ, v) lab (ℓ', v') :=
  DeepWiki.ReactiveSystems.symStep_sound A hstep hZinv hv'

/-- **Theorem 11.5** (§11.5, p.216), completeness for action steps. A concrete
action transition from `v ∈ Z` is matched by a symbolic transition whose target
contains the resulting valuation. -/
theorem thm_11_5_complete_act {Loc : Type*} (A : TimedAutomaton Loc Act C) {ℓ ℓ' : Loc}
    {Z : Set (Valuation C)} {v v' : Valuation C} {a : Act} (hv : v ∈ Z)
    (hstep : A.tlts.act (ℓ, v) a (ℓ', v')) :
    ∃ Z', DeepWiki.ReactiveSystems.SymStep A ℓ Z ℓ' Z' ∧ v' ∈ Z' :=
  DeepWiki.ReactiveSystems.symStep_complete_act A hv hstep

/-- **Theorem 11.5** (§11.5, p.216), completeness for delay steps. A concrete
delay transition from `v ∈ Z` is matched by the symbolic delay step. Together
with `thm_11_5_complete_act`, the symbolic semantics is sound and complete for
reachability (Corollary 11.2's zone-based decision procedure). -/
theorem thm_11_5_complete_delay {Loc : Type*} (A : TimedAutomaton Loc Act C) {ℓ : Loc}
    {Z : Set (Valuation C)} {v v' : Valuation C} {d : ℝ≥0} (hv : v ∈ Z)
    (hstep : A.tlts.delay (ℓ, v) d (ℓ, v')) :
    ∃ Z', DeepWiki.ReactiveSystems.SymStep A ℓ Z ℓ Z' ∧ v' ∈ Z' :=
  DeepWiki.ReactiveSystems.symStep_complete_delay A hv hstep

/-- **Definition 11.6** (§11.2, p.196). Timed bisimilarity lifted to whole automata:
`A₁` and `A₂` are timed bisimilar iff their initial states are timed bisimilar in the
union of the TLTSs they generate. The library's `TimedAutomaton.TimedBisimilar`. -/
abbrev def_11_6 := @DeepWiki.ReactiveSystems.TimedAutomaton.TimedBisimilar

/-- **Exercise 11.2** (§11.1, p.195). The two single-location timed automata of
Example 11.2 (`a`-self-loops with guards `x ≤ 1` resp. `x = 1`) are
untimed-language equivalent yet **not** timed-language equivalent — so the converse
of Theorem 11.1 fails. (`(0, a)` is a timed trace of (a) but not (b), while both
accept every untimed trace.) The library's `taA_taB_untimedEq_not_timedEq`. -/
theorem ex_11_2 :
    (DeepWiki.ReactiveSystems.taA.tlts.untimedLang
        (DeepWiki.ReactiveSystems.taA.initial, fun _ => (0 : ℝ≥0)) =
      DeepWiki.ReactiveSystems.taB.tlts.untimedLang
        (DeepWiki.ReactiveSystems.taB.initial, fun _ => (0 : ℝ≥0))) ∧
    (DeepWiki.ReactiveSystems.taA.tlts.timedLang
        (DeepWiki.ReactiveSystems.taA.initial, fun _ => (0 : ℝ≥0)) ≠
      DeepWiki.ReactiveSystems.taB.tlts.timedLang
        (DeepWiki.ReactiveSystems.taB.initial, fun _ => (0 : ℝ≥0))) :=
  DeepWiki.ReactiveSystems.taA_taB_untimedEq_not_timedEq

/-- **Exercise 11.3** (§11.2, p.196). The network `Worker ∣ Employer` of Figure 10.4
(the lazy worker and his demanding employer, `hit` the only ordinary action) is timed
bisimilar to a single timed automaton `Simple-Jobshop` with only two clocks. The
library's `networkWorkerEmployer_timedBisimilar_simpleJobshop`: the worker's and
employer's mode timers (`x`, `z`) stay equal on every reachable state — so three
clocks collapse to two — and the conjoined working invariant `x ≤ 60 ∧ y ≤ 4` is
exactly the small Jobshop's. -/
theorem ex_11_3 :
    DeepWiki.ReactiveSystems.networkWorkerEmployer.TimedBisimilar
      DeepWiki.ReactiveSystems.SimpleJobshop :=
  DeepWiki.ReactiveSystems.networkWorkerEmployer_timedBisimilar_simpleJobshop

/-- **Exercise 11.5** (§11.2, p.199). The four single-action, single-clock timed
automata `A` (`a[y≤1, y:=0]` twice), `X` (`a[y≤2]` twice), `U` (`a[true]` then
`a[y≤2]`) and `D` (`a[y≤2]` then `a[y≤2]`, plus an `a[y>2]` branch), as the combined
TLTS `tlts115`. The classification of the six pairs of initial states (all at
`y=0`): `U` and `D` are **timed bisimilar**; `A` and `X` are **untimed bisimilar but
not timed bisimilar**; and `A`–`U`, `A`–`D`, `X`–`U`, `X`–`D` are **neither** (`U`,
`D` can always fire `a`, while `A`, `X` cannot after a large enough delay). -/
theorem ex_11_5 :
    TLTS.TimedBisimilar tlts115 (.U, 0) (.D, 0) ∧
    (TLTS.UntimedBisimilar tlts115 (.A, 0) (.X, 0) ∧
      ¬ TLTS.TimedBisimilar tlts115 (.A, 0) (.X, 0)) ∧
    ¬ TLTS.UntimedBisimilar tlts115 (.A, 0) (.U, 0) ∧
    ¬ TLTS.UntimedBisimilar tlts115 (.A, 0) (.D, 0) ∧
    ¬ TLTS.UntimedBisimilar tlts115 (.X, 0) (.U, 0) ∧
    ¬ TLTS.UntimedBisimilar tlts115 (.X, 0) (.D, 0) :=
  ⟨DeepWiki.ReactiveSystems.u_timedBisimilar_d,
    ⟨DeepWiki.ReactiveSystems.a_untimedBisimilar_x,
      DeepWiki.ReactiveSystems.a_not_timedBisimilar_x⟩,
    DeepWiki.ReactiveSystems.a_not_untimedBisimilar_u,
    DeepWiki.ReactiveSystems.a_not_untimedBisimilar_d,
    DeepWiki.ReactiveSystems.x_not_untimedBisimilar_u,
    DeepWiki.ReactiveSystems.x_not_untimedBisimilar_d⟩

/-- **Exercise 11.6**, claim 1 (§11.2, p.197), positive. If two timed automata are
timed bisimilar then they are timed-trace equivalent: timed bisimilarity preserves
the timed language. -/
theorem ex_11_6_timedBisim_timedTrace {T : TLTS Proc Act} {p q : Proc}
    (h : T.TimedBisimilar p q) : T.timedLang p = T.timedLang q :=
  TLTS.timedLang_eq_of_timedBisimilar h

/-- **Exercise 11.6**, claim 2 (§11.2, p.197), positive. If two timed automata are
timed bisimilar then they are untimed-trace equivalent (forget the time-stamps of
the equal timed languages). -/
theorem ex_11_6_timedBisim_untimedTrace {T : TLTS Proc Act} {p q : Proc}
    (h : T.TimedBisimilar p q) : T.untimedLang p = T.untimedLang q :=
  TLTS.untimedLang_eq_of_timedBisimilar h

/-- **Exercise 11.6**, claim 3 (§11.2, p.197), positive. If two timed automata are
untimed bisimilar then they are untimed-trace equivalent: untimed bisimilarity
(delays matched by *some* delay) preserves the untimed language. -/
theorem ex_11_6_untimedBisim_untimedTrace {T : TLTS Proc Act} {p q : Proc}
    (h : T.UntimedBisimilar p q) : T.untimedLang p = T.untimedLang q :=
  TLTS.untimedLang_eq_of_untimedBisimilar h

/-- **Exercise 11.6**, claim 4 (§11.2, p.197), negative. Untimed bisimilarity does
**not** imply timed-trace equivalence: two states acting once after fixed delays
`1` resp. `2` are untimed bisimilar (durations forgotten) yet the timed trace
`[(1, *)]` separates their timed languages. -/
theorem ex_11_6_untimedBisim_not_timedTrace :
    ∃ (Q : Type) (T : TLTS Q Unit) (p q : Q),
      T.UntimedBisimilar p q ∧ T.timedLang p ≠ T.timedLang q :=
  DeepWiki.ReactiveSystems.untimedBisimilar_not_imp_timedLangEq

/-- **Exercise 11.6**, claim 5 (§11.2, p.197), negative. Timed-trace equivalence
does **not** imply untimed bisimilarity: `a.(b + c)` and `a.b + a.c` with no time
delays have the same (empty-only) timed language but are not untimed bisimilar
(branching is lost by trace equivalence). -/
theorem ex_11_6_timedTrace_not_untimedBisim :
    ∃ (Q A : Type) (T : TLTS Q A) (p q : Q),
      T.timedLang p = T.timedLang q ∧ ¬ T.UntimedBisimilar p q :=
  DeepWiki.ReactiveSystems.timedLangEq_not_imp_untimedBisimilar

/-- **Definition 11.6′ / Exercise 11.7** (§11.2, p.197). *Time-abstracted
bisimilarity*: replace every time-delay step by `τ` (the untimed LTS) and take
*weak* bisimilarity. The library's `TLTS.TimeAbstractedBisimilar`. -/
abbrev def_11_7_timeAbstracted := @TLTS.TimeAbstractedBisimilar

/-- **Exercise 11.7** (§11.2, p.197), the holding direction. Untimed bisimilarity
implies time-abstracted bisimilarity: strong bisimilarity on the untimed LTS
refines weak bisimilarity on it. -/
theorem ex_11_7_imp {T : TLTS Proc Act} {p q : Proc} (h : T.UntimedBisimilar p q) :
    T.TimeAbstractedBisimilar p q :=
  TLTS.UntimedBisimilar.timeAbstractedBisimilar h

/-- **Exercise 11.7** (§11.2, p.197), the answer: **no**, time-abstracted
bisimilarity is *not* equivalent to untimed bisimilarity. The converse of `ex_11_7_imp`
fails — a state delaying into a deadlock (`s →delay→ stop`) is time-abstracted
bisimilar to the deadlock (the delay is silent) but not untimed bisimilar to it. -/
theorem ex_11_7 :
    ∃ (Q : Type) (T : TLTS Q Unit) (p q : Q),
      T.TimeAbstractedBisimilar p q ∧ ¬ T.UntimedBisimilar p q :=
  DeepWiki.ReactiveSystems.timeAbstracted_not_imp_untimedBisimilar

end DeepWiki.Rs
