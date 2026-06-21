import DeepWiki.ReactiveSystems.TimedHml
import DeepWiki.ReactiveSystems.TimedHmlClocks
import DeepWiki.ReactiveSystems.TimedHmlNegation
import DeepWiki.ReactiveSystems.TimedHmlRecursion
import DeepWiki.ReactiveSystems.TimedBisimulationHmlStrict
import DeepWiki.ReactiveSystems.TimedHmlExamples
import DeepWiki.ReactiveSystems.TimedHmlClosedFormulae
import DeepWiki.ReactiveSystems.TimedHmlEquivalences
import DeepWiki.ReactiveSystems.CharacteristicFormulaTimed
import DeepWiki.ReactiveSystems.CharacteristicFormulaTimedSimulation
import DeepWiki.ReactiveSystems.TimedHmlIntervalDelay
import DeepWiki.ReactiveSystems.SymbolicModelChecking
import DeepWiki.ReactiveSystems.SymbolicModelCheckingDecidable
import DeepWiki.ReactiveSystems.SymbolicModelCheckingExecutable
import DeepWiki.ReactiveSystems.SymbolicModelCheckingExecutableFull
import DeepWiki.ReactiveSystems.SymbolicModelCheckingExample
import DeepWiki.ReactiveSystems.TimedRegionSuccessorComplete
import DeepWiki.ReactiveSystems.TimedModelCheckingExamples
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 12: Hennessy–Milner logic with time
Book-numbered restatements for the timed logic `Mt` with formula clocks (§12.1,
Definitions 12.1–12.3) and the soundness half of the timed Hennessy–Milner
characterisation (§12.3), discharged by the `DeepWiki.ReactiveSystems` library.

## NOT YET FORMALIZED (subtractive — delete each item once it is formalized)
§12.3: Thm 12.4 unbounded (invariant-free) locations `[external]` (Laroussinie–Larsen–Weise 1995). The
  characteristic-formula construction is mechanized for general timed automata — nondeterministic,
  multi-clock, multi-action, general-guard, *conjunctive* location invariants, *target-invariant-gated*
  actions, *arbitrary* resets, all in one construction `TimedGeneralCharacteristic.fchar_iff` (subsuming
  the per-axis `TimedConjInvCharacteristic.cchar_iff` / `TimedTargetInvCharacteristic.gchar_iff` /
  `TimedFullCharacteristic.uchar_iff`). The one remaining case is locations with **no** invariant (`inv ℓ =
  []`, unbounded delays): the boundary-disjunction forcing is vacuous there, so such a location needs a
  separate pure-`∀∀X_ℓ` body branch (no forcing) — the construction currently assumes `inv ℓ ≠ []` (`hne`).
Ex 12.12 statement 3 (full-`Mt` strictness at `c=√2`) `[research]` (needs a single-irrational-cut region
  + coinductive bisimulation); Ex 12.14 (a sublanguage characterizing untimed bisimilarity) `[research]`;
  Ex 12.15 (`Mt` distinguishes [0,√2] from [0,√2)) `[research]`. -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems
open scoped NNReal

variable {Proc Act D : Type*}

/-! ## §12.1 Hennessy–Milner logic with time (`Mt`) -/

/-- A simplified fragment of timed HML — actions plus the delay quantifiers
`∃∃`/`∀∀`, without formula clocks. The library's `TimedHML`. -/
abbrev timedHML := @TimedHML

/-- Satisfaction of the simplified fragment in a TLTS. The library's
`TLTS.TSat`. -/
abbrev tsat := @TLTS.TSat

/-- **Definition 12.1** (§12.1, p.223). Hennessy–Milner formulae with time `Mt`
over actions `Act` and formula clocks `D`: action modalities `⟨a⟩`/`[a]`, delay
quantifiers `∃∃`/`∀∀`, the reset `x in F`, and atomic clock constraints
`g ∈ B(D)`. The library's `Mt`. -/
abbrev def_12_1 := @Mt

/-- **Definition 12.2** (§12.1, p.224). Semantics of `Mt`: satisfaction at an
extended state `(p, u)` (process plus formula-clock valuation); delay steps
advance the formula clocks `u`, `x in F` resets `x`, and `g` reads `u`. The
library's `TLTS.MtSat`. -/
abbrev def_12_2 := @TLTS.MtSat

/-- **Definition 12.2** (§12.1, p.224), denotational form. The satisfaction *set*
`⟦F⟧ ⊆ ES(Proc)`, defined compositionally with the action/delay set operators (`⟨a·⟩`/`[a·]`,
`⟨ε·⟩`/`[ε·]`) — the book's primary presentation of `Mt`'s semantics, of which `def_12_2`
(`MtSat`) is the equivalent structural-relation form (p.228). The library's `TLTS.denotMt`. -/
abbrev def_12_2_denot := @TLTS.denotMt

/-- **Exercise 12.4** (§12.1, p.228). The structural satisfaction relation (p.228) is equivalent
to Definition 12.2's denotational `⟦F⟧`: an extended state satisfies `F` iff it lies in `⟦F⟧`,
`(p, u) ∈ ⟦F⟧ ↔ (p, u) ⊨ F`, by induction on the formula. The library's
`TLTS.mem_denotMt_iff_mtSat`. -/
theorem ex_12_4 (T : TLTS Proc Act) (F : Mt Act D) (p : Proc) (u : Valuation D) :
    (p, u) ∈ TLTS.denotMt T F ↔ TLTS.MtSat T p u F :=
  TLTS.mem_denotMt_iff_mtSat T F p u

/-- **Definition 12.3** (§12.1, p.225). A state satisfies `F` when the extended
state with every formula clock zero does: `(p, u₀) ⊨ F`. The library's
`TLTS.MtSatState`. -/
abbrev def_12_3 := @TLTS.MtSatState

/-- **Definition 12.4** (§12.1, p.225). A timed automaton `A` satisfies `F ∈ Mt`
when its initial extended state (initial location, all automaton and formula
clocks zero) satisfies `F`. The library's `TimedAutomaton.SatisfiesMt`. -/
abbrev def_12_4 := @TimedAutomaton.SatisfiesMt

/-! ## §12.3 Timed bisimilarity versus HML with time -/

/-- **Theorem 12.3** (§12.3, p.233). In any TLTS, if `p` and `q` are timed
bisimilar then for every formula-clock valuation `u` the extended states `(p, u)`
and `(q, u)` satisfy exactly the same `Mt` formulae (both closed and open). Proved
by structural induction on the formula. -/
theorem thm_12_3 (T : TLTS Proc Act) {p q : Proc} (h : TLTS.TimedBisimilar T p q)
    (u : Valuation D) (F : Mt Act D) : TLTS.MtSat T p u F ↔ TLTS.MtSat T q u F :=
  TLTS.timedBisimilar_mtIff h u F

/-- **Corollary 12.1** (§12.3, p.234). Timed-bisimilar states satisfy exactly the
same `Mt` formulae at the state level (Definition 12.3) — the instantiation of
Theorem 12.3 at the all-zero formula-clock valuation, applied to the TLTSs giving
semantics to timed automata. -/
theorem cor_12_1 (T : TLTS Proc Act) {p q : Proc} (h : TLTS.TimedBisimilar T p q)
    (F : Mt Act D) : TLTS.MtSatState T p F ↔ TLTS.MtSatState T q F :=
  TLTS.timedBisimilar_mtSatState h F

/-- **§12.3** (soundness; the timed analogue of Theorem 5.1, simplified
fragment). Timed-bisimilar states satisfy the same fragment formulae. (This
direction holds for every TLTS; the converse uses the region abstraction of
§11.4, as delay-branching is uncountable.) -/
theorem timed_hm_soundness (T : TLTS Proc Act) {p q : Proc}
    (h : TLTS.TimedBisimilar T p q) : TLTS.TimedHMLEquiv T p q :=
  TLTS.timedBisimilar_timedHmlEquiv h

/-- **§12.3** (soundness for the full logic `Mt`). Timed-bisimilar states satisfy
the same `Mt` formulae (Definition 12.3 satisfaction). The reset and guard
constructs touch only the formula clocks, so soundness extends from the modal
fragment for free. -/
theorem mt_soundness (T : TLTS Proc Act) {p q : Proc}
    (h : TLTS.TimedBisimilar T p q) (F : Mt Act D) :
    TLTS.MtSatState T p F ↔ TLTS.MtSatState T q F :=
  TLTS.timedBisimilar_mtSatState h F

/-- **Theorem 12.4** (§12.3, p.234), completeness reduced to characteristic formulae.
The converse of Theorem 12.3 (`Mt`-equivalent ⇒ timed bisimilar) needs the region
construction of Laroussinie–Larsen–Weise 1995, which enters through one ingredient: a
characteristic `Mt` formula `χ` for the state. Given that, `q` is timed bisimilar to `p`
**iff** it satisfies the same state-level `Mt` formulae — the forward (soundness) half is
unconditional, the converse is the completeness reduction. The construction of `χ` for an
arbitrary timed automaton (over its finite region graph) is the remaining external piece. -/
theorem thm_12_4 (T : TLTS Proc Act) {p : Proc} (χ : Mt Act D)
    (hχ : TLTS.IsCharacteristicMt T p χ) (q : Proc) :
    TLTS.TimedBisimilar T p q ↔ ∀ F : Mt Act D, TLTS.MtSatState T p F ↔ TLTS.MtSatState T q F :=
  TLTS.timedBisimilar_iff_mtEquiv_of_characteristic T χ hχ q

/-- **Theorem 12.4**, an **unconditional** instance. The Example 11.4 automaton has a
recursion-free characteristic `Mt` formula for its live initial state `A 0` (`charA`), so
the characteristic-formula hypothesis is discharged with no region construction: a state
`q` is timed bisimilar to `A 0` iff it satisfies the same state-level `Mt` formulae. -/
theorem thm_12_4_once {c : ℕ} (q : DeepWiki.ReactiveSystems.TLTS.Once) :
    TLTS.TimedBisimilar (DeepWiki.ReactiveSystems.TLTS.onceTLTS c)
        (DeepWiki.ReactiveSystems.TLTS.Once.A 0) q ↔
      ∀ F : Mt Unit Unit,
        (DeepWiki.ReactiveSystems.TLTS.onceTLTS c).MtSatState
          (DeepWiki.ReactiveSystems.TLTS.Once.A 0) F ↔
        (DeepWiki.ReactiveSystems.TLTS.onceTLTS c).MtSatState q F :=
  DeepWiki.ReactiveSystems.TLTS.timedBisimilar_A0_iff_mtEquiv q

/-- **§12.3 / Proposition 12.2** (p.234), the separating witness. The converse of
Theorem 12.3 **fails** over arbitrary TLTSs: the book's `√2` TLTS (boundary `c`)
has `(A,0)` and `(B,0)` *not* timed bisimilar — `(B,0) —c→ (B,c) —a→ End` has no
match from `(A,0)`, which only reaches `(A,c)` (no `a` there). Discharged by the
library's `not_timedBisimilar_sqrt2`. (With `c = √2` the two states are
nonetheless `Mt`-equivalent — Proposition 12.2 / the keenest-reader Exercise
12.12 — so timed bisimilarity is *strictly* finer than `Mt`-equivalence on TLTSs.) -/
theorem prop_12_2_not_bisim (c : ℝ≥0) :
    ¬ TLTS.TimedBisimilar (DeepWiki.ReactiveSystems.sq2TLTS c)
      (DeepWiki.ReactiveSystems.Sq2.A 0) (DeepWiki.ReactiveSystems.Sq2.B 0) :=
  DeepWiki.ReactiveSystems.not_timedBisimilar_sqrt2 c

/-- **Exercise 12.12** (§12.3, statements 1–2). Past the boundary the `√2`-example
states agree: `(A,d)` (`c ≤ d`) and `(B,e)` (`c < e`) are timed bisimilar — both
can henceforth only delay. So `(A,0)` and `(B,0)` differ *only* at the boundary
crossing. Discharged by the library's `timedBisimilar_past_boundary`. -/
theorem ex_12_12_past_boundary (c : ℝ≥0) {d e : ℝ≥0} (hd : c ≤ d) (he : c < e) :
    TLTS.TimedBisimilar (DeepWiki.ReactiveSystems.sq2TLTS c)
      (DeepWiki.ReactiveSystems.Sq2.A d) (DeepWiki.ReactiveSystems.Sq2.B e) :=
  DeepWiki.ReactiveSystems.timedBisimilar_past_boundary c hd he

/-- **Proposition 12.2** (§12.3, p.234), strictness — *basic-`TimedHML` form*. For
any positive boundary `c`, `(A,0)` and `(B,0)` satisfy the same basic timed-HML
formulae (the `∃∃`/`∀∀` fragment without clock constraints) yet are *not* timed
bisimilar, so timed bisimilarity is strictly finer than basic-timed-HML equivalence.
Discharged by the library's `timedHmlEquiv_and_not_timedBisimilar_sq2`. (No
irrationality of `c` is needed here; the book's stronger statement — same formulae
of the *full* `Mt` logic, with clock guards — is what requires `c = √2` irrational,
and is left open. See `prop_12_2_not_bisim` for the non-bisimilarity alone.) -/
theorem prop_12_2_strict_basic (c : ℝ≥0) (hc : 0 < c) :
    (DeepWiki.ReactiveSystems.sq2TLTS c).TimedHMLEquiv
        (DeepWiki.ReactiveSystems.Sq2.A 0) (DeepWiki.ReactiveSystems.Sq2.B 0) ∧
    ¬ TLTS.TimedBisimilar (DeepWiki.ReactiveSystems.sq2TLTS c)
        (DeepWiki.ReactiveSystems.Sq2.A 0) (DeepWiki.ReactiveSystems.Sq2.B 0) :=
  DeepWiki.ReactiveSystems.timedHmlEquiv_and_not_timedBisimilar_sq2 c hc

/-! ## §12.2 Properties of the Example 11.4 automata -/

/-- **Exercise 12.2** (§12.2, p.227). Formulate `Mt` properties of the two Example 11.4
automata (`onceTLTS c`: the single-clock automaton `A —a[x ≤ c, x:=0]→ B`, with `c = 1`
the left automaton and `c = 2` the right). The distinguishing property `onceActLate`
— `y in ∃∃(y > 1 ∧ ⟨a⟩tt)`, "after resetting `y`, time can pass beyond `y > 1` with `a`
still enabled" — holds of the right (`c = 2`) automaton but not the left (`c = 1`); the
shared property `onceActNow` — `⟨a⟩tt` — is afforded by both. -/
theorem ex_12_2 :
    ((TLTS.onceTLTS 2).MtSatState (.A 0) TLTS.onceActLate ∧
      ¬ (TLTS.onceTLTS 1).MtSatState (.A 0) TLTS.onceActLate) ∧
    (∀ c, (TLTS.onceTLTS c).MtSatState (.A 0) TLTS.onceActNow) :=
  ⟨⟨TLTS.onceActLate_two, TLTS.not_onceActLate_one⟩, TLTS.onceActNow_mtSat⟩

/-! ## §12.2 Negation in HML with time -/

/-- **Proposition 12.1** (§12.2, p.229). The *negation* `Fᶜ` of a timed HML
formula (De Morgan duality; negating `x = n` needs the disjunction `x < n ∨
x > n`). The library's `Mt.neg`. -/
abbrev mtNeg := @Mt.neg

/-- **Proposition 12.1** (§12.2, p.229). `Fᶜ` exactly complements `F`:
`(p, u) ⊨ Fᶜ` iff `(p, u) ⊭ F`, i.e. `⟦Fᶜ⟧ = ES(Proc) ∖ ⟦F⟧`. -/
theorem prop_12_1 (T : TLTS Proc Act) (F : Mt Act D) (p : Proc) (u : Valuation D) :
    TLTS.MtSat T p u F.neg ↔ ¬ TLTS.MtSat T p u F := TLTS.mtSat_neg T F p u

/-- **Exercise 12.6(2)** (§12.2, p.229). Double negation: `(Fᶜ)ᶜ` and `F` are
satisfied by the same extended states. -/
theorem ex_12_6 (T : TLTS Proc Act) (F : Mt Act D) (p : Proc) (u : Valuation D) :
    TLTS.MtSat T p u F.neg.neg ↔ TLTS.MtSat T p u F := TLTS.mtSat_neg_neg T F p u

/-- **Exercise 12.5** (§12.2, p.229). The formula `∀∀[a]ff ∨ a in ∃∃(a = 1 ∧
⟨a⟩tt)` over one action and one formula clock (both `Unit`). Its negation
`Mt.neg` computes — by `rfl` — to the De Morgan dual `∃∃⟨a⟩tt ∧ a in ∀∀((a < 1 ∨
a > 1) ∨ [a]ff)`, exactly as the book negates the analogous `y in ∃∃(y = 2 ∧
⟨a⟩tt)` in Example 12.1 (note `¬(a = 1)` becomes `a < 1 ∨ a > 1`). -/
theorem ex_12_5 :
    (Mt.or (Mt.forallDelay (Mt.box () Mt.ff))
        (Mt.reset () (Mt.existsDelay (Mt.and (Mt.guard (.atom () .eq 1)) (Mt.dia () Mt.tt))))
      : Mt Unit Unit).neg =
    Mt.and (Mt.existsDelay (Mt.dia () Mt.tt))
      (Mt.reset () (Mt.forallDelay
        (Mt.or (Mt.or (Mt.guard (.atom () .lt 1)) (Mt.guard (.atom () .gt 1)))
          (Mt.box () Mt.ff)))) :=
  rfl

/-- **Exercise 12.7** (§12.2, p.230), the interval-decorated existential delay
operator `∃∃[a,b)F` ("a delay `d` with `a ≤ d < b` is possible, after which `F`
holds"). It is *definable in `Mt`* — the library's `Mt.existsInterval`, which resets
a fresh formula clock to measure the delay against the bounds. -/
abbrev def_12_7_existsInterval := @Mt.existsInterval

/-- **Exercise 12.7** (§12.2, p.230), the interval-decorated universal delay
operator `∀∀(a,b)F` ("`F` holds after every delay strictly between `a` and `b`"),
definable in `Mt`. The library's `Mt.forallInterval`. -/
abbrev def_12_7_forallInterval := @Mt.forallInterval

/-- **Exercise 12.7** (§12.2, p.230), expressibility of `∃∃[a,b)`. The `Mt` encoding
holds exactly when some delay `d ∈ [a,b)` reaches a state satisfying `F`, so the
decorated operator adds no expressive power over `Mt`. -/
theorem ex_12_7_exists (a b : ℕ) (F : Mt Act D) (T : TLTS Proc Act) (p : Proc)
    (v : Valuation (Option D)) :
    TLTS.MtSat T p v (Mt.existsInterval a b F) ↔
      ∃ d p', (a : ℝ≥0) ≤ d ∧ d < b ∧ T.delay p d p' ∧
        TLTS.MtSat T p' (Valuation.add (fun x => v (some x)) d) F :=
  TLTS.mtSat_existsInterval a b F T p v

/-- **Exercise 12.7** (§12.2, p.230), expressibility of `∀∀(a,b)`. The `Mt` encoding
holds exactly when every delay `d` strictly between `a` and `b` reaches a state
satisfying `F`. -/
theorem ex_12_7_forall (a b : ℕ) (F : Mt Act D) (T : TLTS Proc Act) (p : Proc)
    (v : Valuation (Option D)) :
    TLTS.MtSat T p v (Mt.forallInterval a b F) ↔
      ∀ d p', (a : ℝ≥0) < d → d < b → T.delay p d p' →
        TLTS.MtSat T p' (Valuation.add (fun x => v (some x)) d) F :=
  TLTS.mtSat_forallInterval a b F T p v

/-! ## §12.2 Symbolic model checking over regions -/

/-- **Definition 12.5** (§12.2, p.230). *Symbolic satisfaction* `[ℓ, γ] ⊢ F`: an `Mt`
formula checked against a symbolic state — a location `ℓ` and a region `γ` over the
combined clock set `C ⊎ D` (modelled by a representative combined valuation
`Sum.elim v u`). The library's `SymSat`. (The book prints 8 clauses; the `x in F`
reset and atomic guard `g` are the natural `D`-side region operations, and the
action/delay clauses carry the target/pre invariants to match the TLTS semantics.) -/
abbrev def_12_5 := @DeepWiki.ReactiveSystems.SymSat

/-- **Theorem 12.1** (§12.2, p.231). *Symbolic model checking agrees with concrete
model checking*: `((ℓ,v), u) ⊨ F ↔ [ℓ, vu] ⊢ F`, where `vu` combines the automaton
clocks `v` and the formula clocks `u`. The library's `mtSat_iff_symSat`. -/
theorem thm_12_1 {Loc C : Type*} (A : TimedAutomaton Loc Act C) (F : Mt Act D)
    (ℓ : Loc) (v : Valuation C) (u : Valuation D) :
    A.tlts.MtSat (ℓ, v) u F ↔
      DeepWiki.ReactiveSystems.SymSat A ℓ (DeepWiki.ReactiveSystems.combineVal v u) F :=
  DeepWiki.ReactiveSystems.mtSat_iff_symSat A F ℓ v u

/-- **Exercise 12.9** (§12.2, p.231, *for the keenest*). Theorem 12.1 is proved by
structural induction on the formula `F` — exactly how `mtSat_iff_symSat` is
established. -/
theorem ex_12_9 {Loc C : Type*} (A : TimedAutomaton Loc Act C) (F : Mt Act D)
    (ℓ : Loc) (v : Valuation C) (u : Valuation D) :
    A.tlts.MtSat (ℓ, v) u F ↔
      DeepWiki.ReactiveSystems.SymSat A ℓ (DeepWiki.ReactiveSystems.combineVal v u) F :=
  DeepWiki.ReactiveSystems.mtSat_iff_symSat A F ℓ v u

/-- **Theorem 12.2** (§12.2, p.231), region-determinedness (the decidability core).
Symbolic satisfaction `[ℓ, γ] ⊢ F` depends on the combined valuation only through its
region: region-equivalent valuations satisfy the same `Mt` formulae symbolically. With
finitely many regions (Theorem 11.3) this is what makes timed model checking decidable.
The library's `symSat_congr`. -/
theorem thm_12_2_regionDetermined {Loc C : Type*} [Fintype C] [Fintype D]
    (A : TimedAutomaton Loc Act C) (F : Mt Act D) {ℓ : Loc}
    {w w' : Valuation (C ⊕ D)} (h : DeepWiki.ReactiveSystems.RegionEqAll w w') :
    DeepWiki.ReactiveSystems.SymSat A ℓ w F ↔ DeepWiki.ReactiveSystems.SymSat A ℓ w' F :=
  DeepWiki.ReactiveSystems.symSat_congr A F h

/-- **Theorem 12.2** (§12.2, p.231), *bounded* region-determinedness — the finite core
of decidability. When a single finite clamp `cmax` bounds the automaton
(`A.WellFormed (cmax ∘ Sum.inl)`) and the formula's guards (`F.BoundedByD (cmax ∘
Sum.inr)`), region equivalence *at that one clamp* already determines symbolic
satisfaction. This is what `thm_12_2_regionDetermined` needs to descend to the *finite*
quotient `Region cmax`. The library's `symSat_congr_bounded`. -/
theorem thm_12_2_bounded {Loc C : Type*} [Fintype C] [Fintype D]
    (A : TimedAutomaton Loc Act C) {cmax : C ⊕ D → ℕ}
    (wf : A.WellFormed (cmax ∘ Sum.inl)) (F : Mt Act D)
    (hF : F.BoundedByD (cmax ∘ Sum.inr)) {ℓ : Loc} {w w' : Valuation (C ⊕ D)}
    (h : DeepWiki.ReactiveSystems.RegionEq cmax w w') :
    DeepWiki.ReactiveSystems.SymSat A ℓ w F ↔ DeepWiki.ReactiveSystems.SymSat A ℓ w' F :=
  DeepWiki.ReactiveSystems.symSat_congr_bounded A wf F hF h

/-- **Theorem 12.2** (§12.2, p.231), *decidability* form. For any automaton `A`
well-formed for `cmaxC` and any formula `F`, taking the formula clamp `F.formulaCmax`
gives a finite combined clamp under which concrete satisfaction `((ℓ,v),u) ⊨ F` agrees
with symbolic satisfaction on the **finite** bounded region quotient `Region` — so
model checking `F` against `A` reduces to a finite question. The library's
`mtSat_iff_symSatBoundedRegion_formulaCmax`. -/
theorem thm_12_2 {Loc C : Type*} [Fintype C] [Fintype D]
    (A : TimedAutomaton Loc Act C) {cmaxC : C → ℕ} (wf : A.WellFormed cmaxC)
    (F : Mt Act D) (ℓ : Loc) (v : Valuation C) (u : Valuation D) :
    A.tlts.MtSat (ℓ, v) u F ↔
      DeepWiki.ReactiveSystems.SymSatBoundedRegion A
        (cmax := Sum.elim cmaxC F.formulaCmax) wf F
        (DeepWiki.ReactiveSystems.Mt.boundedByD_formulaCmax F) ℓ
        (DeepWiki.ReactiveSystems.region _ (DeepWiki.ReactiveSystems.combineVal v u)) :=
  DeepWiki.ReactiveSystems.mtSat_iff_symSatBoundedRegion_formulaCmax A wf F ℓ v u

/-- **Theorem 12.2** (§12.2, p.231), *executable* decision procedure (delay-free
fragment). For a finite-data automaton `A` and a delay-free formula `F`, satisfaction
`A ⊨ F` reduces to a `Classical`-free Bool computation `SymSatCode` on the all-zero
initial region code — a genuine, `#eval`-able decision procedure. The library's
`satisfiesMt_iff_decide` (with the constructive `Decidable` instance `decSatisfiesMt`). -/
theorem thm_12_2_executable {Loc C : Type*} [Fintype Loc] [DecidableEq Loc] [DecidableEq Act]
    [DecidableEq C] [DecidableEq D] (A : DeepWiki.ReactiveSystems.FinAutomaton Loc Act C)
    (F : Mt Act D) (hF : F.DelayFree) :
    A.toTimedAutomaton.SatisfiesMt F ↔
      DeepWiki.ReactiveSystems.SymSatCode A (Sum.elim A.cmax F.formulaCmax) A.initial
        (DeepWiki.ReactiveSystems.RegionCode.initial _) F = true :=
  DeepWiki.ReactiveSystems.satisfiesMt_iff_decide A F hF

/-- **Theorem 12.2** (§12.2, p.231), *executable* decision for the FULL logic, modulo a
region successor. Given a sound and complete region time-successor enumerator `succ`, `A ⊨ F`
(any `F`, delay quantifiers included) reduces to the Bool computation `SymSatCodeFull` — an
executable decision for the full timed logic. The successor's *existence* is classical
(`timeSuccessor_of_fintype`); a constructive one (the Alur–Dill successor) is the sole open
step. The library's `satisfiesMt_iff_decideFull`. -/
theorem thm_12_2_executable_full {Loc C : Type*} [Fintype Loc] [DecidableEq Loc] [DecidableEq Act]
    [DecidableEq C] [DecidableEq D] (A : DeepWiki.ReactiveSystems.FinAutomaton Loc Act C)
    (F : Mt Act D)
    (succ : DeepWiki.ReactiveSystems.RegionCode (Sum.elim A.cmax F.formulaCmax) →
      List (DeepWiki.ReactiveSystems.RegionCode (Sum.elim A.cmax F.formulaCmax)))
    (hsound : DeepWiki.ReactiveSystems.SuccSound succ)
    (hcomplete : DeepWiki.ReactiveSystems.SuccComplete succ) :
    A.toTimedAutomaton.SatisfiesMt F ↔
      DeepWiki.ReactiveSystems.SymSatCodeFull A succ A.initial
        (DeepWiki.ReactiveSystems.RegionCode.initial _) F = true :=
  DeepWiki.ReactiveSystems.satisfiesMt_iff_decideFull A F succ hsound hcomplete

/-- **Theorem 12.2** (§12.2, p.231), *unconditional* executable decision for the FULL logic.
The conditional `thm_12_2_executable_full`'s sole open step — a constructive sound + complete
region successor — is now discharged by the Alur–Dill `regionCodeDelaySucc`, so `A ⊨ F` (any `F`)
reduces to the Bool computation `SymSatCodeFull A regionCodeDelaySucc …` with NO hypotheses. The
library's `satisfiesMt_iff_decideFull_delaySucc`. -/
theorem thm_12_2_executable_full_unconditional {Loc C : Type*}
    [Fintype Loc] [Fintype C] [Fintype D]
    [DecidableEq Loc] [DecidableEq Act] [DecidableEq C] [DecidableEq D]
    (A : DeepWiki.ReactiveSystems.FinAutomaton Loc Act C) (F : Mt Act D) :
    A.toTimedAutomaton.SatisfiesMt F ↔
      DeepWiki.ReactiveSystems.SymSatCodeFull A
        (cmax := Sum.elim A.cmax F.formulaCmax) DeepWiki.ReactiveSystems.regionCodeDelaySucc
        A.initial (DeepWiki.ReactiveSystems.RegionCode.initial _) F = true :=
  DeepWiki.ReactiveSystems.satisfiesMt_iff_decideFull_delaySucc A F

/-- **Theorem 12.2** (§12.2, p.231), *decidability* corollary. Satisfaction of any timed
formula `F` by a finite timed automaton is decidable — the region method packaged as a
`Decidable` instance. The library's `decSatisfiesMtFull`. -/
def thm_12_2_decidable {Loc C : Type*}
    [Fintype Loc] [Fintype C] [Fintype D]
    [DecidableEq Loc] [DecidableEq Act] [DecidableEq C] [DecidableEq D]
    (A : DeepWiki.ReactiveSystems.FinAutomaton Loc Act C) (F : Mt Act D) :
    Decidable (A.toTimedAutomaton.SatisfiesMt F) :=
  DeepWiki.ReactiveSystems.decSatisfiesMtFull A F

/-- **Exercise 12.8** (§12.2, p.231). For the one-location automaton with invariant
`x ≤ 2` and an `a`-self-loop guarded `x ≤ 1` (resetting `x`), the initial symbolic
state satisfies `y in ∃∃(y = 2 ∧ [a]ff)`: reset `y`, delay `2` (legal under `x ≤ 2`)
to reach `y = 2` with `x = 2`, where `[a]ff` holds vacuously since `a` is disabled
(`x = 2 > 1`). The library's `boundedLoop_symSat`. -/
theorem ex_12_8 :
    DeepWiki.ReactiveSystems.SymSat DeepWiki.ReactiveSystems.boundedLoopAuto ()
      (DeepWiki.ReactiveSystems.combineVal (fun _ => 0) (fun _ => 0))
      DeepWiki.ReactiveSystems.boundedLoopFormula :=
  DeepWiki.ReactiveSystems.boundedLoop_symSat

/-- **Exercise 12.8, via the executable decision procedure.** The same satisfaction —
`y in ∃∃(y = 2 ∧ [a]ff)` on the bounded loop automaton — discharged *by computation* instead of
by hand: `demoAuto` is the `FinAutomaton` form of `boundedLoopAuto`, and the goal closes by
`decide` through the verified executable checker (`satisfiesMt_iff_decideFull_delaySucc`), with no
region argument. The library's `demoAuto_satisfies_boundedLoopFormula`. -/
theorem ex_12_8_executable :
    DeepWiki.ReactiveSystems.demoAuto.toTimedAutomaton.SatisfiesMt
      DeepWiki.ReactiveSystems.boundedLoopFormula :=
  DeepWiki.ReactiveSystems.demoAuto_satisfies_boundedLoopFormula

/-- **Definition 12.5, verbatim region form** (§12.2, p.230). Symbolic satisfaction
`[ℓ, γ] ⊢ F` with `γ` a genuine *region* (an equivalence class of combined `C ⊕ D`
valuations) — `SymSat` descended to the region quotient, well-defined because it is
region-invariant (`thm_12_2_regionDetermined`). The library's `SymSatRegion`. -/
abbrev def_12_5_region := @DeepWiki.ReactiveSystems.SymSatRegion

/-- **Theorem 12.1, region form** (§12.2, p.231). `((ℓ,v), u) ⊨ F` iff the region
symbolic state `[ℓ, ⟦vu⟧]` satisfies `F`. The library's `mtSat_iff_symSatRegion`. -/
theorem thm_12_1_region {Loc C : Type*} [Fintype C] [Fintype D]
    (A : TimedAutomaton Loc Act C) (F : Mt Act D) (ℓ : Loc) (v : Valuation C) (u : Valuation D) :
    A.tlts.MtSat (ℓ, v) u F ↔
      DeepWiki.ReactiveSystems.SymSatRegion A ℓ
        (Quotient.mk (DeepWiki.ReactiveSystems.regionAllSetoid (C ⊕ D))
          (DeepWiki.ReactiveSystems.combineVal v u)) F :=
  DeepWiki.ReactiveSystems.mtSat_iff_symSatRegion A F ℓ v u

/-! ## §12.4 Recursion in HML with time -/

/-- **§12.4, equation (12.2)** (p.237). The running-example property
`TwoAs := [a](y in ∀∀[a](y ≤ 1))` — however the automaton performs two `a`-actions in a row, the
delay between them is at most one time unit — and the running automaton *satisfies* it (the book's
encouraged check), discharged here *by the executable decision procedure* (`decide` through
`satisfiesMt_iff_decideFull_delaySucc`). The library's `twoAsFormula` / `loopAuto_satisfies_twoAs`. -/
theorem eq_12_2 :
    DeepWiki.ReactiveSystems.loopAuto.toTimedAutomaton.SatisfiesMt
      DeepWiki.ReactiveSystems.twoAsFormula :=
  DeepWiki.ReactiveSystems.loopAuto_satisfies_twoAs

/-- **Definition 12.6** (§12.4, p.240). The semantic functional `O_F(S)` of a
recursive timed-HML formula over the powerset lattice of extended states, with the
variable interpreted as `S`. The library's `TLTS.denotMtR`. -/
abbrev def_12_6 := @TLTS.denotMtR

/-- **§12.4** (eq. 12.5, p.241). The meaning of `X =ν F`: the greatest fixed point
of `O_F` (Tarski, `O_F` monotone). The library's `TLTS.recMax`. -/
abbrev def_12_6_recMax := @TLTS.recMax

/-- **§12.4** (p.241). The meaning of `X =μ F`: the least fixed point of `O_F`.
The library's `TLTS.recMin`. -/
abbrev def_12_6_recMin := @TLTS.recMin

/-- **Exercise 12.16** (§12.4, p.240). Calculating one application of `O_F` (Definition 12.6) of
the characteristic-formula body `charBody` — the RHS of equation (12.3) — on the singleton
`{((ℓ, [x=0]), [y=0])} = {(0, y↦0)}` yields `∅`: the `∀∀X` conjunct forces every delay successor
into the set, which no one-element set can satisfy. The library's `TLTS.denotMtR_charBody_initial`. -/
theorem ex_12_16 :
    TLTS.denotMtR TLTS.runTLTS TLTS.charBody {((0 : ℝ≥0), (fun _ => (0 : ℝ≥0)))} = ∅ :=
  TLTS.denotMtR_charBody_initial

/-- **Exercise 12.17** (§12.4, p.240). `O_F` is monotone in the variable's
interpretation, so its greatest and least fixed points exist. -/
theorem ex_12_17 (T : TLTS Proc Act) (F : MtR Act D) : Monotone (TLTS.denotMtR T F) :=
  TLTS.denotMtR_mono T F

/-- **§12.4.2** (p.245). The real-time *invariant* operator `Inv(F) =ν
F ∧ [Act]X ∧ ∀∀X`. The library's `TLTS.mtInv`. -/
abbrev tInv := @TLTS.mtInv

/-- **§12.4.2** (p.245). The real-time *weak until* `F until G =ν
G ∨ (F ∧ [Act]X ∧ ∀∀X)`. The library's `TLTS.mtUntil`. -/
abbrev tUntil := @TLTS.mtUntil

/-- **§12.4.2** (p.245). Fixed-point unfolding of `Inv(F)`: an extended state is
invariant for `F` iff it satisfies `F` now and stays invariant after every action
(clocks kept) and every delay (clocks advanced). -/
theorem tInv_unfold (T : TLTS Proc Act) (F : Mt Act D) (q : Proc × Valuation D) :
    q ∈ TLTS.mtInv T F ↔
      T.MtSat q.1 q.2 F ∧
      (∀ a p', T.act q.1 a p' → (p', q.2) ∈ TLTS.mtInv T F) ∧
      (∀ d p', T.delay q.1 d p' → (p', q.2.add d) ∈ TLTS.mtInv T F) :=
  TLTS.mtInv_unfold T F q

/-- **Exercise 12.11** (§12.3, p.234). If `p` and `q` are timed bisimilar and every
`Mt` formula satisfied by `p` is also satisfied by `q`, then they satisfy the same
`Mt` formulae. (Timed bisimilarity alone already forces the biconditional — the
extra one-directional hypothesis is redundant; discharged by `timedBisimilar_mtIff`.) -/
theorem ex_12_11 (T : TLTS Proc Act) {p q : Proc} (h : TLTS.TimedBisimilar T p q)
    (_hsub : ∀ (u : Valuation D) (F : Mt Act D), TLTS.MtSat T p u F → TLTS.MtSat T q u F)
    (u : Valuation D) (F : Mt Act D) : TLTS.MtSat T p u F ↔ TLTS.MtSat T q u F :=
  TLTS.timedBisimilar_mtIff h u F

/-- **Exercise 12.18** (§12.4, p.240). The powerset of extended states
`P(ES(Proc)) = Set (Proc × (D → ℝ≥0))`, ordered by `⊆`, is a complete lattice (the
lattice on which the operator `O_F` acts). Reuses Mathlib's `Set` complete lattice. -/
theorem ex_12_18 : Nonempty (CompleteLattice (Set (Proc × Valuation D))) := ⟨inferInstance⟩

/-- **Exercise 12.13** (§12.3, p.234). Theorem 12.3 would fail if `p, q` were only
*untimed* bisimilar: the §11.2 witness TLTS has untimed-bisimilar states `A, B`
distinguished by the `Mt` formula `y in ∃∃(y > 1 ∧ ⟨a⟩tt)` (so the answer to the
exercise is "no"). The library's `untimedBisimilar_insufficient_for_timedHML`. -/
theorem ex_12_13 :
    ∃ (Q : Type) (T : TLTS Q Unit) (p q : Q),
      TLTS.UntimedBisimilar T p q ∧
      ∃ F : Mt Unit Unit, TLTS.MtSatState T p F ∧ ¬ TLTS.MtSatState T q F :=
  DeepWiki.ReactiveSystems.untimedBisimilar_insufficient_for_timedHML

/-- **Exercise 12.10** (§12.3, p.233). The two timed automata of Figure 10.2 are not
timed bisimilar, and `y in ∃∃(y > 1)` distinguishes them (the freely-delaying one
satisfies it; the `1`-bounded one does not). The library's `witnessTLTS_not_timedBisimilar_and_distinguishing_formula`. -/
theorem ex_12_10 :
    ¬ DeepWiki.ReactiveSystems.witnessTLTS.TimedBisimilar .A .B ∧
      TLTS.MtSatState DeepWiki.ReactiveSystems.witnessTLTS .A DeepWiki.ReactiveSystems.mt1210 ∧
      ¬ TLTS.MtSatState DeepWiki.ReactiveSystems.witnessTLTS .B DeepWiki.ReactiveSystems.mt1210 :=
  DeepWiki.ReactiveSystems.witnessTLTS_not_timedBisimilar_and_distinguishing_formula

/-- **Exercise 12.1** (§12.1, p.226). If `F` is a closed `Mt` formula (every guard
clock is within the scope of a reset binding it), the extended states satisfying `F`
are independent of the formula-clock valuation `u`. The library's
`mtSat_closed_valuation_indep`. -/
theorem ex_12_1 (T : TLTS Proc Act) {F : Mt Act D} (hF : F.Closed)
    (p : Proc) (u u' : Valuation D) : TLTS.MtSat T p u F ↔ TLTS.MtSat T p u' F :=
  DeepWiki.ReactiveSystems.mtSat_closed_valuation_indep T hF p u u'

/-- **Exercise 12.1** (§12.1, p.226), second part. Valuation-independence does **not**
hold for arbitrary (non-closed) formulae: the guard `y = 1` is satisfied under `y ↦ 1`
but not `y ↦ 0`. The library's `not_mtSat_valuation_indep_general`. -/
theorem ex_12_1_not_general :
    ∃ (T : TLTS Unit Unit) (p : Unit) (F : Mt Unit Unit) (u u' : Valuation Unit),
      ¬ (TLTS.MtSat T p u F ↔ TLTS.MtSat T p u' F) :=
  DeepWiki.ReactiveSystems.not_mtSat_valuation_indep_general

/-- **Exercise 12.3** (§12.1, p.227). Algebraic `Mt`-equivalences holding by the
satisfaction clauses: `y in (y = 0) ≡ tt` and `y in (y > 0) ≡ ff` (a just-reset
clock reads `0`); `[a]tt ≡ tt`; and reset commutation `x in (y in F) ≡ y in (x in F)`.
The library's `resetClockZero_equiv_tt`/`_1b`/`_3`/`_5`. -/
theorem ex_12_3 (T : TLTS Proc Act) (p : Proc) (u : Valuation D) (x y : D) (a : Act)
    (F : Mt Act D) :
    (TLTS.MtSat T p u (Mt.reset y (Mt.guard (ClockConstraint.atom y Cmp.eq 0))) ↔
      TLTS.MtSat T p u Mt.tt) ∧
    (TLTS.MtSat T p u (Mt.reset y (Mt.guard (ClockConstraint.atom y Cmp.gt 0))) ↔
      TLTS.MtSat T p u Mt.ff) ∧
    (TLTS.MtSat T p u (Mt.box a Mt.tt) ↔ TLTS.MtSat T p u Mt.tt) ∧
    (TLTS.MtSat T p u (Mt.reset x (Mt.reset y F)) ↔
      TLTS.MtSat T p u (Mt.reset y (Mt.reset x F))) :=
  ⟨DeepWiki.ReactiveSystems.resetClockZero_equiv_tt y T p u, DeepWiki.ReactiveSystems.resetClockPos_equiv_ff y T p u,
   DeepWiki.ReactiveSystems.box_tt_equiv_tt a T p u, DeepWiki.ReactiveSystems.reset_comm_mt x y F T p u⟩

/-! ## §12.4.1 Characteristic properties for timed bisimilarity (recursion in `Mt`) -/

/-- **Theorem 12.5** (§12.4.1, p.243), running-example instance. The recursively defined formula
`X =max (y ≤ 1 ⇒ ⟨a⟩(y in X)) ∧ [a](y ≤ 1 ∧ (y in X)) ∧ ∀∀X` is characteristic, modulo timed
bisimilarity, for the running-example timed automaton's location: an extended state `(p, u)`
satisfies `X` iff `p` is timed bisimilar to the running example's clock-`u(y)` state. Here the
tested state `q.1` is itself a `runTLTS` state — the `A = runTLTS` instance of the book's
statement (which compares `X_ℓ` against a state of an arbitrary automaton `A`). Discharged by
`TLTS.mem_charFormula_iff_timedBisimilar`. -/
theorem thm_12_5 {q : ℝ≥0 × Valuation Unit} :
    q ∈ TLTS.charFormula ↔ TLTS.TimedBisimilar TLTS.runTLTS q.1 (q.2 ()) :=
  TLTS.mem_charFormula_iff_timedBisimilar

/-- **Exercise 12.19** (§12.4.1, p.244, strongly recommended). Completing the proof of
Theorem 12.5: satisfying the characteristic formula `X` implies timed bisimilarity to the
running example's clock-`u(y)` state (the satisfaction relation is a timed bisimulation).
Discharged by `TLTS.charFormula_complete`. -/
theorem ex_12_19 {q : ℝ≥0 × Valuation Unit} (hq : q ∈ TLTS.charFormula) :
    TLTS.TimedBisimilar TLTS.runTLTS q.1 (q.2 ()) :=
  TLTS.charFormula_complete hq

/-- **Exercise 12.20** (§12.4.1, p.244). Characteristic formulae for the Example 11.4 automaton
(action guard `x ≤ c`), with a version of Theorem 12.5 — and *no recursion is needed*, since the
action graph is acyclic. The live location's formula `charA c` characterizes its
timed-bisimilarity class: `(q, [y = d]) ⊨ charA c ↔ q ~ A d` (discharged by
`TLTS.mtSat_charA_iff`); the dead location's `charB := ∀∀[a]ff` characterizes the dead class
(`TLTS.mtSat_charB_iff`). -/
theorem ex_12_20 {c : ℕ} {q : TLTS.Once} {d : ℝ≥0} :
    (TLTS.onceTLTS c).MtSat q (fun _ => d) (TLTS.charA c) ↔
      TLTS.TimedBisimilar (TLTS.onceTLTS c) q (TLTS.Once.A d) :=
  TLTS.mtSat_charA_iff

/-- **Exercise 12.21** (§12.4.1, p.245), the definition. A *timed simulation* is the
forward half of a timed bisimulation — simulation over the combined action/delay
labels; `s₁` is timed simulated by `s₂` when one relates them. The library's
`TLTS.TimedSimulated`. -/
abbrev def_12_21_timedSimulated := @TLTS.TimedSimulated

/-- **Exercise 12.21** (§12.4.1, p.245). The characteristic formula for the running
example *modulo timed simulation*: `TLTS.charSimFormula` is the bisimulation
characteristic formula with the universal `[a]` conjunct dropped. The simulation
analogue of Theorem 12.5 holds — an extended state satisfies it iff the running
example's clock-`u(y)` state is timed simulated by it. The library's
`TLTS.mem_charSimFormula_iff_simulated`. -/
theorem ex_12_21 {q : ℝ≥0 × Valuation Unit} :
    q ∈ TLTS.charSimFormula ↔ TLTS.TimedSimulated TLTS.runTLTS (q.2 ()) q.1 :=
  TLTS.mem_charSimFormula_iff_simulated

end DeepWiki.Rs
