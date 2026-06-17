import DeepWiki.ReactiveSystems.TimedHml
import DeepWiki.ReactiveSystems.TimedHmlClocks
import DeepWiki.ReactiveSystems.TimedHmlNegation
import DeepWiki.ReactiveSystems.TimedHmlRecursion
import DeepWiki.ReactiveSystems.TimedBisimulationHmlStrict
import DeepWiki.ReactiveSystems.TimedHmlExamples
import DeepWiki.ReactiveSystems.TimedHmlClosedFormulae
import DeepWiki.ReactiveSystems.TimedHmlEquivalences
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 12: Hennessy–Milner logic with time
Book-numbered restatements for the timed logic `Mt` with formula clocks (§12.1,
Definitions 12.1–12.3) and the soundness half of the timed Hennessy–Milner
characterisation (§12.3), discharged by the `DeepWiki.ReactiveSystems` library.
(The completeness half via regions is future work.) -/

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

/-! ## §12.4 Recursion in HML with time -/

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

end DeepWiki.Rs
