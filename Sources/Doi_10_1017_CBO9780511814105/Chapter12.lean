import DeepWiki.ReactiveSystems.TimedHennessyMilner
import DeepWiki.ReactiveSystems.TimedHennessyMilnerClocks
import DeepWiki.ReactiveSystems.TimedHmlNegation
import DeepWiki.ReactiveSystems.TimedHmlRecursion
import DeepWiki.ReactiveSystems.TimedBisimulationHmlStrict
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

end DeepWiki.Rs
