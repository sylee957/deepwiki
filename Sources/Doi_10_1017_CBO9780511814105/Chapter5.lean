import DeepWiki.ReactiveSystems.HennessyMilner
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 5: Hennessy–Milner logic
Book-numbered restatements for Chapter 5, discharged by the
`DeepWiki.ReactiveSystems` library, with solved exercises. -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems
open DeepWiki.ReactiveSystems.LTS

variable {Proc Act : Type*}

/-! ## §5.1 Introduction to Hennessy–Milner logic -/

/-- **Definition 5.1** (§5.1, p.90). Hennessy–Milner logic formulae
`F ::= tt ∣ ff ∣ F∧F ∣ F∨F ∣ ⟨a⟩F ∣ [a]F`. The library's `HML`. -/
abbrev def_5_1 := @HML

/-- **Definition 5.2** (§5.1, p.91), satisfaction `p ⊨ F`. The library's
`LTS.Sat`. -/
abbrev def_5_2 := @LTS.Sat

/-- **Definition 5.2** (§5.1, p.91), the denotation `⟦F⟧` as the set of states
satisfying `F`. The library's `LTS.denot`. -/
abbrev def_5_2_denot := @LTS.denot

/-- **Proposition 5.1** (§5.1, p.96). The defining clauses of satisfaction:
`tt`/`ff`, the two boolean connectives, and the two modalities behave as their
intended semantics. (Each clause holds definitionally; proved by structural
induction in the book.) -/
theorem prop_5_1 (L : LTS Proc Act) (p : Proc) (a : Act) (F G : HML Act) :
    ((p ⊨[L] HML.tt) ↔ True) ∧ ((p ⊨[L] HML.ff) ↔ False) ∧
      ((p ⊨[L] F.and G) ↔ (p ⊨[L] F) ∧ (p ⊨[L] G)) ∧
      ((p ⊨[L] F.or G) ↔ (p ⊨[L] F) ∨ (p ⊨[L] G)) ∧
      ((p ⊨[L] HML.dia a F) ↔ ∃ p', (L ⊢ p ⟶[a] p') ∧ (p' ⊨[L] F)) ∧
      ((p ⊨[L] HML.box a F) ↔ ∀ p', (L ⊢ p ⟶[a] p') → (p' ⊨[L] F)) :=
  ⟨LTS.sat_tt L p, LTS.sat_ff L p, LTS.sat_and L p F G, LTS.sat_or L p F G,
   LTS.sat_dia L p a F, LTS.sat_box L p a F⟩

/-! ## §5.2 Hennessy–Milner theorem -/

/-- **Definition 5.3** (§5.2, p.98). An LTS is image finite when every state has
finitely many `a`-successors for each `a`. The library's `LTS.ImageFinite`. -/
abbrev def_5_3 := @LTS.ImageFinite

/-- **Theorem 5.1** (Hennessy–Milner theorem, §5.2, p.98). On an image-finite
LTS, strong bisimilarity coincides with HML-equivalence: `p ~ q` iff `p` and `q`
satisfy exactly the same Hennessy–Milner formulae. -/
theorem thm_5_1 (L : LTS Proc Act) (hfin : LTS.ImageFinite L) (p q : Proc) :
    (p ~[L] q) ↔ LTS.HMLEquiv L p q := LTS.hennessyMilner hfin p q

/-- **Theorem 5.1**, easy direction (§5.2, p.98). Bisimilar states satisfy the
same formulae (holds for every LTS). -/
theorem thm_5_1_soundness (L : LTS Proc Act) {p q : Proc} (h : p ~[L] q) :
    LTS.HMLEquiv L p q := LTS.bisimilar_hmlEquiv h

/-- **Theorem 5.1**, hard direction (§5.2, p.98). On an image-finite LTS,
HML-equivalent states are bisimilar. -/
theorem thm_5_1_completeness (L : LTS Proc Act) (hfin : LTS.ImageFinite L) {p q : Proc}
    (h : LTS.HMLEquiv L p q) : p ~[L] q := LTS.hmlEquiv_bisimilar hfin h

/-! ## Solved exercises -/

/-- **Exercise 5.2** (§5.1, p.94). `⟨a⟩tt` expresses that a process can
immediately perform an `a`-action. -/
theorem ex_5_2_can (L : LTS Proc Act) (p : Proc) (a : Act) :
    (p ⊨[L] HML.dia a HML.tt) ↔ ∃ p', (L ⊢ p ⟶[a] p') := LTS.sat_dia_tt L p a

/-- **Exercise 5.2** (§5.1, p.94). `[a]ff` expresses that a process cannot
perform any `a`-action. -/
theorem ex_5_2_cannot (L : LTS Proc Act) (p : Proc) (a : Act) :
    (p ⊨[L] HML.box a HML.ff) ↔ L.Refuses p a := LTS.sat_box_ff L p a

/-- **Exercise 5.8(2)** (§5.1, p.97). The denotation of the dual is the
complement: `⟦F̄⟧ = ⟦F⟧ᶜ`. -/
theorem ex_5_8 (L : LTS Proc Act) (F : HML Act) :
    LTS.denot L F.neg = (LTS.denot L F)ᶜ := LTS.denot_neg L F

/-- **Exercise 5.8(2)** (§5.1, p.97), expressibility form: negation is definable
in HML — every formula has one whose denotation is its complement. -/
theorem ex_5_8_expressible (L : LTS Proc Act) (F : HML Act) :
    ∃ G, LTS.denot L G = (LTS.denot L F)ᶜ := ⟨F.neg, LTS.denot_neg L F⟩

/-- **Exercise 5.6** (§5.1). The operational satisfaction relation `p ⊨ F` and
membership in the denotation `⟦F⟧` coincide. -/
theorem ex_5_6 (L : LTS Proc Act) (p : Proc) (F : HML Act) :
    (p ⊨[L] F) ↔ p ∈ LTS.denot L F := Iff.rfl

/-! **Exercise 5.12** (`~ = ⋂ᵢ ∼ᵢ` on image-finite LTSs) and **Exercise 5.13**
(the non-image-finite counterexample showing the Hennessy–Milner theorem's
hypothesis is sharp) require, respectively, an infinite-pigeonhole/König argument
over the finite successor set and a modal-depth construction; they are deferred. -/

end DeepWiki.Rs
