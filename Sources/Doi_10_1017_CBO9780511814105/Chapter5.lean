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

/-! ## §5.2 Hennessy–Milner theorem -/

/-- **Definition 5.3** (§5.2, p.98). An LTS is image finite when every state has
finitely many `a`-successors for each `a`. The library's `LTS.ImageFinite`. -/
abbrev def_5_3 := @LTS.ImageFinite

/-- **Theorem 5.3** (Hennessy–Milner theorem, §5.2, p.98). On an image-finite
LTS, strong bisimilarity coincides with HML-equivalence: `p ~ q` iff `p` and `q`
satisfy exactly the same Hennessy–Milner formulae. -/
theorem thm_5_3 (L : LTS Proc Act) (hfin : LTS.ImageFinite L) (p q : Proc) :
    (p ~[L] q) ↔ LTS.HMLEquiv L p q := LTS.hennessyMilner hfin p q

/-- **Theorem 5.3**, easy direction (§5.2, p.98). Bisimilar states satisfy the
same formulae (holds for every LTS). -/
theorem thm_5_3_soundness (L : LTS Proc Act) {p q : Proc} (h : p ~[L] q) :
    LTS.HMLEquiv L p q := LTS.bisimilar_hmlEquiv h

/-- **Theorem 5.3**, hard direction (§5.2, p.98). On an image-finite LTS,
HML-equivalent states are bisimilar. -/
theorem thm_5_3_completeness (L : LTS Proc Act) (hfin : LTS.ImageFinite L) {p q : Proc}
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

end DeepWiki.Rs
