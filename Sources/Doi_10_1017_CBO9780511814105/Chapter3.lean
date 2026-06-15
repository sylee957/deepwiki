import DeepWiki.ReactiveSystems.Bisimulation
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 3: Behavioural equivalences
Book-numbered restatements for Chapter 3 (strong bisimilarity), discharged by
the `DeepWiki.ReactiveSystems` library. -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems

variable {Proc Act : Type*}

/-! ## §3.3 Strong bisimilarity -/

/-- **Definition 3.2** (§3.3, p.37). A strong bisimulation `R`: whenever `R p q`,
every `a`-move of `p` is matched by an `a`-move of `q` into `R`, and
symmetrically. The library's `LTS.IsBisimulation`. -/
abbrev def_3_2 := @LTS.IsBisimulation

/-- **Definition 3.2** (§3.3, p.37), strong bisimilarity `~`: `p ~ q` iff some
strong bisimulation relates `p` and `q`. The library's `LTS.Bisimilar`. -/
abbrev def_3_2_bisimilar := @LTS.Bisimilar

/-- **Theorem 3.1**, part 1 (§3.3, p.42). For any LTS, `~` is an equivalence
relation. Discharged by `LTS.equivalence_bisimilar`. -/
theorem thm_3_1_equivalence (L : LTS Proc Act) : Equivalence (LTS.Bisimilar L) :=
  LTS.equivalence_bisimilar

/-- **Theorem 3.1**, part 2 (§3.3, p.42). `~` is the largest strong bisimulation:
it is itself a strong bisimulation, and contains every strong bisimulation. -/
theorem thm_3_1_largest (L : LTS Proc Act) :
    LTS.IsBisimulation L (LTS.Bisimilar L) ∧
      ∀ R, LTS.IsBisimulation L R → ∀ ⦃p q⦄, R p q → LTS.Bisimilar L p q :=
  ⟨LTS.isBisimulation_bisimilar, fun _ hR => hR.le_bisimilar⟩

/-- **Theorem 3.1**, part 3 (§3.3, p.42, eq. 3.3). `~` satisfies the
bisimulation transfer property: `p ~ q` iff every move of one side is matched by
a `~`-related move of the other. Discharged by `LTS.bisimilar_iff`. -/
theorem thm_3_1_transfer (L : LTS Proc Act) (p q : Proc) :
    LTS.Bisimilar L p q ↔
      (∀ a p', L.step p a p' → ∃ q', L.step q a q' ∧ LTS.Bisimilar L p' q') ∧
      (∀ a q', L.step q a q' → ∃ p', L.step p a p' ∧ LTS.Bisimilar L p' q') :=
  LTS.bisimilar_iff p q

end DeepWiki.Rs
