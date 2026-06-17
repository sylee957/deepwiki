import DeepWiki.ReactiveSystems.BisimulationApprox
import DeepWiki.ReactiveSystems.HennessyMilner
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Nat

/-! # Bisimilarity as the intersection of approximants
Over an image-finite LTS, strong bisimilarity coincides with the intersection of
the stratified approximants `∼ᵢ`: `p ~ q` iff `p ∼ᵢ q` for all
`i`. The non-trivial direction is a König/pigeonhole argument — image-finiteness
makes the set of `a`-successors of `q` finite, so a single successor matches `p'`
at infinitely many (hence, by antitonicity, all) approximant levels. -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Proc Act : Type*}

/-- On an image-finite LTS, strong bisimilarity equals the
intersection of the stratified approximants: `p ~ q` iff `p ∼ᵢ q` for every `i`. -/
theorem bisimilar_iff_forall_bisimApprox (L : LTS Proc Act)
    (hfin : L.ImageFinite) (p q : Proc) :
    (p ~[L] q) ↔ ∀ i, bisimApprox L i p q := by
  refine ⟨fun h i => bisimilar_le_bisimApprox L i p q h, fun h => ?_⟩
  set R : Proc → Proc → Prop := fun p q => ∀ i, bisimApprox L i p q with hRdef
  have key : ∀ {p q : Proc}, R p q → ∀ (a : Act) (p' : Proc), L.step p a p' →
      ∃ q', L.step q a q' ∧ R p' q' := by
    intro p q hR a p' hstep
    -- For each `i`, the `(i+1)`-approximant exposes a matching `a`-successor of `q`.
    have hmatch : ∀ i, ∃ q', L.step q a q' ∧ bisimApprox L i p' q' := by
      intro i
      have hi := hR (i + 1)
      rw [bisimApprox_succ] at hi
      exact hi.1 a p' hstep
    choose qf hqf hqfrel using hmatch
    -- `qf` lands in the finite successor set; pigeonhole repeats one value.
    have hfiber : ∃ y, L.step q a y ∧ {i | qf i = y}.Infinite := by
      by_contra hcon
      push Not at hcon
      have hfin' : (Set.univ : Set ℕ).Finite := by
        have hbi := (hfin q a).biUnion
          (t := fun y => {i | qf i = y})
          (fun y hy => hcon y hy)
        refine Set.Finite.subset hbi ?_
        intro i _
        exact Set.mem_biUnion (hqf i) rfl
      exact Set.infinite_univ hfin'
    obtain ⟨y, hystep, hyinf⟩ := hfiber
    refine ⟨y, hystep, fun j => ?_⟩
    obtain ⟨i, hi_mem, hji⟩ := hyinf.exists_gt j
    have hqfi : qf i = y := hi_mem
    have hrel := hqfrel i
    rw [hqfi] at hrel
    exact bisimApprox_le_of_le L (le_of_lt hji) p' y hrel
  have hbisim : IsBisimulation L R := by
    intro p q hR
    refine ⟨key hR, fun a q' hstep => ?_⟩
    have hRsymm : R q p := fun i => (bisimApprox_equivalence L i).symm (hR i)
    obtain ⟨p', hp', hrel⟩ := key hRsymm a q' hstep
    exact ⟨p', hp', fun i => (bisimApprox_equivalence L i).symm (hrel i)⟩
  exact hbisim.le_bisimilar h

end LTS

end DeepWiki.ReactiveSystems
