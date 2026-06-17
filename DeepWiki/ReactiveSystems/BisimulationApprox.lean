import DeepWiki.ReactiveSystems.BisimulationFixedPoint

/-! # Bisimilarity approximants
The stratified approximants `∼ᵢ = Fⁱ(⊤)` of strong bisimilarity:
each is an equivalence relation, they form a decreasing chain, and strong
bisimilarity refines every one of them (being the greatest fixed point of `F`). -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Proc Act : Type*}

/-- `F` preserves reflexivity. -/
theorem bisimFunctional_refl (L : LTS Proc Act) {R : Proc → Proc → Prop}
    (hR : ∀ p, R p p) : ∀ p, bisimFunctional L R p p :=
  fun _ => ⟨fun _ p' hp => ⟨p', hp, hR p'⟩, fun _ q' hq => ⟨q', hq, hR q'⟩⟩

/-- The `i`-th bisimilarity approximant `∼ᵢ = Fⁱ(⊤)`. -/
def bisimApprox (L : LTS Proc Act) (i : ℕ) : Proc → Proc → Prop :=
  (bisimFunctional L)^[i] ⊤

/-- The base approximant `∼₀ = ⊤` relates all processes. -/
@[simp] theorem bisimApprox_zero (L : LTS Proc Act) : bisimApprox L 0 = ⊤ := rfl

/-- The successor approximant `∼_{i+1} = F(∼ᵢ)` applies the bisimulation functional. -/
theorem bisimApprox_succ (L : LTS Proc Act) (i : ℕ) :
    bisimApprox L (i + 1) = bisimFunctional L (bisimApprox L i) :=
  Function.iterate_succ_apply' _ _ _

/-- Each approximant is an equivalence relation. -/
theorem bisimApprox_equivalence (L : LTS Proc Act) (i : ℕ) :
    Equivalence (bisimApprox L i) := by
  induction i with
  | zero => exact ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩
  | succ n ih =>
      rw [bisimApprox_succ]
      refine ⟨bisimFunctional_refl L ih.refl, ?_, ?_⟩
      · intro p q hpq
        exact ⟨fun a p' hp' => (hpq.2 a p' hp').imp fun _ h => ⟨h.1, ih.symm h.2⟩,
               fun a q' hq' => (hpq.1 a q' hq').imp fun _ h => ⟨h.1, ih.symm h.2⟩⟩
      · intro p q r hpq hqr
        refine ⟨fun a p' hp' => ?_, fun a r' hr' => ?_⟩
        · obtain ⟨q', hq', h1⟩ := hpq.1 a p' hp'
          obtain ⟨r', hr', h2⟩ := hqr.1 a q' hq'
          exact ⟨r', hr', ih.trans h1 h2⟩
        · obtain ⟨q', hq', h2⟩ := hqr.2 a r' hr'
          obtain ⟨p', hp', h1⟩ := hpq.2 a q' hq'
          exact ⟨p', hp', ih.trans h1 h2⟩

/-- The approximants form a decreasing chain: `∼_{i+1} ⊆ ∼ᵢ`. -/
theorem bisimApprox_antitone (L : LTS Proc Act) (i : ℕ) :
    bisimApprox L (i + 1) ≤ bisimApprox L i := by
  induction i with
  | zero => exact le_top
  | succ n ih =>
      rw [bisimApprox_succ]
      conv_rhs => rw [bisimApprox_succ]
      exact (bisimFunctional L).monotone ih

/-- Strong bisimilarity refines every approximant: `∼ ⊆ ∼ᵢ`. -/
theorem bisimilar_le_bisimApprox (L : LTS Proc Act) (i : ℕ) :
    Bisimilar L ≤ bisimApprox L i := by
  rw [bisimilar_eq_gfp]
  induction i with
  | zero => exact le_top
  | succ n ih =>
      rw [bisimApprox_succ]
      have h : bisimFunctional L (bisimFunctional L).gfp ≤ bisimFunctional L (bisimApprox L n) :=
        (bisimFunctional L).monotone' ih
      rwa [(bisimFunctional L).map_gfp] at h

end LTS

end DeepWiki.ReactiveSystems
