import DeepWiki.ReactiveSystems.HmlCharacteristicSyntactic
import DeepWiki.ReactiveSystems.Bisimulation
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Set.Insert

/-! # Exercise 6.13 — characteristic formulae for Figure 6.1
Figure 6.1 is the LTS `p —a→ p`, `q —a→ q`, `q —a→ r` (`r` dead). The three states
are pairwise non-bisimilar (`p` loops forever, `q` may reach the dead `r`, `r` is
dead), so each characteristic formula `charSys` pins down exactly its own state:
`⟦charSys p⟧ = {p}` and `⟦charSys q⟧ = {q}`. -/

namespace DeepWiki.ReactiveSystems

open LTS

/-- The single action `a` of Figure 6.1. -/
inductive A61 | a
  deriving DecidableEq, Fintype

/-- States of Figure 6.1. -/
inductive P61 | p | q | r
  deriving DecidableEq, Fintype

/-- Edges: `p —a→ p`, `q —a→ q`, `q —a→ r`; `r` dead. -/
def edge61 : P61 → A61 → P61 → Bool
  | .p, .a, .p => true
  | .q, .a, .q => true
  | .q, .a, .r => true
  | _, _, _ => false

/-- The Figure 6.1 LTS (reducible, so the characteristic-formula machinery has
its decidable-step instance and step facts are decidable). -/
abbrev L61 : LTS P61 A61 := ⟨fun u y v => edge61 u y v = true⟩

/-- A state with an outgoing `a` is never bisimilar to the dead `r`. -/
theorem not_bisim_r {x x' : P61} (h : L61.step x A61.a x') : ¬ (x ~[L61] P61.r) :=
  not_bisim_dead_of_step h (by decide)

/-- `p ≁ q`: `q —a→ r` forces `p —a→ p` with `p ~ r`, impossible. -/
theorem not_bisim_pq : ¬ (P61.p ~[L61] P61.q) := by
  intro hb
  obtain ⟨p', hp', hb'⟩ := ((bisimilar_iff _ _).mp hb).2 A61.a P61.r (by decide)
  obtain rfl : p' = P61.p := (by decide : ∀ z, L61.step P61.p A61.a z → z = P61.p) p' hp'
  exact not_bisim_r (by decide : L61.step P61.p A61.a P61.p) hb'

/-- On Figure 6.1, bisimilarity from `p` is the identity: `p ~ s ↔ s = p`. -/
theorem bisim_p_iff (s : P61) : (P61.p ~[L61] s) ↔ s = P61.p := by
  refine ⟨fun hb => ?_, fun h => h ▸ bisimilar_refl _⟩
  cases s with
  | p => rfl
  | q => exact absurd hb not_bisim_pq
  | r => exact absurd hb (not_bisim_r (by decide : L61.step P61.p A61.a P61.p))

/-- On Figure 6.1, bisimilarity from `q` is the identity: `q ~ s ↔ s = q`. -/
theorem bisim_q_iff (s : P61) : (P61.q ~[L61] s) ↔ s = P61.q := by
  refine ⟨fun hb => ?_, fun h => h ▸ bisimilar_refl _⟩
  cases s with
  | p => exact absurd hb.symm not_bisim_pq
  | q => rfl
  | r => exact absurd hb (not_bisim_r (by decide : L61.step P61.q A61.a P61.q))

/-- **Exercise 6.13** (§6.6, p.134). The characteristic formula of `p` in Figure 6.1
is satisfied by exactly `p`: `⟦charSys p⟧ = {p}` (since `p` is bisimilar to no other
state). -/
theorem charSys_p61_p_singleton : sysMax L61 (charSys L61) P61.p = {P61.p} := by
  ext s
  rw [Set.mem_singleton_iff, charSys_characterizes]
  exact bisim_p_iff s

/-- **Exercise 6.13** (§6.6, p.134). The characteristic formula of `q` in Figure 6.1
is satisfied by exactly `q`: `⟦charSys q⟧ = {q}`. -/
theorem charSys_p61_q_singleton : sysMax L61 (charSys L61) P61.q = {P61.q} := by
  ext s
  rw [Set.mem_singleton_iff, charSys_characterizes]
  exact bisim_q_iff s

end DeepWiki.ReactiveSystems
