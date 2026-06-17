import Mathlib.Order.FixedPoints
import Mathlib.Order.Iterate
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Fintype.Powerset

/-! # Fixed points by finite iteration (Theorem 4.2 / Theorem 6.1)
On a *finite* complete lattice, the least and greatest fixed points of a monotone
map are reached by finite iteration from `⊥` and `⊤`: the ascending chain
`⊥ ≼ f⊥ ≼ ⋯` (resp. descending `⊤ ≽ f⊤ ≽ ⋯`) is eventually constant, and its limit
is the fixed point. This is the engine behind the model-checking iterations of
Chapters 4 and 6. -/

namespace DeepWiki.ReactiveSystems

variable {D : Type*} [CompleteLattice D] [Finite D]

/-- **Theorem 4.2** (least fixed point). `lfp f = fᵐ(⊥)` for some `m`. -/
theorem lfp_eq_iterate_bot (f : D →o D) : ∃ m, OrderHom.lfp f = f^[m] ⊥ := by
  have hmono : Monotone (fun n => f^[n] (⊥ : D)) := f.mono.monotone_iterate_of_le_map bot_le
  obtain ⟨m, hm⟩ := WellFoundedGT.monotone_chain_condition ⟨_, hmono⟩
  have heq : f^[m] (⊥ : D) = f (f^[m] ⊥) := by
    have := hm (m + 1) (Nat.le_succ m)
    simpa [Function.iterate_succ_apply', OrderHom.coe_mk] using this
  have hle : ∀ k, f^[k] (⊥ : D) ≤ OrderHom.lfp f := by
    intro k
    induction k with
    | zero => exact bot_le
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (f.mono ih).trans (OrderHom.map_lfp f).le
  exact ⟨m, le_antisymm (f.lfp_le heq.ge) (hle m)⟩

/-- **Theorem 4.2** (greatest fixed point). `gfp f = fᴹ(⊤)` for some `M`. -/
theorem gfp_eq_iterate_top (f : D →o D) : ∃ M, OrderHom.gfp f = f^[M] ⊤ := by
  have hanti : Antitone (fun n => f^[n] (⊤ : D)) := f.mono.antitone_iterate_of_map_le le_top
  obtain ⟨M, hM⟩ := WellFoundedLT.antitone_chain_condition hanti
  have heq : f^[M] (⊤ : D) = f (f^[M] ⊤) := by
    have := hM (M + 1) (Nat.le_succ M)
    simpa [Function.iterate_succ_apply'] using this
  have hge : ∀ k, OrderHom.gfp f ≤ f^[k] (⊤ : D) := by
    intro k
    induction k with
    | zero => exact le_top
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (OrderHom.map_gfp f).ge.trans (f.mono ih)
  exact ⟨M, le_antisymm (hge M) (f.le_gfp heq.le)⟩

end DeepWiki.ReactiveSystems
