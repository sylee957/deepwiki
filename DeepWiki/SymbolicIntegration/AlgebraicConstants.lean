import DeepWiki.SymbolicIntegration.Constants

/-! # Constants of differential extensions (Bronstein §3.3)
The Wronskian criterion for linear dependence over the constants, in full generality, and the
permanence of linear independence over the constants under differential extension (Corollary
3.3.2). The hard direction of the Wronskian test — a vanishing Wronskian forces linear
dependence over the *constants* — is proved by induction on the number of functions, recasting
the classical analytic argument purely algebraically. -/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

section Wronskian
variable {F : Type*} [Field F] [Differential F]

/-- `linearDependentOverConst y` : the family `y` is linearly dependent over the constants —
some nonzero constant tuple `c` (`∀ j, (c j)′ = 0`, `c ≠ 0`) has `∑ⱼ cⱼ·yⱼ = 0`. -/
def linearDependentOverConst {n : ℕ} (y : Fin n → F) : Prop :=
  ∃ c : Fin n → F, (∀ j, (c j)′ = 0) ∧ c ≠ 0 ∧ ∑ j, c j * y j = 0

/-- Dropping an index keeps a constant dependence: a constant dependence of the `n` functions
`y ∘ j₀.succAbove` lifts to a constant dependence of all `n+1` functions `y` (pad the `j₀`
coordinate with `0`). -/
theorem linearDependentOverConst_succAbove {n : ℕ} (y : Fin (n + 1) → F) (j₀ : Fin (n + 1))
    (h : linearDependentOverConst (fun i : Fin n => y (j₀.succAbove i))) :
    linearDependentOverConst y := by
  obtain ⟨d, hd, hdne, hdep⟩ := h
  refine ⟨Fin.insertNth j₀ 0 d, ?_, ?_, ?_⟩
  · intro k
    refine j₀.succAboveCases ?_ (fun i => ?_) k
    · rw [Fin.insertNth_apply_same]; simp
    · rw [Fin.insertNth_apply_succAbove]; exact hd i
  · intro hcontra
    apply hdne
    funext i
    have := congrFun hcontra (j₀.succAbove i)
    rwa [Fin.insertNth_apply_succAbove, Pi.zero_apply] at this
  · rw [Fin.sum_univ_succAbove _ j₀, Fin.insertNth_apply_same, zero_mul, zero_add]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hdep
    rw [Fin.insertNth_apply_succAbove]

end Wronskian

end DeepWiki.SymbolicIntegration
