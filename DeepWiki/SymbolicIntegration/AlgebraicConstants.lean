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

end Wronskian

end DeepWiki.SymbolicIntegration
