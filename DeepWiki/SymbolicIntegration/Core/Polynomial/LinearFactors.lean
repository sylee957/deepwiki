import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

/-! # Polynomial linear-factor facts

Reusable facts about powers of `X - C α`. -/

namespace DeepWiki.SymbolicIntegration

open Polynomial

variable {K : Type*} [Field K]

/-- `M` is coprime to `(X - C α)^i` when `M.eval α ≠ 0`. -/
theorem isCoprime_M_X_sub_C_pow {M : K[X]} {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    IsCoprime M ((Polynomial.X - Polynomial.C α) ^ i) := by
  have hnd : ¬ (Polynomial.X - Polynomial.C α) ∣ M := by
    rw [dvd_iff_isRoot]; exact fun h => hM h
  exact (((prime_X_sub_C α).coprime_iff_not_dvd.mpr hnd).symm).pow_right

end DeepWiki.SymbolicIntegration
