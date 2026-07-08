import DeepWiki.SymbolicIntegration.Computable.Algebraic.ZassenhausDecider.Iteration

/-! # Zassenhaus coefficient bounds

Mignotte-style coefficient bounds for the Zassenhaus recombination stage.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-- The maximum absolute value of the coefficients of a list-poly (`0` for the empty list). -/
def maxAbsCoeff (f : List ℤ) : ℕ :=
  f.foldr (fun a acc => max a.natAbs acc) 0

/-- Mignotte coefficient over-bound `2^(f.length+1) · (maxAbsCoeff f + 1)` on any `ℤ`-factor of `f`. -/
def mignotteBound (f : List ℤ) : ℕ :=
  2 ^ (f.length + 1) * (maxAbsCoeff f + 1)

/-- `maxAbsCoeff` bounds every coefficient: `|f.getD i 0| ≤ maxAbsCoeff f` for all `i`. -/
theorem natAbs_getD_le_maxAbsCoeff (f : List ℤ) (i : ℕ) :
    (f.getD i 0).natAbs ≤ maxAbsCoeff f := by
  induction f generalizing i with
  | nil => simp [maxAbsCoeff, List.getD]
  | cons a as ih =>
    rw [maxAbsCoeff, List.foldr_cons, ← maxAbsCoeff]
    cases i with
    | zero =>
      rw [List.getD_cons_zero]
      exact le_max_left _ _
    | succ j =>
      rw [List.getD_cons_succ]
      exact le_trans (ih j) (le_max_right _ _)

/-- The Mignotte bound is positive (the `+1` and the power of two). -/
theorem mignotteBound_pos (f : List ℤ) : 0 < mignotteBound f := by
  rw [mignotteBound]
  have h2 : 0 < 2 ^ (f.length + 1) := Nat.two_pow_pos _
  exact Nat.mul_pos h2 (by omega)

/-- `maxAbsCoeff f ≤ mignotteBound f`: the bound dominates the polynomial's own coefficients. -/
theorem maxAbsCoeff_le_mignotteBound (f : List ℤ) : maxAbsCoeff f ≤ mignotteBound f := by
  rw [mignotteBound]
  calc maxAbsCoeff f ≤ maxAbsCoeff f + 1 := by omega
    _ ≤ 1 * (maxAbsCoeff f + 1) := by rw [one_mul]
    _ ≤ 2 ^ (f.length + 1) * (maxAbsCoeff f + 1) :=
        Nat.mul_le_mul_right _ (Nat.one_le_two_pow)

end DeepWiki.SymbolicIntegration
