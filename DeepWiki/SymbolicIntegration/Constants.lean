import DeepWiki.SymbolicIntegration.DifferentialFields
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Constants and extensions (Bronstein §3.3)
How the constant subfield behaves under differential extensions, and the Wronskian test for
linear dependence over the constants. We prove that constants stay constant (Lemma 3.3.1) and
the easy direction of the Wronskian criterion (Lemma 3.3.5): linear dependence over the constants
forces the Wronskian to vanish. The converse (and the algebraic-constants lemmas 3.3.2–3.3.6) are
tracked as remaining work. -/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

section Extension
variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E]

/-- **Lemma 3.3.1** (§3.3): constants stay constant in a differential extension —
if `c′ = 0` in `F` then `(algebraMap F E c)′ = 0` (so `Const_D F ⊆ Const_Δ E`). -/
theorem deriv_algebraMap_eq_zero {c : F} (hc : c′ = 0) : (algebraMap F E c)′ = 0 := by
  rw [deriv_algebraMap, hc, map_zero]

end Extension

section Wronskian
variable {F : Type*} [Field F] [Differential F]

/-- The iterated derivative `Dⁱ x`. -/
noncomputable def iterDeriv (i : ℕ) (x : F) : F := (fun y => y′)^[i] x

@[simp] theorem iterDeriv_zero (x : F) : iterDeriv 0 x = x := rfl

theorem iterDeriv_succ (i : ℕ) (x : F) : iterDeriv (i + 1) x = (iterDeriv i x)′ :=
  Function.iterate_succ_apply' _ _ _

@[simp] theorem iterDeriv_zero_right (i : ℕ) : iterDeriv i (0 : F) = 0 := by
  induction i with
  | zero => rfl
  | succ n ih => rw [iterDeriv_succ, ih]; simp

theorem iterDeriv_add (i : ℕ) (x y : F) :
    iterDeriv i (x + y) = iterDeriv i x + iterDeriv i y := by
  induction i with
  | zero => rfl
  | succ n ih => rw [iterDeriv_succ, ih, map_add, iterDeriv_succ, iterDeriv_succ]

theorem iterDeriv_const_mul {c : F} (hc : c′ = 0) (i : ℕ) (x : F) :
    iterDeriv i (c * x) = c * iterDeriv i x := by
  induction i with
  | zero => rfl
  | succ n ih => rw [iterDeriv_succ, ih, deriv_const_mul _ hc, iterDeriv_succ]

theorem iterDeriv_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (i : ℕ) (f : ι → F) :
    iterDeriv i (∑ j ∈ s, f j) = ∑ j ∈ s, iterDeriv i (f j) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, iterDeriv_add, ih, Finset.sum_insert ha]

/-- **Definition 3.3.1** (§3.3): the Wronskian `W(y₁,…,yₙ) = det(Dⁱ⁻¹ yⱼ)`. -/
noncomputable def wronskian {n : ℕ} (y : Fin n → F) : F :=
  (Matrix.of fun (i j : Fin n) => iterDeriv (i : ℕ) (y j)).det

/-- **Lemma 3.3.5** (§3.3, easy direction): if `y₁,…,yₙ` are linearly dependent over the
constants (a nonzero constant tuple `c` with `∑ⱼ cⱼ yⱼ = 0`), then `W(y₁,…,yₙ) = 0`. -/
theorem wronskian_eq_zero_of_linearDependent {n : ℕ} (y c : Fin n → F)
    (hc : ∀ j, (c j)′ = 0) (hne : c ≠ 0) (hdep : ∑ j, c j * y j = 0) :
    wronskian y = 0 := by
  rw [wronskian]
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hne, ?_⟩
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
  calc ∑ j, iterDeriv (i : ℕ) (y j) * c j
      = ∑ j, iterDeriv (i : ℕ) (c j * y j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [iterDeriv_const_mul (hc j), mul_comm]
    _ = iterDeriv (i : ℕ) (∑ j, c j * y j) := (iterDeriv_sum _ _ _).symm
    _ = 0 := by rw [hdep, iterDeriv_zero_right]

/-- The 2×2 Wronskian: `W(y₁, y₂) = y₁·y₂′ − y₂·y₁′`. -/
theorem wronskian_fin_two (y₁ y₂ : F) : wronskian ![y₁, y₂] = y₁ * y₂′ - y₂ * y₁′ := by
  simp [wronskian, Matrix.det_fin_two, iterDeriv_succ, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Lemma 3.3.5** (§3.3), converse, case `n = 2`: if the Wronskian of `y₁, y₂` vanishes then
they are linearly dependent over the constants. (The general-`n` converse — the induction on `n`
— is still open.) -/
theorem wronskian_two_linearDependent (y₁ y₂ : F) (h : wronskian ![y₁, y₂] = 0) :
    ∃ c₁ c₂ : F, c₁′ = 0 ∧ c₂′ = 0 ∧ (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ * y₁ + c₂ * y₂ = 0 := by
  rw [wronskian_fin_two] at h
  by_cases hy1 : y₁ = 0
  · exact ⟨1, 0, by simp, by simp, Or.inl one_ne_zero, by simp [hy1]⟩
  · refine ⟨y₂ / y₁, -1, ?_, by simp, Or.inr (by simp), ?_⟩
    · rw [deriv_div, show y₁ * y₂′ - y₂ * y₁′ = (0 : F) from h]; simp
    · field_simp; ring

end Wronskian

end DeepWiki.SymbolicIntegration
