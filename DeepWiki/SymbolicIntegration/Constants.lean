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

/-- **Lemma 3.3.5** (§3.3), converse, field-coefficient version (all `n`): a vanishing Wronskian
forces the `yⱼ` to be linearly dependent over the field `F` (the `0`-th row of the kernel vector
is the relation). Upgrading the coefficients to *constants* — the full converse — is the deferred
induction on `n`. -/
theorem wronskian_eq_zero_imp_linearDependent {n : ℕ} [NeZero n] (y : Fin n → F)
    (h : wronskian y = 0) : ∃ c : Fin n → F, c ≠ 0 ∧ ∑ j, c j * y j = 0 := by
  rw [wronskian] at h
  obtain ⟨c, hcne, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  refine ⟨c, hcne, ?_⟩
  have h0 := congrFun hmul (0 : Fin n)
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, Fin.val_zero,
    iterDeriv_zero] at h0
  simpa [mul_comm] using h0

/-- Foundation for the full **Lemma 3.3.5** converse (induction on `n`): a vanishing Wronskian
yields a single nonzero `c : Fin n → F` annihilating *every* derivative row,
`∀ i, ∑ⱼ cⱼ·Dⁱ(yⱼ) = 0` (the kernel vector of `det = 0`). Row `0` is
`wronskian_eq_zero_imp_linearDependent`; differentiating row `i` (which sends it to row `i+1`
plus a `Dc`-term) is the step that upgrades the coefficients to constants. -/
theorem wronskian_eq_zero_dependent_iterDeriv {n : ℕ} [NeZero n] (y : Fin n → F)
    (h : wronskian y = 0) :
    ∃ c : Fin n → F, c ≠ 0 ∧ ∀ i : Fin n, ∑ j, c j * iterDeriv (i : ℕ) (y j) = 0 := by
  rw [wronskian] at h
  obtain ⟨c, hcne, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  refine ⟨c, hcne, fun i => ?_⟩
  have hi := congrFun hmul i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at hi
  rw [← hi]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The recurrence driving the **Lemma 3.3.5** induction: if `c` annihilates every derivative
row (`∀ i, ∑ⱼ cⱼ·Dⁱyⱼ = 0`), then the *derivative* tuple `c′` annihilates each lower row —
`∑ⱼ (cⱼ)′·Dⁱyⱼ = 0` for `i+1 < n`. (Differentiate row `i`: the `D^{i+1}` part is row `i+1`,
itself `0`.) Iterating this is what forces some nonzero `c` to be a *constant* tuple. -/
theorem deriv_dependent_iterDeriv {n : ℕ} (y c : Fin n → F)
    (hc : ∀ i : Fin n, ∑ j, c j * iterDeriv (i : ℕ) (y j) = 0)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    ∑ j, (c j)′ * iterDeriv (i : ℕ) (y j) = 0 := by
  have hd : (∑ j, c j * iterDeriv (i : ℕ) (y j))′ = 0 := by rw [hc i]; simp
  rw [map_sum] at hd
  have hnext : ∑ j, c j * iterDeriv ((i : ℕ) + 1) (y j) = 0 := hc ⟨(i : ℕ) + 1, hi⟩
  have hterm : ∀ j, (c j * iterDeriv (i : ℕ) (y j))′
      = (c j)′ * iterDeriv (i : ℕ) (y j) + c j * iterDeriv ((i : ℕ) + 1) (y j) := by
    intro j
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, iterDeriv_succ]; ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, hnext, add_zero] at hd
  exact hd

/-- Division-reduction step toward the **Lemma 3.3.5** converse: if `y₁ ≠ 0` and the derivatives
`(gᵢ/y₁)′` are linearly dependent over the constants (constants `dᵢ`, not all `0`), then `y₁`
together with the `gᵢ` are linearly dependent over the constants — set `c₀ = −∑ᵢ dᵢ(gᵢ/y₁)`, a
constant by the dependence, with `c₀·y₁ + ∑ᵢ dᵢ·gᵢ = 0`. (This is the inductive step of the
classical proof; connecting `W(y) = 0` to the dependence of the `(gᵢ/y₁)′` is the determinant
reduction `W(y₁,…,yₙ) = y₁ⁿ·W((y₂/y₁)′,…)`, still to formalize.) -/
theorem linearDependent_of_div_deriv_dependent {ι : Type*} [Fintype ι] {y₁ : F} (hy1 : y₁ ≠ 0)
    (g d : ι → F) (hd : ∀ i, (d i)′ = 0) (hdne : ∃ i, d i ≠ 0)
    (hdep : ∑ i, d i * (g i / y₁)′ = 0) :
    ∃ (c₀ : F) (c : ι → F), c₀′ = 0 ∧ (∀ i, (c i)′ = 0) ∧ (c₀ ≠ 0 ∨ ∃ i, c i ≠ 0)
      ∧ c₀ * y₁ + ∑ i, c i * g i = 0 := by
  refine ⟨-(∑ i, d i * (g i / y₁)), d, ?_, hd, Or.inr hdne, ?_⟩
  · rw [map_neg, neg_eq_zero, map_sum]
    rw [show (0 : F) = ∑ i, d i * (g i / y₁)′ from hdep.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hd i, mul_zero, add_zero]
  · rw [neg_mul, Finset.sum_mul,
      show (∑ i, d i * (g i / y₁) * y₁) = ∑ i, d i * g i from
        Finset.sum_congr rfl fun i _ => by rw [mul_assoc, div_mul_cancel₀ _ hy1],
      neg_add_cancel]

end Wronskian

end DeepWiki.SymbolicIntegration
