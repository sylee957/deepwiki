import DeepWiki.SymbolicIntegration.DifferentialAlgebra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Iterated derivatives and Wronskians

Core API for iterated derivatives and Wronskian determinants in differential fields.
-/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

section Wronskian

/-- The `i`-fold iterate of the derivation. -/
noncomputable def iterDeriv {F : Type*} [Field F] [Differential F] (i : ℕ) (x : F) : F :=
  (fun y => y′)^[i] x

/-- The zeroth iterated derivative is the identity. -/
@[simp] theorem iterDeriv_zero {F : Type*} [Field F] [Differential F] (x : F) :
    iterDeriv 0 x = x := rfl

/-- `iterDeriv (i + 1) x = (iterDeriv i x)′`. -/
theorem iterDeriv_succ {F : Type*} [Field F] [Differential F] (i : ℕ) (x : F) :
    iterDeriv (i + 1) x = (iterDeriv i x)′ :=
  Function.iterate_succ_apply' _ _ _

/-- Every iterated derivative of `0` is `0`. -/
@[simp] theorem iterDeriv_zero_right {F : Type*} [Field F] [Differential F] (i : ℕ) :
    iterDeriv i (0 : F) = 0 := by
  induction i with
  | zero => rfl
  | succ n ih => rw [iterDeriv_succ, ih]; simp

/-- `iterDeriv i` preserves addition. -/
theorem iterDeriv_add {F : Type*} [Field F] [Differential F] (i : ℕ) (x y : F) :
    iterDeriv i (x + y) = iterDeriv i x + iterDeriv i y := by
  induction i with
  | zero => rfl
  | succ n ih => rw [iterDeriv_succ, ih, map_add, iterDeriv_succ, iterDeriv_succ]

/-- Multiplication by a constant commutes with `iterDeriv`. -/
theorem iterDeriv_const_mul {F : Type*} [Field F] [Differential F] {c : F} (hc : c′ = 0)
    (i : ℕ) (x : F) :
    iterDeriv i (c * x) = c * iterDeriv i x := by
  induction i with
  | zero => rfl
  | succ n ih => rw [iterDeriv_succ, ih, deriv_const_mul _ hc, iterDeriv_succ]

/-- `iterDeriv i` commutes with finite sums. -/
theorem iterDeriv_sum {F : Type*} [Field F] [Differential F] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (i : ℕ) (f : ι → F) :
    iterDeriv i (∑ j ∈ s, f j) = ∑ j ∈ s, iterDeriv i (f j) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, iterDeriv_add, ih, Finset.sum_insert ha]

open Finset in
/-- General Leibniz rule for `iterDeriv` of a product. -/
theorem iterDeriv_mul {F : Type*} [Field F] [Differential F] (n : ℕ) (a b : F) :
    iterDeriv n (a * b)
      = ∑ k ∈ range n.succ, n.choose k • (iterDeriv (n - k) a * iterDeriv k b) := by
  have hmul : ∀ p q : F, (p * q)′ = p′ * q + p * q′ := fun p q => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
  induction n with
  | zero => simp [iterDeriv]
  | succ n IH =>
    calc
      iterDeriv (n + 1) (a * b)
          = (∑ k ∈ range n.succ, n.choose k • (iterDeriv (n - k) a * iterDeriv k b))′ := by
            rw [iterDeriv_succ, IH]
      _ = (∑ k ∈ range n.succ, n.choose k • (iterDeriv (n - k + 1) a * iterDeriv k b)) +
            ∑ k ∈ range n.succ, n.choose k • (iterDeriv (n - k) a * iterDeriv (k + 1) b) := by
        simp_rw [map_sum, map_nsmul, hmul, ← iterDeriv_succ, smul_add, sum_add_distrib]
      _ = (∑ k ∈ range n.succ, n.choose k.succ • (iterDeriv (n - k) a * iterDeriv (k + 1) b)) +
              1 • (iterDeriv (n + 1) a * iterDeriv 0 b) +
            ∑ k ∈ range n.succ, n.choose k • (iterDeriv (n - k) a * iterDeriv (k + 1) b) := ?_
      _ = ((∑ k ∈ range n.succ, n.choose k • (iterDeriv (n - k) a * iterDeriv (k + 1) b)) +
              ∑ k ∈ range n.succ, n.choose k.succ • (iterDeriv (n - k) a * iterDeriv (k + 1) b)) +
            1 • (iterDeriv (n + 1) a * iterDeriv 0 b) := by rw [add_comm, add_assoc]
      _ = (∑ i ∈ range n.succ,
              (n + 1).choose (i + 1) • (iterDeriv (n + 1 - (i + 1)) a * iterDeriv (i + 1) b)) +
            1 • (iterDeriv (n + 1) a * iterDeriv 0 b) := by
        simp_rw [Nat.choose_succ_succ, Nat.succ_sub_succ, add_smul, sum_add_distrib]
      _ = ∑ k ∈ range n.succ.succ, n.succ.choose k • (iterDeriv (n.succ - k) a * iterDeriv k b) := by
        rw [sum_range_succ' _ n.succ, Nat.choose_zero_right, tsub_zero]
    congr
    refine (sum_range_succ' _ _).trans (congr_arg₂ (· + ·) ?_ ?_)
    · rw [sum_range_succ, Nat.choose_succ_self, zero_smul, add_zero]
      refine sum_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      congr
      omega
    · rw [Nat.choose_zero_right, tsub_zero]

/-- The Wronskian determinant `det (Dⁱ yⱼ)`. -/
noncomputable def wronskian {F : Type*} [Field F] [Differential F] {n : ℕ} (y : Fin n → F) :
    F :=
  (Matrix.of fun (i j : Fin n) => iterDeriv (i : ℕ) (y j)).det

/-- A nonzero constant linear relation forces the Wronskian to vanish. -/
theorem wronskian_eq_zero_of_linearDependent {F : Type*} [Field F] [Differential F] {n : ℕ}
    (y c : Fin n → F)
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

/-- The Wronskian vanishes when two entries of the family coincide. -/
theorem wronskian_eq_zero_of_eq {F : Type*} [Field F] [Differential F] {n : ℕ}
    (y : Fin n → F) {i j : Fin n} (hij : i ≠ j) (h : y i = y j) :
    wronskian y = 0 := by
  rw [wronskian]
  exact Matrix.det_zero_of_column_eq hij (fun k => by simp only [Matrix.of_apply]; rw [h])

/-- The 2×2 Wronskian: `W(y₁, y₂) = y₁·y₂′ − y₂·y₁′`. -/
theorem wronskian_fin_two {F : Type*} [Field F] [Differential F] (y₁ y₂ : F) :
    wronskian ![y₁, y₂] = y₁ * y₂′ - y₂ * y₁′ := by
  simp [wronskian, Matrix.det_fin_two, iterDeriv_succ, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- A vanishing 2×2 Wronskian gives a nonzero constant linear relation. -/
theorem wronskian_two_linearDependent {F : Type*} [Field F] [Differential F] (y₁ y₂ : F)
    (h : wronskian ![y₁, y₂] = 0) :
    ∃ c₁ c₂ : F, c₁′ = 0 ∧ c₂′ = 0 ∧ (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ * y₁ + c₂ * y₂ = 0 := by
  rw [wronskian_fin_two] at h
  by_cases hy1 : y₁ = 0
  · exact ⟨1, 0, by simp, by simp, Or.inl one_ne_zero, by simp [hy1]⟩
  · refine ⟨y₂ / y₁, -1, ?_, by simp, Or.inr (by simp), ?_⟩
    · rw [deriv_div, show y₁ * y₂′ - y₂ * y₁′ = (0 : F) from h]; simp
    · field_simp; ring

/-- A vanishing Wronskian gives a nonzero linear relation over the ambient field. -/
theorem wronskian_eq_zero_imp_linearDependent {F : Type*} [Field F] [Differential F] {n : ℕ}
    [NeZero n] (y : Fin n → F) (h : wronskian y = 0) :
    ∃ c : Fin n → F, c ≠ 0 ∧ ∑ j, c j * y j = 0 := by
  rw [wronskian] at h
  obtain ⟨c, hcne, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  refine ⟨c, hcne, ?_⟩
  have h0 := congrFun hmul (0 : Fin n)
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, Fin.val_zero,
    iterDeriv_zero] at h0
  simpa [mul_comm] using h0

/-- A vanishing Wronskian gives a nonzero vector annihilating every derivative row. -/
theorem wronskian_eq_zero_dependent_iterDeriv {F : Type*} [Field F] [Differential F] {n : ℕ}
    [NeZero n] (y : Fin n → F) (h : wronskian y = 0) :
    ∃ c : Fin n → F, c ≠ 0 ∧ ∀ i : Fin n, ∑ j, c j * iterDeriv (i : ℕ) (y j) = 0 := by
  rw [wronskian] at h
  obtain ⟨c, hcne, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  refine ⟨c, hcne, fun i => ?_⟩
  have hi := congrFun hmul i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at hi
  rw [← hi]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The derivative of a vector annihilating every derivative row annihilates each lower row. -/
theorem deriv_dependent_iterDeriv {F : Type*} [Field F] [Differential F] {n : ℕ}
    (y c : Fin n → F)
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

/-- A constant relation among `(g i / y₁)′` lifts to one among `y₁` and the `g i`. -/
theorem linearDependent_of_div_deriv_dependent {F ι : Type*} [Field F] [Differential F]
    [Fintype ι] {y₁ : F} (hy1 : y₁ ≠ 0) (g d : ι → F) (hd : ∀ i, (d i)′ = 0)
    (hdne : ∃ i, d i ≠ 0)
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

section WronskianConstants
variable {F : Type*} [Field F] [Differential F]

/-- A nonzero linear relation with constant coefficients among the family `y`. -/
def linearDependentOverConst {n : ℕ} (y : Fin n → F) : Prop :=
  ∃ c : Fin n → F, (∀ j, (c j)′ = 0) ∧ c ≠ 0 ∧ ∑ j, c j * y j = 0

/-- A dependence after dropping one coordinate pads to a dependence of the whole family. -/
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

/-- Scaling an annihilator tuple preserves each derivative-row annihilation. -/
theorem dependent_iterDeriv_smul {n : ℕ} (y c : Fin n → F) (a : F)
    (hc : ∀ i : Fin n, ∑ j, c j * iterDeriv (i : ℕ) (y j) = 0) (i : Fin n) :
    ∑ j, (a * c j) * iterDeriv (i : ℕ) (y j) = 0 := by
  simp_rw [mul_assoc, ← Finset.mul_sum, hc i, mul_zero]

/-- A nonzero tuple annihilating all derivative rows gives a constant linear dependence. -/
theorem linearDependentOverConst_of_dependent_iterDeriv {n : ℕ} (y c : Fin n → F) (hcne : c ≠ 0)
    (hc : ∀ i : Fin n, ∑ j, c j * iterDeriv (i : ℕ) (y j) = 0) :
    linearDependentOverConst y := by
  induction n with
  | zero => exact absurd (Subsingleton.elim c 0) hcne
  | succ n IH =>
    -- pick a nonzero coordinate `j₀`
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, c j₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hcne (funext h)
    -- normalise: `c1 j₀ = 1`
    set c1 : Fin (n + 1) → F := fun j => (c j₀)⁻¹ * c j with hc1def
    have hc1row : ∀ i : Fin (n + 1), ∑ j, c1 j * iterDeriv (i : ℕ) (y j) = 0 :=
      fun i => dependent_iterDeriv_smul y c (c j₀)⁻¹ hc i
    have hc1j₀ : c1 j₀ = 1 := by rw [hc1def]; field_simp
    have hc1ne : c1 ≠ 0 := fun h => by
      have := congrFun h j₀; rw [hc1j₀] at this; exact one_ne_zero this
    -- derivative tuple annihilates the lower rows
    have hder : ∀ i : Fin (n + 1), (i : ℕ) + 1 < n + 1 →
        ∑ j, (c1 j)′ * iterDeriv (i : ℕ) (y j) = 0 :=
      fun i hi => deriv_dependent_iterDeriv y c1 hc1row i hi
    have hderj₀ : (c1 j₀)′ = 0 := by rw [hc1j₀]; simp
    by_cases hzero : (fun j => (c1 j)′) = 0
    · -- all coefficients are constants: row 0 is the dependence
      refine ⟨c1, fun j => congrFun hzero j, hc1ne, ?_⟩
      have := hc1row 0
      simpa using this
    · -- derivative tuple is a shorter nonzero annihilator
      refine linearDependentOverConst_succAbove y j₀ (IH (fun i => y (j₀.succAbove i))
        (fun i => (c1 (j₀.succAbove i))′) ?_ ?_)
      · -- nonzero on the dropped family
        intro h
        apply hzero
        funext k
        refine j₀.succAboveCases ?_ (fun i => ?_) k
        · exact hderj₀
        · exact congrFun h i
      · -- annihilates rows `0..n-1` of the dropped family
        intro i
        have hi : (i.castSucc : ℕ) + 1 < n + 1 := by rw [Fin.val_castSucc]; omega
        have hrow := hder i.castSucc hi
        rw [Fin.sum_univ_succAbove _ j₀, hderj₀, zero_mul, zero_add] at hrow
        simpa [Fin.val_castSucc] using hrow

/-- A zero Wronskian gives a nonzero constant linear dependence. -/
theorem linearDependentOverConst_of_wronskian_eq_zero {n : ℕ} [NeZero n] (y : Fin n → F)
    (h : wronskian y = 0) : linearDependentOverConst y := by
  obtain ⟨c, hcne, hrows⟩ := wronskian_eq_zero_dependent_iterDeriv y h
  exact linearDependentOverConst_of_dependent_iterDeriv y c hcne hrows

/-- `wronskian y = 0` iff `y` is linearly dependent over constants. -/
theorem wronskian_eq_zero_iff_linearDependentOverConst {n : ℕ} [NeZero n] (y : Fin n → F) :
    wronskian y = 0 ↔ linearDependentOverConst y := by
  refine ⟨linearDependentOverConst_of_wronskian_eq_zero y, ?_⟩
  rintro ⟨c, hc, hcne, hdep⟩
  exact wronskian_eq_zero_of_linearDependent y c hc hcne hdep

/-- `wronskian y ≠ 0` iff `y` is not linearly dependent over constants. -/
theorem wronskian_ne_zero_iff_not_linearDependentOverConst {n : ℕ} [NeZero n] (y : Fin n → F) :
    wronskian y ≠ 0 ↔ ¬ linearDependentOverConst y :=
  (wronskian_eq_zero_iff_linearDependentOverConst y).not

end WronskianConstants

section WronskianExtension
variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E]

/-- Iterated derivative commutes with `algebraMap`. -/
theorem iterDeriv_algebraMap (i : ℕ) (x : F) :
    iterDeriv i (algebraMap F E x) = algebraMap F E (iterDeriv i x) := by
  induction i with
  | zero => rfl
  | succ n ih => rw [iterDeriv_succ, ih, deriv_algebraMap, iterDeriv_succ]

/-- The Wronskian commutes with `algebraMap`. -/
theorem wronskian_algebraMap {n : ℕ} (y : Fin n → F) :
    wronskian (fun j => algebraMap F E (y j)) = algebraMap F E (wronskian y) := by
  rw [wronskian, wronskian, RingHom.map_det]
  congr 1
  ext i j
  simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, iterDeriv_algebraMap]

/-- Linear independence over constants is preserved by differential extensions. -/
theorem not_linearDependentOverConst_algebraMap {n : ℕ} [NeZero n] (y : Fin n → F)
    (h : ¬ linearDependentOverConst y) :
    ¬ linearDependentOverConst (fun j => algebraMap F E (y j)) := by
  rw [← wronskian_ne_zero_iff_not_linearDependentOverConst] at h ⊢
  rw [wronskian_algebraMap]
  exact fun hcontra => h ((map_eq_zero (algebraMap F E)).mp hcontra)

end WronskianExtension

end DeepWiki.SymbolicIntegration
