import DeepWiki.SymbolicIntegration.Constants

/-! # Wronskian criteria over constants

Wronskian criteria for linear dependence over constants and preservation through
differential extensions.
-/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

section Wronskian
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

end Wronskian

section Extension
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

end Extension

end DeepWiki.SymbolicIntegration
