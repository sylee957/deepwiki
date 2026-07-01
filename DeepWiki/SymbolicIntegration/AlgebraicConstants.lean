import DeepWiki.SymbolicIntegration.Constants

/-! # Constants of differential extensions
Wronskian criteria for dependence over constants and algebraic facts about constants in
differential extensions. -/

open scoped Differential
open Polynomial

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

/-- A root of a separable polynomial with constant coefficients is a constant. -/
theorem deriv_eq_zero_of_separable_algebraic_const {E : Type*} [Field E] [Differential E]
    {c : E} (p : E[X])
    (hp : ∀ i, (p.coeff i)′ = 0) (hroot : p.eval c = 0) (hsep : p.derivative.eval c ≠ 0) :
    c′ = 0 := by
  have hchain : (p.eval c)′ = p.derivative.eval c * c′ := deriv_eval_of_const_coeffs p c hp
  rw [hroot, map_zero] at hchain
  exact (mul_eq_zero.mp hchain.symm).resolve_left hsep

section AlgebraicConstant
variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E]

/-- High coefficients of `Differential.mapCoeffs p` vanish for monic `p`. -/
theorem coeff_mapCoeffs_eq_zero_of_monic {p : F[X]} (hp : p.Monic) {i : ℕ}
    (hi : p.natDegree ≤ i) : (Differential.mapCoeffs p).coeff i = 0 := by
  rw [Differential.coeff_mapCoeffs]
  rcases eq_or_lt_of_le hi with rfl | hlt
  · rw [Polynomial.Monic.coeff_natDegree hp]; simp
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]; simp

/-- `Differential.mapCoeffs p` has degree strictly below monic `p`. -/
theorem degree_mapCoeffs_lt {p : F[X]} (hp : p.Monic) :
    (Differential.mapCoeffs p).degree < p.degree := by
  rw [Polynomial.degree_eq_natDegree hp.ne_zero]
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro k hk
  exact coeff_mapCoeffs_eq_zero_of_monic hp hk

/-- The minimal polynomial of an integral constant has constant coefficients. -/
theorem minpoly_coeff_deriv_eq_zero_of_deriv_eq_zero {c : E} (hc : c′ = 0)
    (hint : IsIntegral F c) :
    ∀ i, ((minpoly F c).coeff i)′ = 0 := by
  set p := minpoly F c with hpdef
  have hpmonic : p.Monic := minpoly.monic hint
  -- the κ_D(p) term vanishes at c
  have hkappa : Polynomial.aeval c (Differential.mapCoeffs p) = 0 := by
    have hchain := Differential.deriv_aeval_eq (A := F) (R := E) c p
    rw [minpoly.aeval, map_zero, hc, mul_zero, add_zero] at hchain
    exact hchain.symm
  -- minimality forces mapCoeffs p = 0
  have hmc0 : Differential.mapCoeffs p = 0 := by
    by_contra hne
    have hle := minpoly.degree_le_of_ne_zero F c hne hkappa
    rw [← hpdef] at hle
    exact absurd (lt_of_le_of_lt hle (degree_mapCoeffs_lt hpmonic)) (lt_irrefl _)
  -- hence every coefficient of p is a constant
  have hconst : ∀ i, (p.coeff i)′ = 0 := fun i => by
    have := congrArg (fun r => Polynomial.coeff r i) hmc0
    rwa [Differential.coeff_mapCoeffs, Polynomial.coeff_zero] at this
  intro i
  exact hconst i

/-- An integral constant has a nonzero annihilating polynomial over the base constants. -/
theorem isAlgebraicOverConst_of_deriv_eq_zero {c : E} (hc : c′ = 0)
    (hint : IsIntegral F c) :
    ∃ p : F[X], p ≠ 0 ∧ (∀ i, (p.coeff i)′ = 0) ∧ Polynomial.aeval c p = 0 := by
  refine ⟨minpoly F c, (minpoly.monic hint).ne_zero, ?_, ?_⟩
  · exact minpoly_coeff_deriv_eq_zero_of_deriv_eq_zero hc hint
  · rw [minpoly.aeval]

/-- Mapping a base-constant annihilator gives an ambient constant-coefficient polynomial. -/
theorem isAlgebraicOverConst_map_of_deriv_eq_zero {c : E} (hc : c′ = 0)
    (hint : IsIntegral F c) :
    ∃ q : E[X], q ≠ 0 ∧ (∀ i, (q.coeff i)′ = 0) ∧ q.eval c = 0 := by
  obtain ⟨p, hpne, hconst, hroot⟩ := isAlgebraicOverConst_of_deriv_eq_zero hc hint
  refine ⟨p.map (algebraMap F E), ?_, ?_, ?_⟩
  · rw [Ne, Polynomial.map_eq_zero_iff (algebraMap F E).injective]
    exact hpne
  · intro i
    rw [Polynomial.coeff_map, deriv_algebraMap, hconst i, map_zero]
  · rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hroot

end AlgebraicConstant

section ConstantsSubfield
variable {E : Type*} [Field E] [Differential E]

/-- Constants of a differential field form a subfield. -/
def constantsSubfield (E : Type*) [Field E] [Differential E] : Subfield E where
  toSubring := constants E
  inv_mem' := fun a (ha : a′ = 0) => by
    show (a⁻¹)′ = 0
    rcases eq_or_ne a 0 with rfl | hne
    · simp
    · have h1 : (a * a⁻¹)′ = 0 := by rw [mul_inv_cancel₀ hne]; simp
      rw [Derivation.leibniz, ha, smul_zero, add_zero, smul_eq_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_left hne

/-- Membership in `constantsSubfield E` is the equation `a′ = 0`. -/
@[simp] theorem mem_constantsSubfield {a : E} : a ∈ constantsSubfield E ↔ a′ = 0 := Iff.rfl

/-- The subfield generated by constants is contained in the constants. -/
theorem subfieldClosure_subset_constants {S : Set E} (hS : ∀ s ∈ S, s′ = 0) :
    Subfield.closure S ≤ constantsSubfield E :=
  (Subfield.closure_le).mpr (fun s hs => mem_constantsSubfield.mpr (hS s hs))

end ConstantsSubfield

end DeepWiki.SymbolicIntegration
