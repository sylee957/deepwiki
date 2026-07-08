import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.RatFunc.Basic
import DeepWiki.SymbolicIntegration.Core.Polynomial.Diophantine
import DeepWiki.SymbolicIntegration.Core.Polynomial.LinearFactors

/-! # Local principal parts of rational functions

Defines the local inverse, Taylor approximant, principal part, and regular remainder
for a denominator split as `(X - C α)^i * M` with `M.eval α ≠ 0`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## Local Taylor approximants and principal parts -/

/-- The local inverse `N` of `M` modulo `(X−α)^i`: the Bézout cofactor with `M·N ≡ 1 (mod (X−α)^i)`. -/
noncomputable def localInverse (M : K[X]) (α : K) (i : ℕ) : K[X] :=
  (diophantineSolve M ((Polynomial.X - Polynomial.C α) ^ i) 1).1

/-- The local-inverse congruence: `(X−α)^i ∣ M·(localInverse M α i) − 1` for `M(α) ≠ 0`. -/
theorem localInverse_spec {M : K[X]} {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    (Polynomial.X - Polynomial.C α) ^ i ∣ M * localInverse M α i - 1 := by
  have hspec := diophantineSolve_spec (isCoprime_M_X_sub_C_pow i hM) (1 : K[X])
  refine ⟨-(diophantineSolve M ((Polynomial.X - Polynomial.C α) ^ i) 1).2, ?_⟩
  rw [localInverse]; linear_combination hspec

/-- The local Taylor approximant `W = (A·N) %ₘ (X−α)^i` satisfying `M·W ≡ A`. -/
noncomputable def localApprox (A M : K[X]) (α : K) (i : ℕ) : K[X] :=
  (A * localInverse M α i) %ₘ (Polynomial.X - Polynomial.C α) ^ i

/-- The defining congruence `M·W ≡ A (mod (X−α)^i)`: `(X−α)^i ∣ A − M·(localApprox A M α i)`. -/
theorem localApprox_spec (A M : K[X]) {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    (Polynomial.X - Polynomial.C α) ^ i ∣ A - M * localApprox A M α i := by
  set g := (Polynomial.X - Polynomial.C α) ^ i with hg
  have hmonic : g.Monic := (monic_X_sub_C α).pow i
  have hAN : g ∣ A * localInverse M α i - localApprox A M α i := by
    have hid : A * localInverse M α i - localApprox A M α i
        = g * ((A * localInverse M α i) /ₘ g) := by
      rw [localApprox, eq_comm, ← sub_eq_iff_eq_add'.mpr (modByMonic_add_div (A * localInverse M α i) g).symm]
    rw [hid]; exact Dvd.intro _ rfl
  have hMN : g ∣ M * localInverse M α i - 1 := localInverse_spec i hM
  have hcomb : A - M * localApprox A M α i
      = A * (-(M * localInverse M α i - 1)) + M * (A * localInverse M α i - localApprox A M α i) := by
    ring
  rw [hcomb]
  exact dvd_add (Dvd.dvd.mul_left ((dvd_neg).mpr hMN) A) (Dvd.dvd.mul_left hAN M)

/-- The Laurent digit `c_d = (taylor α W).coeff d` of the local approximant `W`. -/
noncomputable def localCoeff (A M : K[X]) (α : K) (i d : ℕ) : K :=
  (taylor α (localApprox A M α i)).coeff d

/-- The `(X−α)`-adic reconstruction `localApprox A M α i = ∑_{d<i} c_d·(X−α)^d`. -/
theorem localApprox_eq_sum (A M : K[X]) (α : K) (i : ℕ) :
    localApprox A M α i
      = ∑ d ∈ Finset.range i, Polynomial.C (localCoeff A M α i d)
          * (Polynomial.X - Polynomial.C α) ^ d := by
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    simp only [Finset.range_zero, Finset.sum_empty, localApprox, pow_zero, modByMonic_one]
  set W := localApprox A M α i with hW
  have hmonic : ((Polynomial.X - Polynomial.C α) ^ i).Monic := (monic_X_sub_C α).pow i
  have htay : W = (taylor α W).sum (fun d a => Polynomial.C a * (Polynomial.X - Polynomial.C α) ^ d) :=
    (sum_taylor_eq W α).symm
  have hpowdeg : ((Polynomial.X - Polynomial.C α) ^ i).natDegree = i := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  have hdeg : (taylor α W).natDegree < i := by
    rw [natDegree_taylor]
    rcases eq_or_ne W 0 with h0 | h0
    · rw [h0, natDegree_zero]; exact hipos
    · have hlt := degree_modByMonic_lt (A * localInverse M α i) hmonic
      have hdW : W.natDegree < ((Polynomial.X - Polynomial.C α) ^ i).natDegree :=
        natDegree_lt_natDegree h0 (by rw [hW, localApprox]; exact hlt)
      rwa [hpowdeg] at hdW
  rw [htay, Polynomial.sum_over_range' _ (fun d => by simp) i hdeg]
  rfl

/-- The principal part of `A/((X−α)^i·M)` at `α`. -/
noncomputable def localPrincipalPart (A M : K[X]) (α : K) (i : ℕ) : RatFunc K :=
  ∑ j ∈ Finset.Icc 1 i,
    algebraMap K[X] (RatFunc K) (Polynomial.C (localCoeff A M α i (i - j)))
      / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j

/-- The consolidated denominator form of `localPrincipalPart`. -/
theorem localPrincipalPart_eq_div (A M : K[X]) (α : K) (i : ℕ) :
    localPrincipalPart A M α i
      = algebraMap K[X] (RatFunc K) (localApprox A M α i)
          / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ i := by
  have hX0 : (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero α)
  rw [localApprox_eq_sum A M α i, map_sum, Finset.sum_div, localPrincipalPart]
  refine Finset.sum_nbij' (fun j => i - j) (fun d => i - d) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_Icc] at hj; simp only [Finset.mem_range]; omega
  · intro d hd; simp only [Finset.mem_range] at hd; simp only [Finset.mem_Icc]; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro d hd; simp only [Finset.mem_range] at hd; omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    have hpow : (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ (i - j)
        * (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j
        = (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ i := by
      rw [← pow_add]; congr 1; omega
    rw [map_mul, map_pow, div_eq_div_iff (pow_ne_zero _ hX0) (pow_ne_zero _ hX0), mul_assoc, hpow]

/-- The regular numerator after subtracting the local principal part. -/
noncomputable def localRemainder (A M : K[X]) (α : K) (i : ℕ) : K[X] :=
  (A - M * localApprox A M α i) /ₘ (Polynomial.X - Polynomial.C α) ^ i

/-- `A − M·(localApprox A M α i) = (X−α)^i·(localRemainder A M α i)`. -/
theorem localRemainder_spec (A M : K[X]) {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    A - M * localApprox A M α i
      = (Polynomial.X - Polynomial.C α) ^ i * localRemainder A M α i := by
  have hmonic : ((Polynomial.X - Polynomial.C α) ^ i).Monic := (monic_X_sub_C α).pow i
  conv_lhs => rw [← modByMonic_add_div (A - M * localApprox A M α i)
    ((Polynomial.X - Polynomial.C α) ^ i)]
  rw [(modByMonic_eq_zero_iff_dvd hmonic).2 (localApprox_spec A M i hM), zero_add, localRemainder]

/-- Subtracting `localPrincipalPart` leaves the regular fraction `localRemainder / M`. -/
theorem subtract_localPrincipalPart_eq (A M : K[X]) {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    algebraMap K[X] (RatFunc K) A
        / (algebraMap K[X] (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ i * M))
      - localPrincipalPart A M α i
      = algebraMap K[X] (RatFunc K) (localRemainder A M α i)
          / algebraMap K[X] (RatFunc K) M := by
  set X' := algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α) with hX'
  have hX0 : X' ≠ 0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero α)
  have hM0 : algebraMap K[X] (RatFunc K) M ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (fun h => hM (by rw [h, Polynomial.eval_zero]))
  rw [localPrincipalPart_eq_div]
  rw [map_mul, map_pow, ← hX']
  rw [div_sub_div _ _ (mul_ne_zero (pow_ne_zero i hX0) hM0) (pow_ne_zero i hX0)]
  rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero (pow_ne_zero i hX0) hM0) (pow_ne_zero i hX0)) hM0]
  have hspec : algebraMap K[X] (RatFunc K) A - algebraMap K[X] (RatFunc K) M
        * algebraMap K[X] (RatFunc K) (localApprox A M α i)
      = X' ^ i * algebraMap K[X] (RatFunc K) (localRemainder A M α i) := by
    have h := localRemainder_spec A M i hM
    have := congrArg (algebraMap K[X] (RatFunc K)) h
    rwa [map_sub, map_mul, map_mul, map_pow, ← hX'] at this
  linear_combination (X' ^ i * algebraMap K[X] (RatFunc K) M) * hspec

/-- There is a regular fraction left after subtracting `localPrincipalPart`. -/
theorem exists_regular_sub_localPrincipalPart (A M : K[X]) {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    ∃ (R N : K[X]), N.eval α ≠ 0 ∧
      algebraMap K[X] (RatFunc K) A
          / (algebraMap K[X] (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ i * M))
        - localPrincipalPart A M α i
        = algebraMap K[X] (RatFunc K) R / algebraMap K[X] (RatFunc K) N :=
  ⟨localRemainder A M α i, M, hM, subtract_localPrincipalPart_eq A M i hM⟩

end DeepWiki.SymbolicIntegration
