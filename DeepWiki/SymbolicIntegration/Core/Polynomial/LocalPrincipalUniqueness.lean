import DeepWiki.SymbolicIntegration.Core.Polynomial.LocalPrincipalParts

/-! # Uniqueness of local principal parts

Principal parts at a point are intrinsic: once the remaining summand is regular
at that point, the principal part is forced.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- A bounded-degree numerator over `(X−α)^i` cannot be regular at `α` unless it is zero. -/
theorem eq_zero_of_div_pow_eq_regular {W N M : K[X]} {α : K} (i : ℕ) (hM : M.eval α ≠ 0)
    (hW : W.degree < ((Polynomial.X - Polynomial.C α) ^ i).degree)
    (heq : algebraMap K[X] (RatFunc K) W
            / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ i
          = algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) M) :
    W = 0 := by
  have hX0 : (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero α)
  have hM0 : algebraMap K[X] (RatFunc K) M ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (fun h => hM (by rw [h, Polynomial.eval_zero]))
  rw [div_eq_div_iff (pow_ne_zero i hX0) hM0, ← map_pow, ← map_mul, ← map_mul] at heq
  have hpoly : W * M = N * (Polynomial.X - Polynomial.C α) ^ i :=
    RatFunc.algebraMap_injective K heq
  have hdvd : (Polynomial.X - Polynomial.C α) ^ i ∣ W * M := ⟨N, by rw [hpoly]; ring⟩
  have hcop : IsCoprime ((Polynomial.X - Polynomial.C α) ^ i) M :=
    (isCoprime_M_X_sub_C_pow i hM).symm
  exact eq_zero_of_dvd_of_degree_lt (hcop.dvd_of_dvd_mul_right hdvd) hW

/-- Two local principal parts whose difference is regular at `α` are equal. -/
theorem principalPart_unique {A₁ M₁ A₂ M₂ N₁ N₂ Md₁ Md₂ : K[X]} {α : K} (i : ℕ)
    (hMd₁ : Md₁.eval α ≠ 0) (hMd₂ : Md₂.eval α ≠ 0)
    (heq : localPrincipalPart A₁ M₁ α i
            + algebraMap K[X] (RatFunc K) N₁ / algebraMap K[X] (RatFunc K) Md₁
          = localPrincipalPart A₂ M₂ α i
            + algebraMap K[X] (RatFunc K) N₂ / algebraMap K[X] (RatFunc K) Md₂) :
    localPrincipalPart A₁ M₁ α i = localPrincipalPart A₂ M₂ α i := by
  set W₁ := localApprox A₁ M₁ α i with hW₁
  set W₂ := localApprox A₂ M₂ α i with hW₂
  have hX0 : (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero α)
  have hMd₁0 : algebraMap K[X] (RatFunc K) Md₁ ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (fun h => hMd₁ (by rw [h, Polynomial.eval_zero]))
  have hMd₂0 : algebraMap K[X] (RatFunc K) Md₂ ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (fun h => hMd₂ (by rw [h, Polynomial.eval_zero]))
  have hDp0 : (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ i ≠ 0 :=
    pow_ne_zero i hX0
  have hMd₁₂0 : algebraMap K[X] (RatFunc K) (Md₁ * Md₂) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero hMd₁0 hMd₂0
  rw [localPrincipalPart_eq_div, localPrincipalPart_eq_div, ← hW₁, ← hW₂] at heq
  have heqsub : algebraMap K[X] (RatFunc K) (W₁ - W₂)
        / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ i
      = algebraMap K[X] (RatFunc K) N₂ / algebraMap K[X] (RatFunc K) Md₂
        - algebraMap K[X] (RatFunc K) N₁ / algebraMap K[X] (RatFunc K) Md₁ := by
    rw [map_sub, sub_div]
    linear_combination heq
  have hpolyid : (W₁ - W₂) * (Md₁ * Md₂)
      = (N₂ * Md₁ - N₁ * Md₂) * (Polynomial.X - Polynomial.C α) ^ i := by
    apply RatFunc.algebraMap_injective K
    rw [div_sub_div _ _ hMd₂0 hMd₁0,
      div_eq_div_iff hDp0 (mul_ne_zero hMd₂0 hMd₁0)] at heqsub
    simp only [map_mul, map_sub, map_pow] at heqsub ⊢
    ring_nf
    ring_nf at heqsub
    linear_combination heqsub
  have hdiff : algebraMap K[X] (RatFunc K) (W₁ - W₂)
        / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ i
      = algebraMap K[X] (RatFunc K) (N₂ * Md₁ - N₁ * Md₂)
        / algebraMap K[X] (RatFunc K) (Md₁ * Md₂) := by
    rw [div_eq_div_iff hDp0 hMd₁₂0, ← map_pow, ← map_mul, ← map_mul, hpolyid]
  have hdeg : (W₁ - W₂).degree < ((Polynomial.X - Polynomial.C α) ^ i).degree := by
    have hmonic : ((Polynomial.X - Polynomial.C α) ^ i).Monic := (monic_X_sub_C α).pow i
    have h1 : W₁.degree < ((Polynomial.X - Polynomial.C α) ^ i).degree := by
      rw [hW₁, localApprox]; exact degree_modByMonic_lt _ hmonic
    have h2 : W₂.degree < ((Polynomial.X - Polynomial.C α) ^ i).degree := by
      rw [hW₂, localApprox]; exact degree_modByMonic_lt _ hmonic
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt h1 h2)
  have hMM : (Md₁ * Md₂).eval α ≠ 0 := by
    rw [Polynomial.eval_mul]; exact mul_ne_zero hMd₁ hMd₂
  have hWeq : W₁ - W₂ = 0 := eq_zero_of_div_pow_eq_regular i hMM hdeg hdiff
  rw [localPrincipalPart_eq_div, localPrincipalPart_eq_div, ← hW₁, ← hW₂,
    sub_eq_zero.mp hWeq]

end DeepWiki.SymbolicIntegration
