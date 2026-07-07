import DeepWiki.SymbolicIntegration.Core.Polynomial.LocalPrincipalParts
import DeepWiki.SymbolicIntegration.Core.Polynomial.LocalRegularity

/-! # Assembling local principal parts

Finite products of linear pole factors and the telescoping decomposition obtained
by subtracting one local principal part at a time.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- A proper rational function with nonzero constant denominator is zero. -/
theorem properRatFunc_const_denom_eq_zero {N M : K[X]} (hM : M.natDegree = 0) (hM0 : M ≠ 0)
    (hdeg : N.degree < M.degree) :
    algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) M = 0 := by
  have hMdeg : M.degree = 0 := by
    rw [Polynomial.degree_eq_natDegree hM0, hM]; rfl
  rw [hMdeg] at hdeg
  have hN0 : N = 0 := by
    by_contra hN
    rw [Polynomial.degree_eq_natDegree hN] at hdeg
    exact absurd hdeg (by exact_mod_cast Nat.not_lt_zero _)
  rw [hN0, map_zero, zero_div]

/-- The product `∏ α ∈ R, (X - C α) ^ mult α`. -/
noncomputable def rootProd (R : Finset K) (mult : K → ℕ) : K[X] :=
  ∏ α ∈ R, (Polynomial.X - Polynomial.C α) ^ mult α

/-- The empty root product is `1`. -/
@[simp] theorem rootProd_empty (mult : K → ℕ) : rootProd (∅ : Finset K) mult = 1 := by
  simp [rootProd]

/-- Insert one factor into a root product. -/
theorem rootProd_insert [DecidableEq K] {α : K} {R : Finset K} (mult : K → ℕ) (hα : α ∉ R) :
    rootProd (insert α R) mult = (Polynomial.X - Polynomial.C α) ^ mult α * rootProd R mult := by
  rw [rootProd, Finset.prod_insert hα, rootProd]

/-- `rootProd R mult` does not vanish at a point outside `R`. -/
theorem eval_rootProd_ne_zero {β : K} {R : Finset K} (mult : K → ℕ) (hβ : β ∉ R) :
    (rootProd R mult).eval β ≠ 0 := by
  rw [rootProd, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro α hα
  rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact pow_ne_zero _ (sub_ne_zero.mpr (fun h => hβ (h ▸ hα)))

open Classical in
/-- Decompose a quotient by a root product by subtracting local principal parts. -/
theorem exists_sum_localPrincipalPart (M₀ : K[X]) (mult : K → ℕ) :
    ∀ (R : Finset K), (∀ α ∈ R, M₀.eval α ≠ 0) → ∀ (A : K[X]),
      ∃ (PP : K → RatFunc K) (Rem : K[X]),
        algebraMap K[X] (RatFunc K) A
            / algebraMap K[X] (RatFunc K) (rootProd R mult * M₀)
          = (∑ α ∈ R, PP α) + algebraMap K[X] (RatFunc K) Rem / algebraMap K[X] (RatFunc K) M₀ := by
  intro R
  induction R using Finset.induction_on with
  | empty =>
    intro _ A
    refine ⟨fun _ => 0, A, ?_⟩
    rw [rootProd_empty, one_mul, Finset.sum_empty, zero_add]
  | @insert α R hα ih =>
    intro hpolefree A
    set N := rootProd R mult * M₀ with hNdef
    have hNα : N.eval α ≠ 0 := by
      rw [hNdef, Polynomial.eval_mul]
      exact mul_ne_zero (eval_rootProd_ne_zero mult hα)
        (hpolefree α (Finset.mem_insert_self α R))
    have hpeel := subtract_localPrincipalPart_eq A N (mult α) hNα
    obtain ⟨PP, Rem, hrec⟩ :=
      ih (fun β hβ => hpolefree β (Finset.mem_insert_of_mem hβ)) (localRemainder A N α (mult α))
    refine ⟨fun β => if β = α then localPrincipalPart A N α (mult α) else PP β, Rem, ?_⟩
    rw [Finset.sum_insert hα, if_pos rfl]
    have hsumR : (∑ β ∈ R, (if β = α then localPrincipalPart A N α (mult α) else PP β))
        = ∑ β ∈ R, PP β := by
      refine Finset.sum_congr rfl fun β hβ => ?_
      have hβα : β ≠ α := fun h => hα (h ▸ hβ)
      rw [if_neg hβα]
    rw [hsumR]
    have hden : rootProd (insert α R) mult * M₀
        = (Polynomial.X - Polynomial.C α) ^ mult α * N := by
      rw [rootProd_insert mult hα, hNdef]; ring
    rw [hden]
    have hsplit : algebraMap K[X] (RatFunc K) A
          / algebraMap K[X] (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ mult α * N)
        = localPrincipalPart A N α (mult α)
          + algebraMap K[X] (RatFunc K) (localRemainder A N α (mult α))
              / algebraMap K[X] (RatFunc K) N := by
      have := hpeel
      rw [sub_eq_iff_eq_add] at this
      rw [this]; ring
    rw [hsplit, hrec]
    ring

/-- Dividing by a nonzero constant polynomial is multiplication by the inverse scalar. -/
theorem div_C_eq_algebraMap {Rem : K[X]} {c : K} (hc : c ≠ 0) :
    algebraMap K[X] (RatFunc K) Rem / algebraMap K[X] (RatFunc K) (Polynomial.C c)
      = algebraMap K[X] (RatFunc K) (Polynomial.C c⁻¹ * Rem) := by
  have hCc : algebraMap K[X] (RatFunc K) (Polynomial.C c) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (by simpa using hc)
  rw [map_mul, div_eq_iff hCc, ← map_mul, ← map_mul]
  congr 1
  rw [mul_right_comm, ← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1, one_mul]

open Classical in
/-- A root-product denominator with constant base has a complete principal-part decomposition. -/
theorem completePartialFraction_over_closure (A : K[X]) (mult : K → ℕ) (R : Finset K) {c : K}
    (hc : c ≠ 0) :
    ∃ (P : K[X]) (PP : K → RatFunc K),
      algebraMap K[X] (RatFunc K) A
          / algebraMap K[X] (RatFunc K) (rootProd R mult * Polynomial.C c)
        = algebraMap K[X] (RatFunc K) P + ∑ α ∈ R, PP α := by
  have hpolefree : ∀ α ∈ R, (Polynomial.C c).eval α ≠ 0 := fun α _ => by
    rw [Polynomial.eval_C]; exact hc
  obtain ⟨PP, Rem, hdecomp⟩ := exists_sum_localPrincipalPart (Polynomial.C c) mult R hpolefree A
  refine ⟨Polynomial.C c⁻¹ * Rem, PP, ?_⟩
  rw [hdecomp, div_C_eq_algebraMap hc, add_comm]

open Classical in
/-- Decompose a quotient by root-product principal parts, with regularity certificates at every root. -/
theorem exists_sum_localPrincipalPart_regular (M₀ : K[X]) (mult : K → ℕ) :
    ∀ (R : Finset K), (∀ α ∈ R, M₀.eval α ≠ 0) → ∀ (A : K[X]),
      ∃ (PP : K → RatFunc K) (Rem : K[X]),
        algebraMap K[X] (RatFunc K) A
            / algebraMap K[X] (RatFunc K) (rootProd R mult * M₀)
          = (∑ α ∈ R, PP α) + algebraMap K[X] (RatFunc K) Rem / algebraMap K[X] (RatFunc K) M₀
        ∧ (∀ α ∈ R, RegularAt α
            (algebraMap K[X] (RatFunc K) A
                / algebraMap K[X] (RatFunc K) (rootProd R mult * M₀) - PP α))
        ∧ ∀ α ∈ R, ∃ (A' M' : K[X]), PP α = localPrincipalPart A' M' α (mult α) := by
  intro R
  induction R using Finset.induction_on with
  | empty =>
    intro _ A
    exact ⟨fun _ => 0, A, by rw [rootProd_empty, one_mul, Finset.sum_empty, zero_add],
      (fun α hα => by simp at hα), fun α hα => by simp at hα⟩
  | @insert α₀ R hα₀ ih =>
    intro hpolefree A
    set N := rootProd R mult * M₀ with hNdef
    have hNα₀ : N.eval α₀ ≠ 0 := by
      rw [hNdef, Polynomial.eval_mul]
      exact mul_ne_zero (eval_rootProd_ne_zero mult hα₀)
        (hpolefree α₀ (Finset.mem_insert_self α₀ R))
    have hpeel := subtract_localPrincipalPart_eq A N (mult α₀) hNα₀
    obtain ⟨PP, Rem, hrec, hregrec, hstructrec⟩ :=
      ih (fun β hβ => hpolefree β (Finset.mem_insert_of_mem hβ)) (localRemainder A N α₀ (mult α₀))
    refine ⟨fun β => if β = α₀ then localPrincipalPart A N α₀ (mult α₀) else PP β, Rem, ?_, ?_, ?_⟩
    · simp only [Finset.sum_insert hα₀, if_pos]
      have hsumR : (∑ β ∈ R, (if β = α₀ then localPrincipalPart A N α₀ (mult α₀) else PP β))
          = ∑ β ∈ R, PP β :=
        Finset.sum_congr rfl fun β hβ => if_neg (show β ≠ α₀ from fun h => hα₀ (h ▸ hβ))
      rw [hsumR]
      have hden : rootProd (insert α₀ R) mult * M₀
          = (Polynomial.X - Polynomial.C α₀) ^ mult α₀ * N := by
        rw [rootProd_insert mult hα₀, hNdef]; ring
      rw [hden]
      have hsplit : algebraMap K[X] (RatFunc K) A
            / algebraMap K[X] (RatFunc K) ((Polynomial.X - Polynomial.C α₀) ^ mult α₀ * N)
          = localPrincipalPart A N α₀ (mult α₀)
            + algebraMap K[X] (RatFunc K) (localRemainder A N α₀ (mult α₀))
                / algebraMap K[X] (RatFunc K) N := by
        rw [sub_eq_iff_eq_add] at hpeel; rw [hpeel]; ring
      rw [hsplit, hrec]; ring
    · intro γ hγ
      have hden : rootProd (insert α₀ R) mult * M₀
          = (Polynomial.X - Polynomial.C α₀) ^ mult α₀ * N := by
        rw [rootProd_insert mult hα₀, hNdef]; ring
      have hwhole : algebraMap K[X] (RatFunc K) A
            / algebraMap K[X] (RatFunc K) (rootProd (insert α₀ R) mult * M₀)
          = localPrincipalPart A N α₀ (mult α₀)
            + algebraMap K[X] (RatFunc K) (localRemainder A N α₀ (mult α₀))
                / algebraMap K[X] (RatFunc K) N := by
        rw [sub_eq_iff_eq_add] at hpeel; rw [hden, hpeel]; ring
      rw [hwhole]
      simp only []
      rcases eq_or_ne γ α₀ with hγα₀ | hγα₀
      · subst hγα₀
        rw [if_pos rfl, add_sub_cancel_left]
        exact ⟨localRemainder A N γ (mult γ), N, hNα₀, rfl⟩
      · rw [if_neg hγα₀]
        have hmemR : γ ∈ R := Finset.mem_of_mem_insert_of_ne hγ hγα₀
        have h1 : RegularAt γ (localPrincipalPart A N α₀ (mult α₀)) :=
          RegularAt.localPrincipalPart hγα₀ A N (mult α₀)
        have h2 : RegularAt γ
            (algebraMap K[X] (RatFunc K) (localRemainder A N α₀ (mult α₀))
                / algebraMap K[X] (RatFunc K) N - PP γ) := hregrec γ hmemR
        have hrw : localPrincipalPart A N α₀ (mult α₀)
              + algebraMap K[X] (RatFunc K) (localRemainder A N α₀ (mult α₀))
                  / algebraMap K[X] (RatFunc K) N - PP γ
            = localPrincipalPart A N α₀ (mult α₀)
              + (algebraMap K[X] (RatFunc K) (localRemainder A N α₀ (mult α₀))
                  / algebraMap K[X] (RatFunc K) N - PP γ) := by ring
        rw [hrw]
        exact h1.add h2
    · intro γ hγ
      simp only []
      rcases eq_or_ne γ α₀ with hγα₀ | hγα₀
      · subst hγα₀; exact ⟨A, N, by rw [if_pos rfl]⟩
      · rw [if_neg hγα₀]
        exact hstructrec γ (Finset.mem_of_mem_insert_of_ne hγ hγα₀)

end DeepWiki.SymbolicIntegration
