import DeepWiki.SymbolicIntegration.Core.Polynomial.SquarefreePartDerivatives

/-! # Polynomial Yun recurrence terms

The polynomial terms driving the squarefree-factorization recurrence.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

section SquarefreeYun
open UniqueFactorizationMonoid
variable {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D] [NormalizedGCDMonoid D]

open Classical in
/-- The polynomial `Yₖ = ∑_{i≥k} (i−k+1)·(dAᵢ/dx)·∏_{l≥k, l≠i} Aₗ` driving the
squarefree-factorization recurrence. -/
noncomputable def Yun (A : D[X]) (i : ℕ) : D[X] :=
  ∑ a ∈ ((normalizedFactors A.primPart).toFinset.image
      (fun P => (normalizedFactors A.primPart).count P)).filter (fun a => i ≤ a),
    C ((a - i + 1 : ℕ) : D) * derivative (sqfreeFactPart A a)
      * ∏ l ∈ (((normalizedFactors A.primPart).toFinset.image
          (fun P => (normalizedFactors A.primPart).count P)).filter (fun a => i ≤ a)).erase a,
        sqfreeFactPart A l

omit [IsDomain D] [UniqueFactorizationMonoid D] [NormalizedGCDMonoid D] in
/-- Exponent-shifting helper: `(∏ₗ gₗ^(l−j))·(∏_{l≠b} gₗ) = gᵦ^(b−j)·∏_{l≠b} gₗ^(l−j+1)`. -/
private theorem prod_pow_sub_mul_prod_erase (g : ℕ → D[X]) (s : Finset ℕ) (j b : ℕ) (hb : b ∈ s) :
    (∏ l ∈ s, g l ^ (l - j)) * (∏ l ∈ s.erase b, g l)
      = g b ^ (b - j) * ∏ l ∈ s.erase b, g l ^ (l - j + 1) := by
  rw [← Finset.mul_prod_erase _ (fun l => g l ^ (l - j)) hb, mul_assoc, ← Finset.prod_mul_distrib]
  exact congrArg _ (Finset.prod_congr rfl fun l _ => (pow_succ (g l) (l - j)).symm)

open Classical in
/-- Derivative recurrence `d(A⁻⁽ⁱ⁻¹⁾)/dx = A⁻ⁱ · Yᵢ` (`1 ≤ i`). -/
theorem derivative_deflation_pred (A : D[X]) (i : ℕ) (hi : 1 ≤ i) :
    derivative (deflation A (i - 1)) = deflation A i * Yun A i := by
  set I := (normalizedFactors A.primPart).toFinset.image
    (fun P => (normalizedFactors A.primPart).count P) with hI
  set f := sqfreeFactPart A with hf
  set I' := I.filter (fun a => i ≤ a) with hI'
  have hdefi : deflation A i = ∏ l ∈ I', f l ^ (l - i) := by
    rw [deflation_eq_prod_sqfreeFactPart A i, ← hI, ← hf]
    refine (Finset.prod_subset (Finset.filter_subset _ _) (fun l hlI hl => ?_)).symm
    rw [Finset.mem_filter, not_and] at hl
    rw [show l - i = 0 from by have := hl hlI; omega, pow_zero]
  rw [derivative_deflation A (i - 1), ← hI, ← hf, hdefi, Yun, ← hI, ← hf, ← hI', Finset.mul_sum,
    ← Finset.sum_subset (Finset.filter_subset (fun a => i ≤ a) I) (fun a haI ha => ?_)]
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_filter] at ha
    have hinner : ∏ b ∈ I.erase a, f b ^ (b - (i - 1)) = ∏ b ∈ I'.erase a, f b ^ (b - i + 1) := by
      refine (Finset.prod_subset (Finset.erase_subset_erase a (Finset.filter_subset _ _))
        (fun b hbI hb => ?_)).symm.trans (Finset.prod_congr rfl fun b hb => ?_)
      · rw [Finset.mem_erase] at hbI
        rw [Finset.mem_erase, Finset.mem_filter, not_and] at hb
        rw [show b - (i - 1) = 0 from by
          have : ¬ i ≤ b := fun h => (hb hbI.1) ⟨hbI.2, h⟩
          omega, pow_zero]
      · rw [Finset.mem_erase, Finset.mem_filter] at hb
        rw [show b - (i - 1) = b - i + 1 from by omega]
    rw [show a - (i - 1) = a - i + 1 from by omega, show a - i + 1 - 1 = a - i from by omega, hinner]
    linear_combination (-(C ((a - i + 1 : ℕ) : D) * derivative (f a)))
      * prod_pow_sub_mul_prod_erase f I' i a (Finset.mem_filter.mpr ha)
  · rw [Finset.mem_filter, not_and] at ha
    rw [show a - (i - 1) = 0 from by have := ha haI; omega]
    simp

end SquarefreeYun

end DeepWiki.SymbolicIntegration
