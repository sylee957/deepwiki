import DeepWiki.SymbolicIntegration.Computable.Algebraic.GeneralIntegralSoundness

/-! # Abstract idempotent recombination for function algebras

A derivation kills idempotents, so `D(Σ eᵢ Fᵢ) = g` follows from per-component identities
`eᵢ·D(Fᵢ) = eᵢ·g` and a partition of unity `Σ eᵢ = 1`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace FunctionAlgebra

variable {R Q : Type*} [CommRing R] [CommRing Q] [Algebra R Q] (D : Derivation R Q Q)

/-- A derivation kills an idempotent: for `D : Derivation R Q Q` and idempotent `e` (`e * e = e`),
`D e = 0`. -/
theorem derivation_idempotent_eq_zero (e : Q) (he : IsIdempotentElem e) : D e = 0 := by
  -- `D e = 2·(e·D e)`, i.e. `D e · (1 − 2e) = 0`
  have h1 : D (e * e) = e * D e + e * D e := by rw [Derivation.leibniz]; simp [smul_eq_mul]
  rw [he.eq] at h1
  have h2 : D e * (1 - 2 * e) = 0 := by linear_combination h1
  -- `(1 − 2e)² = 1`, so `1 − 2e` is its own inverse
  have hsq : (1 - 2 * e) * (1 - 2 * e) = 1 := by linear_combination (4 : Q) * he.eq
  calc D e = D e * ((1 - 2 * e) * (1 - 2 * e)) := by rw [hsq, mul_one]
    _ = (D e * (1 - 2 * e)) * (1 - 2 * e) := by ring
    _ = 0 := by rw [h2, zero_mul]

/-- `D(e·F) = e·D(F)` for an idempotent `e`. -/
theorem derivation_eIdx_mul (e F : Q) (he : IsIdempotentElem e) : D (e * F) = e * D F := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivation_idempotent_eq_zero D e he, mul_zero,
    add_zero]

/-- Abstract recombination soundness: over pairs `(eᵢ, Fᵢ)` with each `eᵢ` idempotent, per-component
`eᵢ·D(Fᵢ) = eᵢ·g`, and partition of unity `Σ eᵢ = 1`, the sum `F = Σ eᵢ·Fᵢ` satisfies `D(F) = g`. -/
theorem derivation_recombine_eq (pairs : List (Q × Q)) (g : Q)
    (hidem : ∀ p ∈ pairs, IsIdempotentElem p.1)
    (hcomp : ∀ p ∈ pairs, p.1 * D p.2 = p.1 * g)
    (hsum : (pairs.map (fun p => p.1)).sum = 1) :
    D ((pairs.map (fun p => p.1 * p.2)).sum) = g := by
  rw [map_list_sum]
  -- each `D(eᵢ Fᵢ) = eᵢ D Fᵢ = eᵢ g`
  rw [show (pairs.map (fun p => p.1 * p.2)).map (fun x => D x)
      = pairs.map (fun p => p.1 * g) from by
    rw [List.map_map]
    refine List.map_congr_left (fun p hp => ?_)
    simp only [Function.comp_apply]
    rw [derivation_eIdx_mul D p.1 p.2 (hidem p hp), hcomp p hp]]
  -- `Σ eᵢ g = (Σ eᵢ) g = 1·g = g`
  rw [show (fun p : Q × Q => p.1 * g)
      = (fun p : Q × Q => (fun p : Q × Q => p.1) p * g) from rfl,
    List.sum_map_mul_right, hsum, one_mul]

end FunctionAlgebra

end DeepWiki.SymbolicIntegration
