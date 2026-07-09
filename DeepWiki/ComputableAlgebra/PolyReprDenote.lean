import DeepWiki.ComputableAlgebra.PolyRepr

/-! # Representation-generic denotation for `CPolyRepr` (Step 3)

The denotation `toPoly : P α → (CRingSpec.R α)[X]` reads a representation-independent computable
polynomial as a genuine Mathlib polynomial, via `coeff` alone. The fundamental bridge
`(toPoly p).coeff k = toR (coeff p k)` makes every homomorphism square (`toPoly (add p q) =
toPoly p + toPoly q`, …) fall out coefficient-wise — with **no `List` induction**, so they hold for
every representation at once. See `docs/representation-independent-poly.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.CPolyRepr

variable {P : Type u → Type u} [CPolyRepr P] {α : Type u} [CCommRing α] [CRingSpec α]

/-- Representation-generic denotation into `(CRingSpec.R α)[X]`: `∑ i<degBound, C(toR(coeff p i))·Xⁱ`. -/
noncomputable def toPoly (p : P α) : (CRingSpec.R α)[X] :=
  ∑ i ∈ Finset.range (degBound p), Polynomial.C (CRingSpec.toR (coeff p i)) * X ^ i

/-- **The fundamental coefficient bridge:** `(toPoly p).coeff k = toR (coeff p k)` for every `k`
(past `degBound`, both are `0`). Every homomorphism square reduces to this. -/
theorem coeff_toPoly (p : P α) (k : ℕ) : (toPoly p).coeff k = CRingSpec.toR (coeff p k) := by
  rw [toPoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]
  split
  · rfl
  · rename_i h; simp only [not_lt] at h; rw [coeff_ge p k h, CRingSpec.toR_zero]

/-- `((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i` (list-sum ↔ finset-sum bridge). -/
theorem sum_list_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- `toPoly` is additive. -/
theorem toPoly_add (p q : P α) : toPoly (add p q) = toPoly p + toPoly q := by
  apply Polynomial.ext; intro k
  rw [coeff_toPoly, Polynomial.coeff_add, coeff_toPoly, coeff_toPoly, toR_coeff_add]

/-- `toPoly` commutes with negation. -/
theorem toPoly_neg (p : P α) : toPoly (neg p) = - toPoly p := by
  apply Polynomial.ext; intro k
  rw [coeff_toPoly, Polynomial.coeff_neg, coeff_toPoly, toR_coeff_neg]

/-- `toPoly` realizes scalar multiplication. -/
theorem toPoly_scale (c : α) (p : P α) :
    toPoly (scale c p) = Polynomial.C (CRingSpec.toR c) * toPoly p := by
  apply Polynomial.ext; intro k
  rw [coeff_toPoly, Polynomial.coeff_C_mul, coeff_toPoly, toR_coeff_scale]

/-- `toPoly` is multiplicative: the convolution `mul` realizes polynomial multiplication. -/
theorem toPoly_mul (p q : P α) : toPoly (mul p q) = toPoly p * toPoly q := by
  apply Polynomial.ext; intro k
  rw [coeff_toPoly, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => (toPoly p).coeff a * (toPoly q).coeff b)]
  by_cases hk : k < degBound p + degBound q
  · rw [toR_coeff_mul p q k hk, sum_list_range]
    apply Finset.sum_congr rfl; intro j _; rw [coeff_toPoly, coeff_toPoly]
  · simp only [not_lt] at hk
    rw [mul, coeff_ofFn, if_neg (by omega), CRingSpec.toR_zero]
    symm; apply Finset.sum_eq_zero; intro x hx; rw [Finset.mem_range] at hx
    rw [coeff_toPoly, coeff_toPoly]
    rcases le_or_gt (degBound p) x with h | h
    · rw [coeff_ge p x h, CRingSpec.toR_zero, zero_mul]
    · rw [coeff_ge q (k - x) (by omega), CRingSpec.toR_zero, mul_zero]

end DeepWiki.SymbolicIntegration.CPolyRepr
