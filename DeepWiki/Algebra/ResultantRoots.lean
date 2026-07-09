import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Resultants and common roots

Root-existence criterion for vanishing polynomial resultants.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-- For a nonzero `f` that splits, `res(f, g) = 0` iff some root `α` of `f` has `g(α) = 0`. -/
theorem resultant_eq_zero_iff_exists_root {S : Type*} [CommRing S] [IsDomain S] {f g : S[X]}
    (n : ℕ) (hg : g.natDegree ≤ n) (hf : f.Splits) (hf0 : f ≠ 0) :
    Polynomial.resultant f g f.natDegree n = 0 ↔ ∃ α ∈ f.roots, g.eval α = 0 := by
  rw [Polynomial.resultant_eq_prod_eval f g n hg hf, mul_eq_zero,
    or_iff_right (pow_ne_zero n (leadingCoeff_ne_zero.mpr hf0)),
    Multiset.prod_eq_zero_iff, Multiset.mem_map]

end DeepWiki.SymbolicIntegration
