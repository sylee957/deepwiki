import DeepWiki.SymbolicIntegration.PartialFraction
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # A closed form for `∫ dx/(1+xⁿ)`
Over an algebraically closed field `K` with `(n : K) ≠ 0` and `1 ≤ n`,
`1/(Xⁿ+1) = ∑_ζ (−ζ/n)·logDeriv(X−ζ)` over the roots `ζ` of `Xⁿ+1` — i.e.
`∫ dx/(1+xⁿ) = ∑_ζ (−ζ/n)·log(x−ζ)`; specializes `ratFunc_eq_sum_residue_logDeriv`. -/

open Polynomial
open scoped Differential

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K] [IsAlgClosed K]

open Classical in
/-- The Lagrange nodal product over the distinct roots of `Xⁿ+1` reconstructs it:
`∏_{ζ ∈ (Xⁿ+1).roots}(X − ζ) = Xⁿ+1` (`(n:K) ≠ 0`). `Xⁿ+1` is monic, splits over `K`
algebraically closed, and is separable, so its roots are simple and the per-root product is the
whole polynomial. -/
theorem nodal_roots_X_pow_add_one_eq {n : ℕ} (hn : (n : K) ≠ 0) :
    Lagrange.nodal (X ^ n + 1 : K[X]).roots.toFinset id = X ^ n + 1 := by
  classical
  set D : K[X] := X ^ n + 1 with hD
  have hsep : D.Separable := by
    have hrw : D = X ^ n - C (-1) := by rw [hD, map_neg, map_one]; ring
    rw [hrw]; exact separable_X_pow_sub_C (-1) hn (by simp)
  have hmonic : D.Monic := monic_X_pow_add_C 1 (by rintro rfl; simp at hn)
  have hsplits : D.Splits := IsAlgClosed.splits D
  have hnodup : D.roots.Nodup := nodup_roots hsep
  rw [Lagrange.nodal_eq]; simp only [id_eq]
  have hprod : (D.roots.map (fun a => X - C a)).prod = D := by
    simpa using (hsplits.eq_prod_roots_of_monic hmonic).symm
  have hlhs : (∏ x ∈ D.roots.toFinset, (X - C x))
      = (D.roots.map (fun a => X - C a)).prod := by
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnodup]
  rw [hlhs, hprod]

omit [IsAlgClosed K] in
/-- The residue of `1/(Xⁿ+1)` at a root `ζ` is `−ζ/n`: `1/(Xⁿ+1)′(ζ) = 1/(n·ζⁿ⁻¹) = −ζ/n`,
using `(Xⁿ+1)′ = n·Xⁿ⁻¹` and `ζⁿ = −1` (so `n·ζⁿ⁻¹ = n·ζⁿ/ζ = −n/ζ`); `ζ ≠ 0` since `0ⁿ+1 = 1`. -/
theorem residue_root_X_pow_add_one {n : ℕ} (hn : (n : K) ≠ 0) (ζ : K)
    (hζ : ζ ∈ (X ^ n + 1 : K[X]).roots) :
    (1 : K) / eval ζ (derivative (X ^ n + 1 : K[X])) = -ζ / (n : K) := by
  have hroot : ζ ^ n + 1 = 0 := by
    have hr := (mem_roots'.mp hζ).2
    simpa [IsRoot, eval_add, eval_pow, eval_X, eval_one] using hr
  have hζn : ζ ^ n = -1 := by linear_combination hroot
  have hn1 : n ≠ 0 := by rintro rfl; simp at hn
  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [zero_pow hn1, zero_add] at hroot; exact one_ne_zero hroot
  have hder : eval ζ (derivative (X ^ n + 1 : K[X])) = (n : K) * ζ ^ (n - 1) := by
    rw [derivative_add, derivative_X_pow, derivative_one, add_zero, eval_mul, eval_C, eval_pow,
      eval_X]
  rw [hder]
  have hpow : ζ ^ (n - 1) = ζ ^ n / ζ := by
    rw [eq_div_iff hζ0, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn1)]
  rw [hpow, hζn]; field_simp

open Classical in
/-- `(Xⁿ+1)` has exactly `n` distinct roots over an algebraically closed field with `(n:K) ≠ 0`:
`#(Xⁿ+1).roots.toFinset = n` (separable + `deg = n`). -/
theorem card_roots_X_pow_add_one {n : ℕ} (hn : (n : K) ≠ 0) :
    (X ^ n + 1 : K[X]).roots.toFinset.card = n := by
  classical
  set D : K[X] := X ^ n + 1 with hD
  have hsep : D.Separable := by
    have hrw : D = X ^ n - C (-1) := by rw [hD, map_neg, map_one]; ring
    rw [hrw]; exact separable_X_pow_sub_C (-1) hn (by simp)
  have hnodup : D.roots.Nodup := nodup_roots hsep
  have hsplits : D.Splits := IsAlgClosed.splits D
  have hn1 : n ≠ 0 := by rintro rfl; simp at hn
  rw [Multiset.toFinset_card_of_nodup hnodup, hsplits.natDegree_eq_card_roots.symm, hD]
  compute_degree!
  rw [if_neg hn1]; simp

open Classical in
/-- Closed form for `∫ dx/(1+xⁿ)`: over `K` algebraically closed with `(n:K) ≠ 0` and `1 ≤ n`,
`1/(Xⁿ+1) = ∑_{ζ ∈ (Xⁿ+1).roots} (−ζ/n)·logDeriv(X−ζ)` in `K(x)` — each root contributes a
logarithm with residue `−ζ/n`. Specializes `ratFunc_eq_sum_residue_logDeriv` at `A = 1`,
`D = Xⁿ+1`. -/
theorem inv_one_add_X_pow_eq_sum_residue_logDeriv {n : ℕ} (hn : (n : K) ≠ 0) (hn1 : 1 ≤ n) :
    (1 : RatFunc K) / algebraMap K[X] (RatFunc K) (X ^ n + 1)
      = ∑ ζ ∈ (X ^ n + 1 : K[X]).roots.toFinset,
          algebraMap K[X] (RatFunc K) (C (-ζ / (n : K)))
            * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C ζ)) := by
  classical
  set D : K[X] := X ^ n + 1 with hD
  set s := D.roots.toFinset with hs
  have hnodal : Lagrange.nodal s id = D := nodal_roots_X_pow_add_one_eq hn
  have hA : (1 : K[X]).degree < s.card := by
    rw [card_roots_X_pow_add_one hn, degree_one]; exact_mod_cast hn1
  have key := ratFunc_eq_sum_residue_logDeriv s 1 hA
  rw [hnodal, map_one] at key
  rw [key]
  refine Finset.sum_congr rfl fun ζ hζ => ?_
  have hmem : ζ ∈ D.roots := Multiset.mem_toFinset.mp hζ
  congr 2
  rw [eval_one, residue_root_X_pow_add_one hn ζ hmem]

open Classical in
/-- The `n = 4` case `∫ dx/(1+x⁴)`: over `K` algebraically closed with `(4:K) ≠ 0`,
`1/(X⁴+1) = ∑_{ζ ∈ (X⁴+1).roots} (−ζ/4)·logDeriv(X−ζ)` — the `n = 4` instance of
`inv_one_add_X_pow_eq_sum_residue_logDeriv`. -/
theorem inv_one_add_X_pow_four_eq_sum_residue_logDeriv (h4 : (4 : K) ≠ 0) :
    (1 : RatFunc K) / algebraMap K[X] (RatFunc K) (X ^ 4 + 1)
      = ∑ ζ ∈ (X ^ 4 + 1 : K[X]).roots.toFinset,
          algebraMap K[X] (RatFunc K) (C (-ζ / (4 : K)))
            * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C ζ)) := by
  have hn : ((4 : ℕ) : K) ≠ 0 := by rw [Nat.cast_ofNat]; exact h4
  simpa using inv_one_add_X_pow_eq_sum_residue_logDeriv hn (by norm_num)

-- `∫ dx/(1+xⁿ) = ∑_ζ (−ζ/n)·log(x−ζ)` over the roots of `Xⁿ+1`.
open Classical in
example {n : ℕ} (hn : (n : K) ≠ 0) (hn1 : 1 ≤ n) :
    (1 : RatFunc K) / algebraMap K[X] (RatFunc K) (X ^ n + 1)
      = ∑ ζ ∈ (X ^ n + 1 : K[X]).roots.toFinset,
          algebraMap K[X] (RatFunc K) (C (-ζ / (n : K)))
            * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C ζ)) :=
  inv_one_add_X_pow_eq_sum_residue_logDeriv hn hn1

-- The `n = 4` case `∫ dx/(1+x⁴)`.
open Classical in
example (h4 : (4 : K) ≠ 0) :
    (1 : RatFunc K) / algebraMap K[X] (RatFunc K) (X ^ 4 + 1)
      = ∑ ζ ∈ (X ^ 4 + 1 : K[X]).roots.toFinset,
          algebraMap K[X] (RatFunc K) (C (-ζ / (4 : K)))
            * Differential.logDeriv (algebraMap K[X] (RatFunc K) (X - C ζ)) :=
  inv_one_add_X_pow_four_eq_sum_residue_logDeriv h4

end DeepWiki.SymbolicIntegration
