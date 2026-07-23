import DeepWiki.SymbolicIntegration.DifferentialAlgebra.PolynomialImplicitDerivationDegree
import DeepWiki.Algebra.GcdBasics
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Algebra.Polynomial.Derivative

/-! # Basic implicit-derivative linear-factor facts

Single-factor criteria and elementary products for the monomial derivation
`implicitDeriv v` on `K[X]` (`X′ = v`). -/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

section LinearFactor
open Polynomial

/-- Monomial derivation of a linear factor: `implicitDeriv v (X − a) = v − C a′`. -/
theorem implicitDeriv_X_sub_C {A : Type*} [CommRing A] [Differential A] (v : A[X]) (a : A) :
    Differential.implicitDeriv v (X - C a) = v - C a′ := by
  rw [map_sub, Differential.implicitDeriv_X, Differential.implicitDeriv_C]

/-- Over a field, `IsCoprime (X − a) g ↔ g.eval a ≠ 0`. -/
theorem isCoprime_X_sub_C_iff {K : Type*} [Field K] {a : K} {g : K[X]} :
    IsCoprime (X - C a) g ↔ g.eval a ≠ 0 := by
  rw [(prime_X_sub_C a).coprime_iff_not_dvd, dvd_iff_isRoot]; rfl

open Classical in
/-- Squarefree factorization: `∏_{a∈s}(X − a)^{eₐ} = ∏ₖ (∏_{a : eₐ=k}(X − a))ᵏ`. -/
theorem prod_X_sub_C_pow_eq_squarefree_factorization {K : Type*} [CommRing K] (s : Finset K)
    (e : K → ℕ) :
    (∏ a ∈ s, (X - C a) ^ e a)
      = ∏ k ∈ s.image e, (∏ a ∈ s.filter (fun a => e a = k), (X - C a)) ^ k := by
  rw [← Finset.prod_fiberwise_of_maps_to (t := s.image e)
        (fun a ha => Finset.mem_image_of_mem e ha)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun a ha => by rw [(Finset.mem_filter.mp ha).2]

/-- A product of distinct linear factors `∏_{a∈t}(X − a)` is squarefree. -/
theorem squarefree_prod_X_sub_C {K : Type*} [Field K] (t : Finset K) :
    Squarefree (∏ a ∈ t, (X - C a)) :=
  (separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ h => h)).squarefree

/-- Products of linear factors over *disjoint* root sets are coprime. -/
theorem isCoprime_prod_X_sub_C_of_disjoint {K : Type*} [Field K] {s t : Finset K}
    (h : Disjoint s t) :
    IsCoprime (∏ a ∈ s, (X - C a)) (∏ b ∈ t, (X - C b)) := by
  refine IsCoprime.prod_left (fun a ha => IsCoprime.prod_right (fun b hb => ?_))
  refine isCoprime_X_sub_C_iff.mpr ?_
  rw [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr (fun hab => (Finset.disjoint_left.mp h ha) (hab ▸ hb))

open Classical in
/-- The squarefree-factorization parts for distinct multiplicities `k ≠ k'` are coprime. -/
theorem squarefree_factorization_pairwise_coprime {K : Type*} [Field K] (s : Finset K) (e : K → ℕ)
    {k k' : ℕ} (hkk : k ≠ k') :
    IsCoprime (∏ a ∈ s.filter (fun a => e a = k), (X - C a))
      (∏ a ∈ s.filter (fun a => e a = k'), (X - C a)) :=
  isCoprime_prod_X_sub_C_of_disjoint (Finset.disjoint_left.mpr fun _ ha ha' =>
    hkk ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp ha').2))

/-- Single linear factor, normal: `X − a` is normal iff `v(a) ≠ a′`. -/
theorem isCoprime_X_sub_C_implicitDeriv_iff {K : Type*} [Field K] [Differential K] (v : K[X])
    (a : K) :
    IsCoprime (X - C a) (Differential.implicitDeriv v (X - C a)) ↔ v.eval a ≠ a′ := by
  rw [implicitDeriv_X_sub_C, isCoprime_X_sub_C_iff, eval_sub, eval_C, sub_ne_zero]

/-- Single linear factor, special: `X − a` is special iff `v(a) = a′`. -/
theorem dvd_X_sub_C_implicitDeriv_iff {K : Type*} [Field K] [Differential K] (v : K[X]) (a : K) :
    (X - C a) ∣ Differential.implicitDeriv v (X - C a) ↔ v.eval a = a′ := by
  rw [implicitDeriv_X_sub_C, dvd_iff_isRoot, IsRoot.def, eval_sub, eval_C, sub_eq_zero]

/-- If every scalar is constant, then `X - C a` is special for `implicitDeriv v` iff it divides `v`. -/
theorem dvd_X_sub_C_implicitDeriv_iff_dvd {K : Type*} [Field K] [Differential K]
    (hconst : ∀ a : K, (a : K)′ = 0) (v : K[X]) (a : K) :
    (X - C a) ∣ Differential.implicitDeriv v (X - C a) ↔ (X - C a) ∣ v := by
  rw [dvd_X_sub_C_implicitDeriv_iff, hconst a, dvd_iff_isRoot, IsRoot.def, eq_comm]

/-- Linear-factor power, special: over char `0`, `(X − a)ⁿ` (`n ≥ 1`) is special iff `v(a) = a′`. -/
theorem dvd_X_sub_C_pow_implicitDeriv_iff {K : Type*} [Field K] [CharZero K] [Differential K]
    (v : K[X]) (a : K) {n : ℕ} (hn : 1 ≤ n) :
    (X - C a) ^ n ∣ Differential.implicitDeriv v ((X - C a) ^ n) ↔ v.eval a = a′ := by
  have hnu : IsUnit ((n : K[X])) := by
    rw [← map_natCast (C : K →+* K[X])]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))
  have hD : Differential.implicitDeriv v ((X - C a) ^ n)
      = (X - C a) ^ (n - 1) * ((n : K[X]) * (v - C a′)) := by
    rw [Derivation.leibniz_pow, implicitDeriv_X_sub_C, nsmul_eq_mul, smul_eq_mul]; ring
  rw [hD, show (X - C a) ^ n = (X - C a) ^ (n - 1) * (X - C a) from by
        rw [← pow_succ, Nat.sub_add_cancel hn],
    mul_dvd_mul_iff_left (pow_ne_zero (n - 1) (X_sub_C_ne_zero a)),
    hnu.dvd_mul_left, dvd_iff_isRoot, IsRoot.def, eval_sub, eval_C, sub_eq_zero]

end LinearFactor

end DeepWiki.SymbolicIntegration
