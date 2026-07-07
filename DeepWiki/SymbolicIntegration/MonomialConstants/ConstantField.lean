import DeepWiki.SymbolicIntegration.MonomialConstants.Basic

/-! # Constant-field monomial tests

Linear-factor specialness and normality tests when all scalars are constants. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section ConstantField
variable {K : Type*} [Field K] [Differential K]

/-- If every scalar is constant, then `X - C a` is special for `implicitDeriv v` iff it divides `v`. -/
theorem dvd_X_sub_C_implicitDeriv_iff_dvd (hconst : ∀ a : K, (a : K)′ = 0) (v : K[X]) (a : K) :
    (X - C a) ∣ Differential.implicitDeriv v (X - C a) ↔ (X - C a) ∣ v := by
  rw [dvd_X_sub_C_implicitDeriv_iff, hconst a, dvd_iff_isRoot, IsRoot.def, eq_comm]

/-- If every scalar is constant, then a product of linear factors is special for `implicitDeriv v` iff it divides `v`. -/
theorem dvd_prod_X_sub_C_implicitDeriv_iff_dvd (hconst : ∀ a : K, (a : K)′ = 0) (v : K[X])
    (s : Finset K) :
    (∏ a ∈ s, (X - C a)) ∣ Differential.implicitDeriv v (∏ a ∈ s, (X - C a))
      ↔ (∏ a ∈ s, (X - C a)) ∣ v := by
  rw [dvd_prod_X_sub_C_implicitDeriv_iff]
  constructor
  · intro h
    refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => isCoprime_X_sub_C_iff.mpr
      (by rw [eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr hab)) (fun a ha => ?_)
    rw [dvd_iff_isRoot, IsRoot.def, h a ha, hconst a]
  · intro h a ha
    rw [hconst a]
    exact (dvd_iff_isRoot.mp ((Finset.dvd_prod_of_mem _ ha).trans h))

/-- If every scalar is constant, then a product of linear factors is normal for `implicitDeriv v` iff it is coprime to `v`. -/
theorem isCoprime_prod_X_sub_C_implicitDeriv_iff_isCoprime (hconst : ∀ a : K, (a : K)′ = 0)
    (v : K[X]) (s : Finset K) :
    IsCoprime (∏ a ∈ s, (X - C a)) (Differential.implicitDeriv v (∏ a ∈ s, (X - C a)))
      ↔ IsCoprime (∏ a ∈ s, (X - C a)) v := by
  rw [isCoprime_prod_X_sub_C_implicitDeriv_iff, IsCoprime.prod_left_iff]
  refine forall₂_congr (fun a ha => ?_)
  rw [isCoprime_X_sub_C_iff, hconst a, ne_comm]

end ConstantField

end DeepWiki.SymbolicIntegration
