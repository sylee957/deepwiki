import DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors.Basic
import DeepWiki.SymbolicIntegration.Core.Differential.NormalSpecial

/-! # Product criteria for implicit-derivative linear factors

Product-level normal, special, and splitting criteria for `implicitDeriv v`.
-/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

section LinearFactor
open Polynomial

/-- Squarefree polynomial, normal: `∏_{a∈s}(X − a)` is normal iff `∀ a ∈ s, v(a) ≠ a′`. -/
theorem isCoprime_prod_X_sub_C_implicitDeriv_iff {K : Type*} [Field K] [Differential K]
    (v : K[X]) (s : Finset K) :
    IsCoprime (∏ a ∈ s, (X - C a)) (Differential.implicitDeriv v (∏ a ∈ s, (X - C a)))
      ↔ ∀ a ∈ s, v.eval a ≠ a′ := by
  classical
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  constructor
  · intro hnorm a ha
    have hdvd : (X - C a) ∣ ∏ b ∈ s, (X - C b) := Finset.dvd_prod_of_mem _ ha
    exact (isCoprime_X_sub_C_implicitDeriv_iff v a).mp (IsNormal.of_dvd hnorm hdvd)
  · intro h
    refine IsNormal.prod s (fun a => X - C a) (fun a ha => ?_) (fun a _ b _ hab => ?_)
    · exact (isCoprime_X_sub_C_implicitDeriv_iff v a).mpr (h a ha)
    · exact isCoprime_X_sub_C_iff.mpr (by rw [eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr hab)

/-- Squarefree polynomial, special: `∏_{a∈s}(X − a)` is special iff `∀ a ∈ s, v(a) = a′`. -/
theorem dvd_prod_X_sub_C_implicitDeriv_iff {K : Type*} [Field K] [Differential K] (v : K[X])
    (s : Finset K) :
    (∏ a ∈ s, (X - C a)) ∣ Differential.implicitDeriv v (∏ a ∈ s, (X - C a))
      ↔ ∀ a ∈ s, v.eval a = a′ := by
  classical
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  constructor
  · intro hsp a ha
    rw [← Finset.mul_prod_erase s (fun b => X - C b) ha] at hsp
    have hcop : IsCoprime (X - C a) (∏ b ∈ s.erase a, (X - C b)) := by
      rw [isCoprime_X_sub_C_iff, eval_prod]
      refine Finset.prod_ne_zero_iff.mpr (fun b hb => ?_)
      rw [eval_sub, eval_X, eval_C]
      exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hb).symm
    exact (dvd_X_sub_C_implicitDeriv_iff v a).mp (IsSpecial.of_mul_coprime hsp hcop)
  · intro h
    exact IsSpecial.prod s (fun a => X - C a)
      (fun a ha => (dvd_X_sub_C_implicitDeriv_iff v a).mpr (h a ha))

/-- If every scalar is constant, then a product of linear factors is special for `implicitDeriv v` iff it divides `v`. -/
theorem dvd_prod_X_sub_C_implicitDeriv_iff_dvd {K : Type*} [Field K] [Differential K]
    (hconst : ∀ a : K, (a : K)′ = 0) (v : K[X]) (s : Finset K) :
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
    have hfactor : X - C a ∣ ∏ b ∈ s, (X - C b) :=
      Finset.dvd_prod_of_mem (fun b => X - C b) ha
    have hfactor_v : X - C a ∣ v := hfactor.trans h
    exact dvd_iff_isRoot.mp hfactor_v

/-- If every scalar is constant, then a product of linear factors is normal for `implicitDeriv v` iff it is coprime to `v`. -/
theorem isCoprime_prod_X_sub_C_implicitDeriv_iff_isCoprime {K : Type*} [Field K] [Differential K]
    (hconst : ∀ a : K, (a : K)′ = 0) (v : K[X]) (s : Finset K) :
    IsCoprime (∏ a ∈ s, (X - C a)) (Differential.implicitDeriv v (∏ a ∈ s, (X - C a)))
      ↔ IsCoprime (∏ a ∈ s, (X - C a)) v := by
  rw [isCoprime_prod_X_sub_C_implicitDeriv_iff, IsCoprime.prod_left_iff]
  refine forall₂_congr (fun a ha => ?_)
  rw [isCoprime_X_sub_C_iff, hconst a, ne_comm]

/-- General product, special: over char `0`, `∏_{a∈s}(X − a)^{eₐ}` (each `eₐ ≥ 1`) is special
iff `∀ a ∈ s, v(a) = a′`. -/
theorem dvd_prod_X_sub_C_pow_implicitDeriv_iff {K : Type*} [Field K] [CharZero K] [Differential K]
    (v : K[X]) (s : Finset K) (e : K → ℕ) (he : ∀ a ∈ s, 1 ≤ e a) :
    (∏ a ∈ s, (X - C a) ^ e a) ∣ Differential.implicitDeriv v (∏ a ∈ s, (X - C a) ^ e a)
      ↔ ∀ a ∈ s, v.eval a = a′ := by
  classical
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  constructor
  · intro hsp a ha
    rw [← Finset.mul_prod_erase s (fun b => (X - C b) ^ e b) ha] at hsp
    have hcop : IsCoprime ((X - C a) ^ e a) (∏ b ∈ s.erase a, (X - C b) ^ e b) :=
      IsCoprime.pow_left (IsCoprime.prod_right fun b hb => IsCoprime.pow_right
        (isCoprime_X_sub_C_iff.mpr (by rw [eval_sub, eval_X, eval_C]
                                       exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hb).symm)))
    exact (dvd_X_sub_C_pow_implicitDeriv_iff v a (he a ha)).mp (IsSpecial.of_mul_coprime hsp hcop)
  · intro h
    exact IsSpecial.prod s (fun a => (X - C a) ^ e a)
      (fun a ha => (dvd_X_sub_C_pow_implicitDeriv_iff v a (he a ha)).mpr (h a ha))

open Classical in
/-- Splitting factorization of `∏_{a∈s}(X − a)` into its special part (roots with `v(a) = a′`)
and normal part (roots with `v(a) ≠ a′`). -/
theorem splittingFactorization_prod_X_sub_C {K : Type*} [Field K] [Differential K] (v : K[X])
    (s : Finset K) :
    (∏ a ∈ s, (X - C a))
        = (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a))
          * (∏ a ∈ s.filter (fun a => ¬ v.eval a = a′), (X - C a))
      ∧ (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a))
          ∣ Differential.implicitDeriv v (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a))
      ∧ IsCoprime (∏ a ∈ s.filter (fun a => ¬ v.eval a = a′), (X - C a))
          (Differential.implicitDeriv v
            (∏ a ∈ s.filter (fun a => ¬ v.eval a = a′), (X - C a))) :=
  ⟨(Finset.prod_filter_mul_prod_filter_not s _ _).symm,
   (dvd_prod_X_sub_C_implicitDeriv_iff v _).mpr fun _ ha => (Finset.mem_filter.mp ha).2,
   (isCoprime_prod_X_sub_C_implicitDeriv_iff v _).mpr fun _ ha => (Finset.mem_filter.mp ha).2⟩

open Classical in
/-- Special-part extraction for a general product `∏_{a∈s}(X − a)^{eₐ}`: it factors as its
special part (roots with `v(a)=a′`, with multiplicity) times the rest. -/
theorem isSpecial_special_part {K : Type*} [Field K] [CharZero K] [Differential K] (v : K[X])
    (s : Finset K) (e : K → ℕ) (he : ∀ a ∈ s, 1 ≤ e a) :
    (∏ a ∈ s, (X - C a) ^ e a)
        = (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a) ^ e a)
          * (∏ a ∈ s.filter (fun a => ¬ v.eval a = a′), (X - C a) ^ e a)
      ∧ (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a) ^ e a)
          ∣ Differential.implicitDeriv v
              (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a) ^ e a) :=
  ⟨(Finset.prod_filter_mul_prod_filter_not s _ _).symm,
   (dvd_prod_X_sub_C_pow_implicitDeriv_iff v _ e
       (fun a ha => he a (Finset.mem_of_mem_filter a ha))).mpr
     fun _ ha => (Finset.mem_filter.mp ha).2⟩

open Classical in
/-- The special and normal parts of the squarefree splitting are coprime. -/
theorem isCoprime_splitting_parts {K : Type*} [Field K] [Differential K] (v : K[X]) (s : Finset K) :
    IsCoprime (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a))
      (∏ a ∈ s.filter (fun a => ¬ v.eval a = a′), (X - C a)) :=
  isCoprime_prod_X_sub_C_of_disjoint (Finset.disjoint_filter_filter_not s s _)

end LinearFactor

end DeepWiki.SymbolicIntegration
