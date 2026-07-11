import DeepWiki.SymbolicIntegration.CanonicalRepresentation.Classify
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.NormalSqfree
import DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Radical.Basic

/-! # Squarefree canonical split factors

The one-squarefree-factor normal/special split used by canonical representations.
-/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section SplitSquarefreeFactor
variable {K : Type*} [Field K] [Differential K]

open Classical in
/-- The special part `S = gcd(p, Dp)` of a squarefree `p` (`Dt = v`). Since `p` is squarefree
(`gcd(p, dp/dt) = 1`), the `splitFactor` step's denominator is trivial and `gcd(p, Dp)` is the
whole special part. -/
noncomputable def squarefreeSpecialPart (v p : K[X]) : K[X] :=
  gcd p (Differential.implicitDeriv v p)

open Classical in
/-- The normal part of a squarefree `p`: `N = p / gcd(p, Dp)`. -/
noncomputable def squarefreeNormalPart (v p : K[X]) : K[X] :=
  p / gcd p (Differential.implicitDeriv v p)

open Classical in
/-- The normal/special split of one squarefree factor: `(N, S)` with `N` the normal part
`p/gcd(p,Dp)` and `S = gcd(p,Dp)` the special part. -/
noncomputable def splitSquarefreeFactor (v p : K[X]) : K[X] × K[X] :=
  (squarefreeNormalPart v p, squarefreeSpecialPart v p)

end SplitSquarefreeFactor

section SplitSquarefreeFactorSplit
variable {K : Type*} [Field K] [CharZero K] [Differential K]

open Classical in
omit [CharZero K] in
/-- For a squarefree fully-split `p = ∏_{a∈s}(X − a)`, the special part `gcd(p, Dp)` is exactly the
special factor `∏_{a : v(a)=a′}(X − a)`. -/
theorem squarefreeSpecialPart_prod_X_sub_C_associated (v : K[X]) (s : Finset K) :
    Associated (squarefreeSpecialPart v (∏ a ∈ s, (X - C a)))
      (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a)) :=
  gcd_prod_X_sub_C_implicitDeriv v s

open Classical in
omit [CharZero K] in
/-- `splitSquarefreeFactor` correctness on one squarefree factor: for a squarefree
fully-split `p = ∏_{a∈s}(X − a)`, `splitSquarefreeFactor v p = (N, S)` is a splitting factorization
of `p` (`p = S·N`, `S` special, `N` normal) with both `N, S` squarefree and coprime. -/
theorem splitSquarefreeFactor_prod_X_sub_C (v : K[X]) (s : Finset K) :
    @IsSplittingFactorization _ _ ⟨Differential.implicitDeriv v⟩
        (∏ a ∈ s, (X - C a))
        (splitSquarefreeFactor v (∏ a ∈ s, (X - C a))).2
        (splitSquarefreeFactor v (∏ a ∈ s, (X - C a))).1
      ∧ Squarefree (splitSquarefreeFactor v (∏ a ∈ s, (X - C a))).1
      ∧ Squarefree (splitSquarefreeFactor v (∏ a ∈ s, (X - C a))).2
      ∧ IsCoprime (splitSquarefreeFactor v (∏ a ∈ s, (X - C a))).1
          (splitSquarefreeFactor v (∏ a ∈ s, (X - C a))).2 := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  set p := ∏ a ∈ s, (X - C a) with hp
  set S := squarefreeSpecialPart v p with hS
  set sp := ∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a) with hsp
  set np := ∏ a ∈ s.filter (fun a => ¬ v.eval a = a′), (X - C a) with hnp
  have hSassoc : Associated S sp := squarefreeSpecialPart_prod_X_sub_C_associated v s
  have hsplit := splittingFactorization_prod_X_sub_C v s
  rw [← hp, ← hsp, ← hnp] at hsplit
  obtain ⟨hpeq, hspspec, hnpcop⟩ := hsplit
  have hSne : S ≠ 0 := by
    rw [hS, squarefreeSpecialPart]
    exact fun h => by
      have : p = 0 := eq_zero_of_zero_dvd (h ▸ gcd_dvd_left p _)
      rw [hp, Finset.prod_eq_zero_iff] at this
      obtain ⟨a, _, ha⟩ := this; exact X_sub_C_ne_zero a ha
  have hSdvdp : S ∣ p := gcd_dvd_left _ _
  -- `N = p/S`, and `S · N = p`.
  have hNval : squarefreeNormalPart v p = p / S := rfl
  have hmul : S * squarefreeNormalPart v p = p := by
    rw [hNval, EuclideanDomain.mul_div_cancel' hSne hSdvdp]
  -- splitting factorization: `p = S · N`, S special, N normal.
  have hSspec : IsSpecial S := IsSpecial.of_associated hSassoc.symm hspspec
  have hNassoc : Associated (squarefreeNormalPart v p) np := by
    have : Associated (S * squarefreeNormalPart v p) (sp * np) := by rw [hmul, hpeq]
    exact (Associated.of_mul_left this hSassoc hSne)
  have hNnorm : IsNormal (squarefreeNormalPart v p) :=
    IsNormal.of_associated hNassoc.symm
      ((isCoprime_prod_X_sub_C_implicitDeriv_iff v _).mpr
        (fun a ha => (Finset.mem_filter.mp ha).2))
  refine ⟨⟨(hmul.symm), hSspec, hNnorm⟩, ?_, ?_, ?_⟩
  · -- N squarefree (associated to a squarefree product of distinct linear factors).
    exact hNassoc.squarefree_iff.mpr (squarefree_prod_X_sub_C _)
  · -- S squarefree.
    exact hSassoc.squarefree_iff.mpr (squarefree_prod_X_sub_C _)
  · -- N, S coprime (associated to the coprime normal/special parts).
    exact ((isCoprime_splitting_parts v s).symm.of_isCoprime_of_dvd_left hNassoc.dvd).of_isCoprime_of_dvd_right hSassoc.dvd

end SplitSquarefreeFactorSplit

end DeepWiki.SymbolicIntegration
