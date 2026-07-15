import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BivariateView
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.BivariateSorting
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.LazardDescent

/-! # Lazard factorization API

Content and primitive-part factorization for the `K[x][y]` view used in Lazard descent.
-/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

open scoped Classical in
/-- A local `StrongNormalizedGCDMonoid` on `MvPolynomial (Fin 1) K`. -/
@[reducible] noncomputable def strongNormalizedGcdMonoidMvPolynomialFinOne
    (K : Type*) [Field K] : StrongNormalizedGCDMonoid (MvPolynomial (Fin 1) K) :=
  letI := UniqueFactorizationMonoid.strongNormalizationMonoid
    (α := MvPolynomial (Fin 1) K)
  UniqueFactorizationMonoid.toStrongNormalizedGCDMonoid _

open scoped Classical in
/-- The normalized GCD structure induced by `strongNormalizedGcdMonoidMvPolynomialFinOne`. -/
@[reducible] noncomputable def normalizedGcdMonoidMvPolynomialFinOne (K : Type*) [Field K] :
    NormalizedGCDMonoid (MvPolynomial (Fin 1) K) :=
  letI : StrongNormalizedGCDMonoid (MvPolynomial (Fin 1) K) :=
    strongNormalizedGcdMonoidMvPolynomialFinOne K
  inferInstance

/-- The content of `lazardView f` divides the leading `y`-coefficient of `f`. -/
theorem content_lazardView_dvd_leadingYCoeff {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) :
    @Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView f)
      ∣ leadingYCoeff f := by
  letI : StrongNormalizedGCDMonoid (MvPolynomial (Fin 1) K) :=
    strongNormalizedGcdMonoidMvPolynomialFinOne K
  rw [leadingYCoeff, Polynomial.leadingCoeff]
  exact Polynomial.content_dvd_coeff _

/-- If `C (leadingYCoeff f)` divides `lazardView f`, its content is associated to `leadingYCoeff f`. -/
theorem content_associated_leadingYCoeff_of_C_dvd {K : Type*} [Field K]
    {f : MvPolynomial (Fin 2) K}
    (hdvd : Polynomial.C (leadingYCoeff f) ∣ lazardView f) :
    Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView f))
      (leadingYCoeff f) := by
  letI : StrongNormalizedGCDMonoid (MvPolynomial (Fin 1) K) :=
    strongNormalizedGcdMonoidMvPolynomialFinOne K
  refine associated_of_dvd_dvd (content_lazardView_dvd_leadingYCoeff f) ?_
  exact Polynomial.dvd_content_iff_C_dvd.mpr hdvd

/-- `C (leadingYCoeff f) ∣ lazardView f` iff the content is associated to `leadingYCoeff f`. -/
theorem C_dvd_lazardView_iff_content_associated {K : Type*} [Field K]
    {f : MvPolynomial (Fin 2) K} :
    Polynomial.C (leadingYCoeff f) ∣ lazardView f ↔
      Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView f))
        (leadingYCoeff f) := by
  letI : StrongNormalizedGCDMonoid (MvPolynomial (Fin 1) K) :=
    strongNormalizedGcdMonoidMvPolynomialFinOne K
  refine ⟨content_associated_leadingYCoeff_of_C_dvd, fun hassoc => ?_⟩
  exact Polynomial.dvd_content_iff_C_dvd.mp hassoc.symm.dvd

/-- If `C (leadingYCoeff f)` divides `lazardView f`, the primitive part has unit leading coefficient. -/
theorem leadingCoeff_primPart_isUnit_of_C_dvd {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : f ≠ 0) (hdvd : Polynomial.C (leadingYCoeff f) ∣ lazardView f) :
    IsUnit ((@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
      (lazardView f)).leadingCoeff) := by
  letI : StrongNormalizedGCDMonoid (MvPolynomial (Fin 1) K) :=
    strongNormalizedGcdMonoidMvPolynomialFinOne K
  set c := Polynomial.content (lazardView f) with hc
  set s := Polynomial.primPart (lazardView f) with hs
  have hassoc : Associated c (leadingYCoeff f) := content_associated_leadingYCoeff_of_C_dvd hdvd
  have hc0 : c ≠ 0 := by
    rw [hc, Ne, Polynomial.content_eq_zero_iff]; exact lazardView_eq_zero_iff.not.mpr hf
  have hReq : leadingYCoeff f = c * s.leadingCoeff := by
    conv_lhs => rw [leadingYCoeff, Polynomial.eq_C_content_mul_primPart (lazardView f), ← hc, ← hs]
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
  obtain ⟨u, hu⟩ := hassoc
  have : c * s.leadingCoeff = c * (u : MvPolynomial (Fin 1) K) := by rw [← hReq, hu]
  rw [mul_right_inj' hc0] at this
  rw [this]; exact u.isUnit

/-- Lazard factorization: `lazardView f = C c * S` with `c ∼ leadingYCoeff f` and monic primitive `S`. -/
theorem lazard_Pk_eq_Rk_Sk {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K} (hf : f ≠ 0)
    (hdvd : Polynomial.C (leadingYCoeff f) ∣ lazardView f) :
    ∃ S : Polynomial (MvPolynomial (Fin 1) K),
      lazardView f = Polynomial.C (@Polynomial.content _ _
          (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView f)) * S ∧
        Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
          (lazardView f)) (leadingYCoeff f) ∧
        S.IsPrimitive ∧ IsUnit S.leadingCoeff := by
  letI : StrongNormalizedGCDMonoid (MvPolynomial (Fin 1) K) :=
    strongNormalizedGcdMonoidMvPolynomialFinOne K
  refine ⟨(lazardView f).primPart, Polynomial.eq_C_content_mul_primPart (lazardView f),
    content_associated_leadingYCoeff_of_C_dvd hdvd, Polynomial.isPrimitive_primPart _,
    leadingCoeff_primPart_isUnit_of_C_dvd hf hdvd⟩

/-- Lazard factorization for every sorted basis element once the base divisibility holds. -/
theorem lazard_Pk_eq_Rk_Sk_of_sortedByYDegree {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDvd hB)
    (i : Fin B.card) :
    ∃ S : Polynomial (MvPolynomial (Fin 1) K),
      lazardView (sortedByYDegree hB i) = Polynomial.C (@Polynomial.content _ _
          (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView (sortedByYDegree hB i))) * S ∧
        Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
          (lazardView (sortedByYDegree hB i))) (leadingYCoeff (sortedByYDegree hB i)) ∧
        S.IsPrimitive ∧ IsUnit S.leadingCoeff :=
  lazard_Pk_eq_Rk_Sk (hB.ne_zero (Finset.mem_coe.mpr (sortedByYDegree_mem hB i)))
    (C_dvd_lazardView_sortedByYDegree hB hbase i)

/-- Lazard factorization for every sorted basis element from the degree-zero base condition. -/
theorem lazard_Pk_eq_Rk_Sk_of_sortedByYDegree_of_degreeOf_zero {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hbase : HasLazardBaseDegreeZero hB)
    (i : Fin B.card) :
    ∃ S : Polynomial (MvPolynomial (Fin 1) K),
      lazardView (sortedByYDegree hB i) = Polynomial.C (@Polynomial.content _ _
          (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView (sortedByYDegree hB i))) * S ∧
        Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
          (lazardView (sortedByYDegree hB i))) (leadingYCoeff (sortedByYDegree hB i)) ∧
        S.IsPrimitive ∧ IsUnit S.leadingCoeff :=
  lazard_Pk_eq_Rk_Sk_of_sortedByYDegree hB (baseDvd_of_degreeOf_zero hB hbase) i

end DeepWiki.SymbolicIntegration
