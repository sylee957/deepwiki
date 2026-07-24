import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.NoCommonYFactor

/-! # Divide out the common `K[x][y]` factor

The common-factor gcd and cofactor bridge from an arbitrary reduced bivariate
Groebner basis to the no-common-`y`-factor case.
-/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

open scoped Classical in
/-- A local `StrongNormalizedGCDMonoid` on the `lazardView` ring `K[x][y]`. -/
@[reducible] noncomputable def strongGcdMonoidLazardRing (K : Type*) [Field K] :
    StrongNormalizedGCDMonoid (Polynomial (MvPolynomial (Fin 1) K)) :=
  letI := UniqueFactorizationMonoid.strongNormalizationMonoid
    (α := Polynomial (MvPolynomial (Fin 1) K))
  UniqueFactorizationMonoid.toStrongNormalizedGCDMonoid _

open scoped Classical in
/-- The normalized GCD structure induced by `strongGcdMonoidLazardRing`. -/
@[reducible] noncomputable def gcdMonoidLazardRing (K : Type*) [Field K] :
    NormalizedGCDMonoid (Polynomial (MvPolynomial (Fin 1) K)) :=
  letI : StrongNormalizedGCDMonoid (Polynomial (MvPolynomial (Fin 1) K)) :=
    strongGcdMonoidLazardRing K
  inferInstance

open scoped Classical in
/-- The common `K[x][y]` factor of all sorted basis elements, taken in `lazardView` coordinates. -/
noncomputable def gbYGcd {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) :
    Polynomial (MvPolynomial (Fin 1) K) :=
  letI := gcdMonoidLazardRing K
  (Finset.univ : Finset (Fin B.card)).gcd (fun i => lazardView (sortedByYDegree hB i))

/-- The common `K[x][y]` factor divides every sorted basis element's `lazardView`. -/
theorem gbYGcd_dvd {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (i : Fin B.card) :
    @Dvd.dvd _ _ (gbYGcd hB) (lazardView (sortedByYDegree hB i)) := by
  letI := gcdMonoidLazardRing K
  exact Finset.gcd_dvd (Finset.mem_univ i)

open scoped Classical in
/-- The cofactor family obtained by dividing each basis view by `gbYGcd`. -/
noncomputable def gbYGcdCofactor {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) :
    Fin B.card → Polynomial (MvPolynomial (Fin 1) K) :=
  letI := gcdMonoidLazardRing K
  (Finset.extract_gcd (fun i => lazardView (sortedByYDegree hB i)) hne).choose

/-- Each basis view is `gbYGcd` times its cofactor. -/
theorem gbYGcd_mul_cofactor {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) (i : Fin B.card) :
    lazardView (sortedByYDegree hB i) = gbYGcd hB * gbYGcdCofactor hB hne i := by
  letI := gcdMonoidLazardRing K
  exact (Finset.extract_gcd (fun i => lazardView (sortedByYDegree hB i)) hne).choose_spec.1 i
    (Finset.mem_univ i)

/-- The gcd of the cofactor family is one. -/
theorem gbYGcdCofactor_gcd_eq_one {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) :
    letI := gcdMonoidLazardRing K
    (Finset.univ : Finset (Fin B.card)).gcd (gbYGcdCofactor hB hne) = 1 := by
  letI := gcdMonoidLazardRing K
  exact (Finset.extract_gcd (fun i => lazardView (sortedByYDegree hB i)) hne).choose_spec.2

/-- A common divisor of all cofactors is a unit. -/
theorem cofactor_hasNoCommonYFactor {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty)
    (P : Polynomial (MvPolynomial (Fin 1) K))
    (hP : ∀ i : Fin B.card, P ∣ gbYGcdCofactor hB hne i) : IsUnit P := by
  letI := gcdMonoidLazardRing K
  have hdvd : P ∣ (Finset.univ : Finset (Fin B.card)).gcd (gbYGcdCofactor hB hne) :=
    Finset.dvd_gcd (fun i _ => hP i)
  rw [gbYGcdCofactor_gcd_eq_one hB hne] at hdvd
  exact isUnit_of_dvd_one hdvd

/-- The common `K[x][y]` factor pulled back to `MvPolynomial (Fin 2) K`. -/
noncomputable def gbCommonYFactor {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) :
    MvPolynomial (Fin 2) K :=
  (finSuccEquiv K 1).symm (gbYGcd hB)

/-- The `lazardView` of `gbCommonYFactor` is `gbYGcd`. -/
@[simp] theorem lazardView_gbCommonYFactor {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) :
    lazardView (gbCommonYFactor hB) = gbYGcd hB := by
  rw [gbCommonYFactor, lazardView, AlgEquiv.apply_symm_apply]

/-- The pulled-back common factor divides each sorted basis element. -/
theorem gbCommonYFactor_dvd {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (i : Fin B.card) :
    gbCommonYFactor hB ∣ sortedByYDegree hB i := by
  letI := gcdMonoidLazardRing K
  rw [← map_dvd_iff (finSuccEquiv K 1)]
  show lazardView (gbCommonYFactor hB) ∣ lazardView (sortedByYDegree hB i)
  rw [lazardView_gbCommonYFactor]
  exact gbYGcd_dvd hB i

/-- Divide a reduced bivariate Groebner basis by its common `K[x][y]` factor. -/
theorem lazard_thm1_divideOut {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty) :
    ∃ (H : MvPolynomial (Fin 2) K)
      (b' : Fin B.card → Polynomial (MvPolynomial (Fin 1) K)),
      (∀ i, H ∣ sortedByYDegree hB i) ∧
        (∀ i, lazardView (sortedByYDegree hB i) = lazardView H * b' i) ∧
        (∀ P : Polynomial (MvPolynomial (Fin 1) K),
          (∀ i, P ∣ b' i) → IsUnit P) :=
  ⟨gbCommonYFactor hB, gbYGcdCofactor hB hne, gbCommonYFactor_dvd hB,
    fun i => by rw [lazardView_gbCommonYFactor]; exact gbYGcd_mul_cofactor hB hne i,
    cofactor_hasNoCommonYFactor hB hne⟩

/-- Associated divide-out cofactors transfer `HasNoCommonYFactor` to a divided reduced basis. -/
theorem hasNoCommonYFactor_of_cofactor_associated {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty)
    {I' : Ideal (MvPolynomial (Fin 2) K)} {B' : Finset (MvPolynomial (Fin 2) K)}
    (hB' : IsReducedGroebnerBasis MonomialOrder.lex I' (↑B' : Set (MvPolynomial (Fin 2) K)))
    (hassoc : ∀ i : Fin B.card, ∃ j : Fin B'.card,
      Associated (gbYGcdCofactor hB hne i) (lazardView (sortedByYDegree hB' j))) :
    HasNoCommonYFactor hB' := by
  intro P hP
  refine cofactor_hasNoCommonYFactor hB hne P (fun i => ?_)
  obtain ⟨j, hij⟩ := hassoc i
  exact (hP j).trans hij.symm.dvd

/-- Lazard factorization for any reduced basis representing the divide-out cofactors. -/
theorem lazard_Pk_eq_Rk_Sk_of_divideOut {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hne : (Finset.univ : Finset (Fin B.card)).Nonempty)
    {I' : Ideal (MvPolynomial (Fin 2) K)} {B' : Finset (MvPolynomial (Fin 2) K)}
    (hB' : IsReducedGroebnerBasis MonomialOrder.lex I' (↑B' : Set (MvPolynomial (Fin 2) K)))
    (hassoc : ∀ i : Fin B.card, ∃ j : Fin B'.card,
      Associated (gbYGcdCofactor hB hne i) (lazardView (sortedByYDegree hB' j)))
    (j : Fin B'.card) :
    ∃ S : Polynomial (MvPolynomial (Fin 1) K),
      lazardView (sortedByYDegree hB' j) = Polynomial.C (@Polynomial.content _ _
          (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView (sortedByYDegree hB' j))) * S ∧
        Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
          (lazardView (sortedByYDegree hB' j))) (leadingYCoeff (sortedByYDegree hB' j)) ∧
        S.IsPrimitive ∧ IsUnit S.leadingCoeff :=
  lazard_Pk_eq_Rk_Sk_of_hasNoCommonYFactor hB'
    (hasNoCommonYFactor_of_cofactor_associated hB hne hB' hassoc) j

end DeepWiki.SymbolicIntegration
