import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.LazardFactorization

/-! # No common `y`-factor for Lazard descent

General `K[x][y]` divisor propagation and the no-common-`y`-factor base for Lazard descent.
-/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

/-- A primitive divisor of `C c * g` divides `g`. -/
theorem isPrimitive_dvd_of_dvd_C_mul {K : Type*} [Field K]
    {P g : Polynomial (MvPolynomial (Fin 1) K)} {c : MvPolynomial (Fin 1) K}
    (hP : P.IsPrimitive) (hc : c ≠ 0) (hg : g ≠ 0) (hdvd : P ∣ Polynomial.C c * g) :
    P ∣ g := by
  letI : StrongNormalizedGCDMonoid (MvPolynomial (Fin 1) K) :=
    strongNormalizedGcdMonoidMvPolynomialFinOne K
  have hCg0 : Polynomial.C c * g ≠ 0 :=
    mul_ne_zero (by rwa [Ne, Polynomial.C_eq_zero]) hg
  have hpp : P ∣ (Polynomial.C c * g).primPart :=
    (hP.dvd_primPart_iff_dvd hCg0).mpr hdvd
  rw [Polynomial.primPart_mul hCg0] at hpp
  obtain ⟨u, hu⟩ := Polynomial.isUnit_primPart_C c
  rw [← hu] at hpp
  rw [(u.isUnit).dvd_mul_left] at hpp
  exact (hP.dvd_primPart_iff_dvd hg).mp hpp

/-- The primitive part of `lazardView f` is primitive. -/
theorem isPrimitive_primPart_lazardView {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) :
    (@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView f)).IsPrimitive :=
  letI : StrongNormalizedGCDMonoid (MvPolynomial (Fin 1) K) :=
    strongNormalizedGcdMonoidMvPolynomialFinOne K
  Polynomial.isPrimitive_primPart _

/-- The primitive part of `lazardView f` divides `lazardView f`. -/
theorem primPart_lazardView_dvd {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) :
    (@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView f))
      ∣ lazardView f :=
  letI : StrongNormalizedGCDMonoid (MvPolynomial (Fin 1) K) :=
    strongNormalizedGcdMonoidMvPolynomialFinOne K
  Polynomial.primPart_dvd _

/-- `degreeOf 0 f = 0` iff the primitive part of `lazardView f` is a unit. -/
theorem degreeOf_zero_iff_isUnit_primPart_lazardView {K : Type*} [Field K]
    {f : MvPolynomial (Fin 2) K} :
    degreeOf 0 f = 0 ↔
      IsUnit (@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView f)) := by
  letI : StrongNormalizedGCDMonoid (MvPolynomial (Fin 1) K) :=
    strongNormalizedGcdMonoidMvPolynomialFinOne K
  rw [← natDegree_lazardView, ← Polynomial.natDegree_primPart (p := lazardView f)]
  constructor
  · intro h0
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
    rw [Polynomial.isUnit_C]
    have hprim := Polynomial.isPrimitive_primPart (lazardView f)
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.isPrimitive_iff_content_eq_one,
      Polynomial.content_C, normalize_eq_one] at hprim
    exact hprim
  · intro hu
    exact Polynomial.natDegree_eq_zero_of_isUnit hu

/-- The primitive part of the minimum element's view divides the next sorted basis element's view. -/
theorem primPart_lazardView_min_dvd_succ {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (i0 : Fin B.card) {i i1 : Fin B.card} (hii1 : i < i1)
    (hsucc : ∀ j : Fin B.card, j < i1 → j ≤ i)
    (hIH : ∀ j : Fin B.card, j ≤ i →
      (@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
        (lazardView (sortedByYDegree hB i0))) ∣ lazardView (sortedByYDegree hB j)) :
    (@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
      (lazardView (sortedByYDegree hB i0))) ∣ lazardView (sortedByYDegree hB i1) := by
  letI : StrongNormalizedGCDMonoid (MvPolynomial (Fin 1) K) :=
    strongNormalizedGcdMonoidMvPolynomialFinOne K
  set P := (lazardView (sortedByYDegree hB i0)).primPart with hP_def
  set fi := sortedByYDegree hB i with hfi_def
  set fj := sortedByYDegree hB i1 with hfj_def
  have hfi0 : fi ≠ 0 := hB.ne_zero (Finset.mem_coe.mpr (sortedByYDegree_mem hB i))
  have hfj0 : fj ≠ 0 := hB.ne_zero (Finset.mem_coe.mpr (sortedByYDegree_mem hB i1))
  have hdlt : degreeOf 0 fi < degreeOf 0 fj := degreeOf_sortedByYDegree_strictMono hB hii1
  obtain ⟨q, hq⟩ := leadingYCoeff_sortedByYDegree_dvd_of_lt hB hii1
  set sh := degreeOf 0 fj - degreeOf 0 fi with hsh
  set R := yConst q * fj - X 0 ^ sh * fi with hR_def
  have hRmem : R ∈ I :=
    lazard_lemma3_reductionStep_mem (hB.isGroebnerBasis.1 fi (sortedByYDegree_mem hB i))
      (hB.isGroebnerBasis.1 fj (sortedByYDegree_mem hB i1))
  have hRdeg : degreeOf 0 R < degreeOf 0 fj :=
    lazard_lemma3_reductionStep hfi0 hdlt hq.symm
  have hRdvd : P ∣ lazardView R := by
    by_cases hR0 : R = 0
    · rw [hR0, lazardView_eq_zero_iff.mpr rfl]; exact dvd_zero _
    refine dvd_lazardView_of_mem_of_dvd_bounded hB hRmem hR0 (fun b hb hbdeg => ?_)
    have hbi1 : degreeOf 0 b < degreeOf 0 fj := lt_of_le_of_lt hbdeg hRdeg
    obtain ⟨j, hji1, hbj⟩ := exists_sortedIndex_le_of_degreeOf_le (i := i1) hB hb (le_of_lt hbi1)
    have hjlt : j < i1 := by
      by_contra hge
      rw [not_lt] at hge
      have hle : degreeOf 0 fj ≤ degreeOf 0 (sortedByYDegree hB j) := by
        rcases lt_or_eq_of_le hge with h | h
        · exact le_of_lt (degreeOf_sortedByYDegree_strictMono hB h)
        · rw [hfj_def, h]
      rw [hbj] at hbi1
      exact absurd hbi1 (not_lt.mpr hle)
    rw [hbj]
    exact hIH j (hsucc j hjlt)
  have hfi_dvd : P ∣ lazardView fi := hIH i le_rfl
  have hCq : P ∣ Polynomial.C q * lazardView fj := by
    have heq : Polynomial.C q * lazardView fj
        = lazardView R + Polynomial.X ^ sh * lazardView fi := by
      rw [hR_def, lazardView_reductionStep]; ring
    rw [heq]
    exact dvd_add hRdvd (Dvd.dvd.mul_left hfi_dvd _)
  have hq0 : (q : MvPolynomial (Fin 1) K) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hq
    exact (leadingYCoeff_ne_zero.mpr hfi0) hq
  exact isPrimitive_dvd_of_dvd_C_mul (isPrimitive_primPart_lazardView _) hq0
    (lazardView_eq_zero_iff.not.mpr hfj0) hCq

/-- The primitive part of the minimum element's view divides every sorted basis element's view. -/
theorem primPart_lazardView_min_dvd_all {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (i0 : Fin B.card) (hi0 : i0.val = 0) (i : Fin B.card) :
    (@Polynomial.primPart _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
      (lazardView (sortedByYDegree hB i0))) ∣ lazardView (sortedByYDegree hB i) := by
  letI : StrongNormalizedGCDMonoid (MvPolynomial (Fin 1) K) :=
    strongNormalizedGcdMonoidMvPolynomialFinOne K
  induction hi : i.val using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    subst hi
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · have hii0 : i = i0 := Fin.ext (by rw [h0, hi0])
      rw [hii0]
      exact primPart_lazardView_dvd _
    · set i' : Fin B.card := ⟨i.val - 1, by omega⟩ with hi'_def
      have hi'val : i'.val = i.val - 1 := by rw [hi'_def]
      have hi'lt : i' < i := by rw [Fin.lt_def, hi'val]; omega
      have hsucc : ∀ k : Fin B.card, k < i → k ≤ i' := by
        intro k hk; rw [Fin.le_def, hi'val]; rw [Fin.lt_def] at hk; omega
      have hIH : ∀ j : Fin B.card, j ≤ i' →
          (lazardView (sortedByYDegree hB i0)).primPart ∣ lazardView (sortedByYDegree hB j) := by
        intro j hji'
        exact ih j.val (by rw [Fin.le_def, hi'val] at hji'; omega) j rfl
      exact primPart_lazardView_min_dvd_succ hB i0 hi'lt hsucc hIH

/-- No nonunit `K[x][y]` divisor divides every sorted basis element's `lazardView`. -/
def HasNoCommonYFactor {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 2) K)}
    {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K))) : Prop :=
  ∀ P : Polynomial (MvPolynomial (Fin 1) K),
    (∀ i : Fin B.card, P ∣ lazardView (sortedByYDegree hB i)) → IsUnit P

/-- If there is no common `y`-factor, the minimum sorted basis element has `y`-degree zero. -/
theorem degreeOf_min_eq_zero_of_hasNoCommonYFactor {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hncf : HasNoCommonYFactor hB) (i0 : Fin B.card) (hi0 : i0.val = 0) :
    degreeOf 0 (sortedByYDegree hB i0) = 0 := by
  letI : StrongNormalizedGCDMonoid (MvPolynomial (Fin 1) K) :=
    strongNormalizedGcdMonoidMvPolynomialFinOne K
  have hunit : IsUnit ((lazardView (sortedByYDegree hB i0)).primPart) :=
    hncf _ (fun i => primPart_lazardView_min_dvd_all hB i0 hi0 i)
  exact degreeOf_zero_iff_isUnit_primPart_lazardView.mpr hunit

/-- Lazard descent divisibility follows from the no-common-`y`-factor condition. -/
theorem C_dvd_lazardView_sortedByYDegree_of_hasNoCommonYFactor {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hncf : HasNoCommonYFactor hB) (i : Fin B.card) :
    Polynomial.C (leadingYCoeff (sortedByYDegree hB i)) ∣ lazardView (sortedByYDegree hB i) :=
  C_dvd_lazardView_sortedByYDegree_of_degreeOf_zero hB
    (fun i0 hi0 => degreeOf_min_eq_zero_of_hasNoCommonYFactor hB hncf i0 hi0) i

/-- Lazard factorization follows from the no-common-`y`-factor condition. -/
theorem lazard_Pk_eq_Rk_Sk_of_hasNoCommonYFactor {K : Type*} [Field K]
    {I : Ideal (MvPolynomial (Fin 2) K)} {B : Finset (MvPolynomial (Fin 2) K)}
    (hB : IsReducedGroebnerBasis MonomialOrder.lex I (↑B : Set (MvPolynomial (Fin 2) K)))
    (hncf : HasNoCommonYFactor hB) (i : Fin B.card) :
    ∃ S : Polynomial (MvPolynomial (Fin 1) K),
      lazardView (sortedByYDegree hB i) = Polynomial.C (@Polynomial.content _ _
          (normalizedGcdMonoidMvPolynomialFinOne K) (lazardView (sortedByYDegree hB i))) * S ∧
        Associated (@Polynomial.content _ _ (normalizedGcdMonoidMvPolynomialFinOne K)
          (lazardView (sortedByYDegree hB i))) (leadingYCoeff (sortedByYDegree hB i)) ∧
        S.IsPrimitive ∧ IsUnit S.leadingCoeff :=
  lazard_Pk_eq_Rk_Sk_of_sortedByYDegree_of_degreeOf_zero hB
    (fun i0 hi0 => degreeOf_min_eq_zero_of_hasNoCommonYFactor hB hncf i0 hi0) i

end DeepWiki.SymbolicIntegration
