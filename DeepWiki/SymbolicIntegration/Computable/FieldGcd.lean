import DeepWiki.SymbolicIntegration.Computable.Field

/-! # Generic Euclidean bridge lemmas over a `CField`

Termination support for fuel-free Euclidean division over arbitrary `[CField α]`, proved through
`toPolyG` over `K[X]`, plus a fraction-field clearing lemma used by Hermite-style identities. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]
variable [CFieldSpec α]

/-! ### Termination for the generic Euclidean division

The strict degree drop over `K[X]` and the corresponding normalized-list length drop for the remainder
loop. -/

/-- One Euclidean-division step strictly drops the degree in `(CFieldSpec.K α)[X]`: subtracting
`C (lcP/lcQ)·X^(degP−degQ)·Q` cancels the top coefficient. -/
theorem degreeG_reduce_step_lt {P Q : (CFieldSpec.K α)[X]} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree ≤ P.natDegree) :
    (P - C (P.leadingCoeff / Q.leadingCoeff)
        * X ^ (P.natDegree - Q.natDegree) * Q).degree < P.degree := by
  have hQlc : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hPlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hc0 : P.leadingCoeff / Q.leadingCoeff ≠ 0 := div_ne_zero hPlc hQlc
  have hCc : (C (P.leadingCoeff / Q.leadingCoeff)) ≠ 0 := by rwa [Ne, Polynomial.C_eq_zero]
  have hXk : (X ^ (P.natDegree - Q.natDegree) : (CFieldSpec.K α)[X]) ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  set T := C (P.leadingCoeff / Q.leadingCoeff) * X ^ (P.natDegree - Q.natDegree) * Q with hT
  have hT0 : T ≠ 0 := mul_ne_zero (mul_ne_zero hCc hXk) hQ
  have hTnd : T.natDegree = P.natDegree := by
    rw [hT, Polynomial.natDegree_mul (mul_ne_zero hCc hXk) hQ,
      Polynomial.natDegree_mul hCc hXk, Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    omega
  have hTlc : T.leadingCoeff = P.leadingCoeff := by
    rw [hT, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_X_pow, mul_one, div_mul_cancel₀ _ hQlc]
  exact Polynomial.degree_sub_lt
    (by rw [Polynomial.degree_eq_natDegree hP, Polynomial.degree_eq_natDegree hT0, hTnd]) hP
    hTlc.symm

/-- One reduce step strictly shortens the normalized list: `cnormG (p − (lcP/lcQ)·xᵏ·q)` has
strictly smaller normalized length than `p`. -/
theorem stepG_length_lt (p q : CPolyG α) (hp : cnormG p ≠ []) (hq : cnormG q ≠ [])
    (hpq : (cnormG q : List α).length ≤ (cnormG p : List α).length) :
    (cnormG (csubG (cnormG p)
        (cmulG (cshiftG ((cnormG p : List α).length - (cnormG q : List α).length)
          [CField.div (cleadG p) (cleadG q)])
          (cnormG q))) : List α).length < (cnormG p : List α).length := by
  have hP : toPolyG p ≠ 0 := fun h => hp ((cnormG_eq_nil_iff p).mpr h)
  have hQ : toPolyG q ≠ 0 := fun h => hq ((cnormG_eq_nil_iff q).mpr h)
  have hk : (cnormG p : List α).length - (cnormG q : List α).length
      = (toPolyG p).natDegree - (toPolyG q).natDegree := by
    rw [length_cnormG_of_ne p hp, length_cnormG_of_ne q hq]; omega
  have hc : CFieldSpec.toK (CField.div (cleadG p) (cleadG q))
      = (toPolyG p).leadingCoeff / (toPolyG q).leadingCoeff := by
    rw [CFieldSpec.toK_div, toK_cleadG_eq_leadingCoeff, toK_cleadG_eq_leadingCoeff]
  set step := csubG (cnormG p)
    (cmulG (cshiftG ((cnormG p : List α).length - (cnormG q : List α).length)
      [CField.div (cleadG p) (cleadG q)]) (cnormG q))
    with hstepdef
  have hstep : toPolyG step
      = toPolyG p - C ((toPolyG p).leadingCoeff / (toPolyG q).leadingCoeff)
          * X ^ ((toPolyG p).natDegree - (toPolyG q).natDegree) * toPolyG q := by
    rw [hstepdef]
    simp only [denote, hk]
    simp only [mul_zero, add_zero]
    have hcoef : CFieldSpec.toK (cleadG p) / CFieldSpec.toK (cleadG q)
        = (toPolyG p).leadingCoeff / (toPolyG q).leadingCoeff := by
      simpa [CFieldSpec.toK_div] using hc
    rw [hcoef]
    ring
  have hpq' : (toPolyG q).natDegree ≤ (toPolyG p).natDegree := by
    have e1 := length_cnormG_of_ne p hp
    have e2 := length_cnormG_of_ne q hq
    omega
  have hdeg : (toPolyG step).degree < (toPolyG p).degree := by
    rw [hstep]; exact degreeG_reduce_step_lt hP hQ hpq'
  by_cases hs0 : toPolyG step = 0
  · rw [(cnormG_eq_nil_iff _).mpr hs0, List.length_nil]
    exact List.length_pos_iff.mpr hp
  · have hne : cnormG step ≠ [] := fun h => hs0 ((cnormG_eq_nil_iff _).mp h)
    have hlt := Polynomial.natDegree_lt_natDegree hs0 hdeg
    rw [length_cnormG_of_ne _ hne, length_cnormG_of_ne p hp]
    omega

end CPolyG

/-- Field clearing: from the cleared identity `(P·Dstar + hNum·gden²)·d = a·(gden²·Dstar)` with
`gden, Dstar, d ≠ 0`, the fraction-field identity `P/gden² + hNum/Dstar = a/d` holds in `RatFunc K`. -/
theorem hermite_field_div_of_cleared {K : Type*} [Field K] (P Dstar gden hNum d a : K[X])
    (hden : gden ≠ 0) (hDstar : Dstar ≠ 0) (hd : d ≠ 0)
    (hcleared : (P * Dstar + hNum * (gden * gden)) * d = a * ((gden * gden) * Dstar)) :
    (algebraMap K[X] (RatFunc K) P) / (algebraMap K[X] (RatFunc K) gden) ^ 2
        + (algebraMap K[X] (RatFunc K) hNum) / (algebraMap K[X] (RatFunc K) Dstar)
      = (algebraMap K[X] (RatFunc K) a) / (algebraMap K[X] (RatFunc K) d) := by
  set A := algebraMap K[X] (RatFunc K) with hA
  have hAd : A d ≠ 0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective _)).mpr hd
  have hAden : A gden ≠ 0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective _)).mpr hden
  have hADstar : A Dstar ≠ 0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective _)).mpr hDstar
  have hcl : (A P * A Dstar + A hNum * (A gden * A gden)) * A d
      = A a * (A gden * A gden * A Dstar) := by
    have := congrArg A hcleared
    simpa only [map_mul, map_add] using this
  rw [div_add_div _ _ (pow_ne_zero 2 hAden) hADstar, div_eq_div_iff
    (mul_ne_zero (pow_ne_zero 2 hAden) hADstar) hAd]
  ring_nf
  ring_nf at hcl
  linear_combination hcl

end DeepWiki.SymbolicIntegration
