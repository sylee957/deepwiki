import DeepWiki.Algebra.PolynomialDivisibility
import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.Compute.RationalFunction
import DeepWiki.SymbolicIntegration.Core.Polynomial.RatFuncRegular
import DeepWiki.SymbolicIntegration.RationalFunctionDerivative

/-! # Hermite residual-recovery correctness
Proves the residual-recovery wrapper for `hermiteReduce`: once the rational part `(gnum, gden)` and
radical denominator `Dstar` are known, the computable residual numerator gives the `RatFunc ℚ`
identity. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### The residual-recovery identity -/

/-- The denominators of a Hermite residual wrapper are nonzero. -/
structure IsHermiteResidualInput (D gden Dstar : CPoly ℚ) : Prop where
  /-- The original denominator reads nonzero. -/
  den_ne : toPoly D ≠ 0
  /-- The rational-part denominator reads nonzero. -/
  gden_ne : toPoly gden ≠ 0
  /-- The squarefree residual denominator is nonzero. -/
  radical_ne : cnorm Dstar ≠ []

open scoped Differential in
/-- The residual-recovery numerator identity in `RatFunc ℚ`. -/
theorem residual_numerator_ratFunc (A D gnum gden : ℚ[X]) (hD : D ≠ 0) (hgden : gden ≠ 0) :
    algebraMap ℚ[X] (RatFunc ℚ) A / algebraMap ℚ[X] (RatFunc ℚ) D
        - (algebraMap ℚ[X] (RatFunc ℚ) gnum / algebraMap ℚ[X] (RatFunc ℚ) gden)′
      = algebraMap ℚ[X] (RatFunc ℚ)
          (A * (gden * gden) - D * (derivative gnum * gden - gnum * derivative gden))
        / (algebraMap ℚ[X] (RatFunc ℚ) D * (algebraMap ℚ[X] (RatFunc ℚ) gden
            * algebraMap ℚ[X] (RatFunc ℚ) gden)) := by
  have hinj := RatFunc.algebraMap_injective (K := ℚ)
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  have hd : am D ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD
  have hgd : am gden ≠ 0 := (map_ne_zero_iff _ hinj).mpr hgden
  have hdgnum : (am gnum)′ = am (derivative gnum) := ratFuncDeriv_algebraMap gnum
  have hdgden : (am gden)′ = am (derivative gden) := ratFuncDeriv_algebraMap gden
  have hderiv : (am gnum / am gden)′
      = (am gden * am (derivative gnum) - am gnum * am (derivative gden)) / (am gden ^ 2) := by
    rw [deriv_div, hdgnum, hdgden]
  rw [hderiv]
  simp only [map_sub, map_mul]
  rw [pow_two]
  field_simp

/-! ### The full `hermiteReduce` wrapper correctness -/

open scoped Differential in
/-- Full `hermiteReduce` residual correctness in `RatFunc ℚ` from an exact-division certificate. -/
theorem hermiteReduce_residual_correct (fuel : ℕ) (A D : CPoly ℚ)
    (gnum gden Dstar : CPoly ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hexact : toPoly (cmod fuel
        (cmul (csub (cmul A (cmul gden gden))
            (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
        (cmul D (cmul gden gden))) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cdiv fuel
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  have hD := hden.den_ne
  have hgden := hden.gden_ne
  have hDstar := hden.radical_ne
  have hinj := RatFunc.algebraMap_injective (K := ℚ)
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  set resNum := cmul (csub (cmul A (cmul gden gden))
      (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar with hresNum
  set resDen := cmul D (cmul gden gden) with hresDen
  have hDstar0 : toPoly Dstar ≠ 0 := fun h => hDstar ((cnorm_eq_nil_iff Dstar).mpr h)
  have hresDenPoly0 : toPoly resDen ≠ 0 := by
    rw [hresDen, toPoly_cmul, toPoly_cmul]
    exact mul_ne_zero hD (mul_ne_zero hgden hgden)
  have hresDen0 : cnorm resDen ≠ [] := fun h => hresDenPoly0 ((cnorm_eq_nil_iff resDen).mp h)
  have hdstar : am (toPoly Dstar) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hDstar0
  have htoQ : toQFun (gnum, gden) = am (toPoly gnum) / am (toPoly gden) := rfl
  have hresid := residual_numerator_ratFunc (toPoly A) (toPoly D) (toPoly gnum) (toPoly gden) hD hgden
  have hcdiv := am_cdiv_of_cmod_zero fuel resNum resDen hresDen0 hexact
  have hresNumPoly : toPoly resNum
      = (toPoly A * (toPoly gden * toPoly gden)
          - toPoly D * (derivative (toPoly gnum) * toPoly gden
              - toPoly gnum * derivative (toPoly gden))) * toPoly Dstar := by
    rw [hresNum, toPoly_cmul, toPoly_csub, toPoly_cmul, toPoly_cmul, toPoly_cmul, toPoly_csub,
      toPoly_cmul, toPoly_cmul, toPoly_cderiv, toPoly_cderiv]
  have hresDenPoly : toPoly resDen = toPoly D * (toPoly gden * toPoly gden) := by
    rw [hresDen, toPoly_cmul, toPoly_cmul]
  have hkey : am (toPoly (cdiv fuel resNum resDen)) / am (toPoly Dstar)
      = am (toPoly A * (toPoly gden * toPoly gden)
            - toPoly D * (derivative (toPoly gnum) * toPoly gden - toPoly gnum * derivative (toPoly gden)))
          / (am (toPoly D) * (am (toPoly gden) * am (toPoly gden))) := by
    rw [← hcdiv, hresNumPoly, hresDenPoly, map_mul, map_mul, map_mul, div_div,
      mul_comm (am (toPoly D) * (am (toPoly gden) * am (toPoly gden))) (am (toPoly Dstar)),
      mul_comm (am _) (am (toPoly Dstar)), mul_div_mul_left _ _ hdstar]
  rw [htoQ, hkey]
  linear_combination hresid

/-- `toQFun` is invariant under `cnorm` of both components. -/
theorem toQFun_cnorm (gnum gden : CPoly ℚ) :
    toQFun (cnorm gnum, cnorm gden) = toQFun (gnum, gden) := by
  simp only [toQFun, toPoly_cnorm]

open scoped Differential in
/-- `hermiteReduce` residual correctness with the `cnorm`-wrapped residual numerator. -/
theorem hermiteReduce_spec_cnorm (fuel : ℕ) (A D gnum gden Dstar : CPoly ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hexact : toPoly (cmod fuel
        (cmul (csub (cmul A (cmul gden gden))
            (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
        (cmul D (cmul gden gden))) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cnorm (cdiv fuel
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden)))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  rw [toPoly_cnorm]
  exact hermiteReduce_residual_correct fuel A D gnum gden Dstar hden hexact

open scoped Differential in
/-- `hermiteReduce` residual correctness from an algebraic divisibility certificate. -/
theorem hermiteReduce_residual_correct_of_dvd (fuel : ℕ) (A D gnum gden Dstar : CPoly ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hfuel : (cnorm (cmul (csub (cmul A (cmul gden gden))
        (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)).length ≤ fuel)
    (hdvd : toPoly (cmul D (cmul gden gden))
      ∣ toPoly (cmul (csub (cmul A (cmul gden gden))
          (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cdiv fuel
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  have hD := hden.den_ne
  have hgden := hden.gden_ne
  have hresDenP : toPoly (cmul D (cmul gden gden)) ≠ 0 := by
    rw [toPoly_cmul, toPoly_cmul]
    exact mul_ne_zero hD (mul_ne_zero hgden hgden)
  have hresDen : cnorm (cmul D (cmul gden gden)) ≠ [] :=
    fun h => hresDenP ((cnorm_eq_nil_iff _).mp h)
  exact hermiteReduce_residual_correct fuel A D gnum gden Dstar hden
    (cmod_eq_zero_of_dvd fuel _ _ hresDen hfuel hdvd)

/-! ### Split and radical residual certificates -/

open scoped Differential in
/-- `hermiteReduce` residual correctness from two split divisibility certificates. -/
theorem hermiteReduce_residual_correct_of_split (fuel : ℕ) (A D gnum gden Dstar : CPoly ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hfuel : (cnorm (cmul (csub (cmul A (cmul gden gden))
        (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)).length ≤ fuel)
    (hresD : toPoly (cmod fuel
        (csub (cmul A (cmul gden gden))
          (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) D) = 0)
    (hg2 : toPoly (cmod fuel
        (cmul (cdiv fuel
            (csub (cmul A (cmul gden gden))
              (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) D) Dstar)
        (cmul gden gden)) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cdiv fuel
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  have hD := hden.den_ne
  have hgden := hden.gden_ne
  set resNum' := csub (cmul A (cmul gden gden))
    (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden)))) with hresNum'
  have hDne : cnorm D ≠ [] := fun h => hD ((cnorm_eq_nil_iff D).mp h)
  have hgden2 : toPoly (cmul gden gden) ≠ 0 := by rw [toPoly_cmul]; exact mul_ne_zero hgden hgden
  have hgden2ne : cnorm (cmul gden gden) ≠ [] := fun h => hgden2 ((cnorm_eq_nil_iff _).mp h)
  have hDR : toPoly D ∣ toPoly resNum' := toPoly_dvd_of_cmod_zero fuel resNum' D hDne hresD
  have hMeq : toPoly (cdiv fuel resNum' D) = toPoly resNum' / toPoly D := by
    rw [toPoly_cdiv_of_cmod_zero fuel resNum' D hDne hresD, mul_div_cancel_right₀ _ hD]
  have hg2dvd : toPoly (cmul gden gden) ∣ toPoly (cmul (cdiv fuel resNum' D) Dstar) :=
    toPoly_dvd_of_cmod_zero fuel _ _ hgden2ne hg2
  rw [toPoly_cmul, toPoly_cmul, hMeq] at hg2dvd
  have hdvd : toPoly (cmul D (cmul gden gden)) ∣ toPoly (cmul resNum' Dstar) := by
    rw [toPoly_cmul, toPoly_cmul, toPoly_cmul]
    exact DeepWiki.polynomial_dvd_cleared_identity_of_split hD hDR hg2dvd
  exact hermiteReduce_residual_correct_of_dvd fuel A D gnum gden Dstar hden hfuel hdvd

open scoped Differential in
/-- `hermiteReduce` residual correctness from the radical clause plus one residual certificate. -/
theorem hermiteReduce_residual_correct_of_radical (fuel : ℕ) (A D gnum gden Dstar : CPoly ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hfuel : (cnorm (cmul (csub (cmul A (cmul gden gden))
        (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)).length ≤ fuel)
    (hfuelD : (cnorm D).length ≤ fuel)
    (hDstarD : toPoly Dstar ∣ toPoly D)
    (hWgd : toPoly (cmod fuel
        (csub (cmul A (cmul gden gden))
          (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden)))))
        (cmul (cdiv fuel D Dstar) (cmul gden gden))) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cdiv fuel
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  have hD := hden.den_ne
  have hgden := hden.gden_ne
  have hDstar := hden.radical_ne
  set resNum' := csub (cmul A (cmul gden gden))
    (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden)))) with hresNum'
  have hWeq : toPoly D = toPoly Dstar * toPoly (cdiv fuel D Dstar) := by
    have hrem : toPoly (cmod fuel D Dstar) = 0 := cmod_eq_zero_of_dvd fuel D Dstar hDstar hfuelD hDstarD
    rw [toPoly_cdiv_of_cmod_zero fuel D Dstar hDstar hrem, mul_comm]
  have hWgdne : cnorm (cmul (cdiv fuel D Dstar) (cmul gden gden)) ≠ [] := by
    intro h
    have h0 : toPoly (cmul (cdiv fuel D Dstar) (cmul gden gden)) = 0 := (cnorm_eq_nil_iff _).mp h
    rw [toPoly_cmul, toPoly_cmul] at h0
    rcases mul_eq_zero.mp h0 with h1 | h2
    · rw [hWeq, h1, mul_zero] at hD; exact hD rfl
    · rcases mul_eq_zero.mp h2 with hh | hh <;> exact hgden hh
  have hWgddvd : toPoly (cmul (cdiv fuel D Dstar) (cmul gden gden)) ∣ toPoly resNum' :=
    toPoly_dvd_of_cmod_zero fuel _ _ hWgdne hWgd
  rw [toPoly_cmul, toPoly_cmul] at hWgddvd
  have hdvd : toPoly (cmul D (cmul gden gden)) ∣ toPoly (cmul resNum' Dstar) := by
    rw [toPoly_cmul, toPoly_cmul, toPoly_cmul]
    exact DeepWiki.polynomial_dvd_cleared_identity_of_radical
      (W := toPoly (cdiv fuel D Dstar)) hWeq hWgddvd
  exact hermiteReduce_residual_correct_of_dvd fuel A D gnum gden Dstar hden hfuel hdvd

/-! ### Decidable residual-honesty bundle -/

/-- Decidable residual-recovery honesty bundle for `hermiteReduce`'s computed rational part and radical. -/
def HermiteResComp (fuel : ℕ) (A D gnum gden Dstar : CPoly ℚ) : Prop :=
  let resNum' := csub (cmul A (cmul gden gden))
    (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))
  cnorm (cmod fuel resNum' D) = [] ∧
    cnorm (cmod fuel (cmul (cdiv fuel resNum' D) Dstar) (cmul gden gden)) = []

/-- `HermiteResComp` is decidable. -/
instance decHermiteResComp (fuel : ℕ) (A D gnum gden Dstar : CPoly ℚ) :
    Decidable (HermiteResComp fuel A D gnum gden Dstar) := by
  unfold HermiteResComp; infer_instance

open scoped Differential in
/-- Unconditional `hermiteReduce` residual correctness from the decidable residual-honesty bundle. -/
theorem hermiteReduce_residual_correct_uncond (fuel : ℕ) (A D gnum gden Dstar : CPoly ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hfuel : (cnorm (cmul (csub (cmul A (cmul gden gden))
        (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)).length ≤ fuel)
    (hcomp : HermiteResComp fuel A D gnum gden Dstar) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cdiv fuel
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  obtain ⟨hresD, hg2⟩ := hcomp
  rw [cnorm_eq_nil_iff] at hresD hg2
  exact hermiteReduce_residual_correct_of_split fuel A D gnum gden Dstar hden hfuel
    hresD hg2

open scoped Differential in
example (fuel : ℕ) (A D gnum gden Dstar : CPoly ℚ)
    (hD : toPoly D ≠ 0) (hgden : toPoly gden ≠ 0) (hDstar : cnorm Dstar ≠ [])
    (hfuel : (cnorm (cmul (csub (cmul A (cmul gden gden))
        (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)).length ≤ fuel)
    (hcomp : HermiteResComp fuel A D gnum gden Dstar) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cdiv fuel
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) :=
  hermiteReduce_residual_correct_uncond fuel A D gnum gden Dstar ⟨hD, hgden, hDstar⟩ hfuel hcomp

end DeepWiki.SymbolicIntegration.Compute
