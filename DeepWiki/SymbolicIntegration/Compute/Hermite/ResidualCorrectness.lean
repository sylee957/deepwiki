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

/-- Local bridge from a vanishing well-founded remainder to exact quotient multiplication. -/
private theorem toPoly_cdivWf_of_cmodWf_zero (p q : DensePoly ℚ) (hq : cnorm q ≠ [])
    (hrem : toPoly (DensePoly.cmodWf p q) = 0) :
    toPoly p = toPoly (DensePoly.cdivWf p q) * toPoly q := by
  have hrem' : DensePoly.toPoly (DensePoly.cmodWf p q) = 0 := by
    exact hrem
  have h := DensePoly.toPolyG_cmodWf p q hq
  rw [hrem', add_zero] at h
  exact h

/-- Local divisibility bridge from a vanishing well-founded remainder. -/
private theorem toPoly_dvd_of_cmodWf_zero (p q : DensePoly ℚ) (hq : cnorm q ≠ [])
    (hrem : toPoly (DensePoly.cmodWf p q) = 0) : toPoly q ∣ toPoly p :=
  ⟨toPoly (DensePoly.cdivWf p q), by
    rw [toPoly_cdivWf_of_cmodWf_zero p q hq hrem, mul_comm]⟩

/-- Local bridge from mathematical divisibility to a vanishing well-founded remainder. -/
private theorem cmodWf_eq_zero_of_dvd (p q : DensePoly ℚ) (hq : cnorm q ≠ [])
    (hdvd : toPoly q ∣ toPoly p) : toPoly (DensePoly.cmodWf p q) = 0 := by
  have hdvd' : DensePoly.toPoly q ∣ DensePoly.toPoly p := by
    exact hdvd
  exact DensePoly.toPolyG_cmodWf_eq_zero_of_dvd p q hq hdvd'

/-! ### The residual-recovery identity -/

/-- The denominators of a Hermite residual wrapper are nonzero. -/
structure IsHermiteResidualInput (D gden Dstar : DensePoly ℚ) : Prop where
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
theorem hermiteReduce_residual_correct (A D : DensePoly ℚ)
    (gnum gden Dstar : DensePoly ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hexact : toPoly (DensePoly.cmodWf
        (cmul (csub (cmul A (cmul gden gden))
            (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
        (cmul D (cmul gden gden))) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (DensePoly.cdivWf
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
  have hDstar0 : toPoly Dstar ≠ 0 := fun h => hDstar ((DensePoly.cnormG_eq_nil_iff Dstar).mpr h)
  have hresDenPoly0 : toPoly resDen ≠ 0 := by
    rw [hresDen, DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cmulG]
    exact mul_ne_zero hD (mul_ne_zero hgden hgden)
  have hresDen0 : cnorm resDen ≠ [] := fun h => hresDenPoly0 ((DensePoly.cnormG_eq_nil_iff resDen).mp h)
  have hdstar : am (toPoly Dstar) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hDstar0
  have htoQ : toQFun (gnum, gden) = am (toPoly gnum) / am (toPoly gden) := rfl
  have hresid := residual_numerator_ratFunc (toPoly A) (toPoly D) (toPoly gnum) (toPoly gden) hD hgden
  have hcdiv := am_cdivWf_of_cmodWf_zero resNum resDen hresDen0 hexact
  have hresNumPoly : toPoly resNum
      = (toPoly A * (toPoly gden * toPoly gden)
          - toPoly D * (derivative (toPoly gnum) * toPoly gden
              - toPoly gnum * derivative (toPoly gden))) * toPoly Dstar := by
    rw [hresNum, DensePoly.toPolyG_cmulG, DensePoly.toPolyG_csubG, DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cmulG, DensePoly.toPolyG_csubG,
      DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cderivG, DensePoly.toPolyG_cderivG]
  have hresDenPoly : toPoly resDen = toPoly D * (toPoly gden * toPoly gden) := by
    rw [hresDen, DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cmulG]
  have hkey : am (toPoly (DensePoly.cdivWf resNum resDen)) / am (toPoly Dstar)
      = am (toPoly A * (toPoly gden * toPoly gden)
            - toPoly D * (derivative (toPoly gnum) * toPoly gden - toPoly gnum * derivative (toPoly gden)))
          / (am (toPoly D) * (am (toPoly gden) * am (toPoly gden))) := by
    rw [← hcdiv, hresNumPoly, hresDenPoly, map_mul, map_mul, map_mul, div_div,
      mul_comm (am (toPoly D) * (am (toPoly gden) * am (toPoly gden))) (am (toPoly Dstar)),
      mul_comm (am _) (am (toPoly Dstar)), mul_div_mul_left _ _ hdstar]
  rw [htoQ, hkey]
  linear_combination hresid

/-- `toQFun` is invariant under `cnorm` of both components. -/
theorem toQFun_cnorm (gnum gden : DensePoly ℚ) :
    toQFun (cnorm gnum, cnorm gden) = toQFun (gnum, gden) := by
  simp only [toQFun, DensePoly.toPolyG_cnormG]

open scoped Differential in
/-- `hermiteReduce` residual correctness with the `cnorm`-wrapped residual numerator. -/
theorem hermiteReduce_spec_cnorm (A D gnum gden Dstar : DensePoly ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hexact : toPoly (DensePoly.cmodWf
        (cmul (csub (cmul A (cmul gden gden))
            (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
        (cmul D (cmul gden gden))) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cnorm (DensePoly.cdivWf
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden)))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  simp only [DensePoly.toPolyG_cnormG]
  exact
    hermiteReduce_residual_correct A D gnum gden Dstar hden hexact

open scoped Differential in
/-- `hermiteReduce` residual correctness from an algebraic divisibility certificate. -/
theorem hermiteReduce_residual_correct_of_dvd (A D gnum gden Dstar : DensePoly ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hdvd : toPoly (cmul D (cmul gden gden))
      ∣ toPoly (cmul (csub (cmul A (cmul gden gden))
          (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (DensePoly.cdivWf
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  have hD := hden.den_ne
  have hgden := hden.gden_ne
  have hresDenP : toPoly (cmul D (cmul gden gden)) ≠ 0 := by
    rw [DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cmulG]
    exact mul_ne_zero hD (mul_ne_zero hgden hgden)
  have hresDen : cnorm (cmul D (cmul gden gden)) ≠ [] :=
    fun h => hresDenP ((DensePoly.cnormG_eq_nil_iff _).mp h)
  exact hermiteReduce_residual_correct A D gnum gden Dstar hden
    (cmodWf_eq_zero_of_dvd _ _ hresDen hdvd)

/-! ### Split and radical residual certificates -/

open scoped Differential in
/-- `hermiteReduce` residual correctness from two split divisibility certificates. -/
theorem hermiteReduce_residual_correct_of_split (A D gnum gden Dstar : DensePoly ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hresD : toPoly (DensePoly.cmodWf
        (csub (cmul A (cmul gden gden))
          (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) D) = 0)
    (hg2 : toPoly (DensePoly.cmodWf
        (cmul (DensePoly.cdivWf
            (csub (cmul A (cmul gden gden))
              (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) D) Dstar)
        (cmul gden gden)) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (DensePoly.cdivWf
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  have hD := hden.den_ne
  have hgden := hden.gden_ne
  set resNum' := csub (cmul A (cmul gden gden))
    (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden)))) with hresNum'
  have hDne : cnorm D ≠ [] := fun h => hD ((DensePoly.cnormG_eq_nil_iff D).mp h)
  have hgden2 : toPoly (cmul gden gden) ≠ 0 := by
    rw [DensePoly.toPolyG_cmulG]
    exact mul_ne_zero hgden hgden
  have hgden2ne : cnorm (cmul gden gden) ≠ [] := fun h => hgden2 ((DensePoly.cnormG_eq_nil_iff _).mp h)
  have hDR : toPoly D ∣ toPoly resNum' := toPoly_dvd_of_cmodWf_zero resNum' D hDne hresD
  have hMeq : toPoly (DensePoly.cdivWf resNum' D) = toPoly resNum' / toPoly D := by
    rw [toPoly_cdivWf_of_cmodWf_zero resNum' D hDne hresD, mul_div_cancel_right₀ _ hD]
  have hg2dvd : toPoly (cmul gden gden) ∣ toPoly (cmul (DensePoly.cdivWf resNum' D) Dstar) :=
    toPoly_dvd_of_cmodWf_zero _ _ hgden2ne hg2
  rw [DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cmulG, hMeq] at hg2dvd
  have hdvd : toPoly (cmul D (cmul gden gden)) ∣ toPoly (cmul resNum' Dstar) := by
    rw [DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cmulG]
    exact DeepWiki.polynomial_dvd_cleared_identity_of_split hD hDR hg2dvd
  exact hermiteReduce_residual_correct_of_dvd A D gnum gden Dstar hden hdvd

open scoped Differential in
/-- `hermiteReduce` residual correctness from the radical clause plus one residual certificate. -/
theorem hermiteReduce_residual_correct_of_radical (A D gnum gden Dstar : DensePoly ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hDstarD : toPoly Dstar ∣ toPoly D)
    (hWgd : toPoly (DensePoly.cmodWf
        (csub (cmul A (cmul gden gden))
          (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden)))))
        (cmul (DensePoly.cdivWf D Dstar) (cmul gden gden))) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (DensePoly.cdivWf
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  have hD := hden.den_ne
  have hgden := hden.gden_ne
  have hDstar := hden.radical_ne
  set resNum' := csub (cmul A (cmul gden gden))
    (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden)))) with hresNum'
  have hWeq : toPoly D = toPoly Dstar * toPoly (DensePoly.cdivWf D Dstar) := by
    have hrem : toPoly (DensePoly.cmodWf D Dstar) = 0 :=
      cmodWf_eq_zero_of_dvd D Dstar hDstar hDstarD
    rw [toPoly_cdivWf_of_cmodWf_zero D Dstar hDstar hrem, mul_comm]
  have hWgdne : cnorm (cmul (DensePoly.cdivWf D Dstar) (cmul gden gden)) ≠ [] := by
    intro h
    have h0 : toPoly (cmul (DensePoly.cdivWf D Dstar) (cmul gden gden)) = 0 := (DensePoly.cnormG_eq_nil_iff _).mp h
    rw [DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cmulG] at h0
    rcases mul_eq_zero.mp h0 with h1 | h2
    · rw [hWeq, h1, mul_zero] at hD; exact hD rfl
    · rcases mul_eq_zero.mp h2 with hh | hh <;> exact hgden hh
  have hWgddvd : toPoly (cmul (DensePoly.cdivWf D Dstar) (cmul gden gden)) ∣ toPoly resNum' :=
    toPoly_dvd_of_cmodWf_zero _ _ hWgdne hWgd
  rw [DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cmulG] at hWgddvd
  have hdvd : toPoly (cmul D (cmul gden gden)) ∣ toPoly (cmul resNum' Dstar) := by
    rw [DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cmulG, DensePoly.toPolyG_cmulG]
    exact DeepWiki.polynomial_dvd_cleared_identity_of_radical
      (W := toPoly (DensePoly.cdivWf D Dstar)) hWeq hWgddvd
  exact hermiteReduce_residual_correct_of_dvd A D gnum gden Dstar hden hdvd

/-! ### Decidable residual-honesty bundle -/

/-- Decidable residual-recovery honesty bundle for `hermiteReduce`'s computed rational part and radical. -/
def HermiteResComp (A D gnum gden Dstar : DensePoly ℚ) : Prop :=
  let resNum' := csub (cmul A (cmul gden gden))
    (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))
  cnorm (DensePoly.cmodWf resNum' D) = [] ∧
    cnorm (DensePoly.cmodWf (cmul (DensePoly.cdivWf resNum' D) Dstar) (cmul gden gden)) = []

/-- `HermiteResComp` is decidable. -/
instance decHermiteResComp (A D gnum gden Dstar : DensePoly ℚ) :
    Decidable (HermiteResComp A D gnum gden Dstar) := by
  unfold HermiteResComp; infer_instance

open scoped Differential in
/-- Unconditional `hermiteReduce` residual correctness from the decidable residual-honesty bundle. -/
theorem hermiteReduce_residual_correct_uncond (A D gnum gden Dstar : DensePoly ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hcomp : HermiteResComp A D gnum gden Dstar) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (DensePoly.cdivWf
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) := by
  obtain ⟨hresD, hg2⟩ := hcomp
  rw [DensePoly.cnormG_eq_nil_iff] at hresD hg2
  exact hermiteReduce_residual_correct_of_split A D gnum gden Dstar hden
    hresD hg2

open scoped Differential in
example (A D gnum gden Dstar : DensePoly ℚ)
    (hD : toPoly D ≠ 0) (hgden : toPoly gden ≠ 0) (hDstar : cnorm Dstar ≠ [])
    (hcomp : HermiteResComp A D gnum gden Dstar) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly D)
      = (toQFun (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (DensePoly.cdivWf
              (cmul (csub (cmul A (cmul gden gden))
                  (cmul D (csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))))) Dstar)
              (cmul D (cmul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly Dstar) :=
  hermiteReduce_residual_correct_uncond A D gnum gden Dstar ⟨hD, hgden, hDstar⟩ hcomp

end DeepWiki.SymbolicIntegration.Compute
