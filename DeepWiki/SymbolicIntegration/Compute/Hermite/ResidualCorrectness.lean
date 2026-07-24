import DeepWiki.Algebra.PolynomialDivisibility
import DeepWiki.SymbolicIntegration.Compute.Hermite
import DeepWiki.SymbolicIntegration.Compute.RationalFunction
import DeepWiki.SymbolicIntegration.Core.Polynomial.RatFuncRegular
import DeepWiki.SymbolicIntegration.DifferentialAlgebra.RationalFunctionDerivative

/-! # Hermite residual-recovery correctness
Proves the residual-recovery wrapper for `hermiteReduce`: once the rational part `(gnum, gden)` and
radical denominator `Dstar` are known, the computable residual numerator gives the `RatFunc ℚ`
identity. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

variable {P : Type → Type} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{0,0} P]
  [CPolyEuclidean P] [LawfulCPolyEuclidean.{0,0} P]

/-! ### The residual-recovery identity -/

/-- The denominators of a Hermite residual wrapper are nonzero. -/
structure IsHermiteResidualInput (D gden Dstar : P ℚ) : Prop where
  /-- The original denominator reads nonzero. -/
  den_ne : CPoly.toPoly D ≠ 0
  /-- The rational-part denominator reads nonzero. -/
  gden_ne : CPoly.toPoly gden ≠ 0
  /-- The squarefree residual denominator is nonzero. -/
  radical_ne : CPoly.toPoly Dstar ≠ 0

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
theorem hermiteReduce_residual_correct (A D : P ℚ)
    (gnum gden Dstar : P ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hexact : CPoly.toPoly (CPolyEuclidean.mod
        (CPolyEngine.mul (CPolyEngine.sub (CPolyEngine.mul A (CPolyEngine.mul gden gden))
            (CPolyEngine.mul D (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv gnum) gden) (CPolyEngine.mul gnum (CPolyEngine.deriv gden))))) Dstar)
        (CPolyEngine.mul D (CPolyEngine.mul gden gden))) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly D)
      = (ratFuncOfPair (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (CPoly.toPoly (CPolyEuclidean.div
              (CPolyEngine.mul (CPolyEngine.sub (CPolyEngine.mul A (CPolyEngine.mul gden gden))
                  (CPolyEngine.mul D (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv gnum) gden) (CPolyEngine.mul gnum (CPolyEngine.deriv gden))))) Dstar)
              (CPolyEngine.mul D (CPolyEngine.mul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly Dstar) := by
  have hD := hden.den_ne
  have hgden := hden.gden_ne
  have hDstar := hden.radical_ne
  have hinj := RatFunc.algebraMap_injective (K := ℚ)
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  set resNum := CPolyEngine.mul (CPolyEngine.sub (CPolyEngine.mul A (CPolyEngine.mul gden gden))
      (CPolyEngine.mul D (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv gnum) gden) (CPolyEngine.mul gnum (CPolyEngine.deriv gden))))) Dstar with hresNum
  set resDen := CPolyEngine.mul D (CPolyEngine.mul gden gden) with hresDen
  have hDstar0 : CPoly.toPoly Dstar ≠ 0 := hDstar
  have hresDenPoly0 : CPoly.toPoly resDen ≠ 0 := by
    rw [hresDen, LawfulCPolyEngine.toPoly_mul, LawfulCPolyEngine.toPoly_mul]
    exact mul_ne_zero hD (mul_ne_zero hgden hgden)
  have hdstar : am (CPoly.toPoly Dstar) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hDstar0
  have htoQ : ratFuncOfPair (gnum, gden) = am (CPoly.toPoly gnum) / am (CPoly.toPoly gden) := rfl
  have hresid := residual_numerator_ratFunc (CPoly.toPoly A) (CPoly.toPoly D) (CPoly.toPoly gnum) (CPoly.toPoly gden) hD hgden
  have hcdiv : am (CPoly.toPoly resNum) / am (CPoly.toPoly resDen) =
      am (CPoly.toPoly (CPolyEuclidean.div resNum resDen)) := by
    exact am_div_of_mod_zero resNum resDen hresDenPoly0 hexact
  have hresNumPoly : CPoly.toPoly resNum
      = (CPoly.toPoly A * (CPoly.toPoly gden * CPoly.toPoly gden)
          - CPoly.toPoly D * (derivative (CPoly.toPoly gnum) * CPoly.toPoly gden
              - CPoly.toPoly gnum * derivative (CPoly.toPoly gden))) * CPoly.toPoly Dstar := by
    rw [hresNum, LawfulCPolyEngine.toPoly_mul, CPolyEngine.toPoly_sub,
      LawfulCPolyEngine.toPoly_mul, LawfulCPolyEngine.toPoly_mul,
      LawfulCPolyEngine.toPoly_mul, CPolyEngine.toPoly_sub,
      LawfulCPolyEngine.toPoly_mul, LawfulCPolyEngine.toPoly_mul,
      LawfulCPolyEngine.toPoly_deriv, LawfulCPolyEngine.toPoly_deriv]
  have hresDenPoly : CPoly.toPoly resDen = CPoly.toPoly D * (CPoly.toPoly gden * CPoly.toPoly gden) := by
    rw [hresDen, LawfulCPolyEngine.toPoly_mul, LawfulCPolyEngine.toPoly_mul]
  have hkey : am (CPoly.toPoly (CPolyEuclidean.div resNum resDen)) / am (CPoly.toPoly Dstar)
      = am (CPoly.toPoly A * (CPoly.toPoly gden * CPoly.toPoly gden)
            - CPoly.toPoly D * (derivative (CPoly.toPoly gnum) * CPoly.toPoly gden - CPoly.toPoly gnum * derivative (CPoly.toPoly gden)))
          / (am (CPoly.toPoly D) * (am (CPoly.toPoly gden) * am (CPoly.toPoly gden))) := by
    rw [← hcdiv, hresNumPoly, hresDenPoly, map_mul, map_mul, map_mul, div_div,
      mul_comm (am (CPoly.toPoly D) * (am (CPoly.toPoly gden) * am (CPoly.toPoly gden))) (am (CPoly.toPoly Dstar)),
      mul_comm (am _) (am (CPoly.toPoly Dstar)), mul_div_mul_left _ _ hdstar]
  rw [htoQ, hkey]
  linear_combination hresid

omit [CPolyEuclidean P] [LawfulCPolyEuclidean P] in
/-- `ratFuncOfPair` is invariant under `CPolyEngine.cnorm` of both components. -/
theorem ratFuncOfPair_cnorm (gnum gden : P ℚ) :
    ratFuncOfPair (CPolyEngine.cnorm gnum, CPolyEngine.cnorm gden) = ratFuncOfPair (gnum, gden) := by
  simp only [ratFuncOfPair, LawfulCPolyEngine.toPoly_cnorm]

open scoped Differential in
/-- `hermiteReduce` residual correctness with the `CPolyEngine.cnorm`-wrapped residual numerator. -/
theorem hermiteReduce_spec_cnorm (A D gnum gden Dstar : P ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hexact : CPoly.toPoly (CPolyEuclidean.mod
        (CPolyEngine.mul (CPolyEngine.sub (CPolyEngine.mul A (CPolyEngine.mul gden gden))
            (CPolyEngine.mul D (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv gnum) gden) (CPolyEngine.mul gnum (CPolyEngine.deriv gden))))) Dstar)
        (CPolyEngine.mul D (CPolyEngine.mul gden gden))) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly D)
      = (ratFuncOfPair (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (CPoly.toPoly (CPolyEngine.cnorm (CPolyEuclidean.div
              (CPolyEngine.mul (CPolyEngine.sub (CPolyEngine.mul A (CPolyEngine.mul gden gden))
                  (CPolyEngine.mul D (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv gnum) gden) (CPolyEngine.mul gnum (CPolyEngine.deriv gden))))) Dstar)
              (CPolyEngine.mul D (CPolyEngine.mul gden gden)))))
          / algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly Dstar) := by
  simp only [LawfulCPolyEngine.toPoly_cnorm]
  exact
    hermiteReduce_residual_correct A D gnum gden Dstar hden hexact

open scoped Differential in
/-- `hermiteReduce` residual correctness from an algebraic divisibility certificate. -/
theorem hermiteReduce_residual_correct_of_dvd (A D gnum gden Dstar : P ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hdvd : CPoly.toPoly (CPolyEngine.mul D (CPolyEngine.mul gden gden))
      ∣ CPoly.toPoly (CPolyEngine.mul (CPolyEngine.sub (CPolyEngine.mul A (CPolyEngine.mul gden gden))
          (CPolyEngine.mul D (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv gnum) gden) (CPolyEngine.mul gnum (CPolyEngine.deriv gden))))) Dstar)) :
    algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly D)
      = (ratFuncOfPair (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (CPoly.toPoly (CPolyEuclidean.div
              (CPolyEngine.mul (CPolyEngine.sub (CPolyEngine.mul A (CPolyEngine.mul gden gden))
                  (CPolyEngine.mul D (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv gnum) gden) (CPolyEngine.mul gnum (CPolyEngine.deriv gden))))) Dstar)
              (CPolyEngine.mul D (CPolyEngine.mul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly Dstar) := by
  have hD := hden.den_ne
  have hgden := hden.gden_ne
  have hresDenP : CPoly.toPoly (CPolyEngine.mul D (CPolyEngine.mul gden gden)) ≠ 0 := by
    rw [LawfulCPolyEngine.toPoly_mul, LawfulCPolyEngine.toPoly_mul]
    exact mul_ne_zero hD (mul_ne_zero hgden hgden)
  exact hermiteReduce_residual_correct A D gnum gden Dstar hden
    (CPolyEuclidean.toPoly_mod_eq_zero_of_dvd _ _ hresDenP hdvd)

/-! ### Split and radical residual certificates -/

open scoped Differential in
/-- `hermiteReduce` residual correctness from two split divisibility certificates. -/
theorem hermiteReduce_residual_correct_of_split (A D gnum gden Dstar : P ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hresD : CPoly.toPoly (CPolyEuclidean.mod
        (CPolyEngine.sub (CPolyEngine.mul A (CPolyEngine.mul gden gden))
          (CPolyEngine.mul D (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv gnum) gden) (CPolyEngine.mul gnum (CPolyEngine.deriv gden))))) D) = 0)
    (hg2 : CPoly.toPoly (CPolyEuclidean.mod
        (CPolyEngine.mul (CPolyEuclidean.div
            (CPolyEngine.sub (CPolyEngine.mul A (CPolyEngine.mul gden gden))
              (CPolyEngine.mul D (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv gnum) gden) (CPolyEngine.mul gnum (CPolyEngine.deriv gden))))) D) Dstar)
        (CPolyEngine.mul gden gden)) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly D)
      = (ratFuncOfPair (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (CPoly.toPoly (CPolyEuclidean.div
              (CPolyEngine.mul (CPolyEngine.sub (CPolyEngine.mul A (CPolyEngine.mul gden gden))
                  (CPolyEngine.mul D (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv gnum) gden) (CPolyEngine.mul gnum (CPolyEngine.deriv gden))))) Dstar)
              (CPolyEngine.mul D (CPolyEngine.mul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly Dstar) := by
  have hD := hden.den_ne
  have hgden := hden.gden_ne
  set resNum' := CPolyEngine.sub (CPolyEngine.mul A (CPolyEngine.mul gden gden))
    (CPolyEngine.mul D (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv gnum) gden) (CPolyEngine.mul gnum (CPolyEngine.deriv gden)))) with hresNum'
  have hgden2 : CPoly.toPoly (CPolyEngine.mul gden gden) ≠ 0 := by
    rw [LawfulCPolyEngine.toPoly_mul]
    exact mul_ne_zero hgden hgden
  have hDR : CPoly.toPoly D ∣ CPoly.toPoly resNum' :=
    CPolyEuclidean.toPoly_dvd_of_mod_eq_zero resNum' D hD hresD
  have hMeq : CPoly.toPoly (CPolyEuclidean.div resNum' D) = CPoly.toPoly resNum' / CPoly.toPoly D := by
    rw [CPolyEuclidean.toPoly_eq_div_mul_of_mod_eq_zero resNum' D hD hresD,
      mul_div_cancel_right₀ _ hD]
  have hg2dvd : CPoly.toPoly (CPolyEngine.mul gden gden) ∣ CPoly.toPoly (CPolyEngine.mul (CPolyEuclidean.div resNum' D) Dstar) :=
    CPolyEuclidean.toPoly_dvd_of_mod_eq_zero _ _ hgden2 hg2
  rw [LawfulCPolyEngine.toPoly_mul, LawfulCPolyEngine.toPoly_mul, hMeq] at hg2dvd
  have hdvd : CPoly.toPoly (CPolyEngine.mul D (CPolyEngine.mul gden gden)) ∣ CPoly.toPoly (CPolyEngine.mul resNum' Dstar) := by
    rw [LawfulCPolyEngine.toPoly_mul, LawfulCPolyEngine.toPoly_mul,
      LawfulCPolyEngine.toPoly_mul]
    exact DeepWiki.polynomial_dvd_cleared_identity_of_split hD hDR hg2dvd
  exact hermiteReduce_residual_correct_of_dvd A D gnum gden Dstar hden hdvd

open scoped Differential in
/-- `hermiteReduce` residual correctness from the radical clause plus one residual certificate. -/
theorem hermiteReduce_residual_correct_of_radical (A D gnum gden Dstar : P ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hDstarD : CPoly.toPoly Dstar ∣ CPoly.toPoly D)
    (hWgd : CPoly.toPoly (CPolyEuclidean.mod
        (CPolyEngine.sub (CPolyEngine.mul A (CPolyEngine.mul gden gden))
          (CPolyEngine.mul D (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv gnum) gden) (CPolyEngine.mul gnum (CPolyEngine.deriv gden)))))
        (CPolyEngine.mul (CPolyEuclidean.div D Dstar) (CPolyEngine.mul gden gden))) = 0) :
    algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly D)
      = (ratFuncOfPair (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (CPoly.toPoly (CPolyEuclidean.div
              (CPolyEngine.mul (CPolyEngine.sub (CPolyEngine.mul A (CPolyEngine.mul gden gden))
                  (CPolyEngine.mul D (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv gnum) gden) (CPolyEngine.mul gnum (CPolyEngine.deriv gden))))) Dstar)
              (CPolyEngine.mul D (CPolyEngine.mul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly Dstar) := by
  have hD := hden.den_ne
  have hgden := hden.gden_ne
  have hDstar := hden.radical_ne
  set resNum' := CPolyEngine.sub (CPolyEngine.mul A (CPolyEngine.mul gden gden))
    (CPolyEngine.mul D (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv gnum) gden) (CPolyEngine.mul gnum (CPolyEngine.deriv gden)))) with hresNum'
  have hWeq : CPoly.toPoly D = CPoly.toPoly Dstar * CPoly.toPoly (CPolyEuclidean.div D Dstar) := by
    exact LawfulCPolyEuclidean.div_exact D Dstar hDstar hDstarD
  have hWgdne : CPoly.toPoly
      (CPolyEngine.mul (CPolyEuclidean.div D Dstar) (CPolyEngine.mul gden gden)) ≠ 0 := by
    rw [LawfulCPolyEngine.toPoly_mul, LawfulCPolyEngine.toPoly_mul]
    intro h0
    rcases mul_eq_zero.mp h0 with h1 | h2
    · rw [hWeq, h1, mul_zero] at hD; exact hD rfl
    · rcases mul_eq_zero.mp h2 with hh | hh <;> exact hgden hh
  have hWgddvd : CPoly.toPoly (CPolyEngine.mul (CPolyEuclidean.div D Dstar) (CPolyEngine.mul gden gden)) ∣ CPoly.toPoly resNum' :=
    CPolyEuclidean.toPoly_dvd_of_mod_eq_zero _ _ hWgdne hWgd
  rw [LawfulCPolyEngine.toPoly_mul, LawfulCPolyEngine.toPoly_mul] at hWgddvd
  have hdvd : CPoly.toPoly (CPolyEngine.mul D (CPolyEngine.mul gden gden)) ∣ CPoly.toPoly (CPolyEngine.mul resNum' Dstar) := by
    rw [LawfulCPolyEngine.toPoly_mul, LawfulCPolyEngine.toPoly_mul,
      LawfulCPolyEngine.toPoly_mul]
    exact DeepWiki.polynomial_dvd_cleared_identity_of_radical
      (W := CPoly.toPoly (CPolyEuclidean.div D Dstar)) hWeq hWgddvd
  exact hermiteReduce_residual_correct_of_dvd A D gnum gden Dstar hden hdvd

/-! ### Decidable residual-honesty bundle -/

/-- Decidable residual-recovery honesty bundle for `hermiteReduce`'s computed rational part and radical. -/
def HermiteResComp (A D gnum gden Dstar : P ℚ) : Prop :=
  let resNum' := CPolyEngine.sub (CPolyEngine.mul A (CPolyEngine.mul gden gden))
    (CPolyEngine.mul D (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv gnum) gden) (CPolyEngine.mul gnum (CPolyEngine.deriv gden))))
  CPolyEngine.cisZero (CPolyEuclidean.mod resNum' D) = true ∧
    CPolyEngine.cisZero
      (CPolyEuclidean.mod (CPolyEngine.mul (CPolyEuclidean.div resNum' D) Dstar)
        (CPolyEngine.mul gden gden)) = true

/-- `HermiteResComp` is decidable. -/
instance decHermiteResComp (A D gnum gden Dstar : P ℚ) :
    Decidable (HermiteResComp A D gnum gden Dstar) := by
  unfold HermiteResComp; infer_instance

open scoped Differential in
/-- Unconditional `hermiteReduce` residual correctness from the decidable residual-honesty bundle. -/
theorem hermiteReduce_residual_correct_uncond (A D gnum gden Dstar : P ℚ)
    (hden : IsHermiteResidualInput D gden Dstar)
    (hcomp : HermiteResComp A D gnum gden Dstar) :
    algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly A) / algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly D)
      = (ratFuncOfPair (gnum, gden))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (CPoly.toPoly (CPolyEuclidean.div
              (CPolyEngine.mul (CPolyEngine.sub (CPolyEngine.mul A (CPolyEngine.mul gden gden))
                  (CPolyEngine.mul D (CPolyEngine.sub (CPolyEngine.mul (CPolyEngine.deriv gnum) gden) (CPolyEngine.mul gnum (CPolyEngine.deriv gden))))) Dstar)
              (CPolyEngine.mul D (CPolyEngine.mul gden gden))))
          / algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly Dstar) := by
  obtain ⟨hresD, hg2⟩ := hcomp
  rw [LawfulCPolyEngine.cisZero_iff] at hresD hg2
  exact hermiteReduce_residual_correct_of_split A D gnum gden Dstar hden
    hresD hg2

end DeepWiki.SymbolicIntegration.Compute
