import DeepWiki.SymbolicIntegration.Engine.PolyPartTower
import DeepWiki.SymbolicIntegration.MonomialConstants.Nonlinear

/-! # Eventual polynomial-reduction bounds

Representation-neutral degree arguments showing when the fuel-bounded tower polynomial
reducers reach their requested normal forms. -/

namespace DeepWiki.SymbolicIntegration

open Polynomial
open scoped Differential

universe u

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,u} P]
  {α : Type u} [CField α] [CFieldSpec.{u,u} α] [CDiffField α] [CDiffFieldSpec.{u,u} α]

namespace DensePoly

/-- The nonlinear polynomial-reduction domain: the monomial derivative has degree at least two. -/
def nonlinearPolynomialReductionDomain : PolynomialReductionDomain P α := fun kind Dt _p =>
  kind = .nonlinear ∧ 2 ≤ CPolyEngine.cdeg Dt

/-- Every fuel-bounded nonlinear reduction reconstructs its input polynomial. -/
theorem cPolyReduceTower_reconstruct (Dt : P α) : ∀ (fuel : ℕ) (p : P α),
    CPoly.toPoly p = Differential.implicitDeriv (CPoly.toPoly Dt)
        (CPoly.toPoly (cPolyReduceTower Dt fuel p).1) +
      CPoly.toPoly (cPolyReduceTower Dt fuel p).2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro p
      simp only [cPolyReduceTower, CPoly.toPoly_czero, map_zero, zero_add]
      exact (LawfulCPolyEngine.toPoly_cnorm p).symm
  | succ fuel ih =>
      intro p
      rw [← LawfulCPolyEngine.toPoly_cnorm p]
      simp only [cPolyReduceTower]
      split
      · simp only [CPoly.toPoly_czero, map_zero, zero_add]
      · rename_i hstop
        let n := CPolyEngine.cdeg (CPolyEngine.cnorm p)
        let delta := CPolyEngine.cdeg Dt
        let m := n - delta + 1
        let lam := CPolyEngine.clead Dt
        let c := CField.div (CPolyEngine.clead (CPolyEngine.cnorm p))
          (CCommRing.mul (CField.natCast m) lam)
        let q0 := CPolyEngine.monomial (P := P) c m
        let p' := CPolyEngine.sub (CPolyEngine.cnorm p) (CPolyEngine.monomialDeriv Dt q0)
        have hrec := ih p'
        change CPoly.toPoly (CPolyEngine.cnorm p) =
          Differential.implicitDeriv (CPoly.toPoly Dt)
              (CPoly.toPoly (CPolyEngine.add q0 (cPolyReduceTower Dt fuel p').1)) +
            CPoly.toPoly (cPolyReduceTower Dt fuel p').2
        rw [LawfulCPolyEngine.toPoly_add, map_add, add_assoc, ← hrec,
          CPolyEngine.toPoly_sub, CPolyEngine.toPoly_monomialDeriv]
        ring

variable [CharZero (CFieldSpec.K α)]

/-- One nonlinear cancellation step strictly lowers the represented polynomial degree. -/
theorem cPolyReduceTower_step_degree_lt (Dt p : P α)
    (hdelta : 2 ≤ CPolyEngine.cdeg Dt) (hpzero : CPolyEngine.cisZero p = false)
    (hlarge : ¬ CPolyEngine.cdeg p < CPolyEngine.cdeg Dt) :
    CPolyEngine.cdeg
        (CPolyEngine.sub p
          (CPolyEngine.monomialDeriv Dt
            (CPolyEngine.monomial (P := P)
              (CField.div (CPolyEngine.clead p)
                (CCommRing.mul
                  (CField.natCast (CPolyEngine.cdeg p - CPolyEngine.cdeg Dt + 1))
                  (CPolyEngine.clead Dt)))
              (CPolyEngine.cdeg p - CPolyEngine.cdeg Dt + 1)))) <
      CPolyEngine.cdeg p := by
  let K := CFieldSpec.K α
  let n := CPolyEngine.cdeg p
  let delta := CPolyEngine.cdeg Dt
  let m := n - delta + 1
  let c := CField.div (CPolyEngine.clead p)
    (CCommRing.mul (CField.natCast m) (CPolyEngine.clead Dt))
  let q0 := CPolyEngine.monomial (P := P) c m
  have hp : CPoly.toPoly p ≠ 0 := CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false hpzero
  have hn : (CPoly.toPoly p).natDegree = n := by
    rw [← LawfulCPolyEngine.cdeg_eq_natDegree]
  have hdelta' : 2 ≤ (CPoly.toPoly Dt).natDegree := by
    simpa only [← LawfulCPolyEngine.cdeg_eq_natDegree] using hdelta
  have hdeltaN : (CPoly.toPoly Dt).natDegree = delta := by
    rw [← LawfulCPolyEngine.cdeg_eq_natDegree]
  have hcleadp : CFieldSpec.toK (CPolyEngine.clead p) = (CPoly.toPoly p).leadingCoeff := by
    simpa only [toR_eq_toK] using LawfulCPolyEngine.toR_clead_eq_leadingCoeff p
  have hcleadDt : CFieldSpec.toK (CPolyEngine.clead Dt) =
      (CPoly.toPoly Dt).leadingCoeff := by
    simpa only [toR_eq_toK] using LawfulCPolyEngine.toR_clead_eq_leadingCoeff Dt
  have hnd : delta ≤ n := Nat.le_of_not_gt hlarge
  have hmpos : 1 ≤ m := by
    dsimp [m, n, delta]
    omega
  have hnatm : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlcp : (CPoly.toPoly p).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hlcDt : (CPoly.toPoly Dt).leadingCoeff ≠ 0 := by
    apply leadingCoeff_ne_zero.mpr
    intro hDt
    rw [hDt] at hdelta'
    simp at hdelta'
  have hc : CFieldSpec.toK c ≠ 0 := by
    dsimp [c]
    rw [CFieldSpec.toK_div, CFieldSpec.toK_mul, CFieldSpec.toK_natCast,
      hcleadp, hcleadDt]
    exact div_ne_zero hlcp (mul_ne_zero hnatm hlcDt)
  have hq0 : CPoly.toPoly q0 = Polynomial.monomial m (CFieldSpec.toK c) := by
    dsimp [q0]
    rw [LawfulCPolyEngine.toPoly_monomial, ← Polynomial.C_mul_X_pow_eq_monomial]
    rfl
  have hq0deg : (CPoly.toPoly q0).natDegree = m := by
    rw [hq0, Polynomial.natDegree_monomial_eq _ hc]
  have hq0lead : (CPoly.toPoly q0).leadingCoeff = CFieldSpec.toK c := by
    rw [hq0, Polynomial.leadingCoeff_monomial]
  have hderivdeg :
      (Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly q0)).natDegree = n := by
    rw [natDegree_implicitDeriv_eq _ _ hdelta' (by rw [hq0deg]; exact hmpos), hq0deg]
    rw [hdeltaN]
    dsimp [m, n, delta]
    omega
  have hderivlead :
      (Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly q0)).leadingCoeff =
        (CPoly.toPoly p).leadingCoeff := by
    rw [leadingCoeff_implicitDeriv_nonlinear _ _ hdelta'
      (by rw [hq0deg]; exact hmpos), hq0deg, hq0lead,
      CFieldSpec.toK_div, CFieldSpec.toK_mul, CFieldSpec.toK_natCast,
      hcleadp, hcleadDt]
    dsimp [m, n, delta]
    have hden :
        (↑(CPolyEngine.cdeg p - CPolyEngine.cdeg Dt + 1) : K) *
            (CPoly.toPoly Dt).leadingCoeff ≠ 0 := by
      apply mul_ne_zero
      · simpa only [m, n, delta] using hnatm
      · exact hlcDt
    field_simp [hden]
  rw [show CPolyEngine.cdeg
        (CPolyEngine.sub p (CPolyEngine.monomialDeriv Dt q0)) =
      (CPoly.toPoly
        (CPolyEngine.sub p (CPolyEngine.monomialDeriv Dt q0))).natDegree by
      rw [LawfulCPolyEngine.cdeg_eq_natDegree],
    CPolyEngine.toPoly_sub, CPolyEngine.toPoly_monomialDeriv,
    LawfulCPolyEngine.cdeg_eq_natDegree (P := P) p]
  by_cases hzero : CPoly.toPoly p -
      Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly q0) = 0
  · rw [hzero]
    have hnpositive : 0 < n := by
      dsimp [n, delta] at hnd hdelta
      omega
    simpa only [Polynomial.natDegree_zero, hn] using hnpositive
  ·
    have hnpos : n ≠ 0 := by
      dsimp [n, delta] at hnd hdelta
      omega
    have hderivzero :
        Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly q0) ≠ 0 := by
      intro h
      rw [h] at hderivdeg
      simp at hderivdeg
      exact hnpos hderivdeg.symm
    have hdegree : (CPoly.toPoly p).degree =
        (Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly q0)).degree := by
      rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hderivzero,
        hderivdeg, hn]
    apply (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr
    have hsub := Polynomial.degree_sub_lt hdegree hp hderivlead.symm
    rw [Polynomial.degree_eq_natDegree hp, hn] at hsub
    rw [hn]
    exact hsub

end DensePoly

end DeepWiki.SymbolicIntegration
