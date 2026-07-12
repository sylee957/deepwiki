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

/-- The leading monomial and residual polynomial used by one nonlinear reduction step. -/
def nonlinearReductionStep (Dt p : P α) : P α × P α :=
  let p := CPolyEngine.cnorm p
  let delta := CPolyEngine.cdeg Dt
  let m := CPolyEngine.cdeg p - delta + 1
  let c := CField.div (CPolyEngine.clead p)
    (CCommRing.mul (CField.natCast m) (CPolyEngine.clead Dt))
  let q0 := CPolyEngine.monomial (P := P) c m
  (q0, CPolyEngine.sub p (CPolyEngine.monomialDeriv Dt q0))

omit [LawfulCPolyEngine P] [CFieldSpec α] [CDiffFieldSpec α]
  [CharZero (CFieldSpec.K α)] in
/-- An active nonlinear recursive call exposes its leading monomial and strictly smaller residual. -/
theorem cPolyReduceTower_succ_active (Dt p : P α) (fuel : ℕ)
    (hzero : CPolyEngine.cisZero (CPolyEngine.cnorm p) = false)
    (hsmall : ¬ CPolyEngine.cdeg (CPolyEngine.cnorm p) < CPolyEngine.cdeg Dt) :
    cPolyReduceTower Dt (fuel + 1) p =
      let step := nonlinearReductionStep Dt p
      let rest := cPolyReduceTower Dt fuel step.2
      (CPolyEngine.add step.1 rest.1, rest.2) := by
  simp [cPolyReduceTower, nonlinearReductionStep, hzero, hsmall]

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

/-- An active nonlinear step strictly lowers its residual's represented degree. -/
theorem nonlinearReductionStep_degree_lt (Dt p : P α)
    (hdelta : 2 ≤ CPolyEngine.cdeg Dt)
    (hzero : CPolyEngine.cisZero (CPolyEngine.cnorm p) = false)
    (hsmall : ¬ CPolyEngine.cdeg (CPolyEngine.cnorm p) < CPolyEngine.cdeg Dt) :
    CPolyEngine.cdeg (nonlinearReductionStep Dt p).2 < CPolyEngine.cdeg (CPolyEngine.cnorm p) := by
  unfold nonlinearReductionStep
  exact cPolyReduceTower_step_degree_lt Dt (CPolyEngine.cnorm p) hdelta hzero hsmall

omit [CDiffField α] [CDiffFieldSpec α] [CharZero (CFieldSpec.K α)] in
/-- Normalization preserves the represented polynomial degree. -/
theorem cdeg_cnorm (p : P α) : CPolyEngine.cdeg (CPolyEngine.cnorm p) = CPolyEngine.cdeg p := by
  rw [LawfulCPolyEngine.cdeg_eq_natDegree, LawfulCPolyEngine.toPoly_cnorm,
    ← LawfulCPolyEngine.cdeg_eq_natDegree]

/-- Fuel at least one more than the input degree reaches the nonlinear remainder bound. -/
theorem cPolyReduceTower_normal_of_fuel (Dt : P α) (hdelta : 2 ≤ CPolyEngine.cdeg Dt) :
    ∀ (p : P α) (fuel : ℕ), CPolyEngine.cdeg p + 1 ≤ fuel →
      CPolyEngine.cdeg (cPolyReduceTower Dt fuel p).2 < CPolyEngine.cdeg Dt := by
  intro p fuel hfuel
  generalize hn : CPolyEngine.cdeg p = n at hfuel
  induction n using Nat.strong_induction_on generalizing p fuel with
  | h n ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hpnorm : CPolyEngine.cdeg (CPolyEngine.cnorm p) = n := by
            rw [cdeg_cnorm, hn]
          by_cases hzero : CPolyEngine.cisZero (CPolyEngine.cnorm p) = true
          · have hpzero : CPoly.toPoly (CPolyEngine.cnorm p) = 0 :=
              (LawfulCPolyEngine.cisZero_iff _).mp hzero
            have hdegzero : CPolyEngine.cdeg (CPolyEngine.cnorm p) = 0 := by
              rw [LawfulCPolyEngine.cdeg_eq_natDegree, hpzero]
              simp only [Polynomial.natDegree_zero]
            have hpositive : 0 < CPolyEngine.cdeg Dt := by omega
            simpa [cPolyReduceTower, hzero, hdegzero] using hpositive
          · have hzero' : CPolyEngine.cisZero (CPolyEngine.cnorm p) = false := by
              simpa only [Bool.eq_false_iff] using hzero
            by_cases hsmall : CPolyEngine.cdeg (CPolyEngine.cnorm p) < CPolyEngine.cdeg Dt
            · simp [cPolyReduceTower, hzero', hsmall]
            · let step := nonlinearReductionStep Dt p
              have hstep : CPolyEngine.cdeg step.2 < n := by
                calc
                  CPolyEngine.cdeg step.2 < CPolyEngine.cdeg (CPolyEngine.cnorm p) :=
                    nonlinearReductionStep_degree_lt Dt p hdelta hzero' hsmall
                  _ = n := hpnorm
              have hrec := ih (CPolyEngine.cdeg step.2) hstep step.2 fuel rfl (by omega)
              rw [cPolyReduceTower_succ_active Dt p fuel hzero' hsmall]
              exact hrec

omit [CharZero (CFieldSpec.K α)] in
/-- A denotational reconstruction identity makes the executable reduction check succeed. -/
theorem polynomialReductionCheck_of_reconstruction (Dt p : P α)
    (out : PolynomialReductionResult P α)
    (h : CPoly.toPoly p = Differential.implicitDeriv (CPoly.toPoly Dt)
        (CPoly.toPoly out.antiderivative) + CPoly.toPoly out.remainder) :
    polynomialReductionCheck Dt p out = true := by
  unfold polynomialReductionCheck
  apply (LawfulCPolyEngine.cisZero_iff _).mpr
  rw [CPolyEngine.toPoly_sub, LawfulCPolyEngine.toPoly_add,
    CPolyEngine.toPoly_monomialDeriv]
  exact sub_eq_zero.mpr h.symm

omit [LawfulCPolyEngine P] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CharZero (CFieldSpec.K α)] in
/-- A proved nonlinear degree bound makes the executable normal-form check succeed. -/
theorem nonlinearPolynomialReductionNormalCheck (Dt : P α)
    (out : PolynomialReductionResult P α)
    (h : CPolyEngine.cdeg out.remainder < CPolyEngine.cdeg Dt) :
    polynomialReductionNormalCheck .nonlinear Dt out = true := by
  simp only [polynomialReductionNormalCheck, decide_eq_true_eq]
  exact h

/-- The checked nonlinear reduction succeeds with input-degree fuel. -/
theorem towerPolynomialReduction_nonlinear_runs (Dt p : P α)
    (hdelta : 2 ≤ CPolyEngine.cdeg Dt) :
    ∃ out : PolynomialReductionResult P α,
      (DensePoly.towerPolynomialReduction (P := P) (α := α)).reduce .nonlinear Dt
          (CPolyEngine.cdeg p + 1) p = some out ∧
        IsPolynomialReduction .nonlinear Dt p out := by
  let raw := cPolyReduceTower Dt (CPolyEngine.cdeg p + 1) p
  let out : PolynomialReductionResult P α := ⟨raw.1, raw.2⟩
  have hreconstruct : CPoly.toPoly p = Differential.implicitDeriv (CPoly.toPoly Dt)
      (CPoly.toPoly out.antiderivative) + CPoly.toPoly out.remainder := by
    simpa only [out, raw] using cPolyReduceTower_reconstruct Dt (CPolyEngine.cdeg p + 1) p
  have hnormal : CPolyEngine.cdeg out.remainder < CPolyEngine.cdeg Dt := by
    simpa only [out, raw] using cPolyReduceTower_normal_of_fuel Dt hdelta p
      (CPolyEngine.cdeg p + 1) (by omega)
  refine ⟨out, ?_, ?_⟩
  · simp only [towerPolynomialReduction, out, raw]
    rw [polynomialReductionCheck_of_reconstruction Dt p out hreconstruct,
      nonlinearPolynomialReductionNormalCheck Dt out hnormal]
    rfl
  · constructor
    · exact hreconstruct
    · simpa only [LawfulCPolyEngine.cdeg_eq_natDegree] using hnormal

/-- The checked tower reducer is complete on nonlinear monomial inputs with derivative degree at least two. -/
instance instCompleteCPolynomialReductionNonlinear :
    CompleteCPolynomialReduction (DensePoly.towerPolynomialReduction (P := P) (α := α))
      nonlinearPolynomialReductionDomain where
  relative_complete kind Dt p hdomain _ := by
    rcases hdomain with ⟨rfl, hdelta⟩
    obtain ⟨out, hrun, hresult⟩ := towerPolynomialReduction_nonlinear_runs Dt p hdelta
    exact ⟨CPolyEngine.cdeg p + 1, out, hrun, hresult⟩

end DensePoly

end DeepWiki.SymbolicIntegration
