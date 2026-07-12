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

omit [CharZero (CFieldSpec.K α)] in
/-- The primitive subdomain handled by the termwise kernel: a nonzero constant monomial derivative
and constant polynomial coefficients. -/
def primitivePolynomialReductionDomain : PolynomialReductionDomain P α := fun kind Dt p =>
  kind = .primitive ∧ ∃ η : CFieldSpec.K α,
    CPoly.toPoly Dt = Polynomial.C η ∧ η ≠ 0 ∧ η′ = 0 ∧
      Differential.mapCoeffs (CPoly.toPoly p) = 0

omit [CharZero (CFieldSpec.K α)] in
/-- Coefficientwise differentiation commutes with formal polynomial differentiation. -/
private theorem mapCoeffs_derivative_commute (r : (CFieldSpec.K α)[X]) :
    Differential.mapCoeffs (Polynomial.derivative r) =
      Polynomial.derivative (Differential.mapCoeffs r) := by
  ext n
  rw [Differential.coeff_mapCoeffs, coeff_derivative, coeff_derivative,
    Differential.coeff_mapCoeffs, Derivation.leibniz]
  have hnat : ((↑n + 1 : CFieldSpec.K α))′ = 0 := by
    rw [show ((↑n + 1 : CFieldSpec.K α)) = ((n + 1 : ℕ) : CFieldSpec.K α) by push_cast; ring,
      Derivation.map_natCast]
  rw [hnat, smul_zero, zero_add, smul_eq_mul, mul_comm]

/-- The leading monomial and residual polynomial used by one primitive integration step. -/
def primitiveReductionStep (Dt p : P α) : P α × P α :=
  let p := CPolyEngine.cnorm p
  let m := CPolyEngine.cdeg p
  let c := CField.div (CPolyEngine.clead p)
    (CCommRing.mul (CField.natCast (m + 1)) (CPolyEngine.clead Dt))
  let q0 := CPolyEngine.monomial (P := P) c (m + 1)
  (q0, CPolyEngine.sub p (CPolyEngine.monomialDeriv Dt q0))

omit [LawfulCPolyEngine P] [CFieldSpec α] [CDiffFieldSpec α]
  [CharZero (CFieldSpec.K α)] in
/-- An active primitive recursive call exposes its leading monomial and residual. -/
theorem cPrimitivePolyIntegrate_succ_active (Dt p : P α) (fuel : ℕ)
    (hzero : CPolyEngine.cisZero (CPolyEngine.cnorm p) = false)
    (hpositive : CPolyEngine.cdeg (CPolyEngine.cnorm p) ≠ 0) :
    cPrimitivePolyIntegrate Dt (fuel + 1) p =
      let step := primitiveReductionStep Dt p
      let rest := cPrimitivePolyIntegrate Dt fuel step.2
      (CPolyEngine.add step.1 rest.1, rest.2) := by
  simp [cPrimitivePolyIntegrate, primitiveReductionStep, hzero, hpositive]

/-- A primitive step preserves coefficientwise constancy when both the input and monomial derivative
have constant coefficients. -/
theorem primitiveReductionStep_constants (Dt p : P α) (η : CFieldSpec.K α)
    (hDt : CPoly.toPoly Dt = Polynomial.C η) (hηconst : η′ = 0)
    (hpconst : Differential.mapCoeffs (CPoly.toPoly p) = 0) :
    Differential.mapCoeffs (CPoly.toPoly (primitiveReductionStep Dt p).2) = 0 := by
  let pnorm := CPolyEngine.cnorm p
  let m := CPolyEngine.cdeg pnorm
  let c := CField.div (CPolyEngine.clead pnorm)
    (CCommRing.mul (CField.natCast (m + 1)) (CPolyEngine.clead Dt))
  let q0 := CPolyEngine.monomial (P := P) c (m + 1)
  have hpnormconst : Differential.mapCoeffs (CPoly.toPoly pnorm) = 0 := by
    change Differential.mapCoeffs (CPoly.toPoly (CPolyEngine.cnorm p)) = 0
    rw [LawfulCPolyEngine.toPoly_cnorm]
    exact hpconst
  have hleadconst : (CPoly.toPoly pnorm).leadingCoeff′ = 0 := by
    have hcoeff := congrArg (fun r : (CFieldSpec.K α)[X] => r.coeff (CPoly.toPoly pnorm).natDegree)
      hpnormconst
    change ((CPoly.toPoly pnorm).coeff (CPoly.toPoly pnorm).natDegree)′ = 0
    exact hcoeff
  have hcleadP : CFieldSpec.toK (CPolyEngine.clead pnorm) =
      (CPoly.toPoly pnorm).leadingCoeff := by
    simpa only [toR_eq_toK] using LawfulCPolyEngine.toR_clead_eq_leadingCoeff pnorm
  have hcleadDt : CFieldSpec.toK (CPolyEngine.clead Dt) = η := by
    calc
      CFieldSpec.toK (CPolyEngine.clead Dt) = (CPoly.toPoly Dt).leadingCoeff := by
        simpa only [toR_eq_toK] using LawfulCPolyEngine.toR_clead_eq_leadingCoeff Dt
      _ = η := by rw [hDt]; simp
  have hcformula : CFieldSpec.toK c = (CPoly.toPoly pnorm).leadingCoeff /
      ((↑(m + 1) : CFieldSpec.K α) * η) := by
    dsimp [c]
    rw [CFieldSpec.toK_div, CFieldSpec.toK_mul, CFieldSpec.toK_natCast, hcleadP, hcleadDt]
  have hdenconst : ((↑(m + 1) : CFieldSpec.K α) * η)′ = 0 := by
    rw [Derivation.leibniz, hηconst]
    simp
  have hcconst : (CFieldSpec.toK c)′ = 0 := by
    rw [hcformula, deriv_div, hleadconst, hdenconst]
    ring
  have hq0 : CPoly.toPoly q0 = Polynomial.monomial (m + 1) (CFieldSpec.toK c) := by
    dsimp [q0]
    rw [LawfulCPolyEngine.toPoly_monomial, ← Polynomial.C_mul_X_pow_eq_monomial]
    rfl
  have hqconst : Differential.mapCoeffs (CPoly.toPoly q0) = 0 := by
    rw [hq0, Differential.mapCoeffs_monomial, hcconst]
    simp
  have hderivconst : Differential.mapCoeffs
      (Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly q0)) = 0 := by
    rw [hDt]
    rw [show Differential.implicitDeriv (Polynomial.C η) (CPoly.toPoly q0) =
      Differential.mapCoeffs (CPoly.toPoly q0) + Polynomial.C η * Polynomial.derivative
        (CPoly.toPoly q0) by simp [Differential.implicitDeriv, derivative']]
    rw [map_add, hqconst, Derivation.leibniz, Differential.mapCoeffs_C, hηconst,
      mapCoeffs_derivative_commute, hqconst, Polynomial.derivative_zero]
    simp
  change Differential.mapCoeffs
    (CPoly.toPoly (CPolyEngine.sub pnorm (CPolyEngine.monomialDeriv Dt q0))) = 0
  rw [CPolyEngine.toPoly_sub, CPolyEngine.toPoly_monomialDeriv, map_sub,
    hpnormconst, hderivconst, sub_zero]

/-- An active primitive step cancels its leading term and strictly lowers degree. -/
theorem primitiveReductionStep_degree_lt (Dt p : P α) (η : CFieldSpec.K α)
    (hDt : CPoly.toPoly Dt = Polynomial.C η) (hη : η ≠ 0) (hηconst : η′ = 0)
    (hpconst : Differential.mapCoeffs (CPoly.toPoly p) = 0)
    (hzero : CPolyEngine.cisZero (CPolyEngine.cnorm p) = false)
    (hpositive : CPolyEngine.cdeg (CPolyEngine.cnorm p) ≠ 0) :
    CPolyEngine.cdeg (primitiveReductionStep Dt p).2 < CPolyEngine.cdeg (CPolyEngine.cnorm p) := by
  let K := CFieldSpec.K α
  let pnorm := CPolyEngine.cnorm p
  let m := CPolyEngine.cdeg pnorm
  let c := CField.div (CPolyEngine.clead pnorm)
    (CCommRing.mul (CField.natCast (m + 1)) (CPolyEngine.clead Dt))
  let q0 := CPolyEngine.monomial (P := P) c (m + 1)
  have hp : CPoly.toPoly pnorm ≠ 0 := CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false hzero
  have hm : (CPoly.toPoly pnorm).natDegree = m := by
    rw [← LawfulCPolyEngine.cdeg_eq_natDegree]
  have hmpositive : 1 ≤ m := by
    dsimp [m]
    exact Nat.pos_of_ne_zero hpositive
  have hpnormconst : Differential.mapCoeffs (CPoly.toPoly pnorm) = 0 := by
    change Differential.mapCoeffs (CPoly.toPoly (CPolyEngine.cnorm p)) = 0
    rw [LawfulCPolyEngine.toPoly_cnorm]
    exact hpconst
  have hleadconst : (CPoly.toPoly pnorm).leadingCoeff′ = 0 := by
    have hcoeff := congrArg (fun r : K[X] => r.coeff (CPoly.toPoly pnorm).natDegree) hpnormconst
    change ((CPoly.toPoly pnorm).coeff (CPoly.toPoly pnorm).natDegree)′ = 0
    exact hcoeff
  have hcleadP : CFieldSpec.toK (CPolyEngine.clead pnorm) =
      (CPoly.toPoly pnorm).leadingCoeff := by
    simpa only [toR_eq_toK] using LawfulCPolyEngine.toR_clead_eq_leadingCoeff pnorm
  have hcleadDt : CFieldSpec.toK (CPolyEngine.clead Dt) = η := by
    calc
      CFieldSpec.toK (CPolyEngine.clead Dt) = (CPoly.toPoly Dt).leadingCoeff := by
        simpa only [toR_eq_toK] using LawfulCPolyEngine.toR_clead_eq_leadingCoeff Dt
      _ = η := by rw [hDt]; simp
  have hdenconst : ((↑(m + 1) : K) * η)′ = 0 := by
    rw [Derivation.leibniz, hηconst]
    simp
  have hcformula : CFieldSpec.toK c = (CPoly.toPoly pnorm).leadingCoeff /
      ((↑(m + 1) : K) * η) := by
    dsimp [c]
    rw [CFieldSpec.toK_div, CFieldSpec.toK_mul, CFieldSpec.toK_natCast, hcleadP, hcleadDt]
  have hcconst : (CFieldSpec.toK c)′ = 0 := by
    rw [hcformula, deriv_div, hleadconst, hdenconst]
    ring
  have hc : CFieldSpec.toK c ≠ 0 := by
    rw [hcformula]
    apply div_ne_zero
    · exact leadingCoeff_ne_zero.mpr hp
    · apply mul_ne_zero
      · exact Nat.cast_ne_zero.mpr (by omega)
      · exact hη
  have hq0 : CPoly.toPoly q0 = Polynomial.monomial (m + 1) (CFieldSpec.toK c) := by
    dsimp [q0]
    rw [LawfulCPolyEngine.toPoly_monomial, ← Polynomial.C_mul_X_pow_eq_monomial]
    rfl
  have hqdeg : (CPoly.toPoly q0).natDegree = m + 1 := by
    rw [hq0, Polynomial.natDegree_monomial_eq _ hc]
  have hqlead : (CPoly.toPoly q0).leadingCoeff = CFieldSpec.toK c := by
    rw [hq0, Polynomial.leadingCoeff_monomial]
  have hqconst : Differential.mapCoeffs (CPoly.toPoly q0) = 0 := by
    rw [hq0, Differential.mapCoeffs_monomial, hcconst]
    simp
  have hDq : Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly q0) =
      Polynomial.C η * Polynomial.derivative (CPoly.toPoly q0) := by
    rw [hDt]
    rw [show Differential.implicitDeriv (Polynomial.C η) (CPoly.toPoly q0) =
      Differential.mapCoeffs (CPoly.toPoly q0) + Polynomial.C η * Polynomial.derivative
        (CPoly.toPoly q0) by simp [Differential.implicitDeriv, derivative'], hqconst, zero_add]
  have hDqzero : Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly q0) ≠ 0 := by
    rw [hDq]
    apply mul_ne_zero
    · exact Polynomial.C_ne_zero.mpr hη
    · exact Polynomial.derivative_ne_zero.mpr (by rw [hqdeg]; omega)
  have hDqdeg :
      (Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly q0)).natDegree = m := by
    rw [hDq, Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr hη)
      (Polynomial.derivative_ne_zero.mpr (by rw [hqdeg]; omega)), Polynomial.natDegree_C,
      zero_add, Polynomial.natDegree_derivative, hqdeg]
    omega
  have hDqlead :
      (Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly q0)).leadingCoeff =
        (CPoly.toPoly pnorm).leadingCoeff := by
    rw [hDq, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_derivative, hqlead, hqdeg, hcformula]
    have hden : ((↑(m + 1) : K) * η) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hη
    field_simp [hden]
  change CPolyEngine.cdeg
      (CPolyEngine.sub pnorm (CPolyEngine.monomialDeriv Dt q0)) < CPolyEngine.cdeg pnorm
  rw [LawfulCPolyEngine.cdeg_eq_natDegree, CPolyEngine.toPoly_sub,
    CPolyEngine.toPoly_monomialDeriv, LawfulCPolyEngine.cdeg_eq_natDegree]
  by_cases hreszero : CPoly.toPoly pnorm -
      Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly q0) = 0
  · rw [hreszero]
    simp only [Polynomial.natDegree_zero]
    rw [hm]
    omega
  · apply (Polynomial.natDegree_lt_iff_degree_lt hreszero).mpr
    have hdegree : (CPoly.toPoly pnorm).degree =
        (Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly q0)).degree := by
      rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hDqzero, hDqdeg, hm]
    have hsub := Polynomial.degree_sub_lt hdegree hp hDqlead.symm
    rw [Polynomial.degree_eq_natDegree hp, hm] at hsub
    rw [hm]
    exact hsub

/-- Fuel at least one more than the input degree reduces a constant-coefficient primitive polynomial
to a constant remainder. -/
theorem cPrimitivePolyIntegrate_normal_of_fuel (Dt : P α) (η : CFieldSpec.K α)
    (hDt : CPoly.toPoly Dt = Polynomial.C η) (hη : η ≠ 0) (hηconst : η′ = 0) :
    ∀ (p : P α) (fuel : ℕ), Differential.mapCoeffs (CPoly.toPoly p) = 0 →
      CPolyEngine.cdeg p + 1 ≤ fuel →
        CPolyEngine.cdeg (cPrimitivePolyIntegrate Dt fuel p).2 = 0 := by
  intro p fuel hpconst hfuel
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
            simp [cPrimitivePolyIntegrate, hzero, hdegzero]
          · have hzero' : CPolyEngine.cisZero (CPolyEngine.cnorm p) = false := by
              simpa only [Bool.eq_false_iff] using hzero
            by_cases hpositive : CPolyEngine.cdeg (CPolyEngine.cnorm p) ≠ 0
            · let step := primitiveReductionStep Dt p
              have hstep : CPolyEngine.cdeg step.2 < n := by
                calc
                  CPolyEngine.cdeg step.2 < CPolyEngine.cdeg (CPolyEngine.cnorm p) :=
                    primitiveReductionStep_degree_lt Dt p η hDt hη hηconst hpconst hzero' hpositive
                  _ = n := hpnorm
              have hstepconst : Differential.mapCoeffs (CPoly.toPoly step.2) = 0 :=
                primitiveReductionStep_constants Dt p η hDt hηconst hpconst
              have hrec := ih (CPolyEngine.cdeg step.2) hstep step.2 fuel hstepconst rfl (by omega)
              rw [cPrimitivePolyIntegrate_succ_active Dt p fuel hzero' hpositive]
              exact hrec
            · have hdegzero : CPolyEngine.cdeg (CPolyEngine.cnorm p) = 0 := by
                exact Nat.eq_zero_of_not_pos (by simpa only [Nat.pos_iff_ne_zero] using hpositive)
              simp [cPrimitivePolyIntegrate, hzero', hdegzero]

omit [CharZero (CFieldSpec.K α)] in
/-- Every fuel-bounded primitive integration run reconstructs its input polynomial. -/
private theorem cPrimitivePolyIntegrate_reconstruct_raw (Dt : P α) : ∀ (fuel : ℕ) (p : P α),
    CPoly.toPoly p = Differential.implicitDeriv (CPoly.toPoly Dt)
        (CPoly.toPoly (cPrimitivePolyIntegrate Dt fuel p).1) +
      CPoly.toPoly (cPrimitivePolyIntegrate Dt fuel p).2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro p
      simp only [cPrimitivePolyIntegrate, CPoly.toPoly_czero, map_zero, zero_add]
      exact (LawfulCPolyEngine.toPoly_cnorm p).symm
  | succ fuel ih =>
      intro p
      rw [← LawfulCPolyEngine.toPoly_cnorm p]
      simp only [cPrimitivePolyIntegrate]
      split
      · simp only [CPoly.toPoly_czero, map_zero, zero_add]
      · rename_i hstop
        let m := CPolyEngine.cdeg (CPolyEngine.cnorm p)
        let am := CPolyEngine.clead (CPolyEngine.cnorm p)
        let mp1 : α := CField.natCast (m + 1)
        let dtConst := CPolyEngine.clead Dt
        let c := CField.div am (CCommRing.mul mp1 dtConst)
        let q0 := CPolyEngine.monomial (P := P) c (m + 1)
        let p' := CPolyEngine.sub (CPolyEngine.cnorm p) (CPolyEngine.monomialDeriv Dt q0)
        have hrec := ih p'
        change CPoly.toPoly (CPolyEngine.cnorm p) =
          Differential.implicitDeriv (CPoly.toPoly Dt)
              (CPoly.toPoly (CPolyEngine.add q0 (cPrimitivePolyIntegrate Dt fuel p').1)) +
            CPoly.toPoly (cPrimitivePolyIntegrate Dt fuel p').2
        rw [LawfulCPolyEngine.toPoly_add, map_add, add_assoc, ← hrec,
          CPolyEngine.toPoly_sub, CPolyEngine.toPoly_monomialDeriv]
        ring

omit [CharZero (CFieldSpec.K α)] in
/-- Every fuel-bounded primitive integration run reconstructs its input polynomial. -/
theorem cPrimitivePolyIntegrate_reconstruct (Dt : P α) : ∀ (fuel : ℕ) (p : P α),
    CPoly.toPoly p = Differential.implicitDeriv (CPoly.toPoly Dt)
        (CPoly.toPoly (cPrimitivePolyIntegrate Dt fuel p).1) +
      CPoly.toPoly (cPrimitivePolyIntegrate Dt fuel p).2 :=
  cPrimitivePolyIntegrate_reconstruct_raw Dt

omit [LawfulCPolyEngine P] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CharZero (CFieldSpec.K α)] in
/-- A proved primitive remainder degree makes the executable normal-form check succeed. -/
theorem primitivePolynomialReductionNormalCheck (Dt : P α)
    (out : PolynomialReductionResult P α) (h : CPolyEngine.cdeg out.remainder = 0) :
    polynomialReductionNormalCheck .primitive Dt out = true := by
  simp only [polynomialReductionNormalCheck, decide_eq_true_eq]
  exact h

/-- The checked primitive reduction succeeds with input-degree fuel on its constant-coefficient domain. -/
theorem towerPolynomialReduction_primitive_runs (Dt p : P α) (η : CFieldSpec.K α)
    (hDt : CPoly.toPoly Dt = Polynomial.C η) (hη : η ≠ 0) (hηconst : η′ = 0)
    (hpconst : Differential.mapCoeffs (CPoly.toPoly p) = 0) :
    ∃ out : PolynomialReductionResult P α,
      (DensePoly.towerPolynomialReduction (P := P) (α := α)).reduce .primitive Dt
          (CPolyEngine.cdeg p + 1) p = some out ∧
        IsPolynomialReduction .primitive Dt p out := by
  let raw := cPrimitivePolyIntegrate Dt (CPolyEngine.cdeg p + 1) p
  let out : PolynomialReductionResult P α := ⟨raw.1, raw.2⟩
  have hreconstruct : CPoly.toPoly p = Differential.implicitDeriv (CPoly.toPoly Dt)
      (CPoly.toPoly out.antiderivative) + CPoly.toPoly out.remainder := by
    simpa only [out, raw] using cPrimitivePolyIntegrate_reconstruct Dt (CPolyEngine.cdeg p + 1) p
  have hnormal : CPolyEngine.cdeg out.remainder = 0 := by
    simpa only [out, raw] using cPrimitivePolyIntegrate_normal_of_fuel Dt η hDt hη hηconst p
      (CPolyEngine.cdeg p + 1) hpconst (by omega)
  refine ⟨out, ?_, ?_⟩
  · simp only [towerPolynomialReduction, out, raw]
    rw [polynomialReductionCheck_of_reconstruction Dt p out hreconstruct,
      primitivePolynomialReductionNormalCheck Dt out hnormal]
    rfl
  · constructor
    · exact hreconstruct
    · simpa only [LawfulCPolyEngine.cdeg_eq_natDegree] using hnormal

/-- The checked tower reducer is complete on constant-coefficient primitive monomial inputs. -/
instance instCompleteCPolynomialReductionPrimitive :
    CompleteCPolynomialReduction (DensePoly.towerPolynomialReduction (P := P) (α := α))
      primitivePolynomialReductionDomain where
  relative_complete kind Dt p hdomain _ := by
    rcases hdomain with ⟨rfl, η, hDt, hη, hηconst, hpconst⟩
    obtain ⟨out, hrun, hresult⟩ :=
      towerPolynomialReduction_primitive_runs Dt p η hDt hη hηconst hpconst
    exact ⟨CPolyEngine.cdeg p + 1, out, hrun, hresult⟩

end DensePoly

end DeepWiki.SymbolicIntegration
