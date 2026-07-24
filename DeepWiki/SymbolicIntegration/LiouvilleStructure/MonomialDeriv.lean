import Mathlib.FieldTheory.Differential.Liouville
import Mathlib.RingTheory.Derivation.MapCoeffs

/-! # Monomial derivations in Liouville structure

Degree behaviour for log and exp monomial derivations on `K[θ]`. -/

open scoped Differential
open Polynomial Differential

namespace DeepWiki.SymbolicIntegration.LiouvilleStructure

variable {K : Type*} [Field K] [Differential K]

/-! ## The log monomial `θ′ = c ∈ K` -/

/-- The log-monomial derivation on `K[θ]`: `Differential.implicitDeriv (C c)`, with `θ′ = c ∈ K`. -/
noncomputable def logMonomialDeriv (c : K) : Derivation ℤ K[X] K[X] :=
  Differential.implicitDeriv (C c)

/-- `θ′ = C c` for the log monomial. -/
@[simp]
lemma logMonomialDeriv_X (c : K) : logMonomialDeriv c (X : K[X]) = C c := by
  simp [logMonomialDeriv]

/-- The log monomial extends `K`'s derivation on constants: `D (C b) = C b′`. -/
@[simp]
lemma logMonomialDeriv_C (c b : K) : logMonomialDeriv c (C b) = C b′ := by
  simp [logMonomialDeriv]

/-- Coefficient formula for the log monomial:
`(D p).coeff i = (p.coeff i)′ + c·(i+1)·p.coeff (i+1)`. -/
lemma coeff_logMonomialDeriv (c : K) (p : K[X]) (i : ℕ) :
    (logMonomialDeriv c p).coeff i = (p.coeff i)′ + c * ((i + 1) * p.coeff (i + 1)) := by
  simp only [logMonomialDeriv, implicitDeriv, Derivation.coe_add, Pi.add_apply,
    Derivation.coe_smul, Pi.smul_apply, Derivation.restrictScalars_apply,
    derivative'_apply, coeff_add, coeff_mapCoeffs, smul_eq_mul, coeff_C_mul,
    coeff_derivative]
  ring

/-- Log monomial, top coefficient: `(D p).coeff (natDegree p) = (leadingCoeff p)′` (the degree drop). -/
lemma coeff_natDegree_logMonomialDeriv (c : K) (p : K[X]) :
    (logMonomialDeriv c p).coeff p.natDegree = (p.leadingCoeff)′ := by
  rw [coeff_logMonomialDeriv]
  have h : p.coeff (p.natDegree + 1) = 0 := coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
  rw [h, leadingCoeff]
  simp

/-- The log monomial does not raise `θ`-degree: `natDegree (D p) ≤ natDegree p`. -/
lemma natDegree_logMonomialDeriv_le (c : K) (p : K[X]) :
    (logMonomialDeriv c p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_logMonomialDeriv]
  rw [coeff_eq_zero_of_natDegree_lt hi,
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_of_lt hi) (Nat.lt_succ_self i))]
  simp

/-! ## The exp monomial `θ′/θ = c ∈ K` -/

/-- The exp-monomial derivation on `K[θ]`: `Differential.implicitDeriv (C c · X)`, with `θ′ = c·θ`. -/
noncomputable def expMonomialDeriv (c : K) : Derivation ℤ K[X] K[X] :=
  Differential.implicitDeriv (C c * X)

/-- `θ′ = c·θ` for the exp monomial. -/
@[simp]
lemma expMonomialDeriv_X (c : K) : expMonomialDeriv c (X : K[X]) = C c * X := by
  simp [expMonomialDeriv]

/-- The exp monomial extends `K`'s derivation on constants: `D (C b) = C b′`. -/
@[simp]
lemma expMonomialDeriv_C (c b : K) : expMonomialDeriv c (C b) = C b′ := by
  simp [expMonomialDeriv]

/-- Coefficient formula for the exp monomial: `(D p).coeff i = (p.coeff i)′ + c·i·p.coeff i`. -/
lemma coeff_expMonomialDeriv (c : K) (p : K[X]) (i : ℕ) :
    (expMonomialDeriv c p).coeff i = (p.coeff i)′ + c * (i * p.coeff i) := by
  have hXmul : ((X : K[X]) * derivative p).coeff i = i * p.coeff i := by
    cases i with
    | zero => simp
    | succ n => rw [coeff_X_mul, coeff_derivative]; push_cast; ring
  simp only [expMonomialDeriv, implicitDeriv, Derivation.coe_add, Pi.add_apply,
    Derivation.coe_smul, Pi.smul_apply, Derivation.restrictScalars_apply,
    derivative'_apply, coeff_add, coeff_mapCoeffs, smul_eq_mul]
  have hrw : C c * X * derivative p = C c * (X * derivative p) := by ring
  rw [hrw, coeff_C_mul, hXmul]

/-- Exp monomial, top coefficient:
`(D p).coeff (natDegree p) = (leadingCoeff p)′ + c·(natDegree p)·(leadingCoeff p)` (degree-preserving). -/
lemma coeff_natDegree_expMonomialDeriv (c : K) (p : K[X]) :
    (expMonomialDeriv c p).coeff p.natDegree
      = (p.leadingCoeff)′ + c * (p.natDegree * p.leadingCoeff) := by
  rw [coeff_expMonomialDeriv, leadingCoeff]

/-- The exp monomial does not raise `θ`-degree: `natDegree (D p) ≤ natDegree p`. -/
lemma natDegree_expMonomialDeriv_le (c : K) (p : K[X]) :
    (expMonomialDeriv c p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_expMonomialDeriv, coeff_eq_zero_of_natDegree_lt hi]
  simp

/-! ## Axiom audit -/


#print axioms coeff_natDegree_logMonomialDeriv
#print axioms coeff_natDegree_expMonomialDeriv

end DeepWiki.SymbolicIntegration.LiouvilleStructure
