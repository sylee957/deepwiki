import DeepWiki.SymbolicIntegration.CanonicalRepresentation.Classify
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.NormalSqfree
import DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Radical.Basic

/-! # Root characterization for canonical splits

Roots of the special and normal factors in a coefficient-lifting split are characterized by
whether the root is a differential constant.
-/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section RootCharacterization
variable {K : Type*} [Field K] [CharZero K] [Differential K]

open Classical in
/-- A root `α` of a special polynomial `pₛ` (w.r.t. the coefficient-lifting derivation, `Dt = 0`)
is a constant: `Dα = 0`. -/
theorem deriv_eq_zero_of_isSpecial_of_isRoot {ps : K[X]} (hps0 : ps ≠ 0)
    (hps : @IsSpecial _ _ ⟨Differential.implicitDeriv 0⟩ ps) {α : K} (hα : ps.IsRoot α) :
    α′ = 0 := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv 0⟩
  have hdvd : (X - C α) ∣ ps := dvd_iff_isRoot.mpr hα
  have hprime : Prime (X - C α) := prime_X_sub_C α
  have hmult : IsUnit ((multiplicity (X - C α) ps : K[X])) := by
    rw [← map_natCast (C : K →+* K[X])]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr
      (by have := multiplicity_pos_of_dvd hdvd; omega)))
  have hspX : IsSpecial (X - C α) := isSpecial_of_prime_dvd hprime hdvd hps0 hps hmult
  have := (dvd_X_sub_C_implicitDeriv_iff (0 : K[X]) α).mp hspX
  simpa using this.symm

omit [CharZero K] in
open Classical in
/-- A root `α` of a normal polynomial `pₙ` (w.r.t. the coefficient-lifting derivation, `Dt = 0`)
is nonconstant: `Dα ≠ 0`. -/
theorem deriv_ne_zero_of_isNormal_of_isRoot {pn : K[X]}
    (hpn : @IsNormal _ _ ⟨Differential.implicitDeriv 0⟩ pn) {α : K} (hα : pn.IsRoot α) :
    α′ ≠ 0 := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv 0⟩
  have hdvd : (X - C α) ∣ pn := dvd_iff_isRoot.mpr hα
  have hnX : IsNormal (X - C α) := IsNormal.of_dvd hpn hdvd
  have := (isCoprime_X_sub_C_implicitDeriv_iff (0 : K[X]) α).mp hnX
  simp only [eval_zero] at this
  exact fun h => this h.symm

open Classical in
/-- Root characterization: for a splitting factorization `p = pₛ·pₙ` (coefficient-lifting
derivation, char `0`), a root `α` of `p` is constant iff a root of the special part:
`Dα = 0 ↔ pₛ(α) = 0`. -/
theorem deriv_eq_zero_iff_isRoot_special {p ps pn : K[X]} (hps0 : ps ≠ 0)
    (hfact : @IsSplittingFactorization _ _ ⟨Differential.implicitDeriv 0⟩ p ps pn)
    {α : K} (hα : p.IsRoot α) :
    α′ = 0 ↔ ps.IsRoot α := by
  obtain ⟨hpeq, hspec, hnorm⟩ := hfact
  have hroot : ps.IsRoot α ∨ pn.IsRoot α := by
    have : (ps * pn).IsRoot α := hpeq ▸ hα
    rw [IsRoot, eval_mul, mul_eq_zero] at this
    exact this
  constructor
  · intro hd0
    rcases hroot with hs | hn
    · exact hs
    · exact absurd hd0 (deriv_ne_zero_of_isNormal_of_isRoot hnorm hn)
  · intro hs
    exact deriv_eq_zero_of_isSpecial_of_isRoot hps0 hspec hs

open Classical in
/-- Nonconstant dual of the root characterization: a root `α` of `p` is nonconstant iff it is a
root of the normal part — `Dα ≠ 0 ↔ pₙ(α) = 0`. -/
theorem deriv_ne_zero_iff_isRoot_normal {p ps pn : K[X]} (hps0 : ps ≠ 0)
    (hfact : @IsSplittingFactorization _ _ ⟨Differential.implicitDeriv 0⟩ p ps pn)
    {α : K} (hα : p.IsRoot α) :
    α′ ≠ 0 ↔ pn.IsRoot α := by
  have hpeq := hfact.1
  have hroot : ps.IsRoot α ∨ pn.IsRoot α := by
    have : (ps * pn).IsRoot α := hpeq ▸ hα
    rw [IsRoot, eval_mul, mul_eq_zero] at this
    exact this
  constructor
  · intro hd
    rcases hroot with hs | hn
    · exact absurd ((deriv_eq_zero_iff_isRoot_special hps0 hfact hα).mpr hs) hd
    · exact hn
  · intro hn
    exact deriv_ne_zero_of_isNormal_of_isRoot hfact.2.2 hn

end RootCharacterization

end DeepWiki.SymbolicIntegration
