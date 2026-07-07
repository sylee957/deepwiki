import DeepWiki.SymbolicIntegration.CanonicalRepresentation.NormalSqfree
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Radical.Basic

/-! # Canonical split-factor algorithm

Base split-factor recursion and abstract correctness from a one-step property. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section SplitFactor
variable {K : Type*} [Field K] [Differential K]

open Classical in
/-- The squarefree special factor extracted at one `splitFactor` step:
`S = gcd(p, Dp) / gcd(p, dp/dt)` (`Dt = v`) — the product of the *distinct* special irreducible
factors of `p`. -/
noncomputable def splitFactorStep (v p : K[X]) : K[X] :=
  gcd p (Differential.implicitDeriv v p) / gcd p (derivative p)

open Classical in
/-- The `fuel`-bounded splitting recursion: each step extracts the squarefree special factor
`S = gcd(p,Dp)/gcd(p,dp/dt)`, recursing on `p/S`, and returns `(pₙ, pₛ)`. -/
noncomputable def splitFactorAux (v : K[X]) : K[X] → ℕ → K[X] × K[X]
  | p, 0 => (p, 1)
  | p, (n + 1) =>
    let S := splitFactorStep v p
    if S.natDegree = 0 then (p, 1)
    else
      let q := splitFactorAux v (p / S) n
      (q.1, S * q.2)

open Classical in
/-- The splitting of `p` into its normal part `pₙ` and special part `pₛ` w.r.t. the monomial
derivation `D` (`Dt = v`), with `p = pₙ·pₛ`. Iterates
`S ← gcd(p, Dp)/gcd(p, dp/dt)` until the remaining factor is normal. -/
noncomputable def splitFactor (v p : K[X]) : K[X] × K[X] :=
  splitFactorAux v p p.natDegree

open Classical in
/-- One-step property of the `splitFactor` step `S`: if `S` is constant then `q` is normal;
if non-constant then `S` is a special factor of `q` with strictly smaller-degree quotient. -/
def IsSplitFactorStep (v q : K[X]) : Prop :=
  ((splitFactorStep v q).natDegree = 0 → @IsNormal _ _ ⟨Differential.implicitDeriv v⟩ q) ∧
  (0 < (splitFactorStep v q).natDegree →
    (splitFactorStep v q ∣ q ∧
     (q / splitFactorStep v q).natDegree < q.natDegree ∧
     @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ (splitFactorStep v q)))

open Classical in
/-- Under the one-step property holding everywhere, for fuel `≥ deg p`, `splitFactorAux v p fuel`
returns a splitting factorization `(pₙ, pₛ)` of `p` (`p = pₛ·pₙ`, `pₛ` special, `pₙ` normal). -/
theorem splitFactorAux_isSplittingFactorization (v : K[X])
    (hstep : ∀ q : K[X], IsSplitFactorStep v q) :
    ∀ (fuel : ℕ) (p : K[X]), p.natDegree ≤ fuel →
      @IsSplittingFactorization _ _ ⟨Differential.implicitDeriv v⟩ p
        (splitFactorAux v p fuel).2 (splitFactorAux v p fuel).1 := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  intro fuel
  induction fuel with
  | zero =>
    intro p hp
    rw [Nat.le_zero, Polynomial.natDegree_eq_zero] at hp
    obtain ⟨c, rfl⟩ := hp
    have hdeg0 : (splitFactorStep v (C c)).natDegree = 0 := by
      rcases eq_or_ne c 0 with rfl | hc
      · simp only [map_zero, splitFactorStep, map_zero, gcd_zero_left,
          EuclideanDomain.div_zero, natDegree_zero]
      · have hCcu : IsUnit (C c) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
        have hnum : IsUnit (gcd (C c) (Differential.implicitDeriv v (C c))) :=
          isUnit_of_dvd_unit (gcd_dvd_left _ _) hCcu
        have hden : IsUnit (gcd (C c) (derivative (C c))) :=
          isUnit_of_dvd_unit (gcd_dvd_left _ _) hCcu
        have hSu : IsUnit (splitFactorStep v (C c)) :=
          isUnit_of_dvd_unit (EuclideanDomain.div_dvd_of_dvd hden.dvd) hnum
        exact Polynomial.natDegree_eq_zero_of_isUnit hSu
    have hnorm : IsNormal (C c) := (hstep (C c)).1 hdeg0
    simp only [splitFactorAux]
    exact ⟨(one_mul (C c)).symm, isSpecial_one, hnorm⟩
  | succ n ih =>
    intro p hp
    rw [splitFactorAux]
    simp only
    set S := splitFactorStep v p with hS
    by_cases hdeg : S.natDegree = 0
    · rw [if_pos hdeg]
      exact ⟨(one_mul p).symm, isSpecial_one, (hstep p).1 hdeg⟩
    · rw [if_neg hdeg]
      have hSpos : 0 < S.natDegree := Nat.pos_of_ne_zero hdeg
      obtain ⟨hSdvd, hdrop, hSspec⟩ := (hstep p).2 hSpos
      rw [← hS] at hdrop hSdvd hSspec
      have hSne : S ≠ 0 := fun h => hdeg (by rw [h]; simp)
      have hpS : (p / S).natDegree ≤ n := by omega
      obtain ⟨heq, hq2spec, hq1norm⟩ := ih (p / S) hpS
      refine ⟨?_, hSspec.mul hq2spec, hq1norm⟩
      rw [mul_assoc, ← heq, EuclideanDomain.mul_div_cancel' hSne hSdvd]

open Classical in
/-- `splitFactor` correctness: under the one-step property `IsSplitFactorStep`
holding at every polynomial, `splitFactor v p = (pₙ, pₛ)` is a splitting
factorization of `p` w.r.t. `D` (`Dt = v`) — `p = pₛ·pₙ`, `pₛ` special, `pₙ` normal. -/
theorem splitFactor_isSplittingFactorization (v p : K[X])
    (hstep : ∀ q : K[X], IsSplitFactorStep v q) :
    @IsSplittingFactorization _ _ ⟨Differential.implicitDeriv v⟩ p
      (splitFactor v p).2 (splitFactor v p).1 :=
  splitFactorAux_isSplittingFactorization v hstep p.natDegree p le_rfl

end SplitFactor

end DeepWiki.SymbolicIntegration
