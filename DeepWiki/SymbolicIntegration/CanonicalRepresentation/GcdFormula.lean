import DeepWiki.SymbolicIntegration.CanonicalRepresentation.SplitFactor
import DeepWiki.SymbolicIntegration.MonomialExtensions
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Radical.Basic

/-! # Gcd formulas for canonical split factors

Prime-factor formulas for `gcd(p, Dp)` and the characteristic-zero specialization used by
canonical split-factor correctness.
-/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section GeneralSplitFactor
variable {K : Type*} [Field K] [Differential K]

open UniqueFactorizationMonoid

open Classical in
omit [Differential K] in
/-- Prime-power decomposition of a nonzero polynomial: `p ~ ∏_{π ∈ primeFactors p} π^{m_π}` with
`m_π = count π (normalizedFactors p)`. -/
theorem associated_prod_primeFactors_pow {p : K[X]} (hp : p ≠ 0) :
    Associated p (∏ π ∈ primeFactors p, π ^ (normalizedFactors p).count π) := by
  have h1 : Associated (normalizedFactors p).prod p := prod_normalizedFactors hp
  rw [Finset.prod_multiset_count] at h1
  have hpf : primeFactors p = (normalizedFactors p).toFinset := by
    rw [primeFactors]; congr 1; exact Subsingleton.elim _ _
  rw [hpf]
  exact h1.symm

end GeneralSplitFactor

section GcdDerivAssoc
variable {R : Type*} [CommRing R] [NormalizedGCDMonoid R] [Differential R]

/-- gcd-with-derivative is an associate invariant: `Associated p q → gcd(p, Dp) ~ gcd(q, Dq)`. -/
theorem associated_gcd_deriv_of_associated {p q : R} (h : Associated p q) :
    Associated (gcd p p′) (gcd q q′) := by
  obtain ⟨u, rfl⟩ := h
  have hugcd : IsUnit (gcd p (u : R)) := isUnit_of_dvd_unit (gcd_dvd_right _ _) u.isUnit
  have hbase := associated_gcd_deriv_mul (a := p) (b := (u : R)) hugcd
  have huu : IsUnit (gcd (u : R) ((u : R)′)) :=
    isUnit_of_dvd_unit (gcd_dvd_left _ _) u.isUnit
  refine (hbase.trans ?_).symm
  exact (associated_mul_unit_right _ _ huu).symm

end GcdDerivAssoc

section GeneralGcdFormula
variable {K : Type*} [Field K] [Differential K[X]]

open UniqueFactorizationMonoid

open Classical in
/-- gcd-with-derivative over arbitrary irreducibles: for `p ≠ 0` with every multiplicity a unit
(char `0`), `gcd(p, Dp) ~ (∏_π π^{m_π−1})·∏_π gcd(π, Dπ)`. -/
theorem associated_gcd_deriv_prod_primeFactors {p : K[X]} (hp : p ≠ 0)
    (hunit : ∀ π ∈ primeFactors p, IsUnit (((normalizedFactors p).count π : ℕ) : K[X])) :
    Associated (gcd p p′)
      ((∏ π ∈ primeFactors p, π ^ ((normalizedFactors p).count π - 1))
        * ∏ π ∈ primeFactors p, gcd π π′) := by
  set m : K[X] → ℕ := fun π => (normalizedFactors p).count π with hm
  -- bridge `gcd p (Dp)` to the decomposition.
  have hbridge := associated_gcd_deriv_of_associated (associated_prod_primeFactors_pow hp)
  refine hbridge.trans ?_
  -- pairwise coprimality of distinct prime powers.
  have hco : ∀ π ∈ primeFactors p, ∀ ρ ∈ primeFactors p, π ≠ ρ →
      IsUnit (gcd (π ^ m π) (ρ ^ m ρ)) := by
    intro π hπ ρ hρ hπρ
    refine gcd_isUnit_iff_isRelPrime.mpr ?_
    exact ((pairwise_primeFactors_isRelPrime (a := p)) hπ hρ hπρ).pow
  -- split over the prime powers, then compute each power.
  refine (associated_gcd_deriv_prod (primeFactors p) (fun π => π ^ m π) hco).trans ?_
  have heach : Associated (∏ π ∈ primeFactors p, gcd (π ^ m π) ((π ^ m π)′))
      (∏ π ∈ primeFactors p, π ^ (m π - 1) * gcd π π′) := by
    refine Associated.prod (primeFactors p) _ _ (fun π hπ => ?_)
    rcases Nat.eq_zero_or_pos (m π) with hm0 | hmpos
    · exfalso
      have hmem : π ∈ normalizedFactors p := mem_primeFactors.mp hπ
      have hcount : 0 < (normalizedFactors p).count π := Multiset.count_pos.mpr hmem
      simp only [hm] at hm0; omega
    · exact associated_gcd_deriv_pow hmpos (hunit π hπ)
  refine heach.trans ?_
  rw [Finset.prod_mul_distrib]

open Classical in
/-- Per-prime gcd collapse: `∏_π gcd(π, Dπ) ~ ∏_{π special} π` over the prime factors of `p`. -/
theorem associated_prod_gcd_deriv_primeFactors {p : K[X]} :
    Associated (∏ π ∈ primeFactors p, gcd π π′)
      (∏ π ∈ (primeFactors p).filter (fun π => @IsSpecial _ _ ⟨(Differential.deriv : _)⟩ π), π) := by
  rw [Finset.prod_filter]
  refine Associated.prod (primeFactors p) _ _ (fun π hπ => ?_)
  have hirr : Irreducible π := irreducible_of_normalized_factor π (mem_primeFactors.mp hπ)
  by_cases h : @IsSpecial _ _ ⟨(Differential.deriv : _)⟩ π
  · rw [if_pos h]
    exact (associated_gcd_left_iff.mpr (h : π ∣ π′)).symm
  · rw [if_neg h]
    exact associated_one_iff_isUnit.mpr (hirr.isUnit_gcd_iff.mpr (h : ¬ π ∣ π′))

open Classical in
/-- General gcd formula over arbitrary irreducibles: for `p ≠ 0` with every multiplicity a unit
(char `0`), `gcd(p, Dp) ~ (∏_π π^{m_π−1})·∏_{π special} π`. -/
theorem associated_gcd_deriv_special_part {p : K[X]} (hp : p ≠ 0)
    (hunit : ∀ π ∈ primeFactors p, IsUnit (((normalizedFactors p).count π : ℕ) : K[X])) :
    Associated (gcd p p′)
      ((∏ π ∈ primeFactors p, π ^ ((normalizedFactors p).count π - 1))
        * ∏ π ∈ (primeFactors p).filter (fun π => @IsSpecial _ _ ⟨(Differential.deriv : _)⟩ π), π) :=
  (associated_gcd_deriv_prod_primeFactors hp hunit).trans
    (Associated.mul_left _ associated_prod_gcd_deriv_primeFactors)

end GeneralGcdFormula

section GeneralGcdFormulaCharZero
variable {K : Type*} [Field K] [CharZero K]

open UniqueFactorizationMonoid

open Classical in
/-- In characteristic `0`, a positive prime-factor multiplicity is a unit in `K[X]`. -/
theorem isUnit_natCast_count_primeFactors {p : K[X]} {π : K[X]}
    (hπ : π ∈ primeFactors p) :
    IsUnit (((normalizedFactors p).count π : ℕ) : K[X]) := by
  have hcount : 0 < (normalizedFactors p).count π := Multiset.count_pos.mpr (mem_primeFactors.mp hπ)
  rw [← map_natCast (C : K →+* K[X])]
  exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))

/-- In characteristic `0`, no irreducible polynomial is special under `d/dt`: `π ∤ dπ/dt`. -/
theorem not_isSpecial_derivative_of_irreducible {π : K[X]} (hπ : Irreducible π) :
    ¬ π ∣ derivative π := by
  intro hdvd
  exact hπ.not_isUnit (hπ.separable.isUnit_of_dvd' dvd_rfl hdvd)

end GeneralGcdFormulaCharZero

end DeepWiki.SymbolicIntegration
