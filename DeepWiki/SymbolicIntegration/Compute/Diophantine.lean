import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.SymbolicIntegration.Compute.Hermite
import DeepWiki.SymbolicIntegration.Core.Polynomial.Diophantine

/-! # Computable Diophantine solver correctness
Connects the representation-selected `CPoly.diophantineReduced` solver on `DensePoly ℚ` with the abstract reduced Bezout solver
`diophantineSolveReduced` over `ℚ[X]`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### Uniqueness of the reduced Bezout cofactor -/

/-- Reduced Bezout cofactor uniqueness: proper cofactors solving the same coprime equation agree. -/
theorem reduced_bezout_fst_unique {p q B₁ C₁ B₂ C₂ rhs : ℚ[X]} (hpq : IsCoprime p q)
    (h₁ : B₁ * p + C₁ * q = rhs) (h₂ : B₂ * p + C₂ * q = rhs)
    (hd₁ : B₁.degree < q.degree) (hd₂ : B₂.degree < q.degree) :
    B₁ = B₂ := by
  have hcross : (B₁ - B₂) * p = (C₂ - C₁) * q := by linear_combination h₁ - h₂
  have hdvd : q ∣ (B₁ - B₂) * p := ⟨C₂ - C₁, by rw [hcross]; ring⟩
  have hqB : q ∣ (B₁ - B₂) := (hpq.symm).dvd_of_dvd_mul_right hdvd
  have hsub : B₁ - B₂ = 0 := by
    by_contra hne
    have hle : q.degree ≤ (B₁ - B₂).degree := Polynomial.degree_le_of_dvd hqB hne
    have hlt : (B₁ - B₂).degree < q.degree :=
      lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hd₁ hd₂)
    exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)
  exact sub_eq_zero.mp hsub

/-- Reduced Bezout partner uniqueness: with first cofactor fixed and `q ≠ 0`, the second cofactor agrees. -/
theorem reduced_bezout_snd_unique {p q B C₁ C₂ rhs : ℚ[X]} (hq : q ≠ 0)
    (h₁ : B * p + C₁ * q = rhs) (h₂ : B * p + C₂ * q = rhs) :
    C₁ = C₂ := by
  have : C₁ * q = C₂ * q := by linear_combination h₁ - h₂
  exact mul_right_cancel₀ hq this

/-! ### `CPoly.diophantineReduced` realizes `diophantineSolveReduced` -/

/-- Input certificates for comparing `CPoly.diophantineReduced` with `diophantineSolveReduced`. -/
structure IsDiophantineReducedInput (p q rhs : DensePoly ℚ) : Prop where
  /-- The computable denominator is nonzero. -/
  q_ne : cnorm q ≠ []
  /-- The abstract inputs are coprime. -/
  coprime : IsCoprime (toPoly p) (toPoly q)
  /-- The computed gcd has degree zero. -/
  gcd_degree_zero : (toPoly (CPolyEuclidean.gcdExt p q).1).natDegree = 0
  /-- The computed gcd is nonzero. -/
  gcd_ne : toPoly (CPolyEuclidean.gcdExt p q).1 ≠ 0

open Classical in
/-- First-cofactor agreement: `CPoly.diophantineReduced` realizes `diophantineSolveReduced` through `toPoly`. -/
theorem toPoly_diophantineReduced_fst_eq (p q rhs : DensePoly ℚ)
    (hinput : IsDiophantineReducedInput p q rhs) :
    toPoly (CPoly.diophantineReduced p q rhs).1
      = (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).1 := by
  obtain ⟨hq, hcop, hgdeg, hgne⟩ := hinput
  have hq0 : toPoly q ≠ 0 := fun h => hq ((DensePoly.cnormG_eq_nil_iff q).mpr h)
  have hc_eq : toPoly (CPoly.diophantineReduced p q rhs).1 * toPoly p
      + toPoly (CPoly.diophantineReduced p q rhs).2 * toPoly q = toPoly rhs := by
    exact
      DensePoly.toPolyG_diophantineReduced p q rhs hq hgdeg hgne
  have hc_deg : (toPoly (CPoly.diophantineReduced p q rhs).1).degree < (toPoly q).degree := by
    exact DensePoly.diophantineReduced_fst_degree_lt p q rhs hq
  have ha_eq := diophantineSolveReduced_spec hcop (toPoly rhs)
  have ha_deg := diophantineSolveReduced_fst_degree_lt (a := toPoly p) hq0 (toPoly rhs)
  refine reduced_bezout_fst_unique (C₁ := toPoly (CPoly.diophantineReduced p q rhs).2)
    (C₂ := (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).2)
    (rhs := toPoly rhs) hcop ?_ ?_ hc_deg ha_deg
  · linear_combination hc_eq
  · linear_combination ha_eq

open Classical in
/-- Second-cofactor agreement: the second `CPoly.diophantineReduced` cofactor matches the abstract one. -/
theorem toPoly_diophantineReduced_snd_eq (p q rhs : DensePoly ℚ)
    (hinput : IsDiophantineReducedInput p q rhs) :
    toPoly (CPoly.diophantineReduced p q rhs).2
      = (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).2 := by
  have hq := hinput.q_ne
  have hcop := hinput.coprime
  have hgdeg := hinput.gcd_degree_zero
  have hgne := hinput.gcd_ne
  have hq0 : toPoly q ≠ 0 := fun h => hq ((DensePoly.cnormG_eq_nil_iff q).mpr h)
  have hfst := toPoly_diophantineReduced_fst_eq p q rhs hinput
  have hc_eq : toPoly (CPoly.diophantineReduced p q rhs).1 * toPoly p
      + toPoly (CPoly.diophantineReduced p q rhs).2 * toPoly q = toPoly rhs := by
    exact
      DensePoly.toPolyG_diophantineReduced p q rhs hq hgdeg hgne
  have ha_eq := diophantineSolveReduced_spec hcop (toPoly rhs)
  refine reduced_bezout_snd_unique (p := toPoly p)
    (B := (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).1)
    (rhs := toPoly rhs) hq0 ?_ ?_
  · rw [← hfst]; linear_combination hc_eq
  · linear_combination ha_eq

open Classical in
/-- Full cofactor agreement: `CPoly.diophantineReduced` realizes `diophantineSolveReduced` as a pair. -/
theorem toPoly_diophantineReduced_eq (p q rhs : DensePoly ℚ)
    (hinput : IsDiophantineReducedInput p q rhs) :
    (toPoly (CPoly.diophantineReduced p q rhs).1, toPoly (CPoly.diophantineReduced p q rhs).2)
      = diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs) :=
  Prod.ext (toPoly_diophantineReduced_fst_eq p q rhs hinput)
    (toPoly_diophantineReduced_snd_eq p q rhs hinput)

end DeepWiki.SymbolicIntegration.Compute
