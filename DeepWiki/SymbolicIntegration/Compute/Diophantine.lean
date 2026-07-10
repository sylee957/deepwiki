import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.Core.Polynomial.Diophantine

/-! # Computable Diophantine solver correctness
Connects the concrete `cdiophantine` solver on `DensePoly ℚ` with the abstract reduced Bezout solver
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

/-! ### `cdiophantine` realizes `diophantineSolveReduced` -/

/-- The first computable cofactor is the normalized remainder of the scaled Bezout cofactor. -/
theorem cdiophantine_fst_eq (fuel : ℕ) (p q rhs : DensePoly ℚ) :
    (cdiophantine fuel p q rhs).1
      = cnorm (cmod fuel
          (cscale (clead (cgcdExt fuel p q).1)⁻¹ (cmul rhs (cgcdExt fuel p q).2.1)) q) := by
  rcases hgst : cgcdExt fuel p q with ⟨g, s, t⟩
  simp only [cdiophantine, hgst, cmod]

/-- The first computable cofactor has degree below `q` when the remainder computation has enough fuel. -/
theorem cdiophantine_fst_degree_lt (fuel : ℕ) (p q rhs : DensePoly ℚ) (hq : cnorm q ≠ [])
    (hfuel : (cnorm (cscale (clead (cgcdExt fuel p q).1)⁻¹
        (cmul rhs (cgcdExt fuel p q).2.1))).length ≤ fuel) :
    (toPoly (cdiophantine fuel p q rhs).1).degree < (toPoly q).degree := by
  set S := cscale (clead (cgcdExt fuel p q).1)⁻¹ (cmul rhs (cgcdExt fuel p q).2.1) with hS
  rw [cdiophantine_fst_eq, ← hS]
  have hlen : (cnorm (cmod fuel S q)).length < (cnorm q).length :=
    cmod_length_lt fuel S q hq hfuel
  rw [toPoly_eq_dense, DensePoly.toPolyG_cnormG]
  have hqne0 : toPoly q ≠ 0 := fun h => hq ((cnorm_eq_nil_iff q).mpr h)
  rcases eq_or_ne (cnorm (cmod fuel S q)) [] with h0 | h0
  · have hz : toPoly (cmod fuel S q) = 0 := by
      rw [toPoly_eq_dense, ← DensePoly.toPolyG_cnormG, h0, DensePoly.toPolyG_nil]
    simp only [toPoly_eq_dense] at hqne0 hz ⊢
    rw [hz, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (fun h => hqne0 (Polynomial.degree_eq_bot.mp h))
  · have e1 : (cnorm (cmod fuel S q)).length = (toPoly (cmod fuel S q)).natDegree + 1 :=
      length_cnorm_of_ne _ h0
    have e2 : (cnorm q).length = (toPoly q).natDegree + 1 := length_cnorm_of_ne q hq
    have hndlt : (toPoly (cmod fuel S q)).natDegree < (toPoly q).natDegree := by omega
    have hne1 : toPoly (cmod fuel S q) ≠ 0 := fun h => h0 ((cnorm_eq_nil_iff _).mpr h)
    simp only [toPoly_eq_dense] at hqne0 hndlt hne1 ⊢
    rw [Polynomial.degree_eq_natDegree hne1, Polynomial.degree_eq_natDegree hqne0, Nat.cast_lt]
    exact hndlt

/-- Input certificates for comparing `cdiophantine` with `diophantineSolveReduced`. -/
structure IsCDiophantineInput (fuel : ℕ) (p q rhs : DensePoly ℚ) : Prop where
  /-- The computable denominator is nonzero. -/
  q_ne : cnorm q ≠ []
  /-- The abstract inputs are coprime. -/
  coprime : IsCoprime (toPoly p) (toPoly q)
  /-- The computable gcd reads as its leading constant. -/
  gcd_const : toPoly (cgcdExt fuel p q).1 = Polynomial.C (clead (cgcdExt fuel p q).1)
  /-- The leading coefficient of the computed gcd is nonzero. -/
  gcd_lead_ne : clead (cgcdExt fuel p q).1 ≠ 0
  /-- The modulus fuel bound is large enough for the scaled right-hand side. -/
  fuel_bound : (cnorm (cscale (clead (cgcdExt fuel p q).1)⁻¹
    (cmul rhs (cgcdExt fuel p q).2.1))).length ≤ fuel

open Classical in
/-- First-cofactor agreement: `cdiophantine` realizes `diophantineSolveReduced` through `toPoly`. -/
theorem toPoly_cdiophantine_fst_eq (fuel : ℕ) (p q rhs : DensePoly ℚ)
    (hinput : IsCDiophantineInput fuel p q rhs) :
    toPoly (cdiophantine fuel p q rhs).1
      = (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).1 := by
  obtain ⟨hq, hcop, hg, hgc, hfuel⟩ := hinput
  have hq0 : toPoly q ≠ 0 := fun h => hq ((cnorm_eq_nil_iff q).mpr h)
  have hc_eq := toPoly_cdiophantine fuel p q rhs hq hg hgc
  have hc_deg := cdiophantine_fst_degree_lt fuel p q rhs hq hfuel
  have ha_eq := diophantineSolveReduced_spec hcop (toPoly rhs)
  have ha_deg := diophantineSolveReduced_fst_degree_lt (a := toPoly p) hq0 (toPoly rhs)
  refine reduced_bezout_fst_unique (C₁ := toPoly (cdiophantine fuel p q rhs).2)
    (C₂ := (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).2)
    (rhs := toPoly rhs) hcop ?_ ?_ hc_deg ha_deg
  · linear_combination hc_eq
  · linear_combination ha_eq

open Classical in
/-- Second-cofactor agreement: the second `cdiophantine` cofactor matches the abstract one. -/
theorem toPoly_cdiophantine_snd_eq (fuel : ℕ) (p q rhs : DensePoly ℚ)
    (hinput : IsCDiophantineInput fuel p q rhs) :
    toPoly (cdiophantine fuel p q rhs).2
      = (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).2 := by
  have hq := hinput.q_ne
  have hcop := hinput.coprime
  have hg := hinput.gcd_const
  have hgc := hinput.gcd_lead_ne
  have hq0 : toPoly q ≠ 0 := fun h => hq ((cnorm_eq_nil_iff q).mpr h)
  have hfst := toPoly_cdiophantine_fst_eq fuel p q rhs hinput
  have hc_eq := toPoly_cdiophantine fuel p q rhs hq hg hgc
  have ha_eq := diophantineSolveReduced_spec hcop (toPoly rhs)
  refine reduced_bezout_snd_unique (p := toPoly p)
    (B := (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).1)
    (rhs := toPoly rhs) hq0 ?_ ?_
  · rw [← hfst]; linear_combination hc_eq
  · linear_combination ha_eq

open Classical in
/-- Full cofactor agreement: `cdiophantine` realizes `diophantineSolveReduced` as a pair. -/
theorem toPoly_cdiophantine_eq (fuel : ℕ) (p q rhs : DensePoly ℚ)
    (hinput : IsCDiophantineInput fuel p q rhs) :
    (toPoly (cdiophantine fuel p q rhs).1, toPoly (cdiophantine fuel p q rhs).2)
      = diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs) :=
  Prod.ext (toPoly_cdiophantine_fst_eq fuel p q rhs hinput)
    (toPoly_cdiophantine_snd_eq fuel p q rhs hinput)

example (fuel : ℕ) (p q rhs : DensePoly ℚ)
    (hq : cnorm q ≠ []) (hcop : IsCoprime (toPoly p) (toPoly q))
    (hg : toPoly (cgcdExt fuel p q).1 = Polynomial.C (clead (cgcdExt fuel p q).1))
    (hgc : clead (cgcdExt fuel p q).1 ≠ 0)
    (hfuel : (cnorm (cscale (clead (cgcdExt fuel p q).1)⁻¹
        (cmul rhs (cgcdExt fuel p q).2.1))).length ≤ fuel) :
    toPoly (cdiophantine fuel p q rhs).1
      = (diophantineSolveReduced (toPoly p) (toPoly q) (toPoly rhs)).1 :=
  toPoly_cdiophantine_fst_eq fuel p q rhs ⟨hq, hcop, hg, hgc, hfuel⟩

end DeepWiki.SymbolicIntegration.Compute
