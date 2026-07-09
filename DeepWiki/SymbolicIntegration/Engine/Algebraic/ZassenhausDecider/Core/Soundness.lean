import DeepWiki.SymbolicIntegration.Engine.Algebraic.ZassenhausDecider.Core.Pipeline

/-! # Soundness API for the Zassenhaus decider

Soundness and completeness-facing recombination lemmas for the complete Zassenhaus
`ℚ`-irreducibility decider.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ## Soundness and completeness

The reducibility direction (`recombine` non-empty ⟹ `¬ Irreducible`) is proven outright via the
keystone `dividesExactly_dvd`. The irreducibility direction (`true ⟹ Irreducible`) is proven modulo
one isolated surfacing hypothesis `FactorSurfaces` (Hensel-lift uniqueness over `ZMod (p^k)` plus the
Mignotte bound), which is demonstrably realizable. -/

/-- A polynomial of positive `natDegree` is not a unit. -/
theorem not_isUnit_of_natDegree_pos {p : ℤ[X]} (hp : 0 < p.natDegree) : ¬ IsUnit p := by
  intro hu
  have hd : p.degree = 0 := degree_eq_zero_of_isUnit hu
  have : p.natDegree = 0 := natDegree_eq_of_degree_eq_some hd
  omega

/-- If `recombine f n facs` is non-empty then monic-degree-`N` `toPolyZ f` is reducible
(`¬ Irreducible`): the found candidate and its cofactor are both non-unit proper factors. -/
theorem recombine_imp_not_irreducible {f : List ℤ} {n : ℤ} {facs : List (List ℤ)} {N : ℕ}
    (hmon : IsMonicOfDegree (toPolyZ f) N)
    (hne : recombine f n facs ≠ []) : ¬ Irreducible (toPolyZ f) := by
  -- extract a candidate from the non-empty filterMap
  rw [recombine] at hne
  simp only [ne_eq, List.filterMap_eq_nil_iff, not_forall] at hne
  obtain ⟨sub, hsub_mem, hsub⟩ := hne
  -- decode the `if`: the guard held, so `dividesExactly` is true and the degree is proper
  set cand := recombineCandidate n sub with hcanddef
  set dc := lengthTrim cand with hdcdef
  -- the filterMap predicate produced `some _`, so the `if` condition is true
  by_cases hcond : 2 ≤ dc ∧ dc - 1 < lengthTrim f - 1 ∧ dividesExactly f cand (dc - 1)
  · obtain ⟨hdc2, hdclt, hdivex⟩ := hcond
    -- f = cand * q over ℤ
    have hfac : toPolyZ f = toPoly cand * toPoly (divmodByMonic f cand (dc - 1)).1 :=
      dividesExactly_dvd hdivex
    set q := (divmodByMonic f cand (dc - 1)).1 with hqdef
    -- natDegree (toPoly cand) = dc - 1  (cand reads as nonzero: lengthTrim ≥ 2 > 0)
    have hcandne : lengthTrim cand ≠ 0 := by omega
    have hcanddeg : (toPoly cand).natDegree = dc - 1 := natDegree_toPoly_eq hcandne
    -- N = natDegree f
    have hN : (toPolyZ f).natDegree = N := hmon.natDegree_eq
    have hcandne0 : toPoly cand ≠ 0 := by
      rw [Ne, toPoly_eq_zero_iff_lengthTrim]; omega
    have hfne0 : toPolyZ f ≠ 0 := hmon.monic.ne_zero
    have hqpoly_ne0 : toPoly q ≠ 0 := by
      intro h; rw [hfac, h, mul_zero] at hfne0; exact hfne0 rfl
    -- degree sum: natDegree f = natDegree cand + natDegree q
    have hdegsum : (toPoly cand).natDegree + (toPoly q).natDegree = N := by
      have := Polynomial.natDegree_mul hcandne0 hqpoly_ne0
      rw [← hfac, hN] at this; omega
    -- natDegree cand ≥ 1
    have hcandpos : 0 < (toPoly cand).natDegree := by rw [hcanddeg]; omega
    -- natDegree f = lengthTrim f - 1, so dc - 1 < N gives natDegree q ≥ 1
    have hfdeg : (toPolyZ f).natDegree = lengthTrim f - 1 :=
      natDegree_toPoly_eq (by rw [Ne, ← toPoly_eq_zero_iff_lengthTrim]; exact hfne0)
    have hNbig : dc - 1 < N := by rw [hN] at hfdeg; omega
    have hqpos : 0 < (toPoly q).natDegree := by omega
    -- both factors are non-units; conclude not irreducible
    intro hirr
    rcases hirr.isUnit_or_isUnit hfac with hu | hu
    · exact not_isUnit_of_natDegree_pos hcandpos hu
    · exact not_isUnit_of_natDegree_pos hqpos hu
  · -- the predicate must have been true for `some _` to be produced
    exfalso
    apply hsub
    rw [if_neg hcond]

/-- Contrapositive: an `Irreducible` monic-degree-`N` `toPolyZ f` forces `recombine f n facs = []`. -/
theorem irreducible_imp_recombine_nil {f : List ℤ} {n : ℤ} {facs : List (List ℤ)} {N : ℕ}
    (hmon : IsMonicOfDegree (toPolyZ f) N) (hirr : Irreducible (toPolyZ f)) :
    recombine f n facs = [] := by
  by_contra hne
  exact recombine_imp_not_irreducible hmon hne hirr

/-! ## Recombination completeness — the irreducibility direction (`true ⟹ Irreducible`)

The converse of `recombine_imp_not_irreducible`. The search plumbing (`recombine_ne_nil_of_witness`)
is proven outright; the deep content — Hensel-lift uniqueness over `ZMod (p^k)` plus the Mignotte
bound — is isolated into the surfacing hypothesis `FactorSurfaces`. -/

/-- A witness sublist whose symmetric-reduced subset-product is a proper-degree exact `ℤ`-divisor of
`f` forces `recombine f n facs ≠ []`. -/
theorem recombine_ne_nil_of_witness {f : List ℤ} {n : ℤ} {facs : List (List ℤ)}
    {sub : List (List ℤ)} (hmem : sub ∈ facs.sublists)
    (hdc2 : 2 ≤ lengthTrim (recombineCandidate n sub))
    (hdclt : lengthTrim (recombineCandidate n sub) - 1 < lengthTrim f - 1)
    (hdiv : dividesExactly f (recombineCandidate n sub)
      (lengthTrim (recombineCandidate n sub) - 1) = true) :
    recombine f n facs ≠ [] := by
  rw [recombine]
  simp only [ne_eq, List.filterMap_eq_nil_iff, not_forall]
  refine ⟨sub, hmem, ?_⟩
  intro hcontra
  rw [if_pos ⟨hdc2, hdclt, hdiv⟩] at hcontra
  exact absurd hcontra (by simp)

/-- Surfacing predicate: a reducible monic-degree-`N` `toPolyZ f` has some sublist of `facs` whose
symmetric-reduced subset-product mod `n` is a proper-degree exact `ℤ`-divisor. -/
def FactorSurfaces (f : List ℤ) (n : ℤ) (facs : List (List ℤ)) (N : ℕ) : Prop :=
  IsMonicOfDegree (toPolyZ f) N → ¬ Irreducible (toPolyZ f) →
    ∃ sub ∈ facs.sublists,
      2 ≤ lengthTrim (recombineCandidate n sub) ∧
      lengthTrim (recombineCandidate n sub) - 1 < lengthTrim f - 1 ∧
      dividesExactly f (recombineCandidate n sub)
        (lengthTrim (recombineCandidate n sub) - 1) = true

/-- Given `FactorSurfaces`, a reducible monic-degree-`N` `toPolyZ f` forces `recombine f n facs ≠ []`. -/
theorem recombine_complete {f : List ℤ} {n : ℤ} {facs : List (List ℤ)} {N : ℕ}
    (hsurf : FactorSurfaces f n facs N) (hmon : IsMonicOfDegree (toPolyZ f) N)
    (hred : ¬ Irreducible (toPolyZ f)) :
    recombine f n facs ≠ [] := by
  obtain ⟨sub, hmem, hdc2, hdclt, hdiv⟩ := hsurf hmon hred
  exact recombine_ne_nil_of_witness hmem hdc2 hdclt hdiv

/-- Given `FactorSurfaces`, `recombine f n facs = []` forces `toPolyZ f` irreducible. -/
theorem irreducible_of_recombine_nil {f : List ℤ} {n : ℤ} {facs : List (List ℤ)} {N : ℕ}
    (hsurf : FactorSurfaces f n facs N) (hmon : IsMonicOfDegree (toPolyZ f) N)
    (hnil : recombine f n facs = []) :
    Irreducible (toPolyZ f) := by
  by_contra hred
  exact recombine_complete hsurf hmon hred hnil

/-- A `true` verdict comes from one of two branches: a single mod-`p` factor, or empty recombination. -/
theorem irreducibleZassenhaus_eq_true_cases {p : ℕ} [Fact p.Prime] {f : List ℤ} {n : ℕ}
    (h : irreducibleZassenhaus p f n = true) :
    (factorModP p (reduceCoeffs p f)).length = 1 ∨
    recombine f ((p : ℤ) ^ (2 ^ henselRounds p f))
      (henselLiftMany f ((factorModP p (reduceCoeffs p f)).length + 1)
        (factorModP p (reduceCoeffs p f))) = [] := by
  rw [irreducibleZassenhaus] at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact Or.inl (by rename_i hlen; exact hlen)
    · exact Or.inr (by rw [List.isEmpty_iff] at h; exact h)

/-- `irreducibleZassenhaus p f n = true → Irreducible (toPolyZ f)`, given the surfacing hypothesis
`hsurf` for the recombination branch and `hmodp` for the single-mod-`p`-factor branch. -/
theorem irreducibleZassenhaus_sound {p : ℕ} [Fact p.Prime] {f : List ℤ} {n : ℕ}
    (hmon : IsMonicOfDegree (toPolyZ f) n)
    (hsurf : FactorSurfaces f ((p : ℤ) ^ (2 ^ henselRounds p f))
      (henselLiftMany f ((factorModP p (reduceCoeffs p f)).length + 1)
        (factorModP p (reduceCoeffs p f))) n)
    (hmodp : (factorModP p (reduceCoeffs p f)).length = 1 → Irreducible (toPolyZ f))
    (h : irreducibleZassenhaus p f n = true) :
    Irreducible (toPolyZ f) := by
  rcases irreducibleZassenhaus_eq_true_cases h with hlen | hnil
  · exact hmodp hlen
  · exact irreducible_of_recombine_nil hsurf hmon hnil

end DeepWiki.SymbolicIntegration
