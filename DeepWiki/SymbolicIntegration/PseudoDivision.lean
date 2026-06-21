import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-! # Pseudo-division of polynomials over an integral domain
Bronstein §1.2: over an integral domain `D` the Euclidean division of `A` by `B ≠ 0` need not be
exact (`lc(B)` may not divide `lc(A)`), but after scaling `A` by a power of `b = lc(B)` it is.
The *pseudo-division* produces a pseudo-quotient `Q` and pseudo-remainder `R` with
`bⁿ · A = B·Q + R` and `deg R < deg B`. Mathlib has Euclidean division by a *monic* divisor
(`divByMonic`/`modByMonic`) but not pseudo-division over a domain, so we prove its existence here
(the spec the algorithm `PolyPseudoDivide` realizes). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Pseudo-division existence** (§1.2): for `B ≠ 0` there are a power `n`, a pseudo-quotient `Q`
and pseudo-remainder `Rem` with `lc(B)ⁿ · A = B·Q + Rem` and `deg Rem < deg B`. The minimal such
`n` is `max(0, deg A − deg B + 1)`; this `∃ n` form is the mathematical content of the
`PolyPseudoDivide` algorithm. -/
theorem pseudoDivision_exists (A B : R[X]) (hB : B ≠ 0) :
    ∃ (n : ℕ) (Q Rem : R[X]),
      C B.leadingCoeff ^ n * A = B * Q + Rem ∧ Rem.degree < B.degree := by
  -- strong induction on `A.natDegree`
  suffices H : ∀ m : ℕ, ∀ A : R[X], A.natDegree = m →
      ∃ (n : ℕ) (Q Rem : R[X]), C B.leadingCoeff ^ n * A = B * Q + Rem ∧ Rem.degree < B.degree by
    exact H A.natDegree A rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro A hA
    by_cases hdeg : A.degree < B.degree
    · -- remainder is `A` itself, `n = 0`
      exact ⟨0, 0, A, by simp, hdeg⟩
    · -- one elimination step: cancel the leading term
      rw [not_lt] at hdeg  -- `B.degree ≤ A.degree`
      have hBbot : B.degree ≠ ⊥ := mt degree_eq_bot.mp hB
      have hAne : A ≠ 0 := by
        rintro rfl
        rw [degree_zero] at hdeg
        exact hBbot (le_bot_iff.mp hdeg)
      have hbne : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
      have hane : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
      set b := B.leadingCoeff with hb
      set a := A.leadingCoeff with ha
      set δ := A.natDegree - B.natDegree with hδ
      have hBA : B.natDegree ≤ A.natDegree := natDegree_le_natDegree hdeg
      set p := C b * A with hp
      set q := C a * (B * X ^ δ) with hq
      set A₁ := p - q with hA₁
      -- the two leading terms agree
      have hp_deg : p.degree = A.degree := by
        rw [hp, degree_mul, degree_C hbne, zero_add]
      have hq_deg : q.degree = A.degree := by
        rw [hq, degree_mul, degree_C hane, zero_add, degree_mul, degree_X_pow,
          degree_eq_natDegree hB, degree_eq_natDegree hAne]
        rw [← Nat.cast_add, Nat.add_sub_cancel' hBA]
      have hp_lc : p.leadingCoeff = b * a := by rw [hp, leadingCoeff_mul, leadingCoeff_C]
      have hq_lc : q.leadingCoeff = b * a := by
        rw [hq, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_mul, leadingCoeff_X_pow, mul_one,
          mul_comm]
      have hp_ne : p ≠ 0 := mul_ne_zero (by simpa using hbne) hAne
      have hsub_deg : A₁.degree < A.degree := by
        rw [hA₁, ← hp_deg]
        exact degree_sub_lt (hp_deg.trans hq_deg.symm) hp_ne (by rw [hp_lc, hq_lc])
      -- key rewrite: `C b * A = A₁ + q`
      have hkey : C b * A = A₁ + q := by rw [hA₁]; ring
      by_cases hA₁0 : A₁ = 0
      · -- exact after one scaling: `b¹ · A = B·(a·X^δ) + 0`
        refine ⟨1, C a * X ^ δ, 0, ?_, ?_⟩
        · rw [pow_one, hkey, hA₁0, zero_add, hq]; ring
        · rw [degree_zero]; exact bot_lt_iff_ne_bot.mpr hBbot
      · -- recurse on `A₁`, whose degree dropped
        have hlt : A₁.natDegree < A.natDegree :=
          natDegree_lt_natDegree hA₁0 hsub_deg
        obtain ⟨n₁, Q₁, R₁, hEq, hdeg₁⟩ := IH A₁.natDegree (hA ▸ hlt) A₁ rfl
        refine ⟨n₁ + 1, Q₁ + C b ^ n₁ * C a * X ^ δ, R₁, ?_, hdeg₁⟩
        calc C b ^ (n₁ + 1) * A
            = C b ^ n₁ * (C b * A) := by ring
          _ = C b ^ n₁ * (A₁ + q) := by rw [hkey]
          _ = C b ^ n₁ * A₁ + C b ^ n₁ * q := by ring
          _ = (B * Q₁ + R₁) + C b ^ n₁ * q := by rw [hEq]
          _ = B * (Q₁ + C b ^ n₁ * C a * X ^ δ) + R₁ := by rw [hq]; ring

/-- **Similarity** (§1.5): `A` is *similar* to `B` over `D[x]` when `a · A = b · B` for some
nonzero scalars `a, b ∈ D` (the relation whose classes the PRS gcd-tower preserves). -/
def IsSimilar (A B : R[X]) : Prop := ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ C a * A = C b * B

/-- `IsSimilar` is reflexive (witnesses `a = b = 1`). -/
@[refl] theorem IsSimilar.refl (A : R[X]) : IsSimilar A A :=
  ⟨1, 1, one_ne_zero, one_ne_zero, rfl⟩

omit [IsDomain R] in
/-- `IsSimilar` is symmetric (swap the witnesses). -/
theorem IsSimilar.symm {A B : R[X]} (h : IsSimilar A B) : IsSimilar B A :=
  let ⟨a, b, ha, hb, hab⟩ := h; ⟨b, a, hb, ha, hab.symm⟩

/-- `IsSimilar` is transitive — here `IsDomain R` is essential, so the product witnesses
`c·a` and `b·d` stay nonzero. -/
theorem IsSimilar.trans {A B C₀ : R[X]} (h₁ : IsSimilar A B) (h₂ : IsSimilar B C₀) :
    IsSimilar A C₀ := by
  obtain ⟨a, b, ha, hb, hab⟩ := h₁
  obtain ⟨c, d, hc, hd, hcd⟩ := h₂
  refine ⟨c * a, b * d, mul_ne_zero hc ha, mul_ne_zero hb hd, ?_⟩
  calc C (c * a) * A = C c * (C a * A) := by rw [C_mul]; ring
    _ = C c * (C b * B) := by rw [hab]
    _ = C b * (C c * B) := by ring
    _ = C b * (C d * C₀) := by rw [hcd]
    _ = C (b * d) * C₀ := by rw [C_mul]; ring

/-- **Similarity is an equivalence relation** (§1.5, Exercise 1.11). -/
theorem isSimilar_equivalence : Equivalence (IsSimilar (R := R)) :=
  ⟨IsSimilar.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

end DeepWiki.SymbolicIntegration
