import DeepWiki.ComputableAlgebra.PolyReprDivisionDegree
import DeepWiki.ComputableAlgebra.PolyReprSparse
import DeepWiki.ComputableAlgebra.PolyEngine
import Mathlib.RingTheory.Coprime.Basic

/-! # Abstract executable polynomial Euclidean algorithms

`CPolyEuclidean` selects division and extended-gcd implementations for a polynomial representation.
`LawfulCPolyEuclidean` records their denotation-level Euclidean and Bézout laws; plain gcd selection is
the separate `CPolyGcd` capability. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

/-- Representation-selected executable Euclidean algorithms for computable polynomials. -/
class CPolyEuclidean (P : Type u → Type u) [CPoly P] where
  /-- Polynomial quotient and remainder. -/
  divmod : {α : Type u} → [CField α] → P α → P α → P α × P α
  /-- Extended gcd `(g, s, t)` with Bézout coefficients. -/
  gcdExt : {α : Type u} → [CField α] → P α → P α → P α × P α × P α

namespace CPolyEuclidean

variable {P : Type u → Type u} [CPoly P] [CPolyEuclidean P]

/-- Polynomial quotient selected by `CPolyEuclidean`. -/
def div {α : Type u} [CField α] (p q : P α) : P α := (CPolyEuclidean.divmod p q).1

/-- Polynomial remainder selected by `CPolyEuclidean`. -/
def mod {α : Type u} [CField α] (p q : P α) : P α := (CPolyEuclidean.divmod p q).2

/-- Test represented polynomial divisibility by checking whether the selected remainder is zero. -/
def dvd [CPolyEngine P] {α : Type u} [CField α] (q p : P α) : Bool :=
  CPolyEngine.cisZero (mod p q)

end CPolyEuclidean

/-- Denotation laws for representation-selected polynomial Euclidean algorithms. -/
class LawfulCPolyEuclidean (P : Type u → Type u) [CPoly P] [CPolyEuclidean P] : Prop where
  /-- Quotient and remainder satisfy the Euclidean identity for a nonzero divisor. -/
  divmod_spec : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α] (p q : P α),
    CPoly.toPoly q ≠ 0 →
      CPoly.toPoly p = CPoly.toPoly (CPolyEuclidean.div p q) * CPoly.toPoly q +
        CPoly.toPoly (CPolyEuclidean.mod p q)
  /-- The selected remainder has degree strictly below that of a nonzero divisor. -/
  mod_degree_lt : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α] (p q : P α),
    CPoly.toPoly q ≠ 0 →
      (CPoly.toPoly (CPolyEuclidean.mod p q)).degree < (CPoly.toPoly q).degree
  /-- Exact division reconstructs the dividend when the selected divisor divides it. -/
  div_exact : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α] (p q : P α),
    CPoly.toPoly q ≠ 0 → CPoly.toPoly q ∣ CPoly.toPoly p →
      CPoly.toPoly p = CPoly.toPoly q * CPoly.toPoly (CPolyEuclidean.div p q)
  /-- The selected extended gcd satisfies its Bézout identity. -/
  gcdExt_bezout : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α] (p q : P α),
    CPoly.toPoly (CPolyEuclidean.gcdExt p q).2.1 * CPoly.toPoly p +
        CPoly.toPoly (CPolyEuclidean.gcdExt p q).2.2 * CPoly.toPoly q =
      CPoly.toPoly (CPolyEuclidean.gcdExt p q).1
  /-- The selected extended-gcd component divides both inputs. -/
  gcdExt_dvd : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α] (p q : P α),
    CPoly.toPoly (CPolyEuclidean.gcdExt p q).1 ∣ CPoly.toPoly p ∧
      CPoly.toPoly (CPolyEuclidean.gcdExt p q).1 ∣ CPoly.toPoly q

namespace CPolyEuclidean

variable {P : Type u → Type u} [CPoly P] [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P]
  {α : Type u} [CField α] [CFieldSpec.{u,v} α]

/-- Coprime inputs make the selected extended-gcd component a unit. -/
theorem gcdExt_isUnit_of_isCoprime (p q : P α)
    (hcop : IsCoprime (CPoly.toPoly p) (CPoly.toPoly q)) :
    IsUnit (CPoly.toPoly (gcdExt p q).1) := by
  obtain ⟨hp, hq⟩ := LawfulCPolyEuclidean.gcdExt_dvd (P := P) p q
  exact hcop.isUnit_of_dvd' hp hq

/-- A zero selected remainder turns the Euclidean identity into exact quotient multiplication. -/
theorem toPoly_eq_div_mul_of_mod_eq_zero (p q : P α) (hq : CPoly.toPoly q ≠ 0)
    (hrem : CPoly.toPoly (mod p q) = 0) :
    CPoly.toPoly p = CPoly.toPoly (div p q) * CPoly.toPoly q := by
  simpa only [hrem, add_zero] using LawfulCPolyEuclidean.divmod_spec (P := P) p q hq

/-- A zero selected remainder certifies divisibility of the represented dividend. -/
theorem toPoly_dvd_of_mod_eq_zero (p q : P α) (hq : CPoly.toPoly q ≠ 0)
    (hrem : CPoly.toPoly (mod p q) = 0) : CPoly.toPoly q ∣ CPoly.toPoly p :=
  ⟨CPoly.toPoly (div p q), by
    rw [toPoly_eq_div_mul_of_mod_eq_zero p q hq hrem, mul_comm]⟩

/-- Divisibility by a nonzero represented polynomial forces the selected remainder to denote zero. -/
theorem toPoly_mod_eq_zero_of_dvd (p q : P α) (hq : CPoly.toPoly q ≠ 0)
    (hdvd : CPoly.toPoly q ∣ CPoly.toPoly p) : CPoly.toPoly (mod p q) = 0 := by
  have hspec := LawfulCPolyEuclidean.divmod_spec (P := P) p q hq
  have hexact := LawfulCPolyEuclidean.div_exact (P := P) p q hq hdvd
  calc
    CPoly.toPoly (mod p q) = CPoly.toPoly p - CPoly.toPoly (div p q) * CPoly.toPoly q := by
      rw [hspec]
      ring
    _ = 0 := by rw [hexact]; ring

/-- Exact selected division denotes the mathematical polynomial quotient. -/
theorem toPoly_div_eq_div (p q : P α) (hq : CPoly.toPoly q ≠ 0)
    (hdvd : CPoly.toPoly q ∣ CPoly.toPoly p) :
    CPoly.toPoly (div p q) = CPoly.toPoly p / CPoly.toPoly q := by
  symm
  rw [LawfulCPolyEuclidean.div_exact (P := P) p q hq hdvd]
  exact mul_div_cancel_left₀ _ hq

/-- Exact selected division respects equal dividend and divisor denotations. -/
theorem toPoly_div_congr (p₁ q₁ p₂ q₂ : P α)
    (hp : CPoly.toPoly p₁ = CPoly.toPoly p₂)
    (hq : CPoly.toPoly q₁ = CPoly.toPoly q₂)
    (hq₁ : CPoly.toPoly q₁ ≠ 0) (hdvd₁ : CPoly.toPoly q₁ ∣ CPoly.toPoly p₁) :
    CPoly.toPoly (div p₁ q₁) = CPoly.toPoly (div p₂ q₂) := by
  have hdvd₂ : CPoly.toPoly q₂ ∣ CPoly.toPoly p₂ := by
    rw [← hq, ← hp]
    exact hdvd₁
  have h₁ : CPoly.toPoly (div p₁ q₁) * CPoly.toPoly q₁ = CPoly.toPoly p₁ := by
    simpa only [mul_comm] using
      (LawfulCPolyEuclidean.div_exact (P := P) p₁ q₁ hq₁ hdvd₁).symm
  have h₂ : CPoly.toPoly (div p₂ q₂) * CPoly.toPoly q₂ = CPoly.toPoly p₂ := by
    simpa only [mul_comm] using
      (LawfulCPolyEuclidean.div_exact (P := P) p₂ q₂
        (by simpa only [← hq] using hq₁) hdvd₂).symm
  apply mul_right_cancel₀ hq₁
  rw [h₁, hp, ← h₂, hq]

section Dvd

variable [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]

omit [LawfulCPolyEuclidean.{u,v} P] in
/-- The selected divisibility test is true exactly when the selected remainder denotes zero. -/
theorem dvd_iff (q p : P α) :
    dvd q p = true ↔ CPoly.toPoly (mod p q) = 0 := by
  rw [dvd, LawfulCPolyEngine.cisZero_iff]

/-- A true selected divisibility test certifies polynomial divisibility for a nonzero divisor. -/
theorem toPoly_dvd_of_dvd_eq_true (q p : P α) (hq : CPoly.toPoly q ≠ 0)
    (h : dvd q p = true) : CPoly.toPoly q ∣ CPoly.toPoly p :=
  toPoly_dvd_of_mod_eq_zero p q hq ((dvd_iff q p).mp h)

/-- A false selected divisibility test refutes polynomial divisibility for a nonzero divisor. -/
theorem not_toPoly_dvd_of_dvd_eq_false (q p : P α) (hq : CPoly.toPoly q ≠ 0)
    (h : dvd q p = false) : ¬ CPoly.toPoly q ∣ CPoly.toPoly p := by
  intro hdvd
  have htrue : dvd q p = true :=
    (dvd_iff q p).mpr (toPoly_mod_eq_zero_of_dvd p q hq hdvd)
  rw [htrue] at h
  exact Bool.noConfusion h

end Dvd

/-- Dividing a constant polynomial by a nonzero polynomial produces a constant quotient. -/
theorem div_natDegree_eq_zero_of_natDegree_eq_zero (p q : P α)
    (hp : (CPoly.toPoly p).natDegree = 0) (hq : CPoly.toPoly q ≠ 0) :
    (CPoly.toPoly (div p q)).natDegree = 0 := by
  have hdiv := LawfulCPolyEuclidean.divmod_spec (P := P) p q hq
  have hrem := LawfulCPolyEuclidean.mod_degree_lt (P := P) p q hq
  by_cases hquot : CPoly.toPoly (div p q) = 0
  · simp [hquot]
  have hmuldeg : (CPoly.toPoly q).degree ≤
      (CPoly.toPoly (div p q) * CPoly.toPoly q).degree := by
    rw [Polynomial.degree_mul]
    exact le_add_of_nonneg_left (Polynomial.zero_le_degree_iff.mpr hquot)
  have hpdeg : (CPoly.toPoly p).degree =
      (CPoly.toPoly (div p q) * CPoly.toPoly q).degree := by
    rw [hdiv, add_comm]
    exact Polynomial.degree_add_eq_right_of_degree_lt (lt_of_lt_of_le hrem hmuldeg)
  have hnat := Polynomial.natDegree_eq_of_degree_eq hpdeg
  rw [Polynomial.natDegree_mul hquot hq, hp] at hnat
  omega

end CPolyEuclidean

/-- Sparse polynomials use the representation-generic Euclidean algorithms. -/
instance instCPolyEuclideanSparse : CPolyEuclidean CPoly.SparsePoly where
  divmod := CPoly.cdivmod
  gcdExt := CPoly.cgcdExt

/-- The generic sparse Euclidean implementation satisfies the abstract laws. -/
instance instLawfulCPolyEuclideanSparse : LawfulCPolyEuclidean CPoly.SparsePoly where
  divmod_spec := by
    intro α _ _ p q _
    change CPoly.toPoly p = CPoly.toPoly (CPoly.cdivmod p q).1 * CPoly.toPoly q +
      CPoly.toPoly (CPoly.cdivmod p q).2
    simpa [mul_comm] using CPoly.toPoly_cdivmod p q
  mod_degree_lt := by
    intro α _ _ p q hq
    change (CPoly.toPoly (CPoly.cdivmod p q).2).degree < (CPoly.toPoly q).degree
    have hqz : ¬ CPoly.cisZero q = true := fun hz => hq ((CPoly.cisZero_iff q).mp hz)
    rcases CPoly.cdivmod_remainder_reduced p q hqz with hzero | hlt
    · rw [(CPoly.cisZero_iff _).mp hzero, Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (by simpa [Polynomial.degree_eq_bot] using hq)
    · exact Polynomial.degree_lt_degree (by
        simpa only [CPoly.cdeg_eq_natDegree] using hlt)
  div_exact := by
    intro α _ _ p q hq hdvd
    have hqz : ¬ CPoly.cisZero q = true := fun hz => hq ((CPoly.cisZero_iff q).mp hz)
    change CPoly.toPoly p = CPoly.toPoly q * CPoly.toPoly (CPoly.cdivmod p q).1
    exact CPoly.toPoly_mul_cdiv_of_dvd p q hqz hdvd
  gcdExt_bezout := CPoly.toPoly_cgcdExt
  gcdExt_dvd := CPoly.cgcdExt_dvd

end DeepWiki.SymbolicIntegration
