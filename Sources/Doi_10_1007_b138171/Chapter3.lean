import DeepWiki.SymbolicIntegration.DifferentialFields
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 3: Differential Fields
Each numbered item of the book's Chapter 3 is one declaration named by its book number: an
`abbrev` aliasing the library declaration for definitions, a `theorem` (the book-faithful
statement, discharged by the `DeepWiki.SymbolicIntegration` library) for theorems/lemmas. The
book numbering lives here in the catalog, never in the library; the citation (section, page)
is in each docstring, the source's DOI in `Sources.Doi_10_1007_b138171.Source`. -/

open scoped Differential
open Polynomial DeepWiki.SymbolicIntegration

namespace DeepWiki.Si

/-! ## §3.1 Derivations -/

/-- **Definition 3.1.1** (§3.1, p.75), a *derivation* on a ring (resp. field) `R`: a map
`D : R → R` with `D(a+b) = Da + Db` and `D(ab) = a·Db + b·Da`. The pair `(R, D)` is a
*differential ring* (resp. field). The library uses Mathlib's `Differential` typeclass, which
bundles a `Derivation ℤ R R` (`x′ = D x`); `ℤ`-linearity is exactly additivity. -/
abbrev def_3_1_1 := @Differential

/-- **Definition 3.1.1** (§3.1, p.75), the *constant subring* `Const_D R = {a | Da = 0}`. -/
abbrev def_3_1_1_constants := @constants

/-- **Theorem 3.1.1(i)** (§3.1, p.76): `D(ca) = c·Da` for a constant `c` — `D` is
`Const_D R`-linear. -/
theorem thm_3_1_1_i {R : Type*} [CommRing R] [Differential R] {c : R} (a : R) (hc : c′ = 0) :
    (c * a)′ = c * a′ :=
  deriv_const_mul a hc

/-- **Theorem 3.1.1(ii)** (§3.1, p.76): the quotient rule `D(a/b) = (b·Da − a·Db)/b²` when `R`
is a field. -/
theorem thm_3_1_1_ii {F : Type*} [Field F] [Differential F] (a b : F) (_hb : b ≠ 0) :
    (a / b)′ = (b * a′ - a * b′) / b ^ 2 :=
  deriv_div a b

/-- **Theorem 3.1.1(iii)** (§3.1, p.76): `Const_D R` is a differential subring (subfield) of
`R` — in particular it is closed under `D` (trivially, since `Da = 0` on it). -/
theorem thm_3_1_1_iii {R : Type*} [CommRing R] [Differential R] :
    IsDifferentialIdeal (R := R) ⊥ ∧ ∀ a ∈ constants R, a′ ∈ constants R := by
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · simp only [Ideal.mem_bot] at ha ⊢; simp [ha]
  · simp only [mem_constants] at ha ⊢; simp [ha]

/-- **Theorem 3.1.1(iv)** (§3.1, p.76): the power rule `D(aⁿ) = n·aⁿ⁻¹·Da` (natural exponent). -/
theorem thm_3_1_1_iv {R : Type*} [CommRing R] [Differential R] (a : R) (n : ℕ) :
    (a ^ n)′ = (n : R) * a ^ (n - 1) * a′ :=
  deriv_pow a n

/-- **Theorem 3.1.1(iv)** (§3.1, p.76), field case: the power rule for any integer exponent. -/
theorem thm_3_1_1_iv_zpow {F : Type*} [Field F] [Differential F] (a : F) (n : ℤ) :
    (a ^ n)′ = (n : F) * a ^ (n - 1) * a′ :=
  deriv_zpow a n

/-- **Theorem 3.1.1(v)** (§3.1, p.76), the logarithmic-derivative identity
`D(u₁^{e₁} ⋯ uₙ^{eₙ}) / (u₁^{e₁} ⋯ uₙ^{eₙ}) = e₁·Du₁/u₁ + ⋯ + eₙ·Duₙ/uₙ` (Exercise 3.1). -/
theorem thm_3_1_1_v {F : Type*} [Field F] [Differential F] {ι : Type*} (s : Finset ι)
    (u : ι → F) (e : ι → ℤ) (h : ∀ i ∈ s, u i ≠ 0) :
    Differential.logDeriv (∏ i ∈ s, u i ^ e i)
      = ∑ i ∈ s, (e i : F) * Differential.logDeriv (u i) :=
  logDeriv_prod_zpow s u e h

/-- **Theorem 3.1.1(vi)** (§3.1, p.77), univariate case: the chain rule
`D(P(u)) = P'(u)·Du` for a polynomial `P` with constant coefficients. -/
theorem thm_3_1_1_vi {R : Type*} [CommRing R] [Differential R] (p : R[X]) (u : R)
    (hp : ∀ i, (p.coeff i)′ = 0) :
    (p.eval u)′ = p.derivative.eval u * u′ :=
  deriv_eval_of_const_coeffs p u hp

/-- **Lemma 3.1.1** (§3.1, p.77): the set `Ω(R)` of all derivations on `R` is a left
`R`-module; a linear combination `c·D₁ + D₂` acts pointwise as `a ↦ c·D₁a + D₂a`. -/
theorem lem_3_1_1 {R : Type*} [CommRing R] (c : R) (D₁ D₂ : Derivation ℤ R R) (a : R) :
    (c • D₁ + D₂) a = c * D₁ a + D₂ a :=
  smul_add_derivation_apply c D₁ D₂ a

/-- **Definition 3.1.2** (§3.1, p.78), a *differential ideal* of `(R, D)`: an ideal `I` with
`D I ⊆ I`. -/
abbrev def_3_1_2 := @IsDifferentialIdeal

end DeepWiki.Si
