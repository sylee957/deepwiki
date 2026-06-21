import DeepWiki.SymbolicIntegration.DifferentialFields
import DeepWiki.SymbolicIntegration.Constants
import DeepWiki.SymbolicIntegration.MonomialExtensions
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

/-! ## §3.2 Differential Extensions -/

/-- **Definition 3.2.1** (§3.2, p.79), a *differential extension* `(S, Δ)` of `(R, D)`: an algebra
whose derivation commutes with the structure map (`Δ ∘ algebraMap = algebraMap ∘ D`). Mathlib's
`DifferentialAlgebra`. -/
abbrev def_3_2_1 := @DifferentialAlgebra

/-- **Definition 3.2.2** (§3.2, p.80), the *coefficient lifting* `κ_D : R[X] → R[X]`,
`κ_D(Σ aᵢXⁱ) = Σ (Daᵢ)Xⁱ`; **Lemma 3.2.1** (§3.2, p.80): `κ_D` is a derivation on `R[X]`.
Mathlib's `Derivation.mapCoeffs` (valued in `PolynomialModule R R ≅ R[X]`) *is* this derivation,
so being a derivation is automatic from its type. -/
noncomputable abbrev def_3_2_2 := @Derivation.mapCoeffs

/-- **Lemma 3.2.2** (§3.2, p.81): for a derivation `D` on `R`, `α ∈ R`, `P ∈ R[X]`,
`D(P(α)) = κ_D(P)(α) + (Dα)·(dP/dX)(α)` — the chain rule for evaluating a polynomial (the general
form of `thm_3_1_1_vi`, with the `κ_D(P)(α)` term for non-constant coefficients). Mathlib's
`Derivation.apply_eval_eq`; the `R ⊆ S` extension version is `apply_aeval_eq`. -/
theorem lem_3_2_2 {R : Type*} [CommRing R] [Differential R] (α : R) (P : R[X]) :
    (P.eval α)′ = PolynomialModule.eval α ((Differential.deriv : Derivation ℤ R R).mapCoeffs P)
      + P.derivative.eval α * α′ := by
  simpa [smul_eq_mul] using (Differential.deriv : Derivation ℤ R R).apply_eval_eq α P

-- **Deferred — `DeepWiki.SymbolicIntegration` library work (derivation extensions):**
--   • **Theorem 3.2.1** (§3.2, p.79): a derivation on an integral domain `R` extends *uniquely*
--     to its quotient field (`Δ(a/b) = (b·Da − a·Db)/b²`). [Construct a `Derivation` on
--     `FractionRing R` — not in Mathlib.]
--   • **Theorem 3.2.2** (§3.2, p.81): for `t` transcendental over a differential field `F` and any
--     `w ∈ F(t)`, there is a unique derivation on `F(t)` extending `F`'s with `Δt = w`.

/-! ## §3.3 Constants and Extensions -/

/-- **Lemma 3.3.1** (§3.3, p.85): constants stay constant in a differential extension —
`Const_D F ⊆ Const_Δ E` (if `c′ = 0` then `(algebraMap F E c)′ = 0`). -/
theorem lem_3_3_1 {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E] {c : F} (hc : c′ = 0) : (algebraMap F E c)′ = 0 :=
  deriv_algebraMap_eq_zero hc

/-- **Definition 3.3.1** (§3.3, p.88): the *Wronskian* `W(y₁,…,yₙ) = det(Dⁱ⁻¹ yⱼ)`. -/
noncomputable abbrev def_3_3_1 := @wronskian

/-- **Lemma 3.3.5** (§3.3, p.88), easy direction: if `y₁,…,yₙ` are linearly dependent over the
constants then their Wronskian vanishes, `W(y₁,…,yₙ) = 0`. -/
theorem lem_3_3_5 {F : Type*} [Field F] [Differential F] {n : ℕ} (y c : Fin n → F)
    (hc : ∀ j, (c j)′ = 0) (hne : c ≠ 0) (hdep : ∑ j, c j * y j = 0) : wronskian y = 0 :=
  wronskian_eq_zero_of_linearDependent y c hc hne hdep

-- **Deferred — `DeepWiki.SymbolicIntegration` library work:**
--   • Theorem 3.2.4 (§3.2, p.85): a field automorphism of a separable algebraic extension commutes
--     with `D`; trace/norm relations `Tr(Da/a) = D(Tr a)`, etc.
--   • Lemma 3.3.2 / Corollary 3.3.1 (§3.3): new algebraic constants are exactly the elements
--     algebraic over the initial constant field (needs minimal polynomials + `κ_D`).
--   • Corollary 3.3.2, Lemmas 3.3.3, 3.3.4, 3.3.6 (constant-field behaviour under extensions).
--   • **Lemma 3.3.5 converse** (`W = 0 ⟹ linearly dependent over constants`) — the induction on `n`.

/-! ## §3.4 Monomial Extensions -/

/-- **Definition 3.4.1 / Lemma 3.4.1** (§3.4, p.90–91), the derivation of a *monomial* extension:
`k[t]` is closed under `D` with `Dt = v ∈ k[t]`. Mathlib's `Differential.implicitDeriv v` is this
derivation on `k[X]` (`implicitDeriv_X : implicitDeriv v X = v`, `implicitDeriv_C`); `v = H_t`, the
`D`-degree is `δ(t) = deg v`, the `D`-leading coefficient `λ(t) = lc v`. -/
noncomputable abbrev def_3_4_1 := @Differential.implicitDeriv

/-- **Definition 3.4.2** (§3.4, p.92): `p` is *normal* w.r.t. `D` if `gcd(p, Dp) = 1`. -/
abbrev def_3_4_2_normal := @IsNormal

/-- **Definition 3.4.2** (§3.4, p.92): `p` is *special* w.r.t. `D` if `p ∣ Dp`. -/
abbrev def_3_4_2_special := @IsSpecial

/-- **Lemma 3.4.3** (§3.4, p.92): a special polynomial generates a differential ideal `(p)`. -/
theorem lem_3_4_3 {R : Type*} [CommRing R] [Differential R] {p : R} (hp : IsSpecial p) :
    IsDifferentialIdeal (Ideal.span {p}) :=
  hp.isDifferentialIdeal

/-- **Theorem 3.4.1(ii)** (§3.4, p.93): the special polynomials form a multiplicative monoid
(closed under products, with unit `1`). -/
theorem thm_3_4_1_ii {R : Type*} [CommRing R] [Differential R] {p q : R}
    (hp : IsSpecial p) (hq : IsSpecial q) : IsSpecial (p * q) :=
  hp.mul hq

-- **Deferred — `DeepWiki.SymbolicIntegration` library work (monomial machinery):**
--   • Lemma 3.4.2 (degree bound `deg(Dp) ≤ deg p + max(0, δ(t)−1)`, with equality in the
--     nonlinear case), Lemma 3.4.4 (the `gcd(∏pᵢ^{eᵢ}, D·)` product formula), Theorem 3.4.1(i),(iii)
--     (products of coprime normals are normal; factors of special are special).
--   • Theorems 3.4.2 / 3.4.3 (squarefree `p` normal ⟺ `Dα ≠ H_t(α)`; `p` special ⟺ `Dα = H_t(α)`
--     for all roots `α`), Corollaries 3.4.1 / 3.4.2, Lemmas 3.4.5 / 3.4.6 (new constants ⇔ special
--     polynomials), Theorem 3.4.4 (special of the first kind under algebraic extension).

/-! ## §3.5 The Canonical Representation -/

/-- **Definition 3.5.1** (§3.5, p.99): a *splitting factorization* `p = pₛ·pₙ` of `p` into its
special part `pₛ` and normal part `pₙ`. -/
abbrev def_3_5_1 := @IsSplittingFactorization

/-- A special polynomial is its own special part: splitting factorization `(p, 1)`. -/
theorem isSpecial_splittingFactorization {R : Type*} [CommRing R] [Differential R] {p : R}
    (hp : IsSpecial p) : IsSplittingFactorization p p 1 :=
  hp.splittingFactorization

/-- A normal polynomial is its own normal part: splitting factorization `(1, p)`. -/
theorem isNormal_splittingFactorization {R : Type*} [CommRing R] [Differential R] {p : R}
    (hp : IsNormal p) : IsSplittingFactorization p 1 p :=
  hp.splittingFactorization

-- **Deferred — §3.5 library work:** Theorem 3.5.1 (`pₛ = gcd(p,Dp)/gcd(p,dp/dt)`, the splitting
-- factorization via gcd's; rests on Lemma 3.4.4 + Thms 3.4.2/3.4.3), the `SplitFactor` /
-- `SplitSquarefreeFactor` / `CanonicalRepresentation` algorithms, Def 3.5.2 (simple/reduced
-- elements of `k⟨t⟩`, needs `RatFunc` numerator/denominator), and Theorem 3.5.2 (the `κ_D`
-- splitting separates constant from nonconstant roots).

end DeepWiki.Si
