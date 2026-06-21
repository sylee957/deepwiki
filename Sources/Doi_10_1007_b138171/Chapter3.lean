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

/-- **Theorem 3.2.1** (§3.2, p.79), uniqueness: a derivation on the quotient field of an integral
domain is determined by its restriction to the domain (so the extension, if it exists, is
unique). -/
theorem thm_3_2_1_unique {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {Δ₁ Δ₂ : Derivation ℤ K K}
    (h : ∀ a : R, Δ₁ (algebraMap R K a) = Δ₂ (algebraMap R K a)) : Δ₁ = Δ₂ :=
  derivation_ext_fractionRing h

/-- **Theorem 3.2.2** (§3.2, p.81), polynomial-ring case (existence + uniqueness): there is a
*unique* derivation on `R[X]` extending `D` on the constants and sending `t = X` to a prescribed
`w`. (Existence is Mathlib's `Differential.implicitDeriv w`; uniqueness is
`derivation_polynomial_ext`. The full `F(t)` field version additionally needs the §3.2.1
fraction-field existence.) -/
theorem thm_3_2_2_poly {R : Type*} [CommRing R] [Differential R] (w : R[X]) :
    ∃! Δ : Derivation ℤ R[X] R[X], (∀ c : R, Δ (C c) = C (c′)) ∧ Δ X = w := by
  refine ⟨Differential.implicitDeriv w, ⟨fun c => Differential.implicitDeriv_C w c,
    Differential.implicitDeriv_X w⟩, ?_⟩
  rintro Δ ⟨hC, hX⟩
  exact derivation_polynomial_ext
    (fun c => (hC c).trans (Differential.implicitDeriv_C w c).symm)
    (hX.trans (Differential.implicitDeriv_X w).symm)

-- **Deferred — `DeepWiki.SymbolicIntegration` library work (derivation extensions):**
--   • **Theorem 3.2.1** (§3.2, p.79), *existence*: a derivation on an integral domain `R` extends
--     to its quotient field (`Δ(a/b) = (b·Da − a·Db)/b²`). [Construct a `Derivation` on
--     `FractionRing R` — not in Mathlib; uniqueness is `thm_3_2_1_unique`.]
--   • **Theorem 3.2.2** (§3.2, p.81), full `F(t)` form (the polynomial-ring case is `thm_3_2_2_poly`;
--     the field `F(t)` version additionally needs the §3.2.1 fraction-field existence).

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

/-- **Lemma 3.3.5** (§3.3, p.88), converse, case `n = 2`: a vanishing Wronskian of `y₁, y₂` forces
linear dependence over the constants (`z = y₂/y₁` has `Dz = W/y₁² = 0`, so `z` is constant). -/
theorem lem_3_3_5_converse_two {F : Type*} [Field F] [Differential F] (y₁ y₂ : F)
    (h : wronskian ![y₁, y₂] = 0) :
    ∃ c₁ c₂ : F, c₁′ = 0 ∧ c₂′ = 0 ∧ (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ * y₁ + c₂ * y₂ = 0 :=
  wronskian_two_linearDependent y₁ y₂ h

/-- **Lemma 3.3.5** (§3.3, p.88), converse, field-coefficient version (all `n`): a vanishing
Wronskian forces linear dependence of `y₁,…,yₙ` over `F` (with field — not yet constant —
coefficients). The constant-coefficient upgrade is the deferred induction. -/
theorem lem_3_3_5_converse_field {F : Type*} [Field F] [Differential F] {n : ℕ} [NeZero n]
    (y : Fin n → F) (h : wronskian y = 0) : ∃ c : Fin n → F, c ≠ 0 ∧ ∑ j, c j * y j = 0 :=
  wronskian_eq_zero_imp_linearDependent y h

-- **Deferred — `DeepWiki.SymbolicIntegration` library work:**
--   • Theorem 3.2.4 (§3.2, p.85): a field automorphism of a separable algebraic extension commutes
--     with `D`; trace/norm relations `Tr(Da/a) = D(Tr a)`, etc.
--   • Lemma 3.3.2 / Corollary 3.3.1 (§3.3): new algebraic constants are exactly the elements
--     algebraic over the initial constant field (needs minimal polynomials + `κ_D`).
--   • Corollary 3.3.2, Lemmas 3.3.3, 3.3.4, 3.3.6 (constant-field behaviour under extensions).
--   • **Lemma 3.3.5 converse, general `n`** (`W = 0 ⟹ linearly dependent over constants`) — the
--     induction on `n` (normalize a kernel vector, differentiate, recurse on the `(n−1)`-submatrix).

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

/-- **Definition 3.4.2** (§3.4, p.92), gcd forms: `p` is special iff `gcd(p, Dp) = p`, and a
normal `p` has `gcd(p, Dp) = 1` (up to the unit ambiguity of `gcd`). -/
theorem def_3_4_2_gcd {R : Type*} [CommRing R] [GCDMonoid R] [Differential R] {p : R} :
    (IsSpecial p ↔ Associated (gcd p p′) p) ∧ (IsNormal p → IsUnit (gcd p p′)) :=
  ⟨isSpecial_iff_associated_gcd, IsNormal.isUnit_gcd⟩

/-- **Lemma 3.4.3** (§3.4, p.92): a special polynomial generates a differential ideal `(p)`. -/
theorem lem_3_4_3 {R : Type*} [CommRing R] [Differential R] {p : R} (hp : IsSpecial p) :
    IsDifferentialIdeal (Ideal.span {p}) :=
  hp.isDifferentialIdeal

/-- **Theorem 3.4.1(ii)** (§3.4, p.93): the special polynomials form a multiplicative monoid
(closed under products, with unit `1`). -/
theorem thm_3_4_1_ii {R : Type*} [CommRing R] [Differential R] {p q : R}
    (hp : IsSpecial p) (hq : IsSpecial q) : IsSpecial (p * q) :=
  hp.mul hq

/-- **Theorem 3.4.1(i)** (§3.4, p.93): the product of two *coprime normal* polynomials is
normal. (The general finite product over pairwise-coprime normals follows by induction.) -/
theorem thm_3_4_1_i {R : Type*} [CommRing R] [Differential R] {p q : R}
    (hp : IsNormal p) (hq : IsNormal q) (hpq : IsCoprime p q) : IsNormal (p * q) :=
  hp.mul hq hpq

/-- **Theorem 3.4.1(i)** (§3.4, p.93), finite form: a finite product of pairwise-coprime normal
polynomials is normal. -/
theorem thm_3_4_1_i_prod {R : Type*} [CommRing R] [Differential R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → R) (hf : ∀ i ∈ s, IsNormal (f i))
    (hco : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (f i) (f j)) : IsNormal (∏ i ∈ s, f i) :=
  IsNormal.prod s f hf hco

/-- **Theorem 3.4.1(i)** (§3.4, p.93), second half: any factor of a normal polynomial is
normal. -/
theorem thm_3_4_1_i_factor {R : Type*} [CommRing R] [Differential R] {p q : R}
    (hp : IsNormal p) (hq : q ∣ p) : IsNormal q :=
  IsNormal.of_dvd hp hq

/-- **Theorem 3.4.1** (§3.4, p.93), consequence: every normal polynomial is squarefree. -/
theorem thm_3_4_1_normal_squarefree {R : Type*} [CommRing R] [Differential R] {p : R}
    (hp : IsNormal p) : Squarefree p :=
  IsNormal.squarefree hp

/-- **Theorem 3.4.1(ii)** (§3.4, p.93), finite form: a finite product of special polynomials is
special (`S` is closed under finite products). -/
theorem thm_3_4_1_ii_prod {R : Type*} [CommRing R] [Differential R] {ι : Type*} (s : Finset ι)
    (f : ι → R) (hf : ∀ i ∈ s, IsSpecial (f i)) : IsSpecial (∏ i ∈ s, f i) :=
  IsSpecial.prod s f hf

/-- **Theorem 3.4.1(iii)** (§3.4, p.93), coprime case: a coprime factor of a special polynomial
is special — if `p·q` is special and `p ⊥ q` then `p` is special. -/
theorem thm_3_4_1_iii_coprime {R : Type*} [CommRing R] [Differential R] {p q : R}
    (h : IsSpecial (p * q)) (hco : IsCoprime p q) : IsSpecial p :=
  IsSpecial.of_mul_coprime h hco

/-- **Theorem 3.4.1(iii)** (§3.4, p.93), key step: a *prime* factor of a special polynomial is
special (over a char-`0` UFD-dioid). The general-factor case follows by factoring into primes. -/
theorem thm_3_4_1_iii_prime {R : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    [WfDvdMonoid R] [Differential R] {p π : R} (hπ : Prime π) (hdvd : π ∣ p) (hp0 : p ≠ 0)
    (hp : IsSpecial p) (he : IsUnit ((multiplicity π p : R))) : IsSpecial π :=
  isSpecial_of_prime_dvd hπ hdvd hp0 hp he

/-- **Theorem 3.4.1(iii)** (§3.4, p.93), full general-factor form: any factor of a special
polynomial is special (over a char-`0` UFD-dioid, the multiplicity of each prime factor being a
unit). -/
theorem thm_3_4_1_iii {R : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    [UniqueFactorizationMonoid R] [Differential R] {p q : R} (hp0 : p ≠ 0) (hp : IsSpecial p)
    (hmult : ∀ π, Prime π → π ∣ p → IsUnit ((multiplicity π p : R))) (hdvd : q ∣ p) :
    IsSpecial q :=
  isSpecial_of_dvd hp0 hp hmult hdvd

/-- **Theorem 3.4.1** (§3.4, p.93): `p` is *both* normal and special iff it is a unit (so the
ideal `(p) = (1)`) — the normal-and-special polynomials are exactly the units of `k`. -/
theorem thm_3_4_1_normal_special_iff_isUnit {R : Type*} [CommRing R] [Differential R] {p : R} :
    (IsNormal p ∧ IsSpecial p) ↔ IsUnit p :=
  isNormal_and_isSpecial_iff_isUnit

/-- **Theorem 3.4.1** (§3.4, p.93), corollary: normality and specialness are *associate
invariants* — multiplying by a unit `u` (a nonzero constant, in `k[t]`) changes neither, which is
what lets §3.5 normalize a polynomial by its leading coefficient. -/
theorem thm_3_4_1_unit_mul {R : Type*} [CommRing R] [Differential R] {u : R} (hu : IsUnit u)
    (p : R) : (IsNormal (u * p) ↔ IsNormal p) ∧ (IsSpecial (u * p) ↔ IsSpecial p) :=
  ⟨IsNormal.unit_mul_iff hu p, IsSpecial.unit_mul_iff hu p⟩

/-- **Lemma 3.4.2(i)** (§3.4, p.91): the degree bound for a monomial derivation `D = κ_D + v·d/dX`
on `k[X]` (`Dt = v`, `D`-degree `δ(t) = deg v`): `deg(D p) ≤ deg p + max(0, δ(t) − 1)`. -/
theorem lem_3_4_2 {R : Type*} [CommRing R] [Differential R] (v p : R[X]) :
    (Differential.implicitDeriv v p).natDegree ≤ p.natDegree + max 0 (v.natDegree - 1) :=
  natDegree_implicitDeriv_le v p

/-- **Lemma 3.4.2(i)** (§3.4, p.91), nonlinear equality: over a characteristic-`0` field, the
degree bound is an *equality* once `δ(t) = deg v ≥ 2` (and `deg p ≥ 1`):
`deg(D p) = deg p + δ(t) − 1`. -/
theorem lem_3_4_2_eq {F : Type*} [Field F] [CharZero F] [Differential F] (v p : F[X])
    (hv : 2 ≤ v.natDegree) (hp : 1 ≤ p.natDegree) :
    (Differential.implicitDeriv v p).natDegree = p.natDegree + (v.natDegree - 1) :=
  natDegree_implicitDeriv_eq v p hv hp

/-- **Theorem 3.4.2** (§3.4, p.93), single linear factor: the linear factor `X − a` is normal
w.r.t. the monomial derivation `D` (`Dt = v`, `Hₜ = v`) iff `Dα ≠ Hₜ(α)` at its root — `v(a) ≠ a′`.
(The full squarefree statement quantifies this over all roots.) -/
theorem thm_3_4_2_linear {K : Type*} [Field K] [Differential K] (v : K[X]) (a : K) :
    IsCoprime (X - C a) (Differential.implicitDeriv v (X - C a)) ↔ v.eval a ≠ a′ :=
  isCoprime_X_sub_C_implicitDeriv_iff v a

/-- **Theorem 3.4.3** (§3.4, p.93), single linear factor: `X − a` is special w.r.t. the monomial
derivation `D` (`Dt = v`, `Hₜ = v`) iff `Dα = Hₜ(α)` at its root — `v(a) = a′`. -/
theorem thm_3_4_3_linear {K : Type*} [Field K] [Differential K] (v : K[X]) (a : K) :
    (X - C a) ∣ Differential.implicitDeriv v (X - C a) ↔ v.eval a = a′ :=
  dvd_X_sub_C_implicitDeriv_iff v a

/-- **Lemma 3.4.4** (§3.4, p.94), two-factor base case: for coprime `a, b`,
`gcd(a·b, D(a·b)) ~ gcd(a, Da)·gcd(b, Db)`. (The general `∏pᵢ^{eᵢ}` form follows by induction on
the number of factors plus the `pᵢ^{eᵢ}` power computation.) -/
theorem lem_3_4_4_base {R : Type*} [CommRing R] [NormalizedGCDMonoid R] [Differential R]
    {a b : R} (hab : IsUnit (gcd a b)) :
    Associated (gcd (a * b) ((a * b)′)) (gcd a a′ * gcd b b′) :=
  associated_gcd_deriv_mul hab

/-- **Lemma 3.4.4** (§3.4, p.94), single-power computation: for `n ≥ 1` with `n` a unit
(characteristic `0`), `gcd(pⁿ, D(pⁿ)) ~ pⁿ⁻¹·gcd(p, Dp)`. -/
theorem lem_3_4_4_pow {R : Type*} [CommRing R] [NormalizedGCDMonoid R] [Differential R] {p : R}
    {n : ℕ} (hn : 1 ≤ n) (he : IsUnit (n : R)) :
    Associated (gcd (p ^ n) ((p ^ n)′)) (p ^ (n - 1) * gcd p p′) :=
  associated_gcd_deriv_pow hn he

/-- **Lemma 3.4.4** (§3.4, p.94), general pairwise-coprime product form: for pairwise-coprime
factors `f i`, `gcd(∏ f i, D ∏ f i) ~ ∏ gcd(f i, D f i)`. (Specializing `f i = pᵢ^{eᵢ}` and
applying `lem_3_4_4_pow` to each factor gives the book's `∏ pᵢ^{eᵢ-1} gcd(pᵢ, Dpᵢ)`.) -/
theorem lem_3_4_4 {R : Type*} [CommRing R] [NormalizedGCDMonoid R] [Differential R] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → R)
    (hco : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsUnit (gcd (f i) (f j))) :
    Associated (gcd (∏ i ∈ s, f i) ((∏ i ∈ s, f i)′)) (∏ i ∈ s, gcd (f i) (f i)′) :=
  associated_gcd_deriv_prod s f hco

-- **Deferred — `DeepWiki.SymbolicIntegration` library work (monomial machinery):**
--   • Theorem 3.4.1(iii) — DONE in full: `thm_3_4_1_iii_prime` (prime-factor key step) and
--     `thm_3_4_1_iii` (general factor of a special polynomial is special, via prime factorization).
--   • Theorems 3.4.2 / 3.4.3 (squarefree `p` normal ⟺ `Dα ≠ H_t(α)`; `p` special ⟺ `Dα = H_t(α)`
--     for all roots `α`): the single-linear-factor cases are DONE (`thm_3_4_2_linear`,
--     `thm_3_4_3_linear`); the full statements need `p` split as `c·∏(X−aᵢ)` (squarefree ⇒ distinct
--     roots) + Lemma 3.4.4 (`pairwise_coprime_X_sub_C`) over the roots — `dvd_iff_isRoot`/
--     `isCoprime_X_sub_C_iff` are the per-factor tools. Corollaries 3.4.1 / 3.4.2, Lemmas 3.4.5 /
--     3.4.6 (new constants ⇔ special polynomials), Theorem 3.4.4 (special of the first kind).

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
