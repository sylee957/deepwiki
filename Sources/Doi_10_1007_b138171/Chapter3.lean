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
abbrev thm_3_1_1_i := @deriv_const_mul

/-- **Theorem 3.1.1(ii)** (§3.1, p.76): the quotient rule `D(a/b) = (b·Da − a·Db)/b²` when `R`
is a field. -/
abbrev thm_3_1_1_ii := @deriv_div

/-- **Theorem 3.1.1(iii)** (§3.1, p.76): `Const_D R` is a differential subring (subfield) of
`R` — in particular it is closed under `D` (trivially, since `Da = 0` on it). -/
abbrev thm_3_1_1_iii := @isDifferentialIdeal_bot_and_deriv_mem_constants

/-- **Theorem 3.1.1(iv)** (§3.1, p.76): the power rule `D(aⁿ) = n·aⁿ⁻¹·Da` (natural exponent). -/
abbrev thm_3_1_1_iv := @deriv_pow

/-- **Theorem 3.1.1(iv)** (§3.1, p.76), field case: the power rule for any integer exponent. -/
abbrev thm_3_1_1_iv_zpow := @deriv_zpow

/-- **Theorem 3.1.1(v)** (§3.1, p.76), the logarithmic-derivative identity
`D(u₁^{e₁} ⋯ uₙ^{eₙ}) / (u₁^{e₁} ⋯ uₙ^{eₙ}) = e₁·Du₁/u₁ + ⋯ + eₙ·Duₙ/uₙ` (Exercise 3.1). -/
abbrev thm_3_1_1_v := @logDeriv_prod_zpow

/-- **Theorem 3.1.1(vi)** (§3.1, p.77), univariate case: the chain rule
`D(P(u)) = P'(u)·Du` for a polynomial `P` with constant coefficients. -/
abbrev thm_3_1_1_vi := @deriv_eval_of_const_coeffs

/-- **Lemma 3.1.1** (§3.1, p.77): the set `Ω(R)` of all derivations on `R` is a left
`R`-module; a linear combination `c·D₁ + D₂` acts pointwise as `a ↦ c·D₁a + D₂a`. -/
abbrev lem_3_1_1 := @smul_add_derivation_apply

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
abbrev thm_3_2_1_unique := @derivation_ext_fractionRing

/-- **Theorem 3.2.2** (§3.2, p.81), polynomial-ring case (existence + uniqueness): there is a
*unique* derivation on `R[X]` extending `D` on the constants and sending `t = X` to a prescribed
`w`. (Existence is Mathlib's `Differential.implicitDeriv w`; uniqueness is
`derivation_polynomial_ext`. The full `F(t)` field version additionally needs the §3.2.1
fraction-field existence.) -/
abbrev thm_3_2_2_poly := @existsUnique_derivation_polynomial

-- **Deferred — `DeepWiki.SymbolicIntegration` library work (derivation extensions):**
--   • **Theorem 3.2.1** (§3.2, p.79), *existence*: a derivation on an integral domain `R` extends
--     to its quotient field (`Δ(a/b) = (b·Da − a·Db)/b²`). [Construct a `Derivation` on
--     `FractionRing R` — not in Mathlib; uniqueness is `thm_3_2_1_unique`.]
--   • **Theorem 3.2.2** (§3.2, p.81), full `F(t)` form (the polynomial-ring case is `thm_3_2_2_poly`;
--     the field `F(t)` version additionally needs the §3.2.1 fraction-field existence).

/-! ## §3.3 Constants and Extensions -/

/-- **Lemma 3.3.1** (§3.3, p.85): constants stay constant in a differential extension —
`Const_D F ⊆ Const_Δ E` (if `c′ = 0` then `(algebraMap F E c)′ = 0`). -/
abbrev lem_3_3_1 := @deriv_algebraMap_eq_zero

/-- **Definition 3.3.1** (§3.3, p.88): the *Wronskian* `W(y₁,…,yₙ) = det(Dⁱ⁻¹ yⱼ)`. -/
noncomputable abbrev def_3_3_1 := @wronskian

/-- **Lemma 3.3.5** (§3.3, p.88), easy direction: if `y₁,…,yₙ` are linearly dependent over the
constants then their Wronskian vanishes, `W(y₁,…,yₙ) = 0`. -/
abbrev lem_3_3_5 := @wronskian_eq_zero_of_linearDependent

/-- **Lemma 3.3.5** (§3.3, p.88), converse, case `n = 2`: a vanishing Wronskian of `y₁, y₂` forces
linear dependence over the constants (`z = y₂/y₁` has `Dz = W/y₁² = 0`, so `z` is constant). -/
abbrev lem_3_3_5_converse_two := @wronskian_two_linearDependent

/-- **Lemma 3.3.5** (§3.3, p.88), converse, field-coefficient version (all `n`): a vanishing
Wronskian forces linear dependence of `y₁,…,yₙ` over `F` (with field — not yet constant —
coefficients). The constant-coefficient upgrade is the deferred induction. -/
abbrev lem_3_3_5_converse_field := @wronskian_eq_zero_imp_linearDependent

-- **Deferred — `DeepWiki.SymbolicIntegration` library work:**
--   • Theorem 3.2.4 (§3.2, p.85): a field automorphism of a separable algebraic extension commutes
--     with `D`; trace/norm relations `Tr(Da/a) = D(Tr a)`, etc.
--   • Lemma 3.3.2 / Corollary 3.3.1 (§3.3): new algebraic constants are exactly the elements
--     algebraic over the initial constant field (needs minimal polynomials + `κ_D`).
--   • Corollary 3.3.2, Lemmas 3.3.3, 3.3.4, 3.3.6 (constant-field behaviour under extensions).
--   • **Lemma 3.3.5 converse, general `n`** (`W = 0 ⟹ linearly dependent over constants`) — the
--     induction on `n`. Infrastructure in place: `wronskian_eq_zero_dependent_iterDeriv` (foundation,
--     a kernel vector annihilating all rows), `deriv_dependent_iterDeriv` (the differentiate-row
--     recurrence), and `linearDependent_of_div_deriv_dependent` (the division-reduction inductive
--     step), plus `iterDeriv_mul` (the general Leibniz rule `Dⁿ(ab) = ∑ₖ C(n,k)·Dⁿ⁻ᵏa·Dᵏb`, the
--     algebraic engine of the column reduction). The one remaining piece is the determinant
--     reduction `W(y₁,…,yₙ) = y₁ⁿ·W((y₂/y₁)′,…)` that lets the `(n−1)` induction hypothesis apply.

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
abbrev lem_3_4_3 := @IsSpecial.isDifferentialIdeal

/-- **Theorem 3.4.1(ii)** (§3.4, p.93): the special polynomials form a multiplicative monoid
(closed under products, with unit `1`). -/
abbrev thm_3_4_1_ii := @IsSpecial.mul

/-- **Theorem 3.4.1(i)** (§3.4, p.93): the product of two *coprime normal* polynomials is
normal. (The general finite product over pairwise-coprime normals follows by induction.) -/
abbrev thm_3_4_1_i := @IsNormal.mul

/-- **Theorem 3.4.1(i)** (§3.4, p.93), finite form: a finite product of pairwise-coprime normal
polynomials is normal. -/
abbrev thm_3_4_1_i_prod := @IsNormal.prod

/-- **Theorem 3.4.1(i)** (§3.4, p.93), second half: any factor of a normal polynomial is
normal. -/
abbrev thm_3_4_1_i_factor := @IsNormal.of_dvd

/-- **Theorem 3.4.1** (§3.4, p.93), consequence: every normal polynomial is squarefree. -/
abbrev thm_3_4_1_normal_squarefree := @IsNormal.squarefree

/-- **Theorem 3.4.1(ii)** (§3.4, p.93), finite form: a finite product of special polynomials is
special (`S` is closed under finite products). -/
abbrev thm_3_4_1_ii_prod := @IsSpecial.prod

/-- **Theorem 3.4.1(iii)** (§3.4, p.93), coprime case: a coprime factor of a special polynomial
is special — if `p·q` is special and `p ⊥ q` then `p` is special. -/
abbrev thm_3_4_1_iii_coprime := @IsSpecial.of_mul_coprime

/-- **Theorem 3.4.1(iii)** (§3.4, p.93), key step: a *prime* factor of a special polynomial is
special (over a char-`0` UFD-dioid). The general-factor case follows by factoring into primes. -/
abbrev thm_3_4_1_iii_prime := @isSpecial_of_prime_dvd

/-- **Theorem 3.4.1(iii)** (§3.4, p.93), full general-factor form: any factor of a special
polynomial is special (over a char-`0` UFD-dioid, the multiplicity of each prime factor being a
unit). -/
abbrev thm_3_4_1_iii := @isSpecial_of_dvd

/-- **Theorem 3.4.1** (§3.4, p.93): `p` is *both* normal and special iff it is a unit (so the
ideal `(p) = (1)`) — the normal-and-special polynomials are exactly the units of `k`. -/
abbrev thm_3_4_1_normal_special_iff_isUnit := @isNormal_and_isSpecial_iff_isUnit

/-- **Theorem 3.4.1** (§3.4, p.93), corollary: normality and specialness are *associate
invariants* — multiplying by a unit `u` (a nonzero constant, in `k[t]`) changes neither, which is
what lets §3.5 normalize a polynomial by its leading coefficient. -/
theorem thm_3_4_1_unit_mul {R : Type*} [CommRing R] [Differential R] {u : R} (hu : IsUnit u)
    (p : R) : (IsNormal (u * p) ↔ IsNormal p) ∧ (IsSpecial (u * p) ↔ IsSpecial p) :=
  ⟨IsNormal.unit_mul_iff hu p, IsSpecial.unit_mul_iff hu p⟩

/-- **Lemma 3.4.2(i)** (§3.4, p.91): the degree bound for a monomial derivation `D = κ_D + v·d/dX`
on `k[X]` (`Dt = v`, `D`-degree `δ(t) = deg v`): `deg(D p) ≤ deg p + max(0, δ(t) − 1)`. -/
abbrev lem_3_4_2 := @natDegree_implicitDeriv_le

/-- **Lemma 3.4.2(i)** (§3.4, p.91), nonlinear equality: over a characteristic-`0` field, the
degree bound is an *equality* once `δ(t) = deg v ≥ 2` (and `deg p ≥ 1`):
`deg(D p) = deg p + δ(t) − 1`. -/
abbrev lem_3_4_2_eq := @natDegree_implicitDeriv_eq

/-- **Theorem 3.4.2** (§3.4, p.93), single linear factor: the linear factor `X − a` is normal
w.r.t. the monomial derivation `D` (`Dt = v`, `Hₜ = v`) iff `Dα ≠ Hₜ(α)` at its root — `v(a) ≠ a′`.
(The full squarefree statement quantifies this over all roots.) -/
abbrev thm_3_4_2_linear := @isCoprime_X_sub_C_implicitDeriv_iff

/-- **Theorem 3.4.2** (§3.4, p.93), full squarefree form: a squarefree polynomial, as the product
`∏_{a∈s}(X − a)` of its distinct linear factors, is normal w.r.t. the monomial derivation `D`
(`Dt = v`, `Hₜ = v`) iff `Dα ≠ Hₜ(α)` at every root — `∀ a ∈ s, v(a) ≠ a′`. -/
abbrev thm_3_4_2 := @isCoprime_prod_X_sub_C_implicitDeriv_iff

/-- **Theorem 3.4.3** (§3.4, p.93), single linear factor: `X − a` is special w.r.t. the monomial
derivation `D` (`Dt = v`, `Hₜ = v`) iff `Dα = Hₜ(α)` at its root — `v(a) = a′`. -/
abbrev thm_3_4_3_linear := @dvd_X_sub_C_implicitDeriv_iff

/-- **Theorem 3.4.3** (§3.4, p.93), linear-factor power: over characteristic `0`, `(X − a)ⁿ`
(`n ≥ 1`) is special w.r.t. `D` (`Dt = v`, `Hₜ = v`) iff `Dα = Hₜ(α)` — `v(a) = a′`; the
multiplicity `n` is irrelevant. -/
abbrev thm_3_4_3_pow := @dvd_X_sub_C_pow_implicitDeriv_iff

/-- **Theorem 3.4.3** (§3.4, p.93), full multiplicity form: `∏_{a∈s}(X − a)^{eₐ}` (each `eₐ ≥ 1`,
char `0`) is special w.r.t. the monomial derivation `D` (`Dt = v`, `Hₜ = v`) iff `Dα = Hₜ(α)` at
every root — `∀ a ∈ s, v(a) = a′`. (Generalizes `thm_3_4_3` from squarefree to arbitrary
multiplicities.) -/
abbrev thm_3_4_3_mult := @dvd_prod_X_sub_C_pow_implicitDeriv_iff

/-- **Theorem 3.4.3** (§3.4, p.93), full squarefree form: a squarefree polynomial `∏_{a∈s}(X − a)`
is special w.r.t. the monomial derivation `D` (`Dt = v`, `Hₜ = v`) iff `Dα = Hₜ(α)` at every
root — `∀ a ∈ s, v(a) = a′`. -/
abbrev thm_3_4_3 := @dvd_prod_X_sub_C_implicitDeriv_iff

/-- **Lemma 3.4.4** (§3.4, p.94), two-factor base case: for coprime `a, b`,
`gcd(a·b, D(a·b)) ~ gcd(a, Da)·gcd(b, Db)`. (The general `∏pᵢ^{eᵢ}` form follows by induction on
the number of factors plus the `pᵢ^{eᵢ}` power computation.) -/
abbrev lem_3_4_4_base := @associated_gcd_deriv_mul

/-- **Lemma 3.4.4** (§3.4, p.94), single-power computation: for `n ≥ 1` with `n` a unit
(characteristic `0`), `gcd(pⁿ, D(pⁿ)) ~ pⁿ⁻¹·gcd(p, Dp)`. -/
abbrev lem_3_4_4_pow := @associated_gcd_deriv_pow

/-- **Lemma 3.4.4** (§3.4, p.94), general pairwise-coprime product form: for pairwise-coprime
factors `f i`, `gcd(∏ f i, D ∏ f i) ~ ∏ gcd(f i, D f i)`. (Specializing `f i = pᵢ^{eᵢ}` and
applying `lem_3_4_4_pow` to each factor gives the book's `∏ pᵢ^{eᵢ-1} gcd(pᵢ, Dpᵢ)`.) -/
abbrev lem_3_4_4 := @associated_gcd_deriv_prod

-- **Deferred — `DeepWiki.SymbolicIntegration` library work (monomial machinery):**
--   Corollary 3.4.1; Corollary 3.4.2; Lemma 3.4.5; Lemma 3.4.6 (new constants ⇔ special polynomials);
--   Theorem 3.4.4 (special of the first kind under algebraic extension).

/-! ## §3.5 The Canonical Representation -/

/-- **Definition 3.5.1** (§3.5, p.99): a *splitting factorization* `p = pₛ·pₙ` of `p` into its
special part `pₛ` and normal part `pₙ`. -/
abbrev def_3_5_1 := @IsSplittingFactorization

/-- A special polynomial is its own special part: splitting factorization `(p, 1)`. -/
abbrev isSpecial_splittingFactorization := @IsSpecial.splittingFactorization

/-- A normal polynomial is its own normal part: splitting factorization `(1, p)`. -/
abbrev isNormal_splittingFactorization := @IsNormal.splittingFactorization

/-- **Theorem 3.5.1** (§3.5, p.99), squarefree case: the splitting factorization of a squarefree
polynomial `∏_{a∈s}(X − a)` — its special part collects the roots with `v(a) = a′`, its normal part
the roots with `v(a) ≠ a′`; the first is special and the second normal w.r.t. `D` (`Dt = v`). -/
abbrev thm_3_5_1_squarefree := @splittingFactorization_prod_X_sub_C

/-- **Theorem 3.5.1** (§3.5, p.99), squarefree gcd formula: the special part of a squarefree
polynomial equals `gcd(p, Dp)` — `gcd(∏_{a∈s}(X − a), D ∏) ~ ∏_{a : v(a)=a′}(X − a)`. -/
abbrev thm_3_5_1_gcd := @gcd_prod_X_sub_C_implicitDeriv

/-- **§3.5** canonical representation: the special and normal parts of the squarefree splitting are
coprime — `pₛ ⊥ pₙ`. -/
abbrev splitting_parts_coprime := @isCoprime_splitting_parts

/-- **Theorem 3.5.1** (§3.5, p.99), general special-part extraction: a polynomial `∏_{a∈s}(X−a)^{eₐ}`
factors as its special part (the special roots, with multiplicity) times the rest, the special part
being special w.r.t. `D`. (For `eₐ > 1` the complementary factor is not normal — the full canonical
representation reduces those multiplicities via rational functions.) -/
abbrev thm_3_5_1_special_part := @isSpecial_special_part

/-- **Theorem 3.5.1** (§3.5, p.99), general gcd formula: for `p = ∏_{a∈s}(X − a)^{eₐ}` (each
`eₐ ≥ 1`, char `0`), `gcd(p, Dp) ~ (∏_a (X − a)^{eₐ−1}) · ∏_{a : v(a)=a′}(X − a)` — the multiplicity
defect times the squarefree special part. -/
abbrev thm_3_5_1_gcd_mult := @gcd_prod_X_sub_C_pow_implicitDeriv

/-- **Theorem 3.5.1** (§3.5, p.99), the `d/dt` companion: `gcd(p, dp/dt) ~ ∏_a (X − a)^{eₐ−1}`
for `p = ∏_{a∈s}(X − a)^{eₐ}` (char `0`) — the pure multiplicity defect. With `thm_3_5_1_gcd_mult`,
the special part is `pₛ = gcd(p, Dp)/gcd(p, dp/dt) ~ ∏_{special}(X − a)`. -/
abbrev thm_3_5_1_gcd_dt := @gcd_prod_X_sub_C_pow_derivative

/-- **Theorem 3.5.1** (§3.5, p.99), special-part formula `pₛ = gcd(p, Dp)/gcd(p, dp/dt)` in
multiplicative form: for `p = ∏_{a∈s}(X − a)^{eₐ}` (char `0`),
`gcd(p, Dp) ~ gcd(p, dp/dt) · ∏_{a : v(a)=a′}(X − a)`. The special part `pₛ` is exactly the
squarefree product of `p`'s special roots. -/
abbrev thm_3_5_1 := @gcd_implicitDeriv_associated_gcd_derivative_mul_special

-- **Deferred — §3.5 library work:** Theorem 3.5.1 in full (`pₛ = gcd(p,Dp)/gcd(p,dp/dt)` for
-- general `p`; the squarefree case is `thm_3_5_1_squarefree` / `thm_3_5_1_gcd`), the `SplitFactor` /
-- `SplitSquarefreeFactor` / `CanonicalRepresentation` algorithms, Def 3.5.2 (simple/reduced
-- elements of `k⟨t⟩`, needs `RatFunc` numerator/denominator), and Theorem 3.5.2 (the `κ_D`
-- splitting separates constant from nonconstant roots).

/- ## NOT YET FORMALIZED (chapter summary — audit 2026-06-21; subtractive, delete each when done)
§3.2: Thm 3.2.1 existence (FractionRing derivation); Thm 3.2.2 full `F(t)` form; Thm 3.2.3;
  Thm 3.2.4 (automorphism/trace/norm of separable algebraic extension); Cor 3.2.1.
§3.3: Lemma 3.3.2 (new algebraic constants); Cor 3.3.1; Cor 3.3.2; Lemma 3.3.3; Lemma 3.3.4;
  Lemma 3.3.6; Lemma 3.3.5 converse general-`n` over the *constants* (determinant reduction).
§3.4: Def 3.4.3; Def 3.4.4 (special of the first kind); Lemma 3.4.5; Lemma 3.4.8; Thm 3.4.4
  (special of the first kind under algebraic extension); Cor 3.4.1.
§3.5: Thm 3.5.1 for general (non-squarefree) `p` over `RatFunc`; Thm 3.5.2; Def 3.5.2 (simple/
  reduced elements of `k⟨t⟩`); the `SplitFactor` algorithm; the `CanonicalRepresentation` algorithm.
Examples: Ex 3.1.2; Ex 3.1.3; Ex 3.2.1; Ex 3.2.2; Ex 3.2.3; Ex 3.5.1; Ex 3.5.2.
Exercises: Ex 3.1; Ex 3.2; Ex 3.3; Ex 3.4; Ex 3.6; Ex 3.7; Ex 3.8; Ex 3.9; Ex 3.10; Ex 3.11. -/

end DeepWiki.Si
