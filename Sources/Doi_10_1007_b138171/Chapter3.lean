import DeepWiki.SymbolicIntegration.DifferentialAlgebra
import DeepWiki.SymbolicIntegration.DifferentialAlgebra.Ideals
import DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors
import DeepWiki.SymbolicIntegration.CanonicalRepresentation
import DeepWiki.SymbolicIntegration.SpecialFirstKind
import DeepWiki.SymbolicIntegration.MonomialConstants
import DeepWiki.Algebra.NullstellensatzTransfer
import DeepWiki.SymbolicIntegration.RaoDifferentialPolynomials
import DeepWiki.SymbolicIntegration.Engine.Tower.Integrate
import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCore
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 3: Differential Fields
Each numbered item of the book's Chapter 3 is one declaration named by its book number: an
`abbrev` aliasing the library declaration for definitions, a `theorem` (the book-faithful
statement, discharged by the `DeepWiki.SymbolicIntegration` library) for theorems/lemmas. The
book numbering lives here in the catalog, never in the library; the citation (section, page)
is in each docstring, the source's DOI in `Sources.Doi_10_1007_b138171.Source`. -/

open scoped Differential IntermediateField
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
abbrev thm_3_1_1_iii := @DifferentialIdeal.deriv_mem_constants

/-- **Theorem 3.1.1(iv)** (§3.1, p.76): the power rule `D(aⁿ) = n·aⁿ⁻¹·Da` (natural exponent). -/
abbrev thm_3_1_1_iv := @deriv_pow

/-- **Theorem 3.1.1(iv)** (§3.1, p.76), field case: the power rule for any integer exponent. -/
abbrev thm_3_1_1_iv_zpow := @deriv_zpow

/-- **Theorem 3.1.1(v)** (§3.1, p.76), the logarithmic-derivative identity
`D(u₁^{e₁} ⋯ uₙ^{eₙ}) / (u₁^{e₁} ⋯ uₙ^{eₙ}) = e₁·Du₁/u₁ + ⋯ + eₙ·Duₙ/uₙ` (Exercise 3.1). -/
abbrev thm_3_1_1_v := @logDeriv_prod_zpow

/-- **Theorem 3.1.1(vi)** (§3.1, p.77): `D(P(u)) = ∑ᵢ (∂P/∂Xᵢ)(u)·D(uᵢ)` for a multivariate polynomial over `Const_D R`. -/
abbrev thm_3_1_1_vi := @deriv_mveval₂_constants

/-- **Lemma 3.1.1** (§3.1, p.77): the set `Ω(R)` of all derivations on `R` is a left
`R`-module; a linear combination `c·D₁ + D₂` acts pointwise as `a ↦ c·D₁a + D₂a`. -/
abbrev lem_3_1_1 := @smul_add_derivation_apply

/-- **Definition 3.1.2** (§3.1, p.78), a *differential ideal* of `(R, D)`: an ideal `I` with
`D I ⊆ I`. -/
abbrev def_3_1_2 := @DifferentialIdeal

/-- **Lemma 3.1.2** (§3.1, p.78): a differential ideal `I` induces a derivation `D*` on `R/I` satisfying `D*(a + I) = D(a) + I`, hence `D* ∘ π = π ∘ D`. -/
abbrev lem_3_1_2 := @DifferentialIdeal.exists_quotientDerivation

/-! ## §3.2 Differential Extensions -/

/-- **Definition 3.2.1** (§3.2, p.79), a *differential extension* `(S, Δ)` of `(R, D)`,
bundling the differential structure `Δ` on `S` with its compatibility over `R`. -/
abbrev def_3_2_1 := @DifferentialExtension

/-- **Definition 3.2.1** (§3.2, p.79): `DifferentialAlgebra R S` is the compatibility
condition carried by a differential extension, namely
`(algebraMap R S a)' = algebraMap R S (a')`. -/
abbrev def_3_2_1_compatibility := @DifferentialAlgebra

/-- **Definition 3.2.1** (§3.2, p.79): an algebra is a differential extension iff its
derivation commutes with the base `algebraMap`. -/
abbrev def_3_2_1_iff := @differentialAlgebra_iff_deriv_algebraMap

/-- **Definition 3.2.1** (§3.2, p.79): for a literal subring `R ⊆ S`, differential-extension
compatibility is exactly `Δ(a) = D(a)` for every `a ∈ R`. -/
abbrev def_3_2_1_subring_iff := @differentialAlgebra_subring_iff

/-- **Definition 3.2.2** (§3.2, p.80): the coefficient lifting
`κ_D : R[X] → R[X]` applies `D` to every polynomial coefficient. -/
noncomputable abbrev def_3_2_2 := @Differential.mapCoeffs

/-- **Definition 3.2.2** (§3.2, p.80): `coeff(κ_D(p), i) = D(coeff(p, i))`. -/
abbrev def_3_2_2_coeff := @Differential.coeff_mapCoeffs

/-- **Definition 3.2.2** (§3.2, p.80): `κ_D(Σᵢ₌₀ⁿ aᵢXⁱ) = Σᵢ₌₀ⁿ (Daᵢ)Xⁱ`. -/
abbrev def_3_2_2_sum := @mapCoeffs_sum_C_mul_X_pow

/-- **Lemma 3.2.1** (§3.2, p.80): coefficient lifting is a derivation on `R[X]`. -/
noncomputable abbrev lem_3_2_1 := @Differential.mapCoeffs

/-- **Lemma 3.2.2** (§3.2, p.81): for a derivation `D` on `R`, `α ∈ R`, `P ∈ R[X]`,
`D(P(α)) = κ_D(P)(α) + (Dα)·(dP/dX)(α)`. In Lean, `P.eval α` is the value `P(α)`,
`(Differential.deriv).mapCoeffs P` is `κ_D(P)`, and `PolynomialModule.eval α` evaluates that
coefficient-derivative polynomial at `α`. This is Mathlib's `Derivation.apply_eval_eq` rewritten
with multiplication instead of scalar action. -/
theorem lem_3_2_2 {R : Type*} [CommRing R] [Differential R] (α : R) (P : R[X]) :
    (P.eval α)′ = PolynomialModule.eval α ((Differential.deriv : Derivation ℤ R R).mapCoeffs P)
      + P.derivative.eval α * α′ := by
  simpa [smul_eq_mul] using (Differential.deriv : Derivation ℤ R R).apply_eval_eq α P

/-- **Theorem 3.2.1** (§3.2, p.79), uniqueness: a derivation on the quotient field of an integral
domain is determined by its restriction to the domain. This aliases the library lemma
`derivation_ext_fractionRing`: for `K` with `[IsFractionRing R K]`, two derivations
`Derivation ℤ K K` are equal once they agree on every `algebraMap R K a`. It is the uniqueness
part only, not a construction of the fraction-field derivation. -/
abbrev thm_3_2_1_unique := @derivation_ext_fractionRing

/-- **Theorem 3.2.1** (§3.2, p.79): every derivation on an integral domain extends uniquely to
any realization of its fraction field. This is the algebra-map equation form, whose witness is
`FractionRingDeriv.deriv`. -/
abbrev thm_3_2_1_derivation := @existsUnique_derivation_fractionRing

/-- **Theorem 3.2.1** (§3.2, p.79): the fraction field has a unique differential structure
making it a differential extension of the integral domain. -/
noncomputable abbrev thm_3_2_1 := @uniqueDifferentialExtension_fractionRing

/-- **Theorem 3.2.2** (§3.2, p.81), polynomial-ring case (existence + uniqueness): there is a
unique derivation on `R[X]` extending `D` on the constants and sending `t = X` to a prescribed
polynomial `w`. The witness is Mathlib's `Differential.implicitDeriv w`, whose defining equations
are `implicitDeriv_C` and `implicitDeriv_X`; uniqueness is the library lemma
`derivation_polynomial_ext`, which says a derivation on `R[X]` is determined by constants and `X`. -/
abbrev thm_3_2_2_poly := @existsUnique_derivation_polynomial

/-- **Theorem 3.2.2** (§3.2, p.81), field uniqueness: the derivation on `F(t)` extending `D` with a
prescribed `Δt` is unique. In Lean this is stated for any fraction field `K` of `F[X]`: two
derivations `Derivation ℤ K K` are equal if they agree on the images of all constants `C c` and on
the image of `X`. -/
abbrev thm_3_2_2_field_unique := @unique_derivation_rationalFunction

/-- **Theorem 3.2.2** (§3.2, p.81): if `t : E` is transcendental over the differential field `F`,
then for every `w ∈ F⟮t⟯` there is a unique differential structure `Δ` on `F⟮t⟯` such that
`(F⟮t⟯, Δ)` is a differential extension of `F` and `Δt = w`. -/
abbrev thm_3_2_2 := @existsUnique_differentialAdjoin_of_transcendental

/-- **Theorem 3.2.3** (§3.2, p.83), finite separable case: a finite separable algebraic extension
with `[FiniteDimensional F E]` and `[Algebra.IsSeparable F E]` has exactly one compatible
differential structure: `∃! Δ : Differential E, IsDifferentialExtension F E Δ`. This finite
proof avoids infinite gluing, but the Lean corollary remains classical because Mathlib defines
`Algebra.IsSeparable` through `minpoly`. -/
abbrev thm_3_2_3_finite := @existsUnique_differentialExtension_finiteSeparable

/-- **Theorem 3.2.3** (§3.2, p.83), finite presentation bridge: finite dimensionality and
separability classically select a `SeparablePowerBasisPresentation`, using the primitive-element
theorem and the nonvanishing derivative of its minimal polynomial. -/
noncomputable abbrev thm_3_2_3_finite_presentation :=
  @SeparablePowerBasisPresentation.ofFiniteOfSeparable

/-- **Theorem 3.2.3** (§3.2, p.83), choice-free finite separable presentation: explicit
power-basis coordinates together with an explicit inverse of the defining relation's derivative
give `∃! Δ : Differential E, IsDifferentialExtension F E Δ`. This is the constructive finite
counterpart of `thm_3_2_3_finite`; it replaces Mathlib's choice-bearing `Algebra.IsSeparable`
presentation by `SeparablePowerBasisPresentation`. -/
abbrev thm_3_2_3_finite_explicit :=
  @SeparablePowerBasisPresentation.existsUnique_differentialExtension

/-- **Theorem 3.2.3** (§3.2, p.83): every, possibly non-finitely-generated, separable algebraic
extension has exactly one compatible differential structure. The existence proof uses Mathlib's
classical gluing of the unique lifts on finite simple subextensions; its
`Algebra.IsSeparable` hypothesis is itself represented through `minpoly`. -/
abbrev thm_3_2_3 := @existsUnique_differentialExtension_separable

/-- **Theorem 3.2.3** (§3.2, p.83), uniqueness: any two compatible derivations on a separable
algebraic extension agree. The proof is pointwise from the separable minimal-polynomial
identity and does not require finite generation. -/
abbrev thm_3_2_3_unique := @differentialExtension_separable_unique

/-- **Theorem 3.2.4(i)** (§3.2, p.85): an `F`-automorphism of a separable algebraic extension
commutes with `D`. The Lean statement is pointwise: for `σ : E ≃ₐ[F] E` and `a : E`,
`σ (a') = (σ a)'`, using Mathlib's `Differential.algEquiv_deriv'`. -/
abbrev thm_3_2_4_i := @algEquiv_comm_deriv

/-- **Theorem 3.2.4(ii)** (§3.2, p.85): on a finite separable extension, trace commutes with
`D`: `(Algebra.trace F E a)' = Algebra.trace F E (a')`. The proof expands trace as the sum
over embeddings into a separable closure and commutes each embedding with derivation. -/
abbrev thm_3_2_4_ii_trace := @deriv_trace_eq_trace_deriv

/-- **Theorem 3.2.4(ii)** (§3.2, p.85): `Tr(Da/a) = D(N a)/N a` (logarithmic-derivative trace–norm
relation) for `a ≠ 0` in a finite separable extension. The Lean statement is
`Algebra.trace F E (a' / a) = (Algebra.norm F a)' / Algebra.norm F a`; the proof maps both
sides into a separable closure, rewrites norm as a product over embeddings, and applies the
logarithmic-derivative product rule. -/
abbrev thm_3_2_4_ii_norm := @trace_logDeriv_eq_logDeriv_norm

/-- **Corollary 3.2.1** (§3.2, p.85), extension to `E`: if `E/K` is separable algebraic, then
there is a unique differential structure on `E` extending `D` from `K`. -/
abbrev cor_3_2_1_E := @existsUnique_differentialExtension_separable

/-- **Corollary 3.2.1** (§3.2, p.85), extension to the compositum: in a common overfield `Ω`,
write `EF = IntermediateField.adjoin F (E : Set Ω)`. If `E/K` is separable and `F/K` is a
differential extension, then the derivation on `F` extends uniquely to `EF`. The algebraic
closure in the book supplies `Ω`; its closedness is not needed for this conclusion. -/
abbrev cor_3_2_1_compositum := @existsUnique_differentialExtension_compositum

/-- **Corollary 3.2.1** (§3.2, p.85), compatibility over `E`: for the canonical inclusion
`E →ₐ[K] EF`, compatible extensions on `E` and `EF` make `EF` a differential extension of `E`.
-/
abbrev cor_3_2_1_compatibility := @isDifferentialExtension_compositum_right

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

/-- **Lemma 3.3.5** (§3.3, p.88), intermediate field-coefficient statement (all `n`): a
vanishing Wronskian forces linear dependence of `y₁,…,yₙ` over `F`. -/
abbrev lem_3_3_5_converse_field := @wronskian_eq_zero_imp_linearDependent

/-- **Lemma 3.3.5** (§3.3, p.88), FULL converse, general `n` over the constants: `W(y₁,…,yₙ) = 0` iff
`y₁,…,yₙ` are linearly dependent over `Const_D F` — proved by an algebraic induction dropping a
normalized kernel coordinate (no `W = y₁ⁿ·W(…)` identity needed). -/
abbrev lem_3_3_5_iff := @wronskian_eq_zero_iff_linearDependentOverConst

/-- **Lemma 3.3.2(i)** (§3.3, p.86): a new constant algebraic over `F` is algebraic over the old
constant field `Const_D F`. In Lean, `c′ = 0` and `IsAlgebraic F c` imply
`IsAlgebraic (constantsSubfield F) c`. -/
abbrev lem_3_3_2_i := @isAlgebraic_constantsSubfield_of_deriv_eq_zero

/-- **Lemma 3.3.2(ii)** (§3.3, p.86): an element algebraic and *separable* over `Const_D F` is itself
a constant. In Lean, `IsAlgebraic (constantsSubfield F) c` and
`IsSeparable (constantsSubfield F) c` imply `c′ = 0`. -/
abbrev lem_3_3_2_ii := @deriv_eq_zero_of_isAlgebraic_constantsSubfield_of_isSeparable

/-- **Corollary 3.3.2** (§3.3, p.87): linear independence over the constants is preserved by a
differential extension (the Wronskian commutes with `algebraMap`). -/
abbrev cor_3_3_2 := @not_linearDependentOverConst_algebraMap

/-- **Corollary 3.3.1** (§3.3, p.86), unique extension: a separable algebraic extension `E/F`
admits a unique differential structure extending `D`. -/
abbrev cor_3_3_1_unique_extension := @existsUnique_differentialExtension_separable

/-- **Corollary 3.3.1** (§3.3, p.86), constants: under the book's standing characteristic-zero
hypothesis, the constants of an algebraic extension are exactly the relative algebraic closure of
`Const_D(F)` in `E`. -/
abbrev cor_3_3_1_constants := @constantsIntermediateField_eq_algebraicClosure

/-- **Corollary 3.3.1** (§3.3, p.86), algebraically closed case: if `E` is algebraically closed,
its constants form an algebraic closure of `Const_D(F)`. -/
abbrev cor_3_3_1_isAlgClosure := @isAlgClosure_constantsIntermediateField

/-- **Lemma 3.3.3** (§3.3, p.87), extension claim: if `Ebar` is an algebraic closure of `E`
and `Fbar := algebraicClosure F Ebar`, the differential structures on `E` and `Fbar` extend
uniquely and compatibly to their compositum `E Fbar`. -/
abbrev lem_3_3_3_extension := @existsUnique_differentialExtension_adjoin_algebraicClosure

/-- **Lemma 3.3.3** (§3.3, p.87), constants claim: with `Ebar` and `Fbar` as above, if
`Const_D(F) = Const_Δ(E)`, encoded by `constantsIntermediateField F E = ⊥`, then
`Const_D(Fbar) = Const_Δ(E Fbar)`. -/
abbrev lem_3_3_3_constants := @constantsIntermediateField_adjoin_algebraicClosure_eq_bot

/-- **Lemma 3.3.4** (§3.3, p.87): if `t` is constant in a differential extension `E/F`,
then the constants of the restricted simple extension satisfy
`Const_Δ(F⟮t⟯) = Const_D(F)⟮t⟯`. -/
abbrev lem_3_3_4 := @constantsIntermediateField_restrictAdjoin_eq_adjoin_constants

/-- **Lemma 3.3.6** (§3.3, p.88), post-reduction core: over an algebraically closed constant field, a
constant-coefficient polynomial system solved by an extension-constant point is solved by a
base-constant point (multivariate Nullstellensatz transfer). -/
abbrev lem_3_3_6 := @DeepWiki.exists_base_point_of_exists_extension_point

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
abbrev lem_3_4_3 := @DifferentialIdeal.ofSpecial

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

/-- **Definition 3.4.3** (§3.4, p.97): `u ∈ k` is a *logarithmic derivative of a `k`-radical* if
`n·u = Dv/v` for some `v ∈ k*` and integer `n ≠ 0`. -/
abbrev def_3_4_3 := @IsLogDerivRadical

/-- **Lemma 3.4.8** (§3.4, p.98): for `E` algebraic over `k` (char `0`), an element of `k` that is
not a logarithmic derivative of a `k`-radical is not one of an `E`-radical either. -/
abbrev lem_3_4_8 := @isLogDerivRadical_descent

/-- **Definition 3.4.4** (§3.4, p.98): `q ∈ k[t]` is *special of the first kind* if it is special and
for every root `α` of `q` in the algebraic closure, `(Dt−Dα)/(t−α)` evaluated at `α` is not a
logarithmic derivative of a `k(α)`-radical. -/
abbrev def_3_4_4 := @IsSpecialFirstKind

/-- **Theorem 3.4.4(i)** (§3.4, p.99): a finite product of special-of-the-first-kind polynomials is
special of the first kind. -/
abbrev thm_3_4_4_prod := @isSpecialFirstKind_prod

/-- **Theorem 3.4.4(ii)** (§3.4, p.99): any factor of a special-of-the-first-kind polynomial is
special of the first kind (char `0`). -/
abbrev thm_3_4_4_dvd := @isSpecialFirstKind_of_dvd

/-- **Theorem 3.4.4(iii)** (§3.4, p.99): special of the first kind is preserved under an algebraic
extension `k ⊆ E` (`S₁,k[t]:k ⊆ S₁,E[t]:E`). -/
abbrev thm_3_4_4_map := @isSpecialFirstKind_map

/-- **Corollary 3.4.1** (§3.4), special half: specialness is preserved when base-changing the
monomial derivation along an algebraic scalar tower. -/
abbrev cor_3_4_1_special := @isSpecial_map_of_isSpecial

/-- **Corollary 3.4.1** (§3.4), normal half: a normal `p ∈ k[t]` stays normal in `E[t]` for an
algebraic extension `k ⊆ E` (coprimality lifts along the base change). -/
abbrev cor_3_4_1_normal := @isCoprime_map_implicitDeriv_of_isCoprime

/-- **Corollary 3.4.2(i)** (§3.4), constant-coefficient case: `∏(X − aᵢ)` is special iff it divides
`Dt`. -/
abbrev cor_3_4_2_special := @dvd_prod_X_sub_C_implicitDeriv_iff_dvd

/-- **Corollary 3.4.2(ii)** (§3.4), constant-coefficient case: a squarefree `∏(X − aᵢ)` is normal iff
it is coprime to `Dt`. -/
abbrev cor_3_4_2_normal := @isCoprime_prod_X_sub_C_implicitDeriv_iff_isCoprime

/-- **Lemma 3.4.5** (§3.4, p.94): if `c ∈ Const(k(t))` then both the numerator and denominator of `c`
are special; for `c ≠ 0` and `t` nonlinear (`deg Dt ≥ 2`) they additionally have equal degree. -/
abbrev lem_3_4_5 := @isSpecial_and_natDegree_eq_of_const_quotient_nonlinear

/-- **Lemma 3.4.6** (§3.4, p.96): for `Dt ∈ k` and nonzero `p ∈ k[t]`, `p` is special iff
`D(p/lc(p)) = 0`. -/
abbrev lem_3_4_6 := @isSpecial_iff_deriv_normalize_eq_zero

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

/-- **SplitFactor** (§3.5, p.100): the splitting-factorization algorithm — peel off
`S = gcd(p, Dp)/gcd(p, dp/dt)` and recurse on `p/S`, returning `(pₙ, pₛ)`. -/
noncomputable abbrev splitFactor_algorithm := @splitFactor

/-- **SplitFactor** correctness (§3.5, p.100) into the *stronger* repo predicate (`IsNormal pₙ`),
given the one-step special-part property — discharged on squarefree-split `p`
(`isSplitFactorStep_prod_X_sub_C`). For the book predicate on arbitrary `p`, see the unconditional
`splitFactor_correct_gen`. -/
abbrev splitFactor_correct := @splitFactor_isSplittingFactorization

/-- **SplitSquarefreeFactor** (§3.5, p.102): Yun squarefree factorization, then per factor
`Sᵢ = gcd(pᵢ, Dpᵢ)` (special part) and `Nᵢ = pᵢ/Sᵢ` (normal part). -/
noncomputable abbrev splitSquarefreeFactor_algorithm := @splitSquarefreeFactor

/-- **Definition 3.5.2** (§3.5, p.103): `f ∈ k(t)` is *simple* w.r.t. `D` if its denominator is
normal. -/
abbrev def_3_5_2_simple := @IsSimple

/-- **Definition 3.5.2** (§3.5, p.103): `f ∈ k(t)` is *reduced* w.r.t. `D` if its denominator is
special; the reduced elements form `k⟨t⟩`. -/
abbrev def_3_5_2_reduced := @DeepWiki.SymbolicIntegration.IsReduced

/-- **CanonicalRepresentation** (§3.5, p.103): `f = fₚ + fₛ + fₙ` (polynomial, special, normal parts)
via `PolyDivide` + `SplitFactor` + `ExtendedEuclidean`. -/
noncomputable abbrev canonicalRepresentation_algorithm := @canonicalRepresentation

/-- **CanonicalRepresentation** correctness (§3.5, p.103): the polynomial, special, and normal parts
sum back to `f`. -/
abbrev canonicalRepresentation_correct := @canonicalRepresentation_sum_eq

/-- **Theorem 3.5.2** (§3.5, p.103): the `κ_D`-splitting `p = pₛpₙ` separates constant from
nonconstant roots — a root `α` of `p` has `Dα = 0 ↔ pₛ(α) = 0`. -/
abbrev thm_3_5_2 := @deriv_eq_zero_iff_isRoot_special

/-- **Definition 3.5.1** (§3.5, p.99), book-faithful form: `p = pₛ·pₙ` with `pₛ` special and every
squarefree factor of `pₙ` normal. The repo `def_3_5_1` is the stronger `IsNormal pₙ` form (forces `pₙ`
squarefree); the two agree on squarefree `pₙ`. -/
abbrev def_3_5_1_book := @IsSplittingFactorizationGen

/-- **Theorem 3.5.1(i)** (§3.5, p.99), general `p`: `gcd(p, Dp)/gcd(p, dp/dt)` is associated to the
product of all coprime special irreducible factors of `p` (char `0`) — proven over `K`'s UFD
factorization into general irreducibles, with no algebraic-closure transport. -/
abbrev thm_3_5_1_general := @splitFactorStep_associated_prod_special

/-- **SplitFactor** correctness, UNCONDITIONAL (§3.5, p.100): for any `p ≠ 0`, `splitFactor v p` is a
book-faithful splitting factorization (`def_3_5_1_book`) — no one-step hypothesis, via
`thm_3_5_1_general`. -/
abbrev splitFactor_correct_gen := @splitFactor_isSplittingFactorizationGen

/-! ## Chapter 3 Examples -/

/-- **Example 3.1.1** (§3.1, p.78): for the zero derivation on `R`, every ideal is differential. -/
abbrev ex_3_1_1_ideal := @DifferentialIdeal.ofDerivEqZero

/-- **Example 3.1.1** (§3.1, p.78): every induced quotient derivation is zero. -/
abbrev ex_3_1_1_quotient := @DifferentialIdeal.quotientDerivation_eq_zero_of_deriv_eq_zero

/-- **Example 3.1.2** (§3.1, p.78): the only differential ideals of `(K[X], d/dX)` are `⊥` and `⊤` in characteristic zero. -/
abbrev ex_3_1_2_classification := @differentialIdeal_eq_bot_or_top

section PolynomialDerivative

open scoped FormalDiff

/-- **Example 3.1.2** (§3.1, p.78): `⊥` is a differential ideal of `(K[X], d/dX)`. -/
noncomputable abbrev ex_3_1_2_bot {K : Type*} [Field K] : DifferentialIdeal K[X] := ⊥

/-- **Example 3.1.2** (§3.1, p.78): `⊤` is a differential ideal of `(K[X], d/dX)`. -/
noncomputable abbrev ex_3_1_2_top {K : Type*} [Field K] : DifferentialIdeal K[X] := ⊤

end PolynomialDerivative

/-- **Example 3.1.2** (§3.1, p.78): under `K[X]/⊥ ≃ K[X]`, the induced derivation is `d/dX`. -/
abbrev ex_3_1_2_bot_quotient := @polynomialDerivative_quotientBot_apply

/-- **Example 3.1.2** (§3.1, p.78): the induced derivation on `K[X]/⊤` is zero. -/
abbrev ex_3_1_2_top_quotient := @polynomialDerivative_quotientTop_eq_zero

/-- **Example 3.1.3** (§3.1, p.78): `Δ(aXⁿ) = (Da + n·a)Xⁿ` for `Δ = κ_D + X·d/dX`. -/
abbrev ex_3_1_3_monomial := @implicitDeriv_X_monomial

/-- **Example 3.1.3** (§3.1, p.78): every `(Xᵐ)` with `m > 0` is a differential ideal. -/
noncomputable abbrev ex_3_1_3_ideal := @implicitDerivXSpanXPow

/-- **Example 3.1.3** (§3.1, p.78): under `R[X]/(X) ≃ R`, the projection is substitution `X ↦ 0`. -/
abbrev ex_3_1_3_projection := @quotientSpanXAlgEquiv_mk

/-- **Example 3.1.3** (§3.1, p.78): `Δstar(π(p)) = D(p(0))` under `R[X]/(X) ≃ R`. -/
abbrev ex_3_1_3_quotient_mk := @implicitDeriv_X_quotientDerivation_mk_eval_zero

/-- **Example 3.1.3** (§3.1, p.78): under `R[X]/(X) ≃ R`, the induced derivation is `D`. -/
abbrev ex_3_1_3_quotient := @implicitDeriv_X_quotientSpanX

/-- **Example 3.2.1** (§3.2, p.82): if `x : E` is transcendental over a zero-differential
field `F`, transport of `d/dX` gives the differential extension `d/dx` on `F⟮x⟯`. -/
noncomputable abbrev ex_3_2_1_extension := @transcendentalFormalExtension

/-- **Example 3.2.1** (§3.2, p.82): for transcendental `x`, `dx/dx = 1` in `F⟮x⟯`. -/
abbrev ex_3_2_1_generator := @transcendentalFormalExtension_gen

/-- **Example 3.2.1** (§3.2, p.82): if `x` is transcendental over a zero-differential field
`F`, the only differential extension to `F⟮x⟯` sending `x` to one is `d/dx`. -/
abbrev ex_3_2_1_unique :=
  @differentialExtension_eq_transcendentalFormal_of_gen_eq_one

/-- **Example 3.2.2** (§3.2, p.82): `κ_D` is the coefficient differential extension from `F`
to the simple transcendental extension `F⟮t⟯`. -/
noncomputable abbrev ex_3_2_2_extension := @transcendentalCoefficientExtension

/-- **Example 3.2.2** (§3.2, p.82): the coefficient extension makes `t` constant. -/
abbrev ex_3_2_2_generator := @transcendentalCoefficientExtension_gen

/-- **Example 3.2.2** (§3.2, p.82): `κ_D` differentiates a polynomial in `t` by applying
`D` coefficientwise. -/
abbrev ex_3_2_2_coefficients := @transcendentalCoefficientExtension_aeval

/-- **Example 3.2.2** (§3.2, p.82): the only differential extension to `F⟮t⟯` making `t`
constant is the coefficient extension `κ_D`. -/
abbrev ex_3_2_2_unique :=
  @differentialExtension_eq_transcendentalCoefficient_of_gen_eq_zero

/-- **Example 3.2.3** (§3.2, p.83), uniqueness: if `α` is algebraic over `Const_D(F)`, then
`D` has a unique extension to the simple field extension `F⟮α⟯`. -/
abbrev ex_3_2_3_unique :=
  @existsUnique_differentialAdjoin_of_isIntegral_constantsSubfield

/-- **Example 3.2.3** (§3.2, p.83), displayed equality: evaluating a polynomial over
`Const_D(F)` satisfies `D(P(α)) = P'(α)·Dα`. -/
abbrev ex_3_2_3_chain_rule := @deriv_eval₂_constantsSubfield

/-- **Example 3.2.3** (§3.2, p.83), conclusion: if `α` is algebraic over `Const_D(F)`, then,
using its irreducible minimal polynomial, `Dα = 0`. -/
abbrev ex_3_2_3_constant := @deriv_eq_zero_of_isIntegral_constantsSubfield

/-- **Example 3.2.4** (§3.2, p.83), uniqueness: if `α` is a root of `Y²-X` over `ℚ(X)`, then
`d/dX` has a unique extension to `ℚ(X)⟮α⟯`. -/
theorem ex_3_2_4_unique {E : Type*} [Field E] [Algebra (RatFunc ℚ) E] {α : E}
    (hroot : (X ^ 2 - C (RatFunc.X : RatFunc ℚ)).eval₂
      (algebraMap (RatFunc ℚ) E) α = 0) :
    ∃! Δ : Differential ((RatFunc ℚ)⟮α⟯),
      IsDifferentialExtension (RatFunc ℚ) ((RatFunc ℚ)⟮α⟯) Δ := by
  apply existsUnique_differentialAdjoin_of_sq_eq
  apply sub_eq_zero.mp
  simpa using hroot

/-- **Example 3.2.4** (§3.2, p.83), differentiated relation: every compatible extension to
`ℚ(X)⟮α⟯` satisfies `2α·Dα = 1`. -/
theorem ex_3_2_4_relation {E : Type*} [Field E] [Algebra (RatFunc ℚ) E] {α : E}
    (hroot : (X ^ 2 - C (RatFunc.X : RatFunc ℚ)).eval₂
      (algebraMap (RatFunc ℚ) E) α = 0)
    (Δ : DifferentialExtension (RatFunc ℚ) ((RatFunc ℚ)⟮α⟯)) :
    2 * IntermediateField.AdjoinSimple.gen (RatFunc ℚ) α *
        Δ.deriv (IntermediateField.AdjoinSimple.gen (RatFunc ℚ) α) = 1 := by
  letI : Differential ((RatFunc ℚ)⟮α⟯) := Δ.toDifferential
  haveI : DifferentialAlgebra (RatFunc ℚ) ((RatFunc ℚ)⟮α⟯) := Δ.differentialAlgebra
  apply two_mul_mul_deriv_eq_one_of_sq_eq
    (F := RatFunc ℚ) (E := (RatFunc ℚ)⟮α⟯) (x := RatFunc.X) deriv_ratFunc_X
  apply Subtype.ext
  change α ^ 2 = algebraMap (RatFunc ℚ) E RatFunc.X
  apply sub_eq_zero.mp
  simpa using hroot

/-- **Example 3.2.4** (§3.2, p.83), conclusion: every compatible extension to `ℚ(X)⟮α⟯`
satisfies `Dα = 1/(2α)`. -/
theorem ex_3_2_4_derivative {E : Type*} [Field E] [Algebra (RatFunc ℚ) E] {α : E}
    (hroot : (X ^ 2 - C (RatFunc.X : RatFunc ℚ)).eval₂
      (algebraMap (RatFunc ℚ) E) α = 0)
    (Δ : DifferentialExtension (RatFunc ℚ) ((RatFunc ℚ)⟮α⟯)) :
    Δ.deriv (IntermediateField.AdjoinSimple.gen (RatFunc ℚ) α) =
      1 / (2 * IntermediateField.AdjoinSimple.gen (RatFunc ℚ) α) := by
  apply Δ.adjoin_gen_deriv_eq_one_div_two_mul_of_sq_eq
    (x := RatFunc.X) deriv_ratFunc_X
  apply sub_eq_zero.mp
  simpa using hroot

/-! ### Generic-carrier input builders for the §3.5 split examples (catalog-local)

The §3.5 split examples over the generic ℚ(x) = `DenseFrac ℚ` carrier read their ℚ(x) coefficients as
num/den lists over `DensePoly ℚ = List ℚ`, using `CFrac.ofScalar` for constants and
`CFrac.ofFraction` for arbitrary fractions. Catalog infrastructure, not book items. -/

/-- Example 3.5.1's `Dt = −t²−(3/(2x))t+1/(2x)` over the generic ℚ(x)[t] (low→high in `t`). -/
def ex351Dt : DensePoly (DenseFrac ℚ) := [CFrac.ofFraction [1] [0, 2] (by cfrac_nonzero), CFrac.ofFraction [-3] [0, 2] (by cfrac_nonzero), CFrac.ofFraction [-1] [1] (by cfrac_nonzero)]

/-- Example 3.5.1's degree-5 `p = 4x⁴t⁵−4x³(x+1)t⁴+x²(2x−3)t³+x(2x²+7x+2)t²−(4x²+4x−1)t+2x−1` over the
generic ℚ(x)[t] (low→high in `t`; ℚ[x] coefficients, denominator `1`). -/
def ex351P : DensePoly (DenseFrac ℚ) :=
  [CFrac.ofFraction [-1, 2] [1] (by cfrac_nonzero), CFrac.ofFraction [1, -4, -4] [1] (by cfrac_nonzero), CFrac.ofFraction [0, 2, 7, 2] [1] (by cfrac_nonzero),
   CFrac.ofFraction [0, 0, -3, 2] [1] (by cfrac_nonzero), CFrac.ofFraction [0, 0, 0, -4, -4] [1] (by cfrac_nonzero), CFrac.ofFraction [0, 0, 0, 0, 4] [1] (by cfrac_nonzero)]

/-- Example 3.5.1's expected normal part `pₙ = 4x⁴t³−4x³(x+2)t²+4x²(2x+1)t−4x²` (book p.101). -/
def ex351Pn : DensePoly (DenseFrac ℚ) :=
  [CFrac.ofFraction [0, 0, -4] [1] (by cfrac_nonzero), CFrac.ofFraction [0, 0, 4, 8] [1] (by cfrac_nonzero), CFrac.ofFraction [0, 0, 0, -8, -4] [1] (by cfrac_nonzero), CFrac.ofFraction [0, 0, 0, 0, 4] [1] (by cfrac_nonzero)]

/-- Example 3.5.1's expected special part `pₛ = t²+(1/x)t−(2x−1)/(4x²)` (book p.101). -/
def ex351Ps : DensePoly (DenseFrac ℚ) := [CFrac.ofFraction [1, -2] [0, 0, 4] (by cfrac_nonzero), CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero), CFrac.ofFraction [1] [1] (by cfrac_nonzero)]

/-- Recombine a positional-by-multiplicity factor list `[q₁, q₂, …]` into `∏ᵢ qᵢ^i` over ℚ(x)[t]. -/
def ex352Recombine (qs : List (DensePoly (DenseFrac ℚ))) : DensePoly (DenseFrac ℚ) :=
  qs.zipIdx.foldl (fun acc (qi, i) => DensePoly.cmul acc (DensePoly.cpow qi (i + 1))) [CCommRing.one]

/-- Example 3.5.2's expected normal part `pₙ = N₁N₂² = 4x²(t−1)(xt−1)²` (book p.102), as `4x²·(t−1)·(xt−1)²`. -/
def ex352Pn : DensePoly (DenseFrac ℚ) :=
  DensePoly.cmul [CFrac.ofFraction [0, 0, 4] [1] (by cfrac_nonzero)]
    (DensePoly.cmul [CFrac.ofFraction [-1] [1] (by cfrac_nonzero), CFrac.ofFraction [1] [1] (by cfrac_nonzero)]
      (DensePoly.cmul [CFrac.ofFraction [-1] [1] (by cfrac_nonzero), CFrac.ofFraction [0, 1] [1] (by cfrac_nonzero)] [CFrac.ofFraction [-1] [1] (by cfrac_nonzero), CFrac.ofFraction [0, 1] [1] (by cfrac_nonzero)]))

/-- Example 3.5.2's expected special part `pₛ = S₁ = t²+(1/x)t−(2x−1)/(4x²)` (book p.102). -/
def ex352Ps : DensePoly (DenseFrac ℚ) := [CFrac.ofFraction [1, -2] [0, 0, 4] (by cfrac_nonzero), CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero), CFrac.ofFraction [1] [1] (by cfrac_nonzero)]

/-- **Example 3.5.1** (§3.5, p.101): the COMPUTABLE fraction-free `cSplitFactorFast` (the canonical
generic engine at the generic ℚ(x) = `DenseFrac ℚ`) splits the degree-5 `p` over ℚ(x)[t]
(`Dt = −t²−(3/2x)t+1/(2x)`) into Bronstein's `pₙ` (degree 3) and `pₛ = t²+(1/x)t−(2x−1)/(4x²)` (degree
2), monic-normalized, by `native_decide` — where the naive ℚ(x)-Euclidean kernel did not finish
(coefficient swell). -/
theorem ex_3_5_1 :
    (DensePoly.cdeg (DensePoly.cSplitFactorFast ex351Dt ex351P).1,
       DensePoly.cdeg (DensePoly.cSplitFactorFast ex351Dt ex351P).2) = (3, 2)
    ∧ DensePoly.cisZero (DensePoly.csub
        (DensePoly.cmonic (DensePoly.cSplitFactorFast ex351Dt ex351P).1) (DensePoly.cmonic ex351Pn)) = true
    ∧ DensePoly.cisZero (DensePoly.csub
        (DensePoly.cmonic (DensePoly.cSplitFactorFast ex351Dt ex351P).2) (DensePoly.cmonic ex351Ps)) = true := by
  native_decide

/-- **Example 3.5.2** (§3.5, p.102): the COMPUTABLE fraction-free `cSplitSquarefreeFactorFast` (Yun in
`t` + per-factor differential special/normal split, the generic engine at the generic ℚ(x) =
`DenseFrac ℚ`) on the same degree-5 `p` returns `N`-factor `t`-degrees `[1, 1]` and `S`-factor `t`-degrees
`[2, 0]`, recombining (by multiplicity) to Bronstein's normal part `pₙ = N₁N₂² = 4x²(t−1)(xt−1)²` and
special part `pₛ = S₁ = t²+(1/x)t−(2x−1)/(4x²)`, all monic-normalized, by `native_decide`. -/
theorem ex_3_5_2 :
    (((DensePoly.cSplitSquarefreeFactorFast ex351Dt ex351P).1).map DensePoly.cdeg,
       ((DensePoly.cSplitSquarefreeFactorFast ex351Dt ex351P).2).map DensePoly.cdeg) = ([1, 1], [2, 0])
    ∧ DensePoly.cisZero (DensePoly.csub
        (DensePoly.cmonic (ex352Recombine (DensePoly.cSplitSquarefreeFactorFast ex351Dt ex351P).1))
        (DensePoly.cmonic ex352Pn)) = true
    ∧ DensePoly.cisZero (DensePoly.csub
        (DensePoly.cmonic (ex352Recombine (DensePoly.cSplitSquarefreeFactorFast ex351Dt ex351P).2))
        (DensePoly.cmonic ex352Ps)) = true := by
  native_decide

/-! ## Chapter 3 Exercises -/

/-- **Exercise 3.1** (Ch 3, p.105): `D(∏ uᵢ^eᵢ)/(∏ uᵢ^eᵢ) = ∑ eᵢ·(Duᵢ/uᵢ)` — the logarithmic
derivative of a power product. -/
abbrev ex_3_1 := @logDeriv_prod_zpow_div

/-- **Exercise 3.4** (Ch 3, p.105): with `Δt₁ = Δv/v` (`v = (u+i)/(u−i)`) and `Δt₂ = Δu/(1+u²)`, the
combination `i·t₁ − 2·t₂` is a constant. -/
abbrev ex_3_4 := @deriv_log_arctan_combination_eq_zero

/-- **Exercise 3.6(a)** (Ch 3, p.105): `κ_D(∑ aᵢ Xⁱ) = ∑ (Daᵢ) Xⁱ` is a derivation on `R[X]`. -/
noncomputable abbrev ex_3_6a := @Differential.mapCoeffs

/-- **Exercise 3.7** (Ch 3, p.105): for `Δt = a/b`, `b·Δp = b·κ_D(p) + a·(dp/dt) ∈ k[t]` for any
`p`. -/
abbrev ex_3_7 := @bDeriv_eq

/-- **Exercise 3.8** (Ch 3, p.105): Theorem 3.4.1 holds for Rao's `b·Δ` definition of normal/special —
e.g. the product of two special polynomials is special (and the rest of the family). -/
abbrev ex_3_8 := @IsSpecialRao.mul

/-- **Exercise 3.9** (Ch 3, p.105): a squarefree `p = ∏(X−αᵢ)` is normal (Rao) iff `b(α)·Δα ≠ a(α)` at
every root `α`. -/
abbrev ex_3_9 := @isNormalRao_prod_X_sub_C_iff

/-- **Exercise 3.10** (Ch 3, p.105): a squarefree `p = ∏(X−αᵢ)` is special (Rao) iff `b(α)·Δα = a(α)`
at every root `α`. -/
abbrev ex_3_10 := @isSpecialRao_prod_X_sub_C_iff

/-- **Exercise 3.11** (Ch 3, p.105): a special (Rao) prime `π` is coprime to `b` (so `gcd(p,b)=1` for a
special `p`). -/
abbrev ex_3_11 := @isCoprime_of_isSpecialRao_prime

/-! ## NOT YET FORMALIZED

- Lemma 3.3.6 (front reduction) [infra]: rewrite `F[X]`-coefficient systems over a
  `Const_D(F)`-basis via the `C[X] ⊗_C F` free-module step.
- Exercise 3.2 [infra]: construct the algebraic differential field `ℚ(x, √(2x²))` and its constants.
- Exercise 3.3 [deferred]: prove the algebraic-independence transfer.
- Exercise 3.5 [infra]: define `S^irr` and prove base-change descent.
- Exercise 3.6(b) [infra]: formalize the multivariate decomposition.
- Exercise 3.6(c) [research]: develop the required Darboux-polynomial result.
- Exercise 3.11 (general non-squarefree case) [deferred]: extend the current prime-factor result.
-/

end DeepWiki.Si
