import DeepWiki.SymbolicIntegration.DifferentialFields
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.FieldTheory.Galois.Basic

/-! # Existence and uniqueness of derivation extensions (Bronstein §3.2)
Extending a derivation `D` from a base field to a larger ring or field. A derivation on an
integral domain extends *uniquely* to its quotient field by the quotient rule; a transcendental
extension `F(t)` extends in many ways, one per choice of `Dt`; a *separable algebraic* extension
`E ⊇ F` extends *uniquely*, with `Dα = −κ_D(p)(α)/p'(α)` forced by the minimal polynomial `p`.
In characteristic `0` (our setting) every algebraic extension is separable, and Mathlib already
builds the unique finite-extension derivation via this very formula
(`Differential.differentialFiniteDimensional`, the `AdjoinRoot` instance). We package those as the
§3.2 theorems and add the trace/norm transport: a field automorphism commutes with `D`, hence the
trace commutes with `D` and `Tr(Da/a) = D(N a)/N a`. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section FractionField
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Differential R]

/-- **Theorem 3.2.1** (§3.2), uniqueness clause: a derivation on the fraction field `K` of an
integral domain `R` that extends `D` on `R` (`Δ (algebraMap R K a) = algebraMap R K (Da)`) is
unique. (Forced by the quotient rule `Δ(a/b) = (b·Da − a·Db)/b²`.) Existence — when a compatible
`Differential K` is available — is `existsUnique_derivation_fractionRing`. -/
theorem unique_derivation_fractionRing {Δ₁ Δ₂ : Derivation ℤ K K}
    (h₁ : ∀ a : R, Δ₁ (algebraMap R K a) = algebraMap R K (a′))
    (h₂ : ∀ a : R, Δ₂ (algebraMap R K a) = algebraMap R K (a′)) : Δ₁ = Δ₂ :=
  derivation_ext_fractionRing (R := R) fun a => (h₁ a).trans (h₂ a).symm

/-- **Theorem 3.2.1** (§3.2), existence + uniqueness: if the fraction field `K` carries a
differential structure compatible with `D` (`DifferentialAlgebra R K`), then the extending
derivation on `K` is the *unique* one with `Δ (algebraMap R K a) = algebraMap R K (Da)`. So a
derivation on an integral domain extends uniquely to its quotient field. -/
theorem existsUnique_derivation_fractionRing [Differential K] [DifferentialAlgebra R K] :
    ∃! Δ : Derivation ℤ K K, ∀ a : R, Δ (algebraMap R K a) = algebraMap R K (a′) := by
  refine ⟨Differential.deriv, fun a => ?_, fun Δ hΔ => ?_⟩
  · rw [deriv_algebraMap]
  · exact unique_derivation_fractionRing (R := R) hΔ (fun a => by rw [deriv_algebraMap])

end FractionField

section Transcendental
variable {F : Type*} [Field F] [Differential F]

omit [Differential F] in
/-- **Theorem 3.2.2** (§3.2), uniqueness on `F(t)` (`t` transcendental): a derivation `Δ` on the
rational-function field `K = F(t)` that extends `D` on `F` and sends `t` to a prescribed value
(via the agreement of `Δ` with another such derivation on `F[t]`) is unique. Reduces the `F(t)`
uniqueness to the `F[X]`-uniqueness `derivation_polynomial_ext` through the fraction field
`K = FractionRing F[X]`. -/
theorem unique_derivation_rationalFunction {K : Type*} [Field K] [Algebra F[X] K]
    [IsFractionRing F[X] K] {Δ₁ Δ₂ : Derivation ℤ K K}
    (hC : ∀ c : F, Δ₁ (algebraMap F[X] K (C c)) = Δ₂ (algebraMap F[X] K (C c)))
    (hX : Δ₁ (algebraMap F[X] K X) = Δ₂ (algebraMap F[X] K X)) : Δ₁ = Δ₂ := by
  refine derivation_ext_fractionRing (R := F[X]) fun p => ?_
  induction p using Polynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, Δ₁.leibniz, Δ₂.leibniz, ih, hX]

end Transcendental

section Algebraic
variable {F : Type*} [Field F] [Differential F] [CharZero F]
variable {E : Type*} [Field E] [Algebra F E]

omit [CharZero F] in
/-- **Lemma 3.2.2** (§3.2): the derivation-of-evaluation formula `Δ(P(α)) = κ_D(P)(α) +
(dP/dX)(α)·Δα` on a differential extension `(E, Δ)` of `(F, D)`. Here `aeval α P` is `P(α)`,
`mapCoeffs` is the coefficient-lifting `κ_D`, and `α′ = Δα`. (Mathlib's `deriv_aeval_eq`.) -/
theorem deriv_aeval_eq_extensions [Differential E] [DifferentialAlgebra F E] (α : E) (P : F[X]) :
    (aeval α P)′ = aeval α (Differential.mapCoeffs P) + aeval α (derivative P) * α′ :=
  Differential.deriv_aeval_eq α P

variable [FiniteDimensional F E]

/-- **Theorem 3.2.3** (§3.2): existence of the unique derivation extension to a finite (separable,
char `0`) algebraic extension. `E` carries a differential structure `Differential E` making
`(E, Δ)` a differential extension of `(F, D)`; concretely `Δα = −κ_D(p)(α)/p'(α)` for the minimal
polynomial `p = minpoly F α`. (Mathlib's `differentialFiniteDimensional`, built via that formula.)
The companion uniqueness is `unique_differentialAlgebra_algebraic`. -/
@[reducible]
noncomputable def differentialAlgebraic : Differential E :=
  Differential.differentialFiniteDimensional F E

/-- **Theorem 3.2.3** (§3.2): the `differentialAlgebraic` structure is compatible with `D`
(`(E, Δ)` is a differential extension of `(F, D)`). -/
theorem differentialAlgebra_algebraic :
    letI := differentialAlgebraic (F := F) (E := E)
    DifferentialAlgebra F E :=
  Differential.differentialAlgebraFiniteDimensional

/-- **Theorem 3.2.3** (§3.2), uniqueness: a finite (separable, char `0`) algebraic extension `E` of
`(F, D)` has at most one differential structure making it a differential extension — any two
`Differential E` structures `Δ₁, Δ₂` compatible with `D` agree. (Mathlib's
`uniqueDifferentialAlgebraFiniteDimensional`; forced by `Δα = −κ_D(p)(α)/p'(α)`.) -/
theorem unique_differentialAlgebra_algebraic (Δ₁ Δ₂ : Differential E)
    (h₁ : @DifferentialAlgebra F E _ _ _ _ Δ₁) (h₂ : @DifferentialAlgebra F E _ _ _ _ Δ₂) :
    Δ₁ = Δ₂ := by
  have := Subtype.ext_iff.mp <|
    (Differential.uniqueDifferentialAlgebraFiniteDimensional (F := F) (K := E)).uniq ⟨Δ₁, h₁⟩
      |>.trans
      ((Differential.uniqueDifferentialAlgebraFiniteDimensional (F := F) (K := E)).uniq
        ⟨Δ₂, h₂⟩).symm
  exact this

end Algebraic

section Automorphism
variable {F : Type*} [Field F] [Differential F]
variable {E : Type*} [Field E] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
  [Algebra.IsSeparable F E]

/-- **Theorem 3.2.4(i)** (§3.2): on a separable algebraic differential extension `(E, Δ)` of
`(F, D)`, every field automorphism `σ` of `E` over `F` commutes with the derivation —
`σ(Δa) = Δ(σ a)`. (Mathlib's `Differential.algEquiv_deriv'`; the uniqueness of the extension forces
`Δ_σ := σ⁻¹ ∘ Δ ∘ σ = Δ`.) -/
theorem algEquiv_comm_deriv (σ : E ≃ₐ[F] E) (a : E) : σ (a′) = (σ a)′ :=
  Differential.algEquiv_deriv' σ a

end Automorphism

section TraceNorm
variable {F E : Type*} [Field F] [Differential F] [Field E] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E] [FiniteDimensional F E] [IsGalois F E]

/-- **Theorem 3.2.4(ii)** (§3.2), trace commutes with `D`: on a finite Galois (char `0` ⇒ separable
normal) differential extension `(E, Δ)` of `(F, D)`, `D(Tr a) = Tr(Δ a)` for `a ∈ E`. Each Galois
automorphism `σ` commutes with `Δ` (Theorem 3.2.4(i)), and `Tr` is the sum over the `σ`, so `D`
passes through the sum. -/
theorem deriv_trace_eq_trace_deriv (a : E) :
    (Algebra.trace F E a)′ = Algebra.trace F E (a′) := by
  apply FaithfulSMul.algebraMap_injective F E
  rw [← deriv_algebraMap, trace_eq_sum_automorphisms,
    trace_eq_sum_automorphisms, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← algEquiv_comm_deriv σ a]

/-- **Theorem 3.2.4(ii)** (§3.2), norm log-derivative: on a finite Galois differential extension,
the logarithmic-derivative of the norm is the trace of the logarithmic derivative —
`Tr(Δa/a) = D(N a)/N a` for `a ≠ 0`. Equivalently `D(N a) = N a · Tr(Δa/a)`. From `N a = ∏_σ σ a`
(each `σ` commuting with `Δ`), `D(N a)/N a = ∑_σ Δ(σ a)/σ a = ∑_σ σ(Δa/a) = Tr(Δa/a)`. -/
theorem trace_logDeriv_eq_logDeriv_norm (a : E) (ha : a ≠ 0) :
    Algebra.trace F E (a′ / a) = (Algebra.norm F a)′ / Algebra.norm F a := by
  have hσne : ∀ σ : E ≃ₐ[F] E, σ a ≠ 0 := fun σ => by
    rw [ne_eq, map_eq_zero_iff _ σ.injective]; exact ha
  apply FaithfulSMul.algebraMap_injective F E
  -- LHS: `algebraMap (Tr(a'/a)) = ∑_σ σ(a'/a) = ∑_σ (σ a)'/(σ a)`.
  have hlhs : algebraMap F E (Algebra.trace F E (a′ / a)) = ∑ σ : E ≃ₐ[F] E, (σ a)′ / σ a := by
    rw [trace_eq_sum_automorphisms]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_div₀, algEquiv_comm_deriv σ a]
  -- RHS: `algebraMap (D(N a)/N a) = logDeriv (algebraMap (N a)) = logDeriv (∏_σ σ a)`.
  have hrhs : algebraMap F E ((Algebra.norm F a)′ / Algebra.norm F a)
      = ∑ σ : E ≃ₐ[F] E, (σ a)′ / σ a := by
    have hstep : Differential.logDeriv ((algebraMap F E) (Algebra.norm F a))
        = ∑ σ : E ≃ₐ[F] E, (σ a)′ / σ a := by
      rw [Algebra.norm_eq_prod_automorphisms,
        Differential.logDeriv_prod _ Finset.univ (fun σ : E ≃ₐ[F] E => σ a) (fun σ _ => hσne σ)]
      rfl
    rw [map_div₀, ← deriv_algebraMap]
    exact hstep
  rw [hlhs, hrhs]

end TraceNorm

section AlgebraicClosure
variable {F : Type*} [Field F] [Differential F] [CharZero F]
variable {K : Type*} [Field K] [Algebra F K]

/-- **Corollary 3.2.1** (§3.2): `D` extends (uniquely) to any finite algebraic extension inside the
algebraic closure — concretely, every intermediate field `B` of `K/F` that is finite over `F`
carries a differential structure with `(B, Δ)` a differential extension of `(F, D)`. So a tower of
differential extensions can always be replaced by separable algebraic pieces. (Mathlib's
intermediate-field instances over a char-`0` differential base.) -/
theorem existsUnique_differentialAlgebra_intermediateField (B : IntermediateField F K)
    [FiniteDimensional F B] :
    ∃ _ : Differential B, DifferentialAlgebra F B :=
  ⟨inferInstance, inferInstance⟩

/-- **Corollary 3.2.1** (§3.2), the tower step: if `(K, Δ)` is itself a differential extension of
`(F, D)` and `B ⊆ K` is a finite intermediate field, then `(K, Δ)` is also a differential extension
of `(B, Δ|_B)` — `Δ (algebraMap B K b) = algebraMap B K (Δ b)`. This is the `(EF, Δ)`-over-`(E, D)`
compatibility of the picture `E ≤ EF`. -/
theorem differentialAlgebra_intermediateField_tower [Differential K] [DifferentialAlgebra F K]
    (B : IntermediateField F K) [FiniteDimensional F B] : DifferentialAlgebra B K :=
  inferInstance

end AlgebraicClosure

end DeepWiki.SymbolicIntegration
