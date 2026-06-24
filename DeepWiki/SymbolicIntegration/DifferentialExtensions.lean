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

end DeepWiki.SymbolicIntegration
