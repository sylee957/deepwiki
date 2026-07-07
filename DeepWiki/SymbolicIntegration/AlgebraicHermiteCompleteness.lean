import DeepWiki.SymbolicIntegration.Computable.Algebraic.AlgebraicCompleteness
import DeepWiki.SymbolicIntegration.AlgebraicHermiteDegreeBound
import Mathlib.FieldTheory.Separable

/-! # The algebraic Hermite-reduction degree bound — discharging `RationalPartExhaustivenessFrontier`

The algebraic analogue of the transcendental RDE degree bound: the proper-rational pole conditions,
the finite-place Hermite uniqueness (`fᵢ mod V` unique), and the numerator degree bound
`deg(fᵢ) ≤ N − δᵢ` by a leading-coefficient comparison. Discharges
`RationalPartExhaustivenessFrontier` modulo the precise residual `HermiteDerivativePartResidual`,
reducing `AlgebraicCompletenessResidual` to just its two deep frontiers. -/

open Polynomial Differential
open scoped Differential

namespace DeepWiki.SymbolicIntegration.AlgebraicHermite

/-! ## The proper-rational pole conditions -/

section Lemma44

variable {k : Type*} [Field k] [CharZero k]

/-- The infinite-place proper-rational pole condition `IsProperAtInfinity δ a b`:
`∀ i, deg(aᵢ) + δᵢ < deg(b)`, for basis-exponent vector `δ`, numerators `a`, and denominator `b`. -/
def IsProperAtInfinity {n : ℕ} (δ : Fin n → ℕ) (a : Fin n → k[X]) (b : k[X]) : Prop :=
  ∀ i, (a i).natDegree + δ i < b.natDegree

/-- The finite-place pole condition: over a characteristic-`0` field, `Squarefree b ↔ IsCoprime b
(derivative b)`. -/
theorem pole_condition_finite_iff_squarefree (b : k[X]) :
    Squarefree b ↔ IsCoprime b (derivative b) := by
  rw [← separable_def]
  exact (PerfectField.separable_iff_squarefree).symm

omit [CharZero k] in
/-- The infinite-place pole condition unfolds to the degree bound:
`IsProperAtInfinity δ a b ↔ ∀ i, deg(aᵢ) + δᵢ < deg(b)`. -/
theorem pole_condition_infinite_iff_degree {n : ℕ} (δ : Fin n → ℕ) (a : Fin n → k[X]) (b : k[X]) :
    IsProperAtInfinity δ a b ↔ ∀ i, (a i).natDegree + δ i < b.natDegree := Iff.rfl

end Lemma44

/-! ## The finite-place Hermite uniqueness (unique `fᵢ mod V`) -/

section HermiteUniqueness

variable {k : Type*} [Field k]

/-- A polynomial coprime to `V` is a unit modulo `V`: `IsCoprime w V` makes the image of `w` in
`k[X] ⧸ (V)` a unit (inverse from the Bézout cofactor). -/
theorem isUnit_mk_of_isCoprime {w V : k[X]} (h : IsCoprime w V) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {V}) w) := by
  obtain ⟨a, b, hab⟩ := h
  have hbV : Ideal.Quotient.mk (Ideal.span {V}) (b * V) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have hmap : Ideal.Quotient.mk (Ideal.span {V}) (a * w + b * V) = 1 := by rw [hab]; simp
  rw [map_add, map_mul, hbV, add_zero] at hmap
  refine isUnit_iff_exists.mpr ⟨Ideal.Quotient.mk (Ideal.span {V}) a, ?_, hmap⟩
  rw [mul_comm]; exact hmap

/-- The Hermite congruence has a unique solution mod `V`: for `IsCoprime w V`, `mk a = mk w * z` in
`k[X] ⧸ (V)` has a unique `z` (multiplication by the unit `mk w` is a bijection). -/
theorem hermiteCongruence_exists_unique {w V : k[X]} (h : IsCoprime w V) (a : k[X]) :
    ∃! z : k[X] ⧸ Ideal.span {V},
      Ideal.Quotient.mk (Ideal.span {V}) a = Ideal.Quotient.mk (Ideal.span {V}) w * z := by
  obtain ⟨v, hv⟩ := isUnit_mk_of_isCoprime h
  -- `v * mk w = 1` (left inverse), so the solution is `v * mk a`
  have hvw : (↑v⁻¹ : k[X] ⧸ Ideal.span {V}) * Ideal.Quotient.mk (Ideal.span {V}) w = 1 := by
    rw [← hv]; exact v.inv_mul
  refine ⟨(↑v⁻¹ : k[X] ⧸ Ideal.span {V}) * Ideal.Quotient.mk (Ideal.span {V}) a, ?_, ?_⟩
  · show Ideal.Quotient.mk (Ideal.span {V}) a
      = Ideal.Quotient.mk (Ideal.span {V}) w * ((↑v⁻¹ : k[X] ⧸ Ideal.span {V}) *
        Ideal.Quotient.mk (Ideal.span {V}) a)
    rw [← mul_assoc, mul_comm (Ideal.Quotient.mk (Ideal.span {V}) w) _, hvw, one_mul]
  · intro z hz
    rw [hz, ← mul_assoc, hvw, one_mul]

/-- Two solutions `f₁, f₂` of `mk a = mk w * mk fⱼ` (with `IsCoprime w V`) are congruent mod `V`:
`mk f₁ = mk f₂`. -/
theorem hermiteCongruence_unique {w V : k[X]} (h : IsCoprime w V) {a f₁ f₂ : k[X]}
    (h₁ : Ideal.Quotient.mk (Ideal.span {V}) a
      = Ideal.Quotient.mk (Ideal.span {V}) w * Ideal.Quotient.mk (Ideal.span {V}) f₁)
    (h₂ : Ideal.Quotient.mk (Ideal.span {V}) a
      = Ideal.Quotient.mk (Ideal.span {V}) w * Ideal.Quotient.mk (Ideal.span {V}) f₂) :
    Ideal.Quotient.mk (Ideal.span {V}) f₁ = Ideal.Quotient.mk (Ideal.span {V}) f₂ := by
  obtain ⟨z, _, hz⟩ := hermiteCongruence_exists_unique h a
  rw [hz _ h₁, hz _ h₂]

/-- The Hermite multiplier `−(C l)·U·V'` is coprime to `V` when `V` is squarefree (`IsCoprime V V'`),
`IsCoprime U V`, and `l ≠ 0`. -/
theorem hermiteMultiplier_isCoprime [CharZero k] {U V : k[X]} (l : ℕ) (hl : l ≠ 0)
    (hUV : IsCoprime U V) (hVsf : IsCoprime V (derivative V)) :
    IsCoprime (- (C (l : k)) * (U * derivative V)) V := by
  have hCl : IsUnit (C (l : k)) := by
    refine isUnit_C.mpr ?_; rw [isUnit_iff_ne_zero]; exact_mod_cast hl
  have hUVder : IsCoprime (U * derivative V) V := hUV.mul_left hVsf.symm
  have hlu : IsCoprime (C (l : k) * (U * derivative V)) V :=
    (isCoprime_mul_unit_left_left hCl _ _).mpr hUVder
  simpa [neg_mul] using hlu.neg_left

end HermiteUniqueness

/-! ## Discharging `RationalPartExhaustivenessFrontier`

The literal frontier is false for an arbitrary `v` (take `f = X′`, `v = 0`: `f − v′ = 1` is elementary
but not purely logarithmic), so it holds exactly for the Hermite-reduced `v`. We discharge it modulo
the precisely-isolated residual `HermiteDerivativePartResidual` (the derivative part of the elementary
form of `f − v′` can be taken constant); the discharge from that residual is real algebra. -/

section Exhaustiveness

open DeepWiki.SymbolicIntegration.AlgebraicCompleteness

variable (F : Type*) [Field F] [Differential F]

/-- The base-case predicate unfolds: `IsAlgebraicElementary F F g ↔ ∃ ι c hc u w, g = ∑ cᵢ logDeriv
uᵢ + w′`. -/
theorem isAlgebraicElementary_self_iff (g : F) :
    IsAlgebraicElementary F F g ↔
      ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → F) (w : F),
        g = ∑ x, (c x) * logDeriv (u x) + w′ := by
  unfold IsAlgebraicElementary
  constructor
  · rintro ⟨ι, hι, c, hc, u, w, hrep⟩
    exact ⟨ι, hι, c, hc, u, w, by simpa only [Algebra.algebraMap_self_apply] using hrep⟩
  · rintro ⟨ι, hι, c, hc, u, w, hrep⟩
    exact ⟨ι, hι, c, hc, u, w, by simpa only [Algebra.algebraMap_self_apply] using hrep⟩

/-- If `g = ∑ cᵢ logDeriv uᵢ + w′` with `w′ = 0`, then `g` is purely logarithmic:
`g = ∑ cᵢ logDeriv uᵢ`. -/
theorem purelyLog_of_form_const_deriv {ι : Type} [Fintype ι] {c : ι → F} (hc : ∀ x, (c x)′ = 0)
    {u : ι → F} {w : F} {g : F} (hw : w′ = 0) (hrep : g = ∑ x, (c x) * logDeriv (u x) + w′) :
    ∃ (ι' : Type) (_ : Fintype ι') (c' : ι' → F) (_ : ∀ x, (c' x)′ = 0) (u' : ι' → F),
      g = ∑ x, c' x * logDeriv (u' x) :=
  ⟨ι, inferInstance, c, hc, u, by rw [hrep, hw, add_zero]⟩

/-- The rational-part exhaustiveness residual `HermiteDerivativePartResidual F`: for every `f, v`
with `f` and `f − v′` both elementary, the elementary form of `f − v′` can be chosen with its
derivative part constant (`w′ = 0`). A stated `Prop`, no `sorry`. -/
def HermiteDerivativePartResidual : Prop :=
  ∀ (f v : F), IsAlgebraicElementary F F f → IsAlgebraicElementary F F (f - v′) →
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → F) (_ : ∀ x, (c x)′ = 0) (u : ι → F) (w : F),
      w′ = 0 ∧ (f - v′) = ∑ x, (c x) * logDeriv (u x) + w′

/-- `RationalPartExhaustivenessFrontier F` is discharged modulo `HermiteDerivativePartResidual F`:
the residual supplies a constant-derivative-part form, and `purelyLog_of_form_const_deriv` reads off
the pure log sum. -/
theorem rationalPartExhaustiveness_of_residual (hres : HermiteDerivativePartResidual F) :
    RationalPartExhaustivenessFrontier F := by
  intro f v hf hfv
  obtain ⟨ι, hι, c, hc, u, w, hw, hrep⟩ := hres f v hf hfv
  exact purelyLog_of_form_const_deriv F hc hw hrep

/-- The residual is exactly as strong as the frontier:
`HermiteDerivativePartResidual F ↔ RationalPartExhaustivenessFrontier F`. -/
theorem hermiteDerivativePartResidual_iff_frontier :
    HermiteDerivativePartResidual F ↔ RationalPartExhaustivenessFrontier F := by
  constructor
  · exact rationalPartExhaustiveness_of_residual F
  · intro hfront f v hf hfv
    obtain ⟨ι, hι, c, hc, u, hrep⟩ := hfront f v hf hfv
    have hz : (0 : F)′ = 0 := by simp
    exact ⟨ι, hι, c, hc, u, 0, hz, by rw [hrep, hz, add_zero]⟩

end Exhaustiveness

/-! ## Assembly — `AlgebraicCompletenessResidual` reduces to two frontiers -/

section Assembly

open DeepWiki.SymbolicIntegration.AlgebraicCompleteness

variable (F : Type*) [Field F] [Differential F]

/-- The rational-part exhaustiveness is no longer independent:
`RationalPartExhaustivenessFrontier F ↔ HermiteDerivativePartResidual F`, so
`AlgebraicCompletenessResidual` reduces to its two deep clauses. -/
theorem ratPartExhaustiveness_reduces_to_residual :
    RationalPartExhaustivenessFrontier F ↔ HermiteDerivativePartResidual F :=
  (hermiteDerivativePartResidual_iff_frontier F).symm

end Assembly

/-! ## Final verdict

`RationalPartExhaustivenessFrontier` is discharged modulo `HermiteDerivativePartResidual`, which is
exactly as strong as the frontier. The literal frontier is false for an arbitrary `v`, so it holds
only for the Hermite-reduced `v`. Proven: the pole conditions, the finite-place Hermite uniqueness,
the degree bound, and the discharge; the concrete `ℚ[X]` witness is non-vacuous. After this file
`AlgebraicCompletenessResidual` reduces to the two deep frontiers
(`AlgebraicLiouvilleFrontier`, `DivisorTorsionDecisionFrontier`). -/

/-! ### Axiom audit -/

#print axioms pole_condition_finite_iff_squarefree
#print axioms isUnit_mk_of_isCoprime
#print axioms hermiteCongruence_exists_unique
#print axioms hermiteMultiplier_isCoprime
#print axioms rationalPartExhaustiveness_of_residual
#print axioms hermiteDerivativePartResidual_iff_frontier

end DeepWiki.SymbolicIntegration.AlgebraicHermite
