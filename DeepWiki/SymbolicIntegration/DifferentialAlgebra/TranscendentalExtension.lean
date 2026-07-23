import DeepWiki.SymbolicIntegration.DifferentialAlgebra.FractionField
import DeepWiki.SymbolicIntegration.DifferentialAlgebra.RationalFunctionDerivative
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Simple transcendental differential extensions

Existence and uniqueness of a differential structure on `F⟮t⟯` with prescribed derivative of
the transcendental generator.
-/

open scoped Differential IntermediateField
open Polynomial

namespace DeepWiki.SymbolicIntegration

section RationalFunction

variable {F : Type*} [Field F] [Differential F]

/-- The coefficient derivation on `F[X]`, with `X′ = 0`, as a differential structure. -/
@[reducible] private noncomputable def polynomialCoefficientDifferential : Differential F[X] :=
  ⟨Differential.implicitDeriv 0⟩

/-- The coefficient derivation on `F(X)` obtained by the fraction-field quotient rule. -/
@[reducible] private noncomputable def ratFuncCoefficientDifferential :
    Differential (RatFunc F) :=
  letI : Differential F[X] := polynomialCoefficientDifferential
  FractionRingDeriv.differential (R := F[X]) (K := RatFunc F)

/-- The coefficient derivation on `F[X]` sends `C a` to `C a′`. -/
private theorem polynomialCoefficientDifferential_C (a : F) :
    (polynomialCoefficientDifferential (F := F)).deriv (C a) = C a′ :=
  Differential.implicitDeriv_C 0 a

/-- The coefficient derivation on `F[X]` sends `X` to zero. -/
private theorem polynomialCoefficientDifferential_X :
    (polynomialCoefficientDifferential (F := F)).deriv X = 0 :=
  Differential.implicitDeriv_X 0

/-- The coefficient derivation on `F(X)` sends an embedded `C a` to the embedded `C a′`. -/
private theorem ratFuncCoefficientDifferential_C (a : F) :
    (ratFuncCoefficientDifferential (F := F)).deriv
        (algebraMap F[X] (RatFunc F) (C a)) =
      algebraMap F[X] (RatFunc F) (C a′) := by
  calc
    _ = FractionRingDeriv.deriv
        ((polynomialCoefficientDifferential (F := F)).deriv)
        (algebraMap F[X] (RatFunc F) (C a)) := rfl
    _ = algebraMap F[X] (RatFunc F)
        ((polynomialCoefficientDifferential (F := F)).deriv (C a)) :=
      FractionRingDeriv.deriv_algebraMap (K := RatFunc F)
        ((polynomialCoefficientDifferential (F := F)).deriv) (C a)
    _ = algebraMap F[X] (RatFunc F) (C a′) := by
      rw [polynomialCoefficientDifferential_C]

/-- The coefficient derivation on `F(X)` sends the embedded `X` to zero. -/
private theorem ratFuncCoefficientDifferential_X :
    (ratFuncCoefficientDifferential (F := F)).deriv
        (algebraMap F[X] (RatFunc F) X) = 0 := by
  calc
    _ = FractionRingDeriv.deriv
        ((polynomialCoefficientDifferential (F := F)).deriv)
        (algebraMap F[X] (RatFunc F) X) := rfl
    _ = algebraMap F[X] (RatFunc F)
        ((polynomialCoefficientDifferential (F := F)).deriv X) :=
      FractionRingDeriv.deriv_algebraMap (K := RatFunc F)
        ((polynomialCoefficientDifferential (F := F)).deriv) X
    _ = 0 := by rw [polynomialCoefficientDifferential_X, map_zero]

/-- The differential structure on `F(X)` extending `F` and assigning the prescribed value to `X`. -/
@[reducible] noncomputable def ratFuncDifferentialOfValue (w : RatFunc F) :
    Differential (RatFunc F) :=
  let d₀ := (ratFuncCoefficientDifferential (F := F)).deriv
  let dX := (inferInstance : Differential (RatFunc F)).deriv
  ⟨d₀ + w • dX⟩

/-- `ratFuncDifferentialOfValue w` extends the differential structure on `F`. -/
theorem ratFuncDifferentialOfValue_algebraMap (w : RatFunc F) (a : F) :
    (ratFuncDifferentialOfValue w).deriv (algebraMap F (RatFunc F) a) =
      algebraMap F (RatFunc F) (a′) := by
  rw [show algebraMap F (RatFunc F) a =
    algebraMap F[X] (RatFunc F) (C a) by simp]
  change (ratFuncCoefficientDifferential (F := F)).deriv
      (algebraMap F[X] (RatFunc F) (C a)) +
    w * (inferInstance : Differential (RatFunc F)).deriv
      (algebraMap F[X] (RatFunc F) (C a)) =
      algebraMap F (RatFunc F) (a′)
  rw [ratFuncCoefficientDifferential_C]
  change algebraMap F (RatFunc F) (a′) +
    w * ratFuncDeriv (algebraMap F[X] (RatFunc F) (C a)) =
      algebraMap F (RatFunc F) (a′)
  rw [ratFuncDeriv_algebraMap, derivative_C, map_zero, mul_zero, add_zero]

/-- `ratFuncDifferentialOfValue w` sends `X` to `w`. -/
theorem ratFuncDifferentialOfValue_X (w : RatFunc F) :
    (ratFuncDifferentialOfValue w).deriv (RatFunc.X : RatFunc F) = w := by
  rw [show (RatFunc.X : RatFunc F) = algebraMap F[X] (RatFunc F) X by
    exact RatFunc.algebraMap_X.symm]
  change (ratFuncCoefficientDifferential (F := F)).deriv
      (algebraMap F[X] (RatFunc F) X) +
    w * (inferInstance : Differential (RatFunc F)).deriv
      (algebraMap F[X] (RatFunc F) X) = w
  rw [ratFuncCoefficientDifferential_X]
  change 0 + w * ratFuncDeriv (algebraMap F[X] (RatFunc F) X) = w
  rw [ratFuncDeriv_algebraMap, derivative_X, map_one, mul_one, zero_add]

end RationalFunction

section Adjoin

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Differential structures on `F⟮t⟯` are determined by their values on `F` and on `t`. -/
theorem differential_adjoin_ext (t : E) {Δ₁ Δ₂ : Differential (F⟮t⟯)}
    (hbase : ∀ a : F,
      Δ₁.deriv (algebraMap F (F⟮t⟯) a) = Δ₂.deriv (algebraMap F (F⟮t⟯) a))
    (hgen : Δ₁.deriv (IntermediateField.AdjoinSimple.gen F t) =
      Δ₂.deriv (IntermediateField.AdjoinSimple.gen F t)) :
    Δ₁ = Δ₂ := by
  apply Differential.ext
  apply Derivation.ext
  rintro ⟨x, hx⟩
  apply IntermediateField.adjoin_induction F (p := fun y hy =>
    Δ₁.deriv (⟨y, hy⟩ : F⟮t⟯) = Δ₂.deriv ⟨y, hy⟩)
  · intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact hgen
  · intro a
    exact hbase a
  · intro x y hx hy hxder hyder
    change Δ₁.deriv ((⟨x, hx⟩ : F⟮t⟯) + ⟨y, hy⟩) =
      Δ₂.deriv ((⟨x, hx⟩ : F⟮t⟯) + ⟨y, hy⟩)
    rw [map_add, map_add, hxder, hyder]
  · intro x hx hxder
    change Δ₁.deriv ((⟨x, hx⟩ : F⟮t⟯)⁻¹) =
      Δ₂.deriv ((⟨x, hx⟩ : F⟮t⟯)⁻¹)
    rw [Derivation.leibniz_inv, Derivation.leibniz_inv, hxder]
  · intro x y hx hy hxder hyder
    change Δ₁.deriv ((⟨x, hx⟩ : F⟮t⟯) * ⟨y, hy⟩) =
      Δ₂.deriv ((⟨x, hx⟩ : F⟮t⟯) * ⟨y, hy⟩)
    rw [Derivation.leibniz, Derivation.leibniz, hxder, hyder]

variable [Differential F]

/-- The differential structure on `F⟮t⟯` extending `F` and assigning `w` to a transcendental `t`. -/
@[reducible] noncomputable def transcendentalAdjoinDifferential
    (t : E) (ht : Transcendental F t) (w : F⟮t⟯) : Differential (F⟮t⟯) :=
  let e := RatFunc.algEquivOfTranscendental t ht
  let δ := ratFuncDifferentialOfValue (e.symm w)
  letI : Differential (RatFunc F) := δ
  Differential.equiv e.symm.toRingEquiv

/-- `transcendentalAdjoinDifferential t ht w` extends the differential structure on `F`. -/
theorem transcendentalAdjoinDifferential_algebraMap
    (t : E) (ht : Transcendental F t) (w : F⟮t⟯) (a : F) :
    (transcendentalAdjoinDifferential t ht w).deriv (algebraMap F (F⟮t⟯) a) =
      algebraMap F (F⟮t⟯) (a′) := by
  let e := RatFunc.algEquivOfTranscendental t ht
  change e ((ratFuncDifferentialOfValue (e.symm w)).deriv
    (e.symm (algebraMap F (F⟮t⟯) a))) = algebraMap F (F⟮t⟯) (a′)
  rw [e.symm.commutes, ratFuncDifferentialOfValue_algebraMap, e.commutes]

/-- `transcendentalAdjoinDifferential t ht w` sends the adjoined generator to `w`. -/
theorem transcendentalAdjoinDifferential_gen
    (t : E) (ht : Transcendental F t) (w : F⟮t⟯) :
    (transcendentalAdjoinDifferential t ht w).deriv
      (IntermediateField.AdjoinSimple.gen F t) = w := by
  let e := RatFunc.algEquivOfTranscendental t ht
  change e ((ratFuncDifferentialOfValue (e.symm w)).deriv
    (e.symm (IntermediateField.AdjoinSimple.gen F t))) = w
  rw [RatFunc.algEquivOfTranscendental_symm_gen, ratFuncDifferentialOfValue_X,
    e.apply_symm_apply]

/-- A transcendental simple extension admits a unique differential structure extending `F` and sending `t` to `w`. -/
theorem existsUnique_differentialAdjoin_of_transcendental
    (t : E) (ht : Transcendental F t) (w : F⟮t⟯) :
    ∃! Δ : Differential (F⟮t⟯),
      @DifferentialAlgebra F (F⟮t⟯) _ _ _ _ Δ ∧
        Δ.deriv (IntermediateField.AdjoinSimple.gen F t) = w := by
  let Δ₀ := transcendentalAdjoinDifferential t ht w
  have hAlg : @DifferentialAlgebra F (F⟮t⟯) _ _ _ _ Δ₀ :=
    ⟨fun a => transcendentalAdjoinDifferential_algebraMap t ht w a⟩
  have hgen : Δ₀.deriv (IntermediateField.AdjoinSimple.gen F t) = w :=
    transcendentalAdjoinDifferential_gen t ht w
  refine ⟨Δ₀, ⟨hAlg, hgen⟩, ?_⟩
  intro Δ hΔ
  exact differential_adjoin_ext t
    (fun a => (hΔ.1.deriv_algebraMap a).trans (hAlg.deriv_algebraMap a).symm)
    (hΔ.2.trans hgen.symm)

end Adjoin

end DeepWiki.SymbolicIntegration
