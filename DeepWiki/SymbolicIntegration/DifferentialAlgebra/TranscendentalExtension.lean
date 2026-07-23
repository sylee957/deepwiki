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
@[reducible] private noncomputable def ratFuncDifferentialOfValue (w : RatFunc F) :
    Differential (RatFunc F) :=
  let d₀ := (ratFuncCoefficientDifferential (F := F)).deriv
  let dX := (inferInstance : Differential (RatFunc F)).deriv
  ⟨d₀ + w • dX⟩

/-- `ratFuncDifferentialOfValue w` extends the differential structure on `F`. -/
private theorem ratFuncDifferentialOfValue_algebraMap (w : RatFunc F) (a : F) :
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
private theorem ratFuncDifferentialOfValue_X (w : RatFunc F) :
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

/-- The differential extension on `F(X)` assigning the prescribed derivative to `X`. -/
noncomputable def ratFuncExtensionOfValue (w : RatFunc F) :
    DifferentialExtension F (RatFunc F) := by
  let Δ := ratFuncDifferentialOfValue w
  have hΔ : @DifferentialAlgebra F (RatFunc F) _ _ _ _ Δ :=
    ⟨fun a => ratFuncDifferentialOfValue_algebraMap w a⟩
  exact ⟨Δ, hΔ⟩

/-- `ratFuncExtensionOfValue w` sends `X` to `w`. -/
theorem ratFuncExtensionOfValue_X (w : RatFunc F) :
    (ratFuncExtensionOfValue w).deriv (RatFunc.X : RatFunc F) = w :=
  ratFuncDifferentialOfValue_X w

/-- Differential extensions of `F(X)` are determined by their value on `X`. -/
theorem DifferentialExtension.ratFunc_ext
    {Δ₁ Δ₂ : DifferentialExtension F (RatFunc F)}
    (hX : Δ₁.deriv (RatFunc.X : RatFunc F) = Δ₂.deriv RatFunc.X) :
    Δ₁ = Δ₂ := by
  apply DifferentialExtension.ext
  apply unique_derivation_rationalFunction (F := F) (K := RatFunc F)
  · intro c
    rw [RatFunc.algebraMap_C]
    exact (Δ₁.deriv_algebraMap c).trans (Δ₂.deriv_algebraMap c).symm
  · simpa only [RatFunc.algebraMap_X] using hX

/-- Formal `d/dX` on `F(X)` as an extension of a zero differential on `F`. -/
noncomputable def ratFuncFormalExtension (hzero : ∀ a : F, a′ = 0) :
    DifferentialExtension F (RatFunc F) := by
  let Δ : Differential (RatFunc F) := inferInstance
  have hΔ : @DifferentialAlgebra F (RatFunc F) _ _ _ _ Δ :=
    ⟨fun a => by
      change ratFuncDeriv (RatFunc.C a) = algebraMap F (RatFunc F) (a′)
      rw [ratFuncDeriv_C_eq_zero, hzero, map_zero]⟩
  exact ⟨Δ, hΔ⟩

/-- The derivation of `ratFuncFormalExtension` is the quotient-rule derivative `d/dX`. -/
theorem ratFuncFormalExtension_apply (hzero : ∀ a : F, a′ = 0) (f : RatFunc F) :
    (ratFuncFormalExtension hzero).deriv f = ratFuncDeriv f :=
  rfl

/-- Formal `d/dX` sends the rational-function generator `X` to one. -/
theorem ratFuncFormalExtension_X (hzero : ∀ a : F, a′ = 0) :
    (ratFuncFormalExtension hzero).deriv (RatFunc.X : RatFunc F) = 1 := by
  rw [ratFuncFormalExtension_apply, show (RatFunc.X : RatFunc F) =
    algebraMap F[X] (RatFunc F) X by exact RatFunc.algebraMap_X.symm,
    ratFuncDeriv_algebraMap, derivative_X, map_one]

/-- The only extension of a zero differential to `F(X)` sending `X` to one is `d/dX`. -/
theorem differentialExtension_eq_ratFuncFormal_of_X_eq_one
    (hzero : ∀ a : F, a′ = 0) (Δ : DifferentialExtension F (RatFunc F))
    (hX : Δ.deriv (RatFunc.X : RatFunc F) = 1) :
    Δ = ratFuncFormalExtension hzero :=
  DifferentialExtension.ratFunc_ext (hX.trans (ratFuncFormalExtension_X hzero).symm)

end RationalFunction

section Adjoin

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable [Differential F]

/-- Differential extensions on `F⟮t⟯` are determined by their value on the generator. -/
theorem DifferentialExtension.adjoin_ext
    (t : E) {Δ₁ Δ₂ : DifferentialExtension F (F⟮t⟯)}
    (hgen : Δ₁.deriv (IntermediateField.AdjoinSimple.gen F t) =
      Δ₂.deriv (IntermediateField.AdjoinSimple.gen F t)) :
    Δ₁ = Δ₂ := by
  apply DifferentialExtension.ext
  apply Derivation.ext
  rintro ⟨x, hx⟩
  apply IntermediateField.adjoin_induction F (p := fun y hy =>
    Δ₁.deriv (⟨y, hy⟩ : F⟮t⟯) = Δ₂.deriv ⟨y, hy⟩)
  · intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact hgen
  · intro a
    exact (Δ₁.deriv_algebraMap a).trans (Δ₂.deriv_algebraMap a).symm
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

/-- The differential structure on `F⟮t⟯` extending `F` and assigning `w` to a transcendental `t`. -/
@[reducible] private noncomputable def transcendentalAdjoinDifferential
    (t : E) (ht : Transcendental F t) (w : F⟮t⟯) : Differential (F⟮t⟯) :=
  let e := RatFunc.algEquivOfTranscendental t ht
  let Δ := ratFuncExtensionOfValue (e.symm w)
  letI : Differential (RatFunc F) := Δ.toDifferential
  Differential.equiv e.symm.toRingEquiv

/-- `transcendentalAdjoinDifferential t ht w` extends the differential structure on `F`. -/
private theorem transcendentalAdjoinDifferential_algebraMap
    (t : E) (ht : Transcendental F t) (w : F⟮t⟯) (a : F) :
    (transcendentalAdjoinDifferential t ht w).deriv (algebraMap F (F⟮t⟯) a) =
      algebraMap F (F⟮t⟯) (a′) := by
  let e := RatFunc.algEquivOfTranscendental t ht
  change e ((ratFuncExtensionOfValue (e.symm w)).deriv
    (e.symm (algebraMap F (F⟮t⟯) a))) = algebraMap F (F⟮t⟯) (a′)
  rw [e.symm.commutes, DifferentialExtension.deriv_algebraMap, e.commutes]

/-- `transcendentalAdjoinDifferential t ht w` sends the adjoined generator to `w`. -/
private theorem transcendentalAdjoinDifferential_gen
    (t : E) (ht : Transcendental F t) (w : F⟮t⟯) :
    (transcendentalAdjoinDifferential t ht w).deriv
      (IntermediateField.AdjoinSimple.gen F t) = w := by
  let e := RatFunc.algEquivOfTranscendental t ht
  change e ((ratFuncExtensionOfValue (e.symm w)).deriv
    (e.symm (IntermediateField.AdjoinSimple.gen F t))) = w
  rw [RatFunc.algEquivOfTranscendental_symm_gen, ratFuncExtensionOfValue_X,
    e.apply_symm_apply]

/-- The differential extension on `F⟮t⟯` assigning `w` to a transcendental generator `t`. -/
noncomputable def transcendentalAdjoinExtension
    (t : E) (ht : Transcendental F t) (w : F⟮t⟯) :
    DifferentialExtension F (F⟮t⟯) := by
  let Δ := transcendentalAdjoinDifferential t ht w
  have hΔ : @DifferentialAlgebra F (F⟮t⟯) _ _ _ _ Δ :=
    ⟨fun a => transcendentalAdjoinDifferential_algebraMap t ht w a⟩
  exact ⟨Δ, hΔ⟩

/-- `transcendentalAdjoinExtension t ht w` sends the adjoined generator to `w`. -/
theorem transcendentalAdjoinExtension_gen
    (t : E) (ht : Transcendental F t) (w : F⟮t⟯) :
    (transcendentalAdjoinExtension t ht w).deriv
      (IntermediateField.AdjoinSimple.gen F t) = w :=
  transcendentalAdjoinDifferential_gen t ht w

/-- Formal `d/dt` on `F⟮t⟯`, transported from `d/dX` when the base differential is zero. -/
noncomputable def transcendentalFormalExtension
    (t : E) (ht : Transcendental F t) (hzero : ∀ a : F, a′ = 0) :
    DifferentialExtension F (F⟮t⟯) := by
  let e := RatFunc.algEquivOfTranscendental t ht
  let Δ := ratFuncFormalExtension hzero
  letI : Differential (RatFunc F) := Δ.toDifferential
  let δ : Differential (F⟮t⟯) := Differential.equiv e.symm.toRingEquiv
  have hδ : @DifferentialAlgebra F (F⟮t⟯) _ _ _ _ δ :=
    ⟨fun a => by
      change e (Δ.deriv (e.symm (algebraMap F (F⟮t⟯) a))) =
        algebraMap F (F⟮t⟯) (a′)
      rw [e.symm.commutes, DifferentialExtension.deriv_algebraMap, e.commutes]⟩
  exact ⟨δ, hδ⟩

/-- Formal `d/dt` sends the adjoined transcendental generator to one. -/
theorem transcendentalFormalExtension_gen
    (t : E) (ht : Transcendental F t) (hzero : ∀ a : F, a′ = 0) :
    (transcendentalFormalExtension t ht hzero).deriv
      (IntermediateField.AdjoinSimple.gen F t) = 1 := by
  let e := RatFunc.algEquivOfTranscendental t ht
  change e ((ratFuncFormalExtension hzero).deriv
    (e.symm (IntermediateField.AdjoinSimple.gen F t))) = 1
  rw [RatFunc.algEquivOfTranscendental_symm_gen, ratFuncFormalExtension_X, map_one]

/-- The only zero-base extension to `F⟮t⟯` sending transcendental `t` to one is `d/dt`. -/
theorem differentialExtension_eq_transcendentalFormal_of_gen_eq_one
    (t : E) (ht : Transcendental F t) (hzero : ∀ a : F, a′ = 0)
    (Δ : DifferentialExtension F (F⟮t⟯))
    (hgen : Δ.deriv (IntermediateField.AdjoinSimple.gen F t) = 1) :
    Δ = transcendentalFormalExtension t ht hzero :=
  DifferentialExtension.adjoin_ext t
    (hgen.trans (transcendentalFormalExtension_gen t ht hzero).symm)

/-- The coefficient differential extension on `F⟮t⟯`, for which `t` is constant. -/
noncomputable def transcendentalCoefficientExtension
    (t : E) (ht : Transcendental F t) :
    DifferentialExtension F (F⟮t⟯) :=
  transcendentalAdjoinExtension t ht 0

/-- The adjoined generator is constant for the coefficient differential extension. -/
theorem transcendentalCoefficientExtension_gen
    (t : E) (ht : Transcendental F t) :
    (transcendentalCoefficientExtension t ht).deriv
      (IntermediateField.AdjoinSimple.gen F t) = 0 :=
  transcendentalAdjoinExtension_gen t ht 0

/-- The coefficient extension differentiates an evaluated polynomial coefficientwise. -/
theorem transcendentalCoefficientExtension_aeval
    (t : E) (ht : Transcendental F t) (p : F[X]) :
    (transcendentalCoefficientExtension t ht).deriv
        (aeval (IntermediateField.AdjoinSimple.gen F t) p) =
      aeval (IntermediateField.AdjoinSimple.gen F t) (Differential.mapCoeffs p) := by
  let Δ := transcendentalCoefficientExtension t ht
  letI : Differential (F⟮t⟯) := Δ.toDifferential
  haveI : DifferentialAlgebra F (F⟮t⟯) := Δ.differentialAlgebra
  change (aeval (IntermediateField.AdjoinSimple.gen F t) p)′ =
    aeval (IntermediateField.AdjoinSimple.gen F t) (Differential.mapCoeffs p)
  rw [deriv_aeval_eq_extensions, show (IntermediateField.AdjoinSimple.gen F t)′ = 0 by
    exact transcendentalCoefficientExtension_gen t ht, mul_zero, add_zero]

/-- An extension making a transcendental generator constant is the coefficient extension. -/
theorem differentialExtension_eq_transcendentalCoefficient_of_gen_eq_zero
    (t : E) (ht : Transcendental F t) (Δ : DifferentialExtension F (F⟮t⟯))
    (hgen : Δ.deriv (IntermediateField.AdjoinSimple.gen F t) = 0) :
    Δ = transcendentalCoefficientExtension t ht :=
  DifferentialExtension.adjoin_ext t
    (hgen.trans (transcendentalCoefficientExtension_gen t ht).symm)

/-- A transcendental simple extension admits a unique differential extension sending `t` to `w`. -/
theorem existsUnique_differentialAdjoin_of_transcendental
    (t : E) (ht : Transcendental F t) (w : F⟮t⟯) :
    ∃! Δ : DifferentialExtension F (F⟮t⟯),
      Δ.deriv (IntermediateField.AdjoinSimple.gen F t) = w := by
  let Δ₀ := transcendentalAdjoinExtension t ht w
  have hgen : Δ₀.deriv (IntermediateField.AdjoinSimple.gen F t) = w :=
    transcendentalAdjoinExtension_gen t ht w
  refine ⟨Δ₀, hgen, ?_⟩
  intro Δ hΔ
  exact DifferentialExtension.adjoin_ext t (hΔ.trans hgen.symm)

end Adjoin

end DeepWiki.SymbolicIntegration
