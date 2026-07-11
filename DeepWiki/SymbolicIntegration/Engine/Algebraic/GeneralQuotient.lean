import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralSetup
import DeepWiki.SymbolicIntegration.Engine.RischDE.TowerGlue

/-! # Quotient API for general algebraic-function carriers

Quotient facts for `K(x)[y]/(f)`: the curve ideal `afIdeal`, transport of `CPoly.reduceMod`/`CPoly.mulMod`
through `Ideal.Quotient.mk`, and the `toPoly` readings of the partial derivatives. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace DensePoly

variable {α : Type*} [CField α] [CFieldSpec α]

/-- The curve ideal `(toPoly f)` for the carrier `K[X] ⧸ (toPoly f)`. -/
noncomputable def afIdeal (f : DensePoly α) : Ideal (CFieldSpec.K α)[X] :=
  Ideal.span {toPoly f}

/-- Any multiple of `toPoly f` lies in `afIdeal f`. -/
theorem mul_curve_mem (f : DensePoly α) (c : (CFieldSpec.K α)[X]) :
    c * toPoly f ∈ afIdeal f :=
  Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))

/-- `CPoly.reduceMod` preserves the quotient modulo `afIdeal f`. -/
theorem mk_toPoly_reduceMod (f p : DensePoly α) (hf : cnorm f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (CPoly.reduceMod f p))
      = Ideal.Quotient.mk (afIdeal f) (toPoly p) := by
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  have hfnz : CPoly.toPoly f ≠ 0 := fun h =>
    hf ((cnormG_eq_nil_iff f).mpr (by simpa only [toPoly_list_eq] using h))
  have hid : toPoly p = toPoly (CPolyEuclidean.div p f) * toPoly f +
      toPoly (CPoly.reduceMod f p) := by
    simpa only [CPoly.reduceMod, toPoly_list_eq] using
      LawfulCPolyEuclidean.divmod_spec (P := DensePoly) p f hfnz
  have hsub : toPoly (CPoly.reduceMod f p) - toPoly p
      = - (toPoly (CPolyEuclidean.div p f) * toPoly f) := by
    linear_combination -hid
  rw [hsub]
  exact neg_mem (mul_curve_mem f _)

/-- `CPoly.mulMod` realizes multiplication in the quotient modulo `afIdeal f`. -/
theorem mk_toPoly_mulMod (f a b : DensePoly α) (hf : cnorm f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (CPoly.mulMod f a b))
      = Ideal.Quotient.mk (afIdeal f) (toPoly a)
        * Ideal.Quotient.mk (afIdeal f) (toPoly b) := by
  rw [CPoly.mulMod, mk_toPoly_reduceMod f _ hf]
  rw [show toPoly (CPolyEngine.mul a b) = toPoly a * toPoly b from by
    simpa only [toPoly_list_eq] using LawfulCPolyEngine.toPoly_mul a b, map_mul]

variable [CDiffField α] [CDiffFieldSpec α]

/-- `afFx` reads as coefficientwise base derivation through `toPoly`. -/
theorem mapCoeffs_toPolyG_eq_afFx (f : DensePoly α) :
    Differential.mapCoeffs (toPoly f) = toPoly (afFx f) := by
  exact (toPolyG_cmapDeriv f).symm

end DensePoly

end DeepWiki.SymbolicIntegration
