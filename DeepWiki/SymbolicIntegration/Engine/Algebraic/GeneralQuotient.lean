import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralSetup
import DeepWiki.SymbolicIntegration.Engine.RischDE.TowerGlue

/-! # Quotient API for general algebraic-function carriers

Quotient facts for `K(x)[y]/(f)`: the curve ideal `afIdeal`, transport of `afReduce`/`afMul`
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

/-- `afReduce` preserves the quotient modulo `afIdeal f`. -/
theorem mk_toPolyG_afReduce (f p : DensePoly α) (hf : cnorm f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (afReduce f p))
      = Ideal.Quotient.mk (afIdeal f) (toPoly p) := by
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  have hid := toPolyG_cmodWf p f hf
  have hsub : toPoly (afReduce f p) - toPoly p
      = - (toPoly (cdivWf p f) * toPoly f) := by
    show toPoly (cmodWf p f) - toPoly p = _
    linear_combination -hid
  rw [hsub]
  exact neg_mem (mul_curve_mem f _)

/-- `afMul` realizes multiplication in the quotient modulo `afIdeal f`. -/
theorem mk_toPolyG_afMul (f a b : DensePoly α) (hf : cnorm f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (afMul f a b))
      = Ideal.Quotient.mk (afIdeal f) (toPoly a)
        * Ideal.Quotient.mk (afIdeal f) (toPoly b) := by
  rw [afMul, mk_toPolyG_afReduce f _ hf]
  simp only [denote, map_mul]

variable [CDiffField α] [CDiffFieldSpec α]

/-- `afFx` reads as coefficientwise base derivation through `toPoly`. -/
theorem mapCoeffs_toPolyG_eq_afFx (f : DensePoly α) :
    Differential.mapCoeffs (toPoly f) = toPoly (afFx f) := by
  exact (toPolyG_cmapDeriv f).symm

end DensePoly

end DeepWiki.SymbolicIntegration
