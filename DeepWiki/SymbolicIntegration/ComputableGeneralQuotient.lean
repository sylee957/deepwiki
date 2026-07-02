import DeepWiki.SymbolicIntegration.ComputableGeneralSetup
import DeepWiki.SymbolicIntegration.Computable.RischDE.TowerGlue

/-! # Quotient API for general algebraic-function carriers

Quotient facts for `K(x)[y]/(f)`: the curve ideal `afIdeal`, transport of `afReduce`/`afMul`
through `Ideal.Quotient.mk`, and the `toPolyG` readings of the partial derivatives. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α]

/-- The curve ideal `(toPolyG f)` for the carrier `K[X] ⧸ (toPolyG f)`. -/
noncomputable def afIdeal (f : CPolyG α) : Ideal (CFieldSpec.K α)[X] :=
  Ideal.span {toPolyG f}

/-- Any multiple of `toPolyG f` lies in `afIdeal f`. -/
theorem mul_curve_mem (f : CPolyG α) (c : (CFieldSpec.K α)[X]) :
    c * toPolyG f ∈ afIdeal f :=
  Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))

/-- `afReduce` preserves the quotient modulo `afIdeal f`. -/
theorem mk_toPolyG_afReduce (f p : CPolyG α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afReduce f p))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG p) := by
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  have hid := toPolyG_cmodWf p f hf
  have hsub : toPolyG (afReduce f p) - toPolyG p
      = - (toPolyG (cdivWf p f) * toPolyG f) := by
    show toPolyG (cmodWf p f) - toPolyG p = _
    linear_combination -hid
  rw [hsub]
  exact neg_mem (mul_curve_mem f _)

/-- `afMul` realizes multiplication in the quotient modulo `afIdeal f`. -/
theorem mk_toPolyG_afMul (f a b : CPolyG α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f a b))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG a)
        * Ideal.Quotient.mk (afIdeal f) (toPolyG b) := by
  rw [afMul, mk_toPolyG_afReduce f _ hf, toPolyG_cmulG, map_mul]

variable [CDiffField α] [CDiffFieldSpec α]

/-- `afFx` reads as coefficientwise base derivation through `toPolyG`. -/
theorem mapCoeffs_toPolyG_eq_afFx (f : CPolyG α) :
    Differential.mapCoeffs (toPolyG f) = toPolyG (afFx f) := by
  rw [afFx, ← cmapDeriv, toPolyG_cmapDeriv]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `afFy` reads as the formal derivative through `toPolyG`. -/
theorem derivative_toPolyG_eq_afFy (f : CPolyG α) :
    Polynomial.derivative (toPolyG f) = toPolyG (afFy f) := by
  rw [afFy, toPolyG_cderivG]

end CPolyG

end DeepWiki.SymbolicIntegration
