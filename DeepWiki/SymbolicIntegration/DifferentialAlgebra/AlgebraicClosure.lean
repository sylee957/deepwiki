import DeepWiki.SymbolicIntegration.DifferentialAlgebra.AlgebraicExtensions
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Differential structure on an algebraic closure

The separable-extension API supplies the canonical compatible differential structure in
characteristic zero.
-/

namespace DeepWiki.SymbolicIntegration.DifferentialAlgClosure

variable {K : Type*} [Field K] [Differential K] [CharZero K]

/-- The differential extension of `K` to its algebraic closure. -/
noncomputable def algebraicClosureExtension :
    DifferentialExtension K (AlgebraicClosure K) :=
  differentialExtensionSeparable

/-- The differential structure on `AlgebraicClosure K` extending that on `K`. -/
noncomputable instance instDifferentialAlgebraicClosure :
    Differential (AlgebraicClosure K) :=
  algebraicClosureExtension.toDifferential

/-- The algebraic closure is a differential extension of its base field. -/
noncomputable instance : DifferentialAlgebra K (AlgebraicClosure K) :=
  algebraicClosureExtension.differentialAlgebra

end DeepWiki.SymbolicIntegration.DifferentialAlgClosure
