import Mathlib.FieldTheory.Differential.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # A derivation on the algebraic closure (`Differential (AlgebraicClosure K)`)

Mathlib's differential-field library extends a derivation to any **finite** extension
(`differentialFiniteDimensional`) but stops there. The Risch LRT soundness `IsIntegralResultLrtG` is stated
`∀ E [IsAlgClosed E] [Differential E] …` — to instantiate it at a concrete algebraically-closed extension we
need `Differential (AlgebraicClosure K)`, which Mathlib lacks. This file builds it: every element of the
algebraic closure lies in a finite simple subextension `K⟮x⟯` (which has a canonical derivation), and those
derivations glue (uniqueness of the extension) into a global one.

The key that makes this work (rather than needing the full colimit machinery): `Derivation.algHom_deriv` —
an injective differential-algebra hom commutes with `′` on separable elements — so the value `derivAt x`
(computed in `K⟮x⟯`) agrees with the derivation of *any* finite intermediate field containing `x`
(`derivAt_eq_val_deriv`). The derivation laws then reduce any finite set of elements to the common finite
subextension `K⟮x, y⟯`, where the canonical `differentialFiniteDimensional` derivation is a genuine
`Derivation`. Char 0 gives the separability. -/

namespace DeepWiki.SymbolicIntegration.DifferentialAlgClosure

open IntermediateField Differential Polynomial

variable {K : Type*} [Field K] [Differential K] [CharZero K]

/-- Every element of the algebraic closure generates a finite-dimensional simple subextension. -/
instance finiteDim_adjoin_simple (x : AlgebraicClosure K) : FiniteDimensional K K⟮x⟯ :=
  adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral

/-- The derivation value at an algebraic element `x`, computed inside its finite simple extension `K⟮x⟯`
(which carries the canonical `differentialFiniteDimensional` derivation) and mapped back. -/
noncomputable def derivAt (x : AlgebraicClosure K) : AlgebraicClosure K :=
  K⟮x⟯.val (Differential.deriv (⟨x, mem_adjoin_simple_self K x⟩ : K⟮x⟯))

/-- **Compatibility (the crux).** `derivAt x` agrees with the derivation of *any* finite intermediate field
`B ∋ x`, mapped back to the closure — because the inclusion `K⟮x⟯ ↪ B` is an injective differential-algebra
hom and `x` is separable (char 0), so `algHom_deriv` commutes it with `′`. This lets the derivation laws
reduce every finite set of elements to a common finite subextension. -/
theorem derivAt_eq_val_deriv (B : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K B]
    (x : AlgebraicClosure K) (hx : x ∈ B) :
    derivAt x = B.val (Differential.deriv (⟨x, hx⟩ : B)) := by
  have hle : K⟮x⟯ ≤ B := adjoin_simple_le_iff.mpr hx
  have hsep : IsSeparable K (⟨x, mem_adjoin_simple_self K x⟩ : K⟮x⟯) :=
    Algebra.IsSeparable.isSeparable K _
  have hcompat := algHom_deriv (A := K) (IntermediateField.inclusion hle)
    (IntermediateField.inclusion_injective hle) (⟨x, mem_adjoin_simple_self K x⟩ : K⟮x⟯) hsep
  unfold derivAt
  have hxeq : (⟨x, hx⟩ : B) = IntermediateField.inclusion hle ⟨x, mem_adjoin_simple_self K x⟩ := rfl
  have hval : ∀ z : K⟮x⟯, B.val (IntermediateField.inclusion hle z) = K⟮x⟯.val z := fun _ => rfl
  rw [hxeq, ← hcompat, hval]

omit [Differential K] [CharZero K] in
/-- The finite intermediate field `K⟮x, y⟯ = adjoin K {x, y}` containing both `x` and `y`. -/
private theorem finiteDim_adjoin_pair (x y : AlgebraicClosure K) :
    FiniteDimensional K (IntermediateField.adjoin K {x, y}) :=
  IntermediateField.finiteDimensional_adjoin
    (fun z _ => (Algebra.IsAlgebraic.isAlgebraic (R := K) z).isIntegral)

/-- **`derivAt` is additive.** Reduce `x`, `y`, `x + y` to the common finite field `K⟮x, y⟯` (compatibility),
where the canonical derivation is a genuine `Derivation` and hence additive. -/
theorem derivAt_add (x y : AlgebraicClosure K) : derivAt (x + y) = derivAt x + derivAt y := by
  letI := finiteDim_adjoin_pair x y
  set B := IntermediateField.adjoin K {x, y}
  have hxB : x ∈ B := IntermediateField.subset_adjoin K _ (by simp)
  have hyB : y ∈ B := IntermediateField.subset_adjoin K _ (by simp)
  have hxyB : x + y ∈ B := B.add_mem hxB hyB
  rw [derivAt_eq_val_deriv B x hxB, derivAt_eq_val_deriv B y hyB, derivAt_eq_val_deriv B (x + y) hxyB,
    show (⟨x + y, hxyB⟩ : B) = ⟨x, hxB⟩ + ⟨y, hyB⟩ from rfl, map_add, map_add]

/-- **`derivAt` satisfies the Leibniz rule.** Reduce to the common finite field `K⟮x, y⟯`, where the
canonical derivation is a `Derivation`. -/
theorem derivAt_mul (x y : AlgebraicClosure K) :
    derivAt (x * y) = x * derivAt y + y * derivAt x := by
  letI := finiteDim_adjoin_pair x y
  set B := IntermediateField.adjoin K {x, y}
  have hxB : x ∈ B := IntermediateField.subset_adjoin K _ (by simp)
  have hyB : y ∈ B := IntermediateField.subset_adjoin K _ (by simp)
  have hxyB : x * y ∈ B := B.mul_mem hxB hyB
  have cx : B.val (⟨x, hxB⟩ : B) = x := rfl
  have cy : B.val (⟨y, hyB⟩ : B) = y := rfl
  rw [derivAt_eq_val_deriv B x hxB, derivAt_eq_val_deriv B y hyB, derivAt_eq_val_deriv B (x * y) hxyB,
    show (⟨x * y, hxyB⟩ : B) = ⟨x, hxB⟩ * ⟨y, hyB⟩ from rfl, Derivation.leibniz, smul_eq_mul,
    smul_eq_mul, map_add, map_mul, map_mul, cx, cy]

/-- **`derivAt` sends `0` to `0`** (from additivity). -/
theorem derivAt_zero : derivAt (0 : AlgebraicClosure K) = 0 := by
  have h := derivAt_add (0 : AlgebraicClosure K) 0
  rw [add_zero] at h
  exact add_left_cancel (a := derivAt (0 : AlgebraicClosure K)) (by rw [add_zero]; exact h.symm)

/-- **`derivAt` sends `1` to `0`.** -/
theorem derivAt_one : derivAt (1 : AlgebraicClosure K) = 0 := by
  letI := finiteDim_adjoin_pair (1 : AlgebraicClosure K) 1
  set B := IntermediateField.adjoin K {(1 : AlgebraicClosure K), 1}
  have h1B : (1 : AlgebraicClosure K) ∈ B := IntermediateField.subset_adjoin K _ (by simp)
  rw [derivAt_eq_val_deriv B 1 h1B, show (⟨1, h1B⟩ : B) = 1 from rfl,
    Derivation.map_one_eq_zero, map_zero]

/-- **The derivation on the algebraic closure**, extending `K`'s. -/
noncomputable def closureDerivation : Derivation ℤ (AlgebraicClosure K) (AlgebraicClosure K) where
  toFun := derivAt
  map_add' := derivAt_add
  map_smul' n a := by
    -- `derivAt` is additive (an `AddMonoidHom`), hence automatically `ℤ`-linear.
    show derivAt (n • a) = n • derivAt a
    exact (AddMonoidHom.mk' derivAt derivAt_add).toIntLinearMap.map_smul n a
  leibniz' a b := by
    show derivAt (a * b) = a • derivAt b + b • derivAt a
    rw [derivAt_mul, smul_eq_mul, smul_eq_mul]
  map_one_eq_zero' := derivAt_one

/-- **`Differential (AlgebraicClosure K)`** — a derivation on the algebraic closure extending `K`'s,
built by gluing the finite-subextension derivations. Un-blocks instantiating the LRT soundness
`IsIntegralResultLrtG` (`∀ E [IsAlgClosed E] [Differential E] …`) at `E = AlgebraicClosure K`. -/
noncomputable instance instDifferentialAlgebraicClosure : Differential (AlgebraicClosure K) where
  deriv := closureDerivation

/-- **`DifferentialAlgebra K (AlgebraicClosure K)`** — the closure derivation restricts to `K`'s on the base
(`(algebraMap a)′ = algebraMap a′`), so `K → AlgebraicClosure K` is a differential-algebra map. This is what
lets a `∀ E [DifferentialAlgebra K E] …` statement (the LRT soundness) be instantiated at the closure. -/
noncomputable instance : DifferentialAlgebra K (AlgebraicClosure K) where
  deriv_algebraMap a := by
    set ā := algebraMap K (AlgebraicClosure K) a with hā
    have hmem : ā ∈ K⟮ā⟯ := mem_adjoin_simple_self K ā
    show derivAt ā = algebraMap K (AlgebraicClosure K) (a′)
    rw [derivAt_eq_val_deriv K⟮ā⟯ ā hmem,
      show (⟨ā, hmem⟩ : K⟮ā⟯) = algebraMap K K⟮ā⟯ a from rfl,
      DifferentialAlgebra.deriv_algebraMap]
    rfl

end DeepWiki.SymbolicIntegration.DifferentialAlgClosure
