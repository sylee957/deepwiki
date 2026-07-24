import DeepWiki.SymbolicIntegration.DifferentialAlgebra.AlgebraicExtensions
import DeepWiki.SymbolicIntegration.DifferentialAlgebra.RationalFunctionDerivative

/-! # Quadratic differential extensions

Unique differential structures and implicit derivatives for square-root extensions.
-/

open scoped Differential IntermediateField

namespace DeepWiki.SymbolicIntegration

/-- A square root over a characteristic-zero differential field generates a unique differential extension. -/
theorem existsUnique_differentialAdjoin_of_sq_eq
    {F E : Type*} [Field F] [Differential F] [CharZero F]
    [Field E] [Algebra F E] {x : F} {α : E}
    (hα : α ^ 2 = algebraMap F E x) :
    ∃! Δ : Differential (F⟮α⟯), IsDifferentialExtension F (F⟮α⟯) Δ := by
  have hαF : IsIntegral F α := IsIntegral.of_pow (n := 2) (by decide) (by
    rw [hα]
    exact isIntegral_algebraMap)
  letI : FiniteDimensional F (F⟮α⟯) :=
    IntermediateField.adjoin.finiteDimensional hαF
  exact existsUnique_differentialExtension_finiteSeparable

/-- Differentiating `α² = x` with `x′ = 1` gives `2 * α * α′ = 1`. -/
theorem two_mul_mul_deriv_eq_one_of_sq_eq
    {F E : Type*} [Field F] [Differential F]
    [Field E] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
    {x : F} {α : E} (hx : x′ = 1) (hα : α ^ 2 = algebraMap F E x) :
    2 * α * α′ = 1 := by
  have hd := congrArg (fun z : E => z′) hα
  rw [deriv_pow, deriv_algebraMap, hx, map_one] at hd
  norm_num at hd
  exact hd

/-- Over characteristic zero, `α² = x` and `x′ = 1` imply `α′ = 1 / (2 * α)`. -/
theorem deriv_eq_one_div_two_mul_of_sq_eq
    {F E : Type*} [Field F] [Differential F] [CharZero F]
    [Field E] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
    {x : F} {α : E} (hx : x′ = 1) (hα : α ^ 2 = algebraMap F E x) :
    α′ = 1 / (2 * α) := by
  have hxne : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact zero_ne_one hx
  have hαne : α ≠ 0 := by
    intro h
    apply hxne
    apply (algebraMap F E).injective
    rw [← hα, h]
    norm_num
  have h2 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (map_ne_zero (algebraMap F E)).2 (by norm_num)
  have hd := two_mul_mul_deriv_eq_one_of_sq_eq hx hα
  rw [eq_div_iff (mul_ne_zero h2 hαne)]
  linear_combination hd

/-- A compatible derivation on `F⟮α⟯` sends its square-root generator to `1 / (2 * α)`. -/
theorem DifferentialExtension.adjoin_gen_deriv_eq_one_div_two_mul_of_sq_eq
    {F E : Type*} [Field F] [Differential F] [CharZero F]
    [Field E] [Algebra F E] {x : F} {α : E}
    (hx : x′ = 1) (hα : α ^ 2 = algebraMap F E x)
    (Δ : DifferentialExtension F (F⟮α⟯)) :
    Δ.deriv (IntermediateField.AdjoinSimple.gen F α) =
      1 / (2 * IntermediateField.AdjoinSimple.gen F α) := by
  letI : Differential (F⟮α⟯) := Δ.toDifferential
  haveI : DifferentialAlgebra F (F⟮α⟯) := Δ.differentialAlgebra
  apply deriv_eq_one_div_two_mul_of_sq_eq hx
  apply Subtype.ext
  change α ^ 2 = algebraMap F E x
  exact hα

end DeepWiki.SymbolicIntegration
