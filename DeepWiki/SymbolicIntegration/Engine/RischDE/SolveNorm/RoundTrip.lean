import DeepWiki.SymbolicIntegration.Engine.RischDE.TowerGcdUnit
import DeepWiki.SymbolicIntegration.Engine.RischDE.Structural

/-! # Field round-trip for weak-normalized Risch-DE solving

Pure field algebra for transforming a normalized solution back to the original Risch-DE. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac GBPolyCore

variable {K : Type*} [Field K] (D : Derivation ℤ (RatFunc K) (RatFunc K))

/-- `roundtrip_field`: if `Ỹ` solves `D(Ỹ) + (F − D(Q)/Q)·Ỹ = Q·G` with `Q ≠ 0`, then `Y = Ỹ/Q`
solves `D(Y) + F·Y = G`. -/
theorem roundtrip_field (F G Q Ytilde : RatFunc K) (hQ : Q ≠ 0)
    (hnorm : D Ytilde + (F - D Q / Q) * Ytilde = Q * G) :
    D (Ytilde / Q) + F * (Ytilde / Q) = G := by
  -- quotient rule: `D(Ỹ/Q) = Q⁻¹²·(Q·DỸ − Ỹ·DQ)`, with `•` over `RatFunc K` reading as `*`
  have hquot : D (Ytilde / Q) = (Q * D Ytilde - Ytilde * D Q) / Q ^ 2 := by
    rw [Derivation.leibniz_div, smul_sub, smul_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      div_eq_inv_mul, inv_pow, mul_sub, mul_assoc]
  rw [hquot]
  -- clear `Q` (and `Q²`): everything multiplied through by `Q²` and matched
  have hQ2 : Q ^ 2 ≠ 0 := pow_ne_zero 2 hQ
  field_simp at hnorm ⊢
  -- `hnorm` now reads (cleared) the normalized identity; rearrange to the goal cleared form
  ring_nf at hnorm ⊢
  linear_combination hnorm

end DeepWiki.SymbolicIntegration
