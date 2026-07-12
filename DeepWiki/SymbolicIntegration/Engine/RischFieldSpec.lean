import DeepWiki.SymbolicIntegration.Engine.IntegrateTowerCorrectG

/-! # Abstract soundness spec `CRischFieldSpec` for the field-level RDE oracle

`CRischFieldSpec α` asserts that a successful `CRischField.crischDESolve b g = some y` yields the
field-level Risch-DE identity `(toK y)′ + (toK b)·(toK y) = toK g` over `K = CFieldSpec.K α`, with the
constant base instance over `ℚ`, the pure-integration residual `D(∫R) = R`, and the cleared-to-field
layer bridge `rischDE_field_of_cleared`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

/-! ### The `CRischFieldSpec` class

The abstract soundness of the field-level RDE oracle, read through `CFieldSpec.toK` into the genuine
field `K = CFieldSpec.K α` with `′` the `CDiffFieldSpec` derivation. -/

/-- Abstract soundness of the field-level RDE oracle `CRischField.crischDESolve`: whenever
`crischDESolve b g = some y`, the returned `y` solves `Dy + b·y = g` over `K = CFieldSpec.K α`,
read through `toK`: `(toK y)′ + (toK b)·(toK y) = toK g`, with `′` the `CDiffFieldSpec`
derivation. Carried as a typeclass so the tower recursion threads it. -/
class CRischFieldSpec (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CRischField α] where
  /-- A successful solve returns a genuine field-level RDE solution `(toK y)′ + (toK b)·(toK y) = toK g`. -/
  crischDESolve_spec : ∀ b g y : α, CRischField.crischDESolve b g = some y →
    @Differential.deriv _ _ CDiffFieldSpec.diffK (CFieldSpec.toK y)
        + CFieldSpec.toK b * CFieldSpec.toK y
      = CFieldSpec.toK g

/-! ### The constant base instance `CRischFieldSpec ℚ` -/

/-- `CRischFieldSpec ℚ`, the constant-field base soundness: over `ℚ` (`D = 0`, `toK = id`) the
oracle is `crischDESolve b g = g/b` (`b ≠ 0`) or `0` (`b = 0 ∧ g = 0`), and the spec `0 + b·y = g`
is the division soundness `b·(g/b) = g`. -/
instance instCRischFieldSpecQ : CRischFieldSpec ℚ where
  crischDESolve_spec b g y hsolve := by
    -- `crischDESolve b g = if b = 0 then (if g = 0 then some 0 else none) else some (g / b)`.
    show @Differential.deriv _ _ CDiffFieldSpec.diffK (id y) + id b * id y = id g
    -- the `ℚ` derivation is `0`, `toK = id`.
    have hderiv : @Differential.deriv _ _ (CDiffFieldSpec.diffK (α := ℚ)) (id y) = 0 := by
      show @Differential.deriv _ _ instDifferentialQ y = 0
      show (0 : Derivation ℤ ℚ ℚ) y = 0
      rw [Derivation.coe_zero]; rfl
    rw [hderiv, zero_add]
    show id b * id y = id g
    simp only [id_eq]
    -- `crischDESolve b g = if b = 0 then (if g = 0 then some 0 else none) else some (g / b)`.
    simp only [CRischField.crischDESolve] at hsolve
    by_cases hb : b = 0
    · -- `b = 0`: the solve is `if g = 0 then some 0 else none`, so `g = 0`, `y = 0`.
      rw [if_pos hb] at hsolve
      by_cases hg : g = 0
      · rw [if_pos hg, Option.some.injEq] at hsolve
        rw [hb, ← hsolve, hg]; ring
      · rw [if_neg hg] at hsolve; exact absurd hsolve (by simp)
    · -- `b ≠ 0`: the solve is `some (g / b)`, so `y = g / b` and `b·(g/b) = g`.
      rw [if_neg hb, Option.some.injEq] at hsolve
      rw [← hsolve, mul_div_cancel₀ g hb]

/-! ### The pure-integration residual `D(∫R) = R`

For the pure-integration RDE `Dy = R` (`b = 0`), a successful base-oracle solve gives the
antiderivative identity `D(∫R) = R` lifted to the tower fraction field, for an arbitrary
residual `R : α`. -/

section ResidualDischarge

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CRischField α] [CRischFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]

omit [CRischField α] [CRischFieldSpec α] in
/-- `towerFractionFieldDeriv Dt (am α (C k)) = am α (C k′)`: the tower fraction-field derivation
of a constant is the constant of its `CDiffFieldSpec` derivative. -/
theorem towerFractionFieldDerivG_amG_C (Dt : DensePoly α) (k : CFieldSpec.K α) :
    towerFractionFieldDeriv Dt (am α (Polynomial.C k))
      = am α (Polynomial.C (@Differential.deriv _ _ CDiffFieldSpec.diffK k)) := by
  rw [towerFractionFieldDeriv, am, extendDeriv_algebraMap, Differential.implicitDeriv_C]

/-- The pure-integration residual `D(∫R) = R`: if `crischDESolve 0 R = some intR`, the constant
`intR` embedded into the tower fraction field as `am (C (toK intR))` differentiates back to
`am (C (toK R))`. This is the base-oracle identity used by residual-feedback normal reduction. -/
theorem crischDESolve_zero_intDeriv (Dt : DensePoly α) (R intR : α)
    (hsolve : CRischField.crischDESolve (CCommRing.zero : α) R = some intR) :
    towerFractionFieldDeriv Dt (am α (Polynomial.C (CFieldSpec.toK intR)))
      = am α (Polynomial.C (CFieldSpec.toK R)) := by
  rw [towerFractionFieldDerivG_amG_C]
  -- the `b = 0` spec: `(toK intR)′ + (toK 0)·(toK intR) = toK R`, and `toK 0 = 0`.
  have hspec := CRischFieldSpec.crischDESolve_spec (CCommRing.zero : α) R intR hsolve
  rw [CFieldSpec.toK_zero, zero_mul, add_zero] at hspec
  rw [hspec]

end ResidualDischarge

/-! ### The cleared-to-field layer bridge for the RDE oracle

Translates the cleared polynomial identity over `(CFieldSpec.K α)[X]` (the shape
`cRischDEG_rdeCleared_gen` outputs) into the field-level RDE identity over
`RatFunc (CFieldSpec.K α)`, via the quotient rule `towerFractionFieldDerivG_div`. -/

section ClearedToField

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

open DensePoly

/-- Cleared-to-field layer bridge for the RDE oracle: given the cleared polynomial identity of
`cRischDEG_rdeCleared_gen` (with `D = implicitDeriv (toPoly Dt)`) and the denominators `fden`,
`gden`, `yden` nonzero, the field-level Risch-DE identity
`towerFractionFieldDeriv Dt (am ynum/am yden) + (am fnum/am fden)·(am ynum/am yden)
= am gnum/am gden` holds over `RatFunc (CFieldSpec.K α)`. -/
theorem rischDE_field_of_cleared (Dt fnum fden gnum gden ynum yden : DensePoly α)
    (hfden : toPoly fden ≠ 0) (hgden : toPoly gden ≠ 0) (hyden : toPoly yden ≠ 0)
    (hcleared : am α (toPoly gden) * am α (toPoly fden)
          * (am α (Differential.implicitDeriv (toPoly Dt) (toPoly ynum)) * am α (toPoly yden)
              - am α (toPoly ynum) * am α (Differential.implicitDeriv (toPoly Dt) (toPoly yden)))
        + am α (toPoly gden) * am α (toPoly fnum) * am α (toPoly ynum) * am α (toPoly yden)
      = am α (toPoly gnum) * am α (toPoly fden) * am α (toPoly yden) ^ 2) :
    towerFractionFieldDeriv Dt (am α (toPoly ynum) / am α (toPoly yden))
        + am α (toPoly fnum) / am α (toPoly fden)
          * (am α (toPoly ynum) / am α (toPoly yden))
      = am α (toPoly gnum) / am α (toPoly gden) := by
  -- nonzero readings
  have hFDne : am α (toPoly fden) ≠ 0 := am_ne_zero hfden
  have hGDne : am α (toPoly gden) ≠ 0 := am_ne_zero hgden
  have hYDne : am α (toPoly yden) ≠ 0 := am_ne_zero hyden
  -- the quotient rule reads `D(YN/YD) = (am(D ynum)·YD − YN·am(D yden))/YD²`
  rw [towerFractionFieldDerivG_div, div_mul_div_comm,
    div_add_div _ _ (pow_ne_zero 2 hYDne) (mul_ne_zero hFDne hYDne),
    div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hYDne) (mul_ne_zero hFDne hYDne)) hGDne]
  ring_nf
  ring_nf at hcleared
  linear_combination am α (toPoly yden) * hcleared

end ClearedToField

/-! ### Recursive `CRischFieldSpec (DenseFrac β)` layer boundary

The cleared → field half is supplied by `rischDE_field_of_cleared`; a recursive instance over
`DenseFrac β` also needs a structural decomposition theorem for the generic RDE pipeline. -/

end DeepWiki.SymbolicIntegration
