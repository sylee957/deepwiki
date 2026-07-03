import DeepWiki.SymbolicIntegration.Computable.IntegrateTowerCorrectG

/-! # The tower single-step Hermite identity

The per-step kernel of the inner Hermite loop `cHermiteReduceTowerInnerWf`, over the tower fraction
field `RatFunc (CFieldSpec.K α)` with the monomial derivation `D = implicitDeriv (toPolyG Dt)`
(realized as `towerFractionFieldDerivG Dt`). Ports `hermiteInner_step_ratFunc` — which is specialized
to `d/dx` only through `ratFuncDeriv_algebraMap` — to the tower derivation, whose polynomial-image
bridge is `towerFractionFieldDerivG_div` at `den = 1`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- The tower derivation on a polynomial image: `D_tower(amG p) = amG (D p)` for
`D = implicitDeriv (toPolyG Dt)` (the `den = 1` case of the quotient rule). -/
theorem towerFractionFieldDerivG_amG (Dt : CPolyG α) (p : (CFieldSpec.K α)[X]) :
    towerFractionFieldDerivG Dt (amG α p)
      = amG α (Differential.implicitDeriv (toPolyG Dt) p) := by
  have h := towerFractionFieldDerivG_div Dt p 1
  simpa using h

/-- **The tower Hermite lowering step** (the `cHermiteReduceTowerInnerWf` single step). With
`D = implicitDeriv (toPolyG Dt)`, `U, V ≠ 0`, and the Diophantine relation
`B·(U·DV) + C·V = -A·C((j+1)⁻¹)`, one step drops the `V`-power by one and emits `B/V^(j+1)`:
`amG A/(amG U · amG V^(j+2)) = D_tower(amG B/amG V^(j+1)) + amG(-(C(j+1))·C - U·DB)/(amG U·amG V^(j+1))`.
Ports `hermiteInner_step_ratFunc` to the tower derivation. -/
theorem towerFractionFieldDerivG_hermite_step [CharZero (CFieldSpec.K α)] (Dt : CPolyG α)
    (A B C U V : (CFieldSpec.K α)[X]) (hU : U ≠ 0) (hV : V ≠ 0) (j : ℕ)
    (hrel : B * (U * Differential.implicitDeriv (toPolyG Dt) V) + C * V
        = -A * Polynomial.C (((j : CFieldSpec.K α) + 1)⁻¹)) :
    amG α A / (amG α U * amG α V ^ (j + 2))
      = towerFractionFieldDerivG Dt (amG α B / amG α V ^ (j + 1))
        + amG α (-(Polynomial.C ((j : CFieldSpec.K α) + 1)) * C
              - U * Differential.implicitDeriv (toPolyG Dt) B)
          / (amG α U * amG α V ^ (j + 1)) := by
  set D := Differential.implicitDeriv (toPolyG Dt) with hDdef
  set am := amG α with hamdef
  have hinj : Function.Injective am := RatFunc.algebraMap_injective (CFieldSpec.K α)
  have hu : am U ≠ 0 := (map_ne_zero_iff _ hinj).mpr hU
  have hv : am V ≠ 0 := (map_ne_zero_iff _ hinj).mpr hV
  have hvp : am V ^ (j + 1) ≠ 0 := pow_ne_zero _ hv
  have hn1 : ((j : CFieldSpec.K α) + 1) ≠ 0 := Nat.cast_add_one_ne_zero j
  -- constant casts: `am (C k) = algebraMap K (RatFunc K) k`, and `(j+1)·(j+1)⁻¹ = 1`.
  have e1 : ∀ k : CFieldSpec.K α, am (Polynomial.C k) = algebraMap (CFieldSpec.K α) (RatFunc _) k :=
    fun k => by
      rw [hamdef, amG, ← Polynomial.algebraMap_eq]
      exact (IsScalarTower.algebraMap_apply (CFieldSpec.K α) (CFieldSpec.K α)[X] (RatFunc _) k).symm
  have hc1 : am (Polynomial.C ((j : CFieldSpec.K α) + 1)) = (j : RatFunc (CFieldSpec.K α)) + 1 := by
    rw [e1, map_add, map_natCast, map_one]
  have hκ : ((j : RatFunc (CFieldSpec.K α)) + 1) * am (Polynomial.C ((j : CFieldSpec.K α) + 1)⁻¹) = 1 := by
    rw [e1, ← hc1, e1, ← map_mul, mul_inv_cancel₀ hn1, map_one]
  -- `am`-of-derivation rewrites (the `den = 1` quotient rule).
  have hdB : towerFractionFieldDerivG Dt (am B) = am (D B) := towerFractionFieldDerivG_amG Dt B
  have hdV : towerFractionFieldDerivG Dt (am V) = am (D V) := towerFractionFieldDerivG_amG Dt V
  -- map the polynomial Diophantine relation into the fraction field.
  have hbez : am B * (am U * am (D V)) + am C * am V
      = -am A * am (Polynomial.C ((j : CFieldSpec.K α) + 1)⁻¹) := by
    have h := congrArg am hrel
    rw [map_add, map_mul, map_mul, map_mul, map_mul, map_neg] at h
    exact h
  have hbez2 : ((j : RatFunc (CFieldSpec.K α)) + 1) * (am B * (am U * am (D V)) + am C * am V)
      = -am A := by
    rw [hbez]; linear_combination (-am A) * hκ
  -- the polynomial power rule, mapped into the fraction field.
  have hDVpoly : am (D (V ^ (j + 1)))
      = ((j : RatFunc (CFieldSpec.K α)) + 1) * am V ^ j * am (D V) := by
    rw [hDdef, Derivation.leibniz_pow, Nat.add_sub_cancel, map_nsmul, smul_eq_mul, map_mul,
      map_pow, nsmul_eq_mul]
    push_cast; ring
  -- expand the derivative term via the tower quotient rule.
  have hderiv : towerFractionFieldDerivG Dt (am B / am V ^ (j + 1))
      = (am (D B) * am V ^ (j + 1)
          - am B * (((j : RatFunc (CFieldSpec.K α)) + 1) * am V ^ j * am (D V)))
        / (am V ^ (j + 1)) ^ 2 := by
    have h := towerFractionFieldDerivG_div Dt B (V ^ (j + 1))
    rw [map_pow] at h
    rw [h, hDVpoly]
  rw [hderiv, map_sub, map_mul, map_mul, map_neg, hc1]
  have hA : am A = -((j : RatFunc (CFieldSpec.K α)) + 1) * (am B * (am U * am (D V)) + am C * am V) := by
    linear_combination hbez2
  rw [hA, pow_succ]
  field_simp
  ring

end DeepWiki.SymbolicIntegration
