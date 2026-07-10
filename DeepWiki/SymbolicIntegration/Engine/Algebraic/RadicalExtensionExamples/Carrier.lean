import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension

/-! # Carrier validation examples for simple radical extensions

Concrete `native_decide` checks for the `RadElem` carrier, diagonal derivation,
and projection operators.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The carrier validates: `y = √(x³+1)` over `ℚ(x)`

`F = DenseFrac ℚ ≅ ℚ(x)`, `n = 2`, `f = x³+1`: checks `y·y = f` and `D(y) = (3x²/(2(x³+1)))·y`. -/

open RadElem

/-- `y·y = f` over `ℚ(x)`: `y = √(x³+1)` squared in `(DenseFrac ℚ)[y]/(y² − (x³+1))` folds to `f = x³+1`. -/
theorem radGen_sq_eq_radicand :
    DensePoly.cisZero (DensePoly.csub (radMul 2 radicandX3p1 (radGen : RadElem (DenseFrac ℚ)) radGen) [radicandX3p1])
      = true := by native_decide

/-- `D(y) = (3x²/(2(x³+1)))·y` over `ℚ(x)`: the diagonal derivation of `y = √(x³+1)` is `ℓ·y`,
`ℓ = f'/(2f) = 3x²/(2(x³+1))`. -/
theorem radDeriv_radGen_eq :
    DensePoly.cisZero (DensePoly.csub (radDeriv 2 radicandX3p1 (radGen : RadElem (DenseFrac ℚ)))
        [CCommRing.zero, radicandLogDer]) = true := by native_decide

/-- `D(1) = 0` over `ℚ(x)`: the radical derivation annihilates the constant `1`. -/
theorem radDeriv_radOne_eq_zero :
    DensePoly.cisZero (radDeriv 2 radicandX3p1 (radOne : RadElem (DenseFrac ℚ))) = true := by native_decide

/-- Ring sanity `y·1 = y` over `ℚ(x)`: `radMul` with `radOne` is the identity. -/
theorem radMul_radOne_eq :
    DensePoly.cisZero (DensePoly.csub (radMul 2 radicandX3p1 (radGen : RadElem (DenseFrac ℚ)) radOne) radGen)
      = true := by native_decide

/-- Ring sanity `(1+y)·(1+y) = 1 + 2y + f` over `ℚ(x)`: `1 + 2y + y²` folds `y² → f = x³+1`. -/
theorem radMul_onePlusGen_sq :
    DensePoly.cisZero (DensePoly.csub
        (radMul 2 radicandX3p1 [CCommRing.one, CCommRing.one] [(CCommRing.one : DenseFrac ℚ), CCommRing.one])
        [CCommRing.add CCommRing.one radicandX3p1, CCommRing.add CCommRing.one CCommRing.one]) = true := by
  native_decide

/-! #### `Tᵢ` decoupling validates over `√(x³+1)`

`Tᵢ(yʲ) = yʲ·[i=j]`, `Tᵢ ∘ D = D ∘ Tᵢ`, and the `∫(g₀+g₁y)` split, on `α = ℚ(x)`, `n = 2`, `f = x³+1`. -/

/-- `T₁(y) = y`: the projection onto the `y`-power fixes `y = √(x³+1)`. -/
theorem radProj_one_radGen :
    DensePoly.cisZero (DensePoly.csub (radProj 1 (radGen : RadElem (DenseFrac ℚ))) radGen) = true := by native_decide

/-- `T₀(y) = 0`: the projection onto the constant power kills `y`. -/
theorem radProj_zero_radGen :
    DensePoly.cisZero (radProj 0 (radGen : RadElem (DenseFrac ℚ))) = true := by native_decide

/-- `T₁(1) = 0`: the projection onto the `y`-power kills the constant `1`. -/
theorem radProj_one_radOne :
    DensePoly.cisZero (radProj 1 (radOne : RadElem (DenseFrac ℚ))) = true := by native_decide

/-- A mixed element `g = (x³+1) + 3x²·y ∈ ℚ(x)[y]/(y²−(x³+1))` (`g₀ = f`, `g₁ = f'`), test integrand for
the `Tᵢ` decoupling. -/
def mixedElem : RadElem (DenseFrac ℚ) := [radicandX3p1, radicandDeriv]

/-- `T₁ ∘ D = D ∘ T₁` on the mixed element: `T₁(D g) = D(T₁ g)` for `g = (x³+1) + 3x²·y`. -/
theorem radProj_one_radDeriv_comm :
    DensePoly.cisZero (DensePoly.csub
        (radProj 1 (radDeriv 2 radicandX3p1 mixedElem))
        (radDeriv 2 radicandX3p1 (radProj 1 mixedElem))) = true := by native_decide

/-- `T₀ ∘ D = D ∘ T₀` on the mixed element: `T₀(D g) = D(T₀ g)`. -/
theorem radProj_zero_radDeriv_comm :
    DensePoly.cisZero (DensePoly.csub
        (radProj 0 (radDeriv 2 radicandX3p1 mixedElem))
        (radDeriv 2 radicandX3p1 (radProj 0 mixedElem))) = true := by native_decide

/-- The `∫(g₀+g₁y)` split: `D(g) = D(T₀ g) + D(T₁ g)` decomposes additively into `1`- and `y`-components
sharing no power of `y`, so `∫g` reduces to `∫g₀ + ∫g₁y` independently. -/
theorem radDeriv_decouples :
    DensePoly.cisZero (DensePoly.csub
        (radDeriv 2 radicandX3p1 mixedElem)
        (DensePoly.cadd (radDeriv 2 radicandX3p1 (radProj 0 mixedElem))
          (radDeriv 2 radicandX3p1 (radProj 1 mixedElem)))) = true := by native_decide

/-- The `y`-component of `D(g)` stays in the `y`-component: `D(T₁ g) = T₁(D(T₁ g))`, so the rational
part of `∫g₁y` is `v₁·y`. -/
theorem radDeriv_projOne_stays :
    DensePoly.cisZero (DensePoly.csub
        (radDeriv 2 radicandX3p1 (radProj 1 mixedElem))
        (radProj 1 (radDeriv 2 radicandX3p1 (radProj 1 mixedElem)))) = true := by native_decide

end DeepWiki.SymbolicIntegration
