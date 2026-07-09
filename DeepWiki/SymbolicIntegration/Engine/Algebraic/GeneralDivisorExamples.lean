import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralDivisor

/-! # Fractional ideal divisors on the cuspidal cubic

Executable checks for `GenDivisor` on `y³ = x²` with integral basis `[1, y, y²/x]`. -/

namespace DeepWiki.SymbolicIntegration

open CPoly

/-! ### `div(y)` and `div(y²)` as fractional `O`-ideals -/

/-- The principal divisor `div(y) = y·O` on `y³ = x²`. -/
def gdDivY : GenDivisor := principalDivisor gcuspCubicF gcuspCubicBasis gcuspCubicY

/-- The principal divisor `div(y²) = y²·O` on `y³ = x²`. -/
def gdDivYsq : GenDivisor := principalDivisor gcuspCubicF gcuspCubicBasis gcuspCubicYsq

/-- The identity divisor `O` on `y³ = x²`. -/
def gdIdentity : GenDivisor := idealIdentity (cdeg gcuspCubicF)

-- Sanity print: the integral basis `[1, y, y²/x]`.
#eval gcuspCubicBasis.map (fun b => b.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ))))

-- Sanity print: `div(y)` as a `[w]`-coordinate matrix over `ℚ(x)`.
#eval gdDivY.map (fun row => row.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ))))

-- Sanity print: `div(y²)` as a `[w]`-coordinate matrix over `ℚ(x)`.
#eval gdDivYsq.map (fun row => row.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ))))

-- Sanity print: `div(y) · div(y)`.
#eval (idealProduct gcuspCubicF gcuspCubicBasis gdDivY gdDivY).map
  (fun row => row.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ))))

/-! ### The integral basis is genuinely non-trivial (`native_decide`) -/

/-- The integral basis of `y³ = x²` is `[1, y, y²/x]`, not the power basis. -/
theorem gd_integralBasis_nontrivial :
    (cisZero (csub (gcuspCubicBasis.getD 2 []) [CField.zero, CField.zero, qxOfFrac [1] [0, 1] (by decide)])
      && cisZero (csub (gcuspCubicBasis.getD 0 []) [CField.one])
      && cisZero (csub (gcuspCubicBasis.getD 1 []) [CField.zero, CField.one])) = true := by
  native_decide

/-! ### The Pic group law `div(y)·div(y) = div(y²)` on `y³ = x²` (`native_decide`) -/

/-- The Pic group law `div(y) · div(y) = div(y²)` on `y³ = x²`. -/
theorem gd_pic_grouplaw_divY_sq :
    idealEq (idealProduct gcuspCubicF gcuspCubicBasis gdDivY gdDivY) gdDivYsq = true := by native_decide

/-! ### The identity law `I·O = I` (`native_decide`) -/

/-- The Pic identity law `div(y) · O = div(y)`. -/
theorem gd_pic_identity_divY :
    idealEq (idealProduct gcuspCubicF gcuspCubicBasis gdDivY gdIdentity) gdDivY = true := by native_decide

/-- The Pic identity law `div(y²) · O = div(y²)`. -/
theorem gd_pic_identity_divYsq :
    idealEq (idealProduct gcuspCubicF gcuspCubicBasis gdDivYsq gdIdentity) gdDivYsq = true := by
  native_decide

/-! ### Integrality of the principal divisors (`native_decide`) -/

/-- `div(y)` and `div(y²)` are integral fractional ideals. -/
theorem gd_divY_divYsq_integral :
    (idealIsIntegral gdDivY && idealIsIntegral gdDivYsq) = true := by native_decide

/-! ### The end-to-end general-divisor milestone (`native_decide`) -/

/-- The general-curve divisor representation validates on `y³ = x²`. -/
theorem gen_divisor_representation_validates :
    -- the integral basis is genuinely non-trivial (not the power basis)
    (cisZero (csub (gcuspCubicBasis.getD 2 [])
        [CField.zero, CField.zero, qxOfFrac [1] [0, 1] (by decide)]))
    -- the Pic group law div(y)·div(y) = div(y²)
    ∧ idealEq (idealProduct gcuspCubicF gcuspCubicBasis gdDivY gdDivY) gdDivYsq = true
    -- the identity law I·O = I for two principal divisors
    ∧ idealEq (idealProduct gcuspCubicF gcuspCubicBasis gdDivY gdIdentity) gdDivY = true
    ∧ idealEq (idealProduct gcuspCubicF gcuspCubicBasis gdDivYsq gdIdentity) gdDivYsq = true
    -- the principal divisors are integral
    ∧ (idealIsIntegral gdDivY && idealIsIntegral gdDivYsq) = true := by native_decide

/-! ### Axiom audit (`#print axioms`) -/

#print axioms gd_integralBasis_nontrivial
#print axioms gd_pic_grouplaw_divY_sq
#print axioms gd_pic_identity_divY
#print axioms gd_pic_identity_divYsq
#print axioms gd_divY_divYsq_integral
#print axioms gen_divisor_representation_validates

end DeepWiki.SymbolicIntegration
