import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalIntegrate
import DeepWiki.SymbolicIntegration.Engine.FuelFreeDiophantine

/-! # Algebraic-function integration: Case 2 reduction validated through `radDeriv`

The `C/(Wᵏy)` partial-fraction step for `W` a squarefree factor of the radicand, re-derived directly
from the diagonal derivation `radDeriv` (`n = 2`, `y² = f`, `h = f/W`):
`radDeriv(Bf/(Wᵏy)) = (B·(½−k)·W'·h)/(Wᵏy) + (B'h + ½Bh')/(W^{k−1}y)`. Lowering `C/(Wᵏy)` solves
`B·(½−k)·W'·h ≡ C (mod W)` with residual `D = (B·(½−k)W'h − C)/W + B'h + ½Bh'`, validated end-to-end
on a branch example `y² = x³−x`, `W = x`, `k = 2`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem DensePoly

namespace DensePoly

variable {α : Type*} [CField α]

/-- Case-2 cofactor (`n = 2`) `radCase2CofactorC k W h C = B`: the degree-`< deg W` polynomial solving
`B·(½−k)·W'·h ≡ C (mod W)` via `cdiophantine ((½−k)W'h) W C`. `h = f/W`, `W'` is `cderiv W`. -/
def radCase2CofactorC (k : ℕ) (W h C : DensePoly α) : DensePoly α :=
  let half : DensePoly α := [CField.div CCommRing.one (cnatCast 2)]              -- ½
  let coef := cmul (csub half [cnatCast k]) (cmul (cderiv W) h)        -- (½ − k)·W'·h
  (cdiophantine coef W C).1

/-- Case-2 residual (`n = 2`) `radCase2ResidualC k W h C B = D`: the lowered-`k` numerator
`D = (B·(½−k)W'h − C)/W + B'h + ½Bh'`; `B'` is `cderiv B`, `h'` is `cderiv h`, division by `W` is
`cdivWf`. -/
def radCase2ResidualC (k : ℕ) (W h C B : DensePoly α) : DensePoly α :=
  let half : DensePoly α := [CField.div CCommRing.one (cnatCast 2)]              -- ½
  let coef := cmul (csub half [cnatCast k]) (cmul (cderiv W) h)        -- (½ − k)·W'·h
  let topNum := csub (cmul B coef) C                                      -- B·(½−k)W'h − C
  let quotient := cdivWf topNum W                                           -- /W
  cadd quotient (cadd (cmul (cderiv B) h)                              -- + B'h
    (cmul half (cmul B (cderiv h))))                                     -- + ½Bh'

end DensePoly

/-! #### Case 2 validated through `radDeriv`: `y² = x³−x`, `W = x`, `k = 2`

Radicand `y² = f = x³ − x`, squarefree factor `W = x`, `h = f/W = x² − 1`, `k = 2`, `C = 1`; the
congruence gives `B = 2/3` and residual `D = −x/3`, dropping the multiplicity `k = 2 → 1`. -/

open DensePoly

/-- Example radicand `f = x³ − x = x(x−1)(x+1)` (`y² = f`, squarefree), `ℚ[x]` `[0,−1,0,1]`. -/
def case2cF : DensePoly ℚ := [0, -1, 0, 1]

/-- Example squarefree factor `W = x` (a branch place of `√(x³−x)`), `[0,1]`. -/
def case2cW : DensePoly ℚ := [0, 1]

/-- Example cofactor `h = f/W = x² − 1`, `[−1,0,1]`. -/
def case2cH : DensePoly ℚ := [-1, 0, 1]

/-- Example numerator `C = 1`, `[1]`. -/
def case2cC : DensePoly ℚ := [1]

/-- The Case-2 cofactor `B` for `B·(½−2)·W'·h ≡ 1 (mod x)` — expected `B = 2/3`. -/
def case2cB : DensePoly ℚ := radCase2CofactorC 2 case2cW case2cH case2cC

/-- The Case-2 residual `D` — expected `−x/3` (multiplicity dropped `k = 2 → 1`). -/
def case2cD : DensePoly ℚ := radCase2ResidualC 2 case2cW case2cH case2cC case2cB

/-- The cofactor is `B = 2/3`: `cisZero (case2cB − 2/3)`. -/
theorem case2c_cofactor_eq :
    cisZero (csub case2cB [(2/3 : ℚ)]) = true := by native_decide

/-- The residual is `D = −x/3`, dropping the multiplicity `k = 2 → 1`. -/
theorem case2c_residual_eq :
    cisZero (csub case2cD [(0 : ℚ), -1/3]) = true := by native_decide

/-- The Case-2 congruence `B·(½−k)·W'·h − C ≡ 0 (mod W)` holds: `cmodWf (B·(½−k)W'h − C) W` vanishes. -/
theorem case2c_congruence :
    cisZero (cmodWf
      (csub (cmul case2cB
        (cmul (csub [CField.div CCommRing.one (cnatCast 2)] [cnatCast 2])
          (cmul (cderiv case2cW) case2cH))) case2cC)
      case2cW) = true := by native_decide

/-- The Case-2 cleared identity `B·(½−k)W'h − C + W·(B'h + ½Bh') = W·D` in `ℚ[x]` (`B = 2/3`, `D = −x/3`). -/
theorem case2c_cleared_identity :
    cisZero (csub
      (cadd
        (csub (cmul case2cB
          (cmul (csub [CField.div CCommRing.one (cnatCast 2)] [cnatCast 2])
            (cmul (cderiv case2cW) case2cH))) case2cC)
        (cmul case2cW
          (cadd (cmul (cderiv case2cB) case2cH)
            (cmul [CField.div CCommRing.one (cnatCast 2)] (cmul case2cB (cderiv case2cH))))))
      (cmul case2cW case2cD)) = true := by native_decide

/-! #### The end-to-end `radDeriv` validation

Over `(CFrac ℚ)[y]/(y² − (x³−x))`, the rational part `v = Bf/(Wᵏy)`, integrand `C/(Wᵏy)`, and residual
`D/(W^{k−1}y)` lift to pure-`y` elements, and `radDeriv 2 (x³−x)` confirms `D(v) = C/(Wᵏy) + D/(W^{k−1}y)`. -/

/-- The radicand `f = x³ − x` lifted to `ℚ(x)` (`CFrac ℚ`) for `radDeriv 2`. -/
def case2cFqx : CFrac ℚ := qxOfNum [0, -1, 0, 1]

/-- `Wᵏ = x²` as a `ℚ[x]` polynomial (`k = 2`). -/
def case2cWk : DensePoly ℚ := cpow case2cW 2

/-- The rational part `v = Bf/(Wᵏy)` lifted to the pure-`y` element `[0, (Bf/Wᵏ)/f] ∈ RadElem (CFrac ℚ)`. -/
def case2cVlift : RadElem (CFrac ℚ) :=
  [CCommRing.zero,
    CField.div (qxOfNum (cmul case2cB case2cF))
      (qxOfNum (cmul case2cWk case2cF))]

/-- The integrand rational part `C/(Wᵏy) + D/(W^{k−1}y)` lifted to the pure-`y` element
`[0, (C/Wᵏ)/f + (D/W^{k−1})/f] ∈ RadElem (CFrac ℚ)` (what `radDeriv(v)` equals). -/
def case2cRatLift : RadElem (CFrac ℚ) :=
  [CCommRing.zero,
    CCommRing.add
      (CField.div (qxOfNum case2cC) (qxOfNum (cmul case2cWk case2cF)))
      (CField.div (qxOfNum case2cD) (qxOfNum (cmul case2cW case2cF)))]

/-- Case 2 integrates `∫ 1/(x²·√(x³−x))`: over `(CFrac ℚ)[y]/(y² − (x³−x))`, `radDeriv 2 (x³−x)` of the
rational part `v = Bf/(W²√(x³−x))` equals `C/(W²√(x³−x)) + D/(W·√(x³−x))`. -/
theorem case2cDriver_integrates :
    radIsZero (radSub (radDeriv 2 case2cFqx case2cVlift) case2cRatLift) = true := by native_decide

end DeepWiki.SymbolicIntegration
