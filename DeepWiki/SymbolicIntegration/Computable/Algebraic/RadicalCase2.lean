import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalIntegrate
import DeepWiki.SymbolicIntegration.Computable.FuelFreeDiophantine

/-! # Algebraic-function integration: Case 2 reduction validated through `radDeriv`

The `C/(Wᵏy)` partial-fraction step for `W` a squarefree factor of the radicand, re-derived directly
from the diagonal derivation `radDeriv` (`n = 2`, `y² = f`, `h = f/W`):
`radDeriv(Bf/(Wᵏy)) = (B·(½−k)·W'·h)/(Wᵏy) + (B'h + ½Bh')/(W^{k−1}y)`. Lowering `C/(Wᵏy)` solves
`B·(½−k)·W'·h ≡ C (mod W)` with residual `D = (B·(½−k)W'h − C)/W + B'h + ½Bh'`, validated end-to-end
on a branch example `y² = x³−x`, `W = x`, `k = 2`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

namespace CPolyG

variable {α : Type*} [CField α]

/-- Case-2 cofactor (`n = 2`) `radCase2CofactorC k W h C = B`: the degree-`< deg W` polynomial solving
`B·(½−k)·W'·h ≡ C (mod W)` via `cdiophantineGWf ((½−k)W'h) W C`. `h = f/W`, `W'` is `cderivG W`. -/
def radCase2CofactorC (k : ℕ) (W h C : CPolyG α) : CPolyG α :=
  let half : CPolyG α := [CField.div CField.one (cnatCastG 2)]              -- ½
  let coef := cmulG (csubG half [cnatCastG k]) (cmulG (cderivG W) h)        -- (½ − k)·W'·h
  (cdiophantineGWf coef W C).1

/-- Case-2 residual (`n = 2`) `radCase2ResidualC k W h C B = D`: the lowered-`k` numerator
`D = (B·(½−k)W'h − C)/W + B'h + ½Bh'`; `B'` is `cderivG B`, `h'` is `cderivG h`, division by `W` is
`cdivWf`. -/
def radCase2ResidualC (k : ℕ) (W h C B : CPolyG α) : CPolyG α :=
  let half : CPolyG α := [CField.div CField.one (cnatCastG 2)]              -- ½
  let coef := cmulG (csubG half [cnatCastG k]) (cmulG (cderivG W) h)        -- (½ − k)·W'·h
  let topNum := csubG (cmulG B coef) C                                      -- B·(½−k)W'h − C
  let quotient := cdivWf topNum W                                           -- /W
  caddG quotient (caddG (cmulG (cderivG B) h)                              -- + B'h
    (cmulG half (cmulG B (cderivG h))))                                     -- + ½Bh'

end CPolyG

/-! #### Case 2 validated through `radDeriv`: `y² = x³−x`, `W = x`, `k = 2`

Radicand `y² = f = x³ − x`, squarefree factor `W = x`, `h = f/W = x² − 1`, `k = 2`, `C = 1`; the
congruence gives `B = 2/3` and residual `D = −x/3`, dropping the multiplicity `k = 2 → 1`. -/

open CPolyG

/-- Example radicand `f = x³ − x = x(x−1)(x+1)` (`y² = f`, squarefree), `ℚ[x]` `[0,−1,0,1]`. -/
def case2cF : CPolyG ℚ := [0, -1, 0, 1]

/-- Example squarefree factor `W = x` (a branch place of `√(x³−x)`), `[0,1]`. -/
def case2cW : CPolyG ℚ := [0, 1]

/-- Example cofactor `h = f/W = x² − 1`, `[−1,0,1]`. -/
def case2cH : CPolyG ℚ := [-1, 0, 1]

/-- Example numerator `C = 1`, `[1]`. -/
def case2cC : CPolyG ℚ := [1]

/-- The Case-2 cofactor `B` for `B·(½−2)·W'·h ≡ 1 (mod x)` — expected `B = 2/3`. -/
def case2cB : CPolyG ℚ := radCase2CofactorC 2 case2cW case2cH case2cC

/-- The Case-2 residual `D` — expected `−x/3` (multiplicity dropped `k = 2 → 1`). -/
def case2cD : CPolyG ℚ := radCase2ResidualC 2 case2cW case2cH case2cC case2cB

/-- The cofactor is `B = 2/3`: `cisZeroG (case2cB − 2/3)`. -/
theorem case2c_cofactor_eq :
    cisZeroG (csubG case2cB [(2/3 : ℚ)]) = true := by native_decide

/-- The residual is `D = −x/3`, dropping the multiplicity `k = 2 → 1`. -/
theorem case2c_residual_eq :
    cisZeroG (csubG case2cD [(0 : ℚ), -1/3]) = true := by native_decide

/-- The Case-2 congruence `B·(½−k)·W'·h − C ≡ 0 (mod W)` holds: `cmodWf (B·(½−k)W'h − C) W` vanishes. -/
theorem case2c_congruence :
    cisZeroG (cmodWf
      (csubG (cmulG case2cB
        (cmulG (csubG [CField.div CField.one (cnatCastG 2)] [cnatCastG 2])
          (cmulG (cderivG case2cW) case2cH))) case2cC)
      case2cW) = true := by native_decide

/-- The Case-2 cleared identity `B·(½−k)W'h − C + W·(B'h + ½Bh') = W·D` in `ℚ[x]` (`B = 2/3`, `D = −x/3`). -/
theorem case2c_cleared_identity :
    cisZeroG (csubG
      (caddG
        (csubG (cmulG case2cB
          (cmulG (csubG [CField.div CField.one (cnatCastG 2)] [cnatCastG 2])
            (cmulG (cderivG case2cW) case2cH))) case2cC)
        (cmulG case2cW
          (caddG (cmulG (cderivG case2cB) case2cH)
            (cmulG [CField.div CField.one (cnatCastG 2)] (cmulG case2cB (cderivG case2cH))))))
      (cmulG case2cW case2cD)) = true := by native_decide

/-! #### The end-to-end `radDeriv` validation

Over `(QFunNZG ℚ)[y]/(y² − (x³−x))`, the rational part `v = Bf/(Wᵏy)`, integrand `C/(Wᵏy)`, and residual
`D/(W^{k−1}y)` lift to pure-`y` elements, and `radDeriv 2 (x³−x)` confirms `D(v) = C/(Wᵏy) + D/(W^{k−1}y)`. -/

/-- The radicand `f = x³ − x` lifted to `ℚ(x)` (`QFunNZG ℚ`) for `radDeriv 2`. -/
def case2cFqx : QFunNZG ℚ := qxOfNum [0, -1, 0, 1]

/-- `Wᵏ = x²` as a `ℚ[x]` polynomial (`k = 2`). -/
def case2cWk : CPolyG ℚ := cpowG case2cW 2

/-- The rational part `v = Bf/(Wᵏy)` lifted to the pure-`y` element `[0, (Bf/Wᵏ)/f] ∈ RadElem (QFunNZG ℚ)`. -/
def case2cVlift : RadElem (QFunNZG ℚ) :=
  [CField.zero,
    CField.div (qxOfNum (cmulG case2cB case2cF))
      (qxOfNum (cmulG case2cWk case2cF))]

/-- The integrand rational part `C/(Wᵏy) + D/(W^{k−1}y)` lifted to the pure-`y` element
`[0, (C/Wᵏ)/f + (D/W^{k−1})/f] ∈ RadElem (QFunNZG ℚ)` (what `radDeriv(v)` equals). -/
def case2cRatLift : RadElem (QFunNZG ℚ) :=
  [CField.zero,
    CField.add
      (CField.div (qxOfNum case2cC) (qxOfNum (cmulG case2cWk case2cF)))
      (CField.div (qxOfNum case2cD) (qxOfNum (cmulG case2cW case2cF)))]

/-- Case 2 integrates `∫ 1/(x²·√(x³−x))`: over `(QFunNZG ℚ)[y]/(y² − (x³−x))`, `radDeriv 2 (x³−x)` of the
rational part `v = Bf/(W²√(x³−x))` equals `C/(W²√(x³−x)) + D/(W·√(x³−x))`. -/
theorem case2cDriver_integrates :
    radIsZero (radSub (radDeriv 2 case2cFqx case2cVlift) case2cRatLift) = true := by native_decide

end DeepWiki.SymbolicIntegration
