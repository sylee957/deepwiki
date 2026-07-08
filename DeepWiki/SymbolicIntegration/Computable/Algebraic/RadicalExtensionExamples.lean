import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalExtension

/-! # Validation examples for simple radical extensions

Concrete `native_decide` checks for the simple radical-extension carrier,
projection, and rational-part reduction routines.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The carrier validates: `y = √(x³+1)` over `ℚ(x)`

`F = QFunNZG ℚ ≅ ℚ(x)`, `n = 2`, `f = x³+1`: checks `y·y = f` and `D(y) = (3x²/(2(x³+1)))·y`. -/

open RadElem

/-- `y·y = f` over `ℚ(x)`: `y = √(x³+1)` squared in `(QFunNZG ℚ)[y]/(y² − (x³+1))` folds to `f = x³+1`. -/
theorem radGen_sq_eq_radicand :
    radIsZero (radSub (radMul 2 radicandX3p1 (radGen : RadElem (QFunNZG ℚ)) radGen) [radicandX3p1])
      = true := by native_decide

/-- `D(y) = (3x²/(2(x³+1)))·y` over `ℚ(x)`: the diagonal derivation of `y = √(x³+1)` is `ℓ·y`,
`ℓ = f'/(2f) = 3x²/(2(x³+1))`. -/
theorem radDeriv_radGen_eq :
    radIsZero (radSub (radDeriv 2 radicandX3p1 (radGen : RadElem (QFunNZG ℚ)))
        [CField.zero, radicandLogDer]) = true := by native_decide

/-- `D(1) = 0` over `ℚ(x)`: the radical derivation annihilates the constant `1`. -/
theorem radDeriv_radOne_eq_zero :
    radIsZero (radDeriv 2 radicandX3p1 (radOne : RadElem (QFunNZG ℚ))) = true := by native_decide

/-- Ring sanity `y·1 = y` over `ℚ(x)`: `radMul` with `radOne` is the identity. -/
theorem radMul_radOne_eq :
    radIsZero (radSub (radMul 2 radicandX3p1 (radGen : RadElem (QFunNZG ℚ)) radOne) radGen)
      = true := by native_decide

/-- Ring sanity `(1+y)·(1+y) = 1 + 2y + f` over `ℚ(x)`: `1 + 2y + y²` folds `y² → f = x³+1`. -/
theorem radMul_onePlusGen_sq :
    radIsZero (radSub
        (radMul 2 radicandX3p1 [CField.one, CField.one] [(CField.one : QFunNZG ℚ), CField.one])
        [CField.add CField.one radicandX3p1, CField.add CField.one CField.one]) = true := by
  native_decide

/-! #### `Tᵢ` decoupling validates over `√(x³+1)`

`Tᵢ(yʲ) = yʲ·[i=j]`, `Tᵢ ∘ D = D ∘ Tᵢ`, and the `∫(g₀+g₁y)` split, on `α = ℚ(x)`, `n = 2`, `f = x³+1`. -/

/-- `T₁(y) = y`: the projection onto the `y`-power fixes `y = √(x³+1)`. -/
theorem radProj_one_radGen :
    radIsZero (radSub (radProj 1 (radGen : RadElem (QFunNZG ℚ))) radGen) = true := by native_decide

/-- `T₀(y) = 0`: the projection onto the constant power kills `y`. -/
theorem radProj_zero_radGen :
    radIsZero (radProj 0 (radGen : RadElem (QFunNZG ℚ))) = true := by native_decide

/-- `T₁(1) = 0`: the projection onto the `y`-power kills the constant `1`. -/
theorem radProj_one_radOne :
    radIsZero (radProj 1 (radOne : RadElem (QFunNZG ℚ))) = true := by native_decide

/-- A mixed element `g = (x³+1) + 3x²·y ∈ ℚ(x)[y]/(y²−(x³+1))` (`g₀ = f`, `g₁ = f'`), test integrand for
the `Tᵢ` decoupling. -/
def mixedElem : RadElem (QFunNZG ℚ) := [radicandX3p1, radicandDeriv]

/-- `T₁ ∘ D = D ∘ T₁` on the mixed element: `T₁(D g) = D(T₁ g)` for `g = (x³+1) + 3x²·y`. -/
theorem radProj_one_radDeriv_comm :
    radIsZero (radSub
        (radProj 1 (radDeriv 2 radicandX3p1 mixedElem))
        (radDeriv 2 radicandX3p1 (radProj 1 mixedElem))) = true := by native_decide

/-- `T₀ ∘ D = D ∘ T₀` on the mixed element: `T₀(D g) = D(T₀ g)`. -/
theorem radProj_zero_radDeriv_comm :
    radIsZero (radSub
        (radProj 0 (radDeriv 2 radicandX3p1 mixedElem))
        (radDeriv 2 radicandX3p1 (radProj 0 mixedElem))) = true := by native_decide

/-- The `∫(g₀+g₁y)` split: `D(g) = D(T₀ g) + D(T₁ g)` decomposes additively into `1`- and `y`-components
sharing no power of `y`, so `∫g` reduces to `∫g₀ + ∫g₁y` independently. -/
theorem radDeriv_decouples :
    radIsZero (radSub
        (radDeriv 2 radicandX3p1 mixedElem)
        (radAdd (radDeriv 2 radicandX3p1 (radProj 0 mixedElem))
          (radDeriv 2 radicandX3p1 (radProj 1 mixedElem)))) = true := by native_decide

/-- The `y`-component of `D(g)` stays in the `y`-component: `D(T₁ g) = T₁(D(T₁ g))`, so the rational
part of `∫g₁y` is `v₁·y`. -/
theorem radDeriv_projOne_stays :
    radIsZero (radSub
        (radDeriv 2 radicandX3p1 (radProj 1 mixedElem))
        (radProj 1 (radDeriv 2 radicandX3p1 (radProj 1 mixedElem)))) = true := by native_decide

/-! #### Case 1 validates: `∫ C/(V²y)` with `y = √x`, `V = x−1`

Radicand `y² = f = x`, `V = x − 1`, `k = 2`, `C = 1` (integrand `1/((x−1)²√x)`): the congruence gives
`B = −1` and residual `D = 1/2` (constant), dropping the multiplicity `2 → 1`; `g = f'/2 = 1/2`. -/

open CPolyG

/-- Case-1 example radicand `f = x` (`y² = x`, `y = √x`), as a `ℚ[x]` polynomial `[0, 1]`. -/
def case1F : CPolyG ℚ := [0, 1]

/-- Case-1 example squarefree denominator factor `V = x − 1` (coprime to `f = x`), `[−1, 1]`. -/
def case1V : CPolyG ℚ := [-1, 1]

/-- Case-1 example numerator `C = 1`, `[1]`. -/
def case1C : CPolyG ℚ := [1]

/-- `V' = (x−1)' = 1` over `ℚ[x]` (`cderivG`, `θ' = 1`, ℚ-constant coefficients). -/
def case1Vder : CPolyG ℚ := cderivG case1V

/-- `g = ((n−1)/n)·f' = (1/2)·1 = 1/2` for `n = 2`, `f = x` squarefree (`(f/y)' = g/y`), `[1/2]`. -/
def case1G : CPolyG ℚ := cscaleG (1/2 : ℚ) (cderivG case1F)

/-- The solved Case-1 cofactor `B` for `−x·B ≡ 1 (mod x−1)` — expected `B = −1`. -/
def case1B : CPolyG ℚ := radCase1Cofactor 2 case1V case1Vder case1F case1C

/-- The Case-1 residual `D` — expected the constant `1/2`. -/
def case1D : CPolyG ℚ :=
  radCase1Residual 2 case1V case1Vder case1F case1G case1B case1C (cderivG case1B)

/-- The cofactor is `B = −1`: `−x·B ≡ 1 (mod x−1)` gives `B = −1`. -/
theorem case1_cofactor_eq :
    cisZeroG (csubG case1B [(-1 : ℚ)]) = true := by native_decide

/-- The Case-1 congruence `(1−k)V'fB − C ≡ 0 (mod V)` holds: `cmodWf ((1−k)V'fB − C) V` vanishes. -/
theorem case1_congruence :
    cisZeroG (cmodWf
      (csubG (cmulG (cnegG [cnatCastG 1]) (cmulG case1Vder (cmulG case1F case1B))) case1C)
      case1V) = true := by native_decide

/-- The Case-1 cleared identity `(1−k)V'fB − C + V·(B'f + Bg) = V·D` in `ℚ[x]` (`B = −1`, `D = 1/2`). -/
theorem case1_cleared_identity :
    cisZeroG (csubG
      (caddG
        (csubG (cmulG (cnegG [cnatCastG 1]) (cmulG case1Vder (cmulG case1F case1B))) case1C)
        (cmulG case1V (caddG (cmulG (cderivG case1B) case1F) (cmulG case1B case1G))))
      (cmulG case1V case1D)) = true := by native_decide

/-- The residual `D = 1/2` has degree `< deg V`, so the multiplicity dropped `k = 2 → 1`. -/
theorem case1_residual_eq :
    cisZeroG (csubG case1D [(1/2 : ℚ)]) = true := by native_decide

/-! #### Case 2 validates: `∫ C/(W²y)` with `y = √(x³−x)`, `W = x`

Radicand `y² = f = x³ − x`, squarefree factor `W = x`, `h = f/W = x² − 1`, `k = 2`, `C = 1` (integrand
`1/(x²√(x³−x))`): the congruence gives `B = 2/3` and residual `D = −x/3`, dropping the multiplicity
`k = 2 → 1`. -/

/-- Case-2 example radicand `f = x³ − x = x(x−1)(x+1)` (`y² = f`, squarefree), `ℚ[x]` `[0,−1,0,1]`. -/
def case2F : CPolyG ℚ := [0, -1, 0, 1]

/-- Case-2 example squarefree denominator factor `W = x` (a factor of `f`, a branch place), `[0, 1]`. -/
def case2W : CPolyG ℚ := [0, 1]

/-- Case-2 example cofactor `h = f/W = x² − 1`, `[−1, 0, 1]`. -/
def case2H : CPolyG ℚ := [-1, 0, 1]

/-- Case-2 example numerator `C = 1`, `[1]`. -/
def case2C : CPolyG ℚ := [1]

/-- `W' = x' = 1` over `ℚ[x]` (`cderivG`, `θ' = 1`). -/
def case2Wder : CPolyG ℚ := cderivG case2W

/-- The solved Case-2 cofactor `B` for `B·(½−2)·W'·h ≡ 1 (mod x)` — expected `B = 2/3`. -/
def case2B : CPolyG ℚ := radCase2Cofactor 2 case2W case2H case2C

/-- The Case-2 residual `D` — expected `−x/3` (multiplicity dropped `k = 2 → 1`). -/
def case2D : CPolyG ℚ :=
  radCase2Residual 2 case2W case2H case2C case2B

/-- The cofactor is `B = 2/3`: `B·(½−2)·W'·h ≡ 1 (mod x)` gives `B = 2/3`. -/
theorem case2_cofactor_eq :
    cisZeroG (csubG case2B [(2/3 : ℚ)]) = true := by native_decide

/-- The Case-2 congruence `B·(½−k)·W'·h − C ≡ 0 (mod W)` holds: `cmodWf (B·(½−k)W'h − C) W` vanishes. -/
theorem case2_congruence :
    cisZeroG (cmodWf
      (csubG (cmulG case2B
        (cmulG (csubG [CField.div CField.one (cnatCastG 2)] [cnatCastG 2])
          (cmulG case2Wder case2H))) case2C)
      case2W) = true := by native_decide

/-- The Case-2 cleared identity `B·(½−k)W'h − C + W·(B'h + ½Bh') = W·D` in `ℚ[x]` (`B = 2/3`, `D = −x/3`). -/
theorem case2_cleared_identity :
    cisZeroG (csubG
      (caddG
        (csubG (cmulG case2B
          (cmulG (csubG [CField.div CField.one (cnatCastG 2)] [cnatCastG 2])
            (cmulG case2Wder case2H))) case2C)
        (cmulG case2W
          (caddG (cmulG (cderivG case2B) case2H)
            (cmulG [CField.div CField.one (cnatCastG 2)] (cmulG case2B (cderivG case2H))))))
      (cmulG case2W case2D)) = true := by native_decide

/-- The residual `D = −x/3`, so the Case-2 step lowered the multiplicity of `W = x` from `k = 2` to `1`. -/
theorem case2_residual_eq :
    cisZeroG (csubG case2D [(0 : ℚ), -1/3]) = true := by native_decide

/-! #### Case 3 validates: degree-lowering `∫ (x²+x)/√x` with `y = √x`

Radicand `y² = f = x`, `g = 1/2`, `C = x² + x`: the leading-coefficient solve gives `B = (2/5)x²` and
residual `D = −x` of degree `1 < deg C = 2`, lowering `deg C` by one. -/

/-- Case-3 example radicand `f = x` (`y² = x`, `m = deg f = 1`), as a `ℚ[x]` polynomial `[0, 1]`. -/
def case3F : CPolyG ℚ := [0, 1]

/-- `g = ((n−1)/n)·f' = (1/2)·1 = 1/2` for `n = 2`, `f = x` (`(f/y)' = g/y`, `lcf(g) = 1/2`), `[1/2]`. -/
def case3G : CPolyG ℚ := cscaleG (1/2 : ℚ) (cderivG case3F)

/-- Case-3 example numerator `C = x² + x` (`deg C = 2 ≥ m = 1`), `[0, 1, 1]`. -/
def case3C : CPolyG ℚ := [0, 1, 1]

/-- The solved Case-3 leading-coefficient cofactor `B = (2/5)x²` (`j+1 = 2`, `b = 1/(2+1/2) = 2/5`). -/
def case3B : CPolyG ℚ := radCase3Cofactor case3F case3G case3C

/-- The Case-3 residual `D = B'f + Bg − C` — expected `−x` (degree `1 < deg C = 2`). -/
def case3D : CPolyG ℚ := radCase3Residual case3F case3G case3B case3C (cderivG case3B)

/-- The cofactor is `B = (2/5)x²`: `b = lcf(C)/((j+1)+lcf(g)) = 1/(2+1/2) = 2/5` at degree `j+1 = 2`. -/
theorem case3_cofactor_eq :
    cisZeroG (csubG case3B [(0 : ℚ), 0, 2/5]) = true := by native_decide

/-- The Case-3 cleared identity `B'f + Bg − C = D` in `ℚ[x]` (`B = (2/5)x²`, `D = −x`). -/
theorem case3_cleared_identity :
    cisZeroG (csubG
      (csubG (caddG (cmulG (cderivG case3B) case3F) (cmulG case3B case3G)) case3C)
      case3D) = true := by native_decide

/-- The residual `D = −x` has degree `1`, strictly below `deg C = 2`. -/
theorem case3_residual_eq :
    cisZeroG (csubG case3D [(0 : ℚ), -1]) = true := by native_decide

/-- The Case-3 step strictly lowers `deg C`: `deg D = 1 < deg C = 2`. -/
theorem case3_degree_drop : cdegG case3D < cdegG case3C := by native_decide

/-! #### `θ = log v` validates: degree-lowering `∫ C/y` over `ℚ(x)[log x]`, `y = √(log x)`

A 2-level tower: base `ℚ(x)`, monomial `θ = log x` (`θ' = 1/x`), radicand `y² = f = log x`, `g = 1/(2x)`.
For `C` with leading term `(5/(2x))θ²` the bracket `(j+1)·θ' + lcf(g) = 5/(2x)` gives the constant `b = 1`,
`B = θ²`, and residual `D = −θ`, dropping `deg_θ C` by one. -/

/-- `θ' = (log x)' = v'/v = 1/x ∈ ℚ(x)` (numerator `[1]`, denominator `[0,1] = x`), the derivative of
the monomial `θ = log x`. -/
def logDt : QFunNZG ℚ := qxOfFrac [1] [0, 1] (by decide)

/-- The ℚ(x) leading coefficient `lcf(g) = g = 1/(2x)` for `f = θ`, `g = (1/2)f'/f·f = 1/(2x)`
(numerator `[1]`, denominator `[0,2] = 2x`). -/
def logGlead : QFunNZG ℚ := qxOfFrac [1] [0, 2] (by decide)

/-- The radicand `f = θ = log x ∈ ℚ(x)[θ]` (`y² = log x`), the `θ`-polynomial `[0, 1]`. -/
def logF : CPolyG (QFunNZG ℚ) := [CField.zero, CField.one]

/-- `g = 1/(2x)` as a degree-`0`-in-θ element of `ℚ(x)[θ]` (`(f/y)' = g/y`), `[1/(2x)]`. -/
def logG : CPolyG (QFunNZG ℚ) := [logGlead]

/-- The numerator `C = (5/(2x))θ² + θ ∈ ℚ(x)[θ]` (`deg_θ C = 2 ≥ m`), with leading coefficient
`5/(2x) = (j+1)θ' + lcf(g)` chosen so the constant `b = 1` solves eq. 5. -/
def logC : CPolyG (QFunNZG ℚ) := [CField.zero, CField.one, qxOfFrac [5] [0, 2] (by decide)]

/-- The `θ`-derivative as a polynomial `[θ'] = [1/x] ∈ ℚ(x)[θ]`, the `Dt` for `cmonomialDeriv`. -/
def logDtPoly : CPolyG (QFunNZG ℚ) := [logDt]

/-- The solved `θ = log v` leading-coefficient cofactor `B = b·θ² = 1·θ²` (`b = lcf(C)/bracket =
(5/(2x))/(5/(2x)) = 1`, a constant). -/
def logB : CPolyG (QFunNZG ℚ) := radCase3CofactorGen logDt logF logG logC

/-- The `θ = log v` residual `D = B'f + Bg − C`, with `B' = cmonomialDeriv [θ'] B` the full log-monomial
derivative — expected `−θ` (degree `1 < deg_θ C = 2`). -/
def logD : CPolyG (QFunNZG ℚ) :=
  radCase3Residual logF logG logB logC (cmonomialDeriv logDtPoly logB)

/-- The `log` cofactor is the constant monomial `B = θ²`: `b = (5/(2x))/((2)(1/x) + 1/(2x)) = 1` at
degree `j+1 = 2`. -/
theorem logCase_cofactor_eq :
    cisZeroG (csubG logB [CField.zero, CField.zero, (CField.one : QFunNZG ℚ)]) = true := by
  native_decide

/-- The `θ = log v` cleared identity `B'f + Bg − C = D` in `ℚ(x)[log x]` (`B = θ²`, `B' = cmonomialDeriv
[1/x] B`, `D = −θ`). -/
theorem logCase_cleared_identity :
    cisZeroG (csubG
      (csubG (caddG (cmulG (cmonomialDeriv logDtPoly logB) logF) (cmulG logB logG)) logC)
      logD) = true := by native_decide

/-- The `log` residual `D = −θ` has `θ`-degree `1`, strictly below `deg_θ C = 2`. -/
theorem logCase_residual_eq :
    cisZeroG (csubG logD [CField.zero, (CField.neg CField.one : QFunNZG ℚ)]) = true := by native_decide

/-- The `θ = log v` step strictly lowers `deg_θ C`: `deg D = 1 < deg C = 2` over `ℚ(x)[log x]`. -/
theorem logCase_degree_drop : cdegG logD < cdegG logC := by native_decide

/-! #### `θ = exp v` validates: `∫ C/(θy)` over `ℚ(x)[eˣ]`, `y = √(eˣ+1)`

A 2-level exponential tower: base `ℚ(x)`, monomial `θ = exp x` (`θ' = θ`), radicand `y² = f = eˣ + 1`,
`g = (1/2)θ`. The `C/(θy)` step (`k = 1`, `C = θ + 1`): the constant-term match gives `b₀ = −1`,
`B = [−1]`, residual `D = −1/2`, dropping `k = 1 → 0`. -/

/-- The radicand `f = θ + 1 = eˣ + 1 ∈ ℚ(x)[θ]` (`y² = eˣ + 1`, `θ ∤ f`, `f₀ = 1`), `[1, 1]`. -/
def expF : CPolyG (QFunNZG ℚ) := [CField.one, CField.one]

/-- `g = (1/2)θ ∈ ℚ(x)[θ]` for `f = θ+1`, `θ = exp x` (`(f/y)' = g/y`, `g₀ = 0`), `[0, 1/2]`. -/
def expG : CPolyG (QFunNZG ℚ) := [CField.zero, qxOfNum [1/2]]

/-- The numerator `C = θ + 1 ∈ ℚ(x)[θ]` (`c₀ = 1`), `[1, 1]`. -/
def expC : CPolyG (QFunNZG ℚ) := [CField.one, CField.one]

/-- `v' = (x)' = 1 ∈ ℚ(x)` for `θ = exp x` (`v = x`), the `CField.one` of `QFunNZG ℚ`. -/
def expVder : QFunNZG ℚ := CField.one

/-- `θ' = v'·θ = θ` as the `Dt` polynomial `[0, 1] ∈ ℚ(x)[θ]` for `cmonomialDeriv` (`θ = exp x` is a
factor of its own derivative). -/
def expDtPoly : CPolyG (QFunNZG ℚ) := [CField.zero, CField.one]

/-- The solved `θ = exp v` `C/(θy)` cofactor `B = [b₀] = [−1]` (`b₀ = c₀/(g₀ − kv'f₀) = 1/(0−1) = −1`,
a constant). -/
def expB : CPolyG (QFunNZG ℚ) := radExpCofactor 1 expVder expF expG expC

/-- The `θ = exp v` `C/(θy)` residual `D = ((B'f + Bg − kv'Bf) − C)/θ`, `B' = cmonomialDeriv [θ] B` —
expected `−1/2` (the multiplicity dropped `k = 1 → 0`). -/
def expD : CPolyG (QFunNZG ℚ) :=
  radExpResidual 1 expVder expF expG expB expC (cmonomialDeriv expDtPoly expB)

/-- The `exp` cofactor is the constant `B = [−1]`: `b₀ = 1/(0 − 1·1·1) = −1` over `ℚ(x)[eˣ]`. -/
theorem expCase_cofactor_eq :
    cisZeroG (csubG expB [(CField.neg CField.one : QFunNZG ℚ)]) = true := by native_decide

/-- The `θ = exp v` constant-term congruence `(B'f + Bg − kv'Bf) − C ≡ 0 (mod θ)`: the numerator `(−1/2)θ`
is divisible by `θ`. -/
theorem expCase_congruence :
    cisZeroG (cmodWf
      (csubG (csubG (caddG (cmulG (cmonomialDeriv expDtPoly expB) expF) (cmulG expB expG))
          (cmulG [CField.mul (cnatCastG 1) expVder] (cmulG expB expF))) expC)
      [CField.zero, CField.one]) = true := by native_decide

/-- The `θ = exp v` cleared identity `(B'f + Bg − k·v'·B·f) − C = θ·D` in `ℚ(x)[eˣ]` (`B = [−1]`,
`D = [−1/2]`). -/
theorem expCase_cleared_identity :
    cisZeroG (csubG
      (csubG (csubG (caddG (cmulG (cmonomialDeriv expDtPoly expB) expF) (cmulG expB expG))
          (cmulG [CField.mul (cnatCastG 1) expVder] (cmulG expB expF))) expC)
      (cmulG [CField.zero, CField.one] expD)) = true := by native_decide

/-- The `exp` residual `D = −1/2` (a `θ`-constant): the `C/(θᵏy)` step lowered the `θ`-power multiplicity
`k = 1 → 0`. -/
theorem expCase_residual_eq :
    cisZeroG (csubG expD [qxOfNum [-1/2]]) = true := by native_decide

end DeepWiki.SymbolicIntegration
