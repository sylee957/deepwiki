import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalIntegrate
import DeepWiki.SymbolicIntegration.Computable.FuelFreeDiophantine

/-! # Algebraic-function integration: Case 2 reduction, validated through `radDeriv` (Trager A §2.2)

`ComputableRadicalExtension` ships a Case-2 reduction (`radCase2Cofactor`/`radCase2Residual`,
`case2_cleared_identity`) for the partial-fraction piece `C/(Wᵏy)` with `W = Pⱼ` a squarefree factor
of the radicand. That cleared identity is a *true polynomial identity* — but it does **not** correspond
to the actual diagonal derivation `radDeriv` (unlike Case 1, whose `sqrtxDriver_integrates` /
`cubeDriver_integrates` are validated through `radDeriv`). The transcribed congruence
`B·g − k·W'·h ≡ C (mod W)` (with a `−kW'h` term lacking the `B` factor) does not match the
`radDeriv` of the lifted rational part `Bf/(Wᵏy)`.

**This file re-derives the Case-2 reduction directly from `radDeriv` (the ground truth) and validates
it end-to-end**, mirroring the Case-1 drivers. For a simple radical `y² = f` with `f` squarefree
(`d = 1`, every `eᵢ = 1`, so the integrating factor `∏Pᵢ` *is* the radicand `f`), `W = Pⱼ` a factor of
`f`, `h = f/W`, the **actual** derivation `radDeriv 2 f` satisfies (proved by `radDeriv` over `ℚ(x)`):

`radDeriv(Bf/(Wᵏy)) = (B·(½−k)·W'·h)/(Wᵏy) + (B'h + ½Bh')/(W^{k−1}y)`.

So lowering `C/(Wᵏy)` needs `B` with `B·(½−k)·W'·h ≡ C (mod W)` (solvable: `gcd(W'h, W) = 1` for `W`
squarefree coprime to `h`, and `½ − k ≠ 0` for `k ≥ 1`), residual `D = (B·(½−k)W'h − C)/W + B'h + ½Bh'`,
and `∫ C/(Wᵏy) = Bf/(Wᵏy) − ∫ D/(W^{k−1}y)`. The `½ − k = 1 − k − eⱼ/n` bracket is exactly Trager's
congruence on p. 76 (`B(1−k−eⱼ/n)W'h ≡ C (mod W)`) at `eⱼ = 1, n = 2` — the engine's earlier
`radCase2Cofactor` had mis-transcribed it.

* **`radCase2CofactorC`/`radCase2ResidualC`** — the corrected (n = 2) cofactor / residual.
* **`case2c_cleared_identity`** — the cleared `ℚ[x]` identity `B·(½−k)W'h − C + W·(B'h+½Bh') = W·D`.
* **`case2cDriver_integrates`** — the end-to-end `D(v) = rational-part` check through `radDeriv 2 f`,
  on a genuine branch example `y² = x³−x`, `W = x`, `k = 2` (a pole at the branch place `x = 0`).

**Restriction** (documented): `n = 2`. The pure-`y` lift `1/y = y/f` (`R/y ↦ [0, R/f]`) that puts the
integrand into the radical extension is special to `n = 2`; for `n ≥ 3`, `1/y = y^{n−1}/f` lands in the
`y^{n−1}`-component and the coefficient bracket becomes `1 − k − eⱼ/n` (Trager, general). The `n = 2`
clean-squarefree case is exactly what the Case-1 drivers (`sqrtxDriver_integrates`,
`cubeDriver_integrates`) and the simple-radical catalog use. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

namespace CPolyG

variable {α : Type*} [CField α]

/-- **Corrected Case-2 cofactor (n = 2)** `radCase2CofactorC k W h C = B` — the polynomial `B`
(degree `< deg W`) solving the `radDeriv`-validated Case-2 congruence `B·(½−k)·W'·h ≡ C (mod W)` (Trager
Appendix A §2.2, `B(1−k−eⱼ/n)W'h ≡ C (mod W)` at `eⱼ = 1, n = 2`), via `cdiophantineGWf ((½−k)W'h) W C`
(`gcd((½−k)W'h, W) = 1` since `W = Pⱼ` is squarefree, coprime to `h = f/W`, and `½ − k ≠ 0` for
`k ≥ 1`). `h = f/W` and `W` are passed in (the caller supplies `f/W`); `W'` is `cderivG W`. Generic over
`[CField α]`. -/
def radCase2CofactorC (k : ℕ) (W h C : CPolyG α) : CPolyG α :=
  let half : CPolyG α := [CField.div CField.one (cnatCastG 2)]              -- ½
  let coef := cmulG (csubG half [cnatCastG k]) (cmulG (cderivG W) h)        -- (½ − k)·W'·h
  (cdiophantineGWf coef W C).1

/-- **Corrected Case-2 residual (n = 2)** `radCase2ResidualC k W h C B = D` — the lowered-`k`
residual numerator `D = (B·(½−k)W'h − C)/W + B'h + ½Bh'` of the `radDeriv`-validated Case-2 step. `h = f/W`,
`W` passed in; `B'` is `cderivG B`, `h'` is `cderivG h`. The exact division by `W` is `cdivWf`
(`W ∣ B·(½−k)W'h − C` by the cofactor congruence). With this `D`,
`radDeriv(Bf/(Wᵏy)) = C/(Wᵏy) + D/(W^{k−1}y)`. Generic over `[CField α]`. -/
def radCase2ResidualC (k : ℕ) (W h C B : CPolyG α) : CPolyG α :=
  let half : CPolyG α := [CField.div CField.one (cnatCastG 2)]              -- ½
  let coef := cmulG (csubG half [cnatCastG k]) (cmulG (cderivG W) h)        -- (½ − k)·W'·h
  let topNum := csubG (cmulG B coef) C                                      -- B·(½−k)W'h − C
  let quotient := cdivWf topNum W                                           -- /W
  caddG quotient (caddG (cmulG (cderivG B) h)                              -- + B'h
    (cmulG half (cmulG B (cderivG h))))                                     -- + ½Bh'

end CPolyG

/-! #### ★ Corrected Case 2 validates through `radDeriv`: `y² = x³−x`, `W = x`, `k = 2` (`native_decide`)

`F = ℚ` (constants), `θ = x` (`θ' = 1`), radicand `y² = f = x³ − x = x(x−1)(x+1)` (`n = 2`, squarefree,
so the integrating factor `∏Pᵢ = f`). Squarefree factor `W = x` (a *branch place* `x = 0` of the
radical), `h = f/W = x² − 1`, `W' = 1`, `k = 2`, `C = 1` — integrand `1/(x²·√(x³−x))`. The corrected
congruence `B·(½−2)·1·(x²−1) ≡ 1 (mod x)` is `B·(−3/2)·(−1) ≡ 1 (mod x)`, i.e. `(3/2)B(0) = 1`, so
`B = 2/3`. The residual is `D = (B·(½−2)W'h − 1)/x + B'h + ½Bh' = −x/3`, dropping the multiplicity
`k = 2 → 1`. -/

open CPolyG

/-- Case-2 corrected example radicand `f = x³ − x = x(x−1)(x+1)` (`y² = f`, squarefree), `ℚ[x]`
`[0,−1,0,1]`. -/
def case2cF : CPolyG ℚ := [0, -1, 0, 1]

/-- Case-2 corrected example squarefree factor `W = x` (a branch place `x = 0` of `√(x³−x)`), `[0,1]`. -/
def case2cW : CPolyG ℚ := [0, 1]

/-- Case-2 corrected example cofactor `h = f/W = x² − 1`, `[−1,0,1]`. -/
def case2cH : CPolyG ℚ := [-1, 0, 1]

/-- Case-2 corrected example numerator `C = 1`, `[1]`. -/
def case2cC : CPolyG ℚ := [1]

/-- The corrected Case-2 cofactor `B` for `B·(½−2)·W'·h ≡ 1 (mod x)` — expected `B = 2/3`. -/
def case2cB : CPolyG ℚ := radCase2CofactorC 2 case2cW case2cH case2cC

/-- The corrected Case-2 residual `D` — expected `−x/3` (multiplicity dropped `k = 2 → 1`). -/
def case2cD : CPolyG ℚ := radCase2ResidualC 2 case2cW case2cH case2cC case2cB

/-- **The corrected cofactor is `B = 2/3`** (`native_decide`): the diophantine solve of
`B·(½−2)·W'·h ≡ 1 (mod x)` gives `B = 2/3` (`cisZeroG` of `B − 2/3`). -/
theorem case2c_cofactor_eq :
    cisZeroG (csubG case2cB [(2/3 : ℚ)]) = true := by native_decide

/-- **The corrected residual is `D = −x/3`** (`native_decide`): `D = −x/3` (`cisZeroG` of `D + x/3`),
of degree `1` — the Case-2 step lowered the apparent denominator multiplicity of `W = x` from `k = 2`
to `k − 1 = 1`, eliminating one `f`-factor. -/
theorem case2c_residual_eq :
    cisZeroG (csubG case2cD [(0 : ℚ), -1/3]) = true := by native_decide

/-- **★ The corrected Case-2 congruence holds**: `B·(½−k)·W'·h − C ≡ 0 (mod W)` (`native_decide`) — the
numerator `B·(½−2)·1·(x²−1) − 1` is divisible by `W = x`, the defining property of the corrected cofactor
`B`. Checked by `cisZeroG` of `cmodWf (B·(½−k)W'h − C) W`. -/
theorem case2c_congruence :
    cisZeroG (cmodWf
      (csubG (cmulG case2cB
        (cmulG (csubG [CField.div CField.one (cnatCastG 2)] [cnatCastG 2])
          (cmulG (cderivG case2cW) case2cH))) case2cC)
      case2cW) = true := by native_decide

/-- **★ The corrected Case-2 cleared identity** (`native_decide`): cleared over the common denominator
`Wᵏy`, the reduction is the pure `ℚ[x]` identity `B·(½−k)W'h − C + W·(B'h + ½Bh') = W·D`. With `B = 2/3`,
`D = −x/3`. Checked by `cisZeroG` of LHS − RHS over `ℚ[x]`. -/
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

/-! #### ★ The end-to-end `radDeriv` validation (the deliverable, mirroring Case 1)

Over the genuine radical extension `(QFunNZG ℚ)[y]/(y² − (x³−x))`, the rational part `v = Bf/(Wᵏy)` lifts
to the pure-`y` element `[0, (Bf/Wᵏ)/f] = [0, B/Wᵏ]` (an `R/y` form is `[0, R/f]` since `R/y = (R/f)y`),
the integrand `C/(Wᵏy)` to `[0, (C/Wᵏ)/f]`, and the residual `D/(W^{k−1}y)` to `[0, (D/W^{k−1})/f]`. The
**actual** diagonal derivation `radDeriv 2 (x³−x)` confirms `D(v) = C/(Wᵏy) + D/(W^{k−1}y)` — i.e. the
corrected `v` integrates the rational part of `1/(x²·√(x³−x))`, modulo the leftover at the lowered
multiplicity. This is the Case-2 analogue of `sqrtxDriver_integrates`. -/

/-- The radicand `f = x³ − x` lifted to `ℚ(x)` (`QFunNZG ℚ`), the Picture-B radicand for `radDeriv 2`. -/
def case2cFqx : QFunNZG ℚ := qxOfNum [0, -1, 0, 1]

/-- `Wᵏ = x²` and `W^{k−1} = x¹` as `ℚ[x]` polynomials (`k = 2`). -/
def case2cWk : CPolyG ℚ := cpowG case2cW 2

/-- The rational part `v = Bf/(Wᵏy)` lifted to `RadElem (QFunNZG ℚ)` — the pure-`y` element
`[0, (Bf/Wᵏ)/f]` over `ℚ(x)`. -/
def case2cVlift : RadElem (QFunNZG ℚ) :=
  [CField.zero,
    CField.div (qxOfNum (cmulG case2cB case2cF))
      (qxOfNum (cmulG case2cWk case2cF))]

/-- The integrand's rational part `C/(Wᵏy) + D/(W^{k−1}y)` lifted to `RadElem (QFunNZG ℚ)` — the pure-`y`
element `[0, (C/Wᵏ)/f + (D/W^{k−1})/f]` over `ℚ(x)` (what `radDeriv(v)` is to equal). -/
def case2cRatLift : RadElem (QFunNZG ℚ) :=
  [CField.zero,
    CField.add
      (CField.div (qxOfNum case2cC) (qxOfNum (cmulG case2cWk case2cF)))
      (CField.div (qxOfNum case2cD) (qxOfNum (cmulG case2cW case2cF)))]

/-- **★ Corrected Case 2 integrates `∫ 1/(x²·√(x³−x))`: `D(v) = rational part of the integrand`**
(`native_decide`). Over the genuine radical extension `(QFunNZG ℚ)[y]/(y² − (x³−x))` (a pole at the
branch place `x = 0`), the **actual** diagonal radical derivation `radDeriv 2 (x³−x)` of the corrected
rational part `v = Bf/(W²√(x³−x))` equals `C/(W²√(x³−x)) + D/(W·√(x³−x))`, the rational part of the
integrand `1/(x²·√(x³−x))`. Checked by `radIsZero` of the difference over `ℚ(x)`. **THE CORRECTED CASE-2
REDUCTION IS `radDeriv`-VALIDATED END-TO-END** — `D(∫) = rational-part`, like the Case-1 drivers, at a
branch place of the radical. (The earlier `case2_cleared_identity` was a true polynomial identity for a
mis-transcribed congruence; this is the faithful reduction.) -/
theorem case2cDriver_integrates :
    radIsZero (radSub (radDeriv 2 case2cFqx case2cVlift) case2cRatLift) = true := by native_decide

/-! ### `#print axioms` — the corrected Case-2 headline

The corrected cofactor/residual, the cleared identity, and the end-to-end `radDeriv` validation carry the
standard `[propext, Classical.choice, Quot.sound]` plus the `native_decide` compiler axiom — no `sorry`,
no extra axiom. Case 2 now matches Case 1: the rational part `v = Bf/(Wᵏy)` assembled by the corrected
reduction has `radDeriv(v)` equal to the rational part of the integrand, validated by the real
derivation at a branch place. -/

#print axioms case2c_cofactor_eq
#print axioms case2c_congruence
#print axioms case2c_cleared_identity
-- ★ The deliverable: Case 2 validated through the actual `radDeriv`, like Case 1:
#print axioms case2cDriver_integrates

end DeepWiki.SymbolicIntegration
