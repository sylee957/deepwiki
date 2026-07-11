import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtensionExamples
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalCase2
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalWellFounded
import Sources.Hdl_1721_1_15391.Source

/-! # Trager catalog — Appendix A: Simple Radical Extensions
Trager's practical reductions for a simple radical extension `F(y)` with `yⁿ = f ∈ F` (`F` a
differential field, char 0) — the most common algebraic case. The `DeepWiki.SymbolicIntegration`
library renders the appendix's **rational part** as computable algorithms over the generic
ℚ(x) = `DenseFrac ℚ` carrier (`ComputableRadicalExtension` / `ComputableRadicalCase2` /
`ComputableRadicalWellFounded`), each `native_decide`-validated on its cleared Hermite identity, and
proves the end-to-end driver capstone `D(v) = (rational part of the integrand)` with the actual
diagonal derivation `radDeriv`.

**Computable-vs-abstract.** Every entry below is a computable function (or a `native_decide`
witness on a worked example); the abstract correctness theorems (that the assembled `v` is the
integral's rational part) are validated only by `native_decide`, not proved in general. The
rational part here joins the residue resultant and the principal-case log-argument solve of
`Sources.Hdl_1721_1_15391.Chapter5` in the unified fuel-free full integrator `cIntegrateAlgebraicWf`
(catalog `Sources.Hdl_1721_1_15391.IntegrateFull`), which assembles `∫ = v + Σ cᵢ log uᵢ`. Only the
NON-PRINCIPAL / torsion log part (divisors Ch. 5 §3, the principal-divisor / torsion test Ch. 6) is
unformalized — see those catalogs and the block below.

## NOT YET FORMALIZED (audit 2026-06-26)
App. A §2.1 Case 1 (`C/(Vᵏy)`): the `k = 1` lower-coefficient solve (the residual `Crem/(Vy)`,
  a Risch first-order ODE) is the deferred `cRischDE` glue `[deferred]`.
App. A §2.4 `θ = exp v`: the `C/y` sub-case (eq. 6) and the *lower* (non-leading,
  non-constant) coefficient ODE solves of the `θ = log v` / `θ = exp v` variants
  (Risch first-order ODE for each coefficient) `[deferred]`.
App. A: the radical degree `n ≥ 3` (only `n = 2` validated end-to-end; the carrier `radMul` /
  `radDeriv` are generic in `n`, but the Case-2 bracket `1−k−eⱼ/n` and the drivers are
  exercised only at `n = 2`) `[deferred]`. -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.RadElem
open DeepWiki.SymbolicIntegration.DensePoly

namespace DeepWiki.Tiaf

/-! ## The simple-radical carrier and the diagonal derivation (App. A §1) -/

/-- **The simple-radical-extension carrier** (Trager, Appendix A §1, p.73): an element of
`F(y)`, `yⁿ = f`, is a coefficient list `[a₀,…,a_{n−1}]` for `Σ aᵢyⁱ` in `α[y]/(yⁿ − f)`. The
library's `RadElem α = DensePoly α` (the degree `n` and radicand `f` are carried by the operations).
The thesis writes this carrier `RadExt α n f`; the realized type is `RadElem`. -/
abbrev appA_radicalCarrier := @RadElem

/-- **The diagonal derivation** `radDeriv` (Trager, Appendix A §1, p.74): since
`y' = f'/(n·y^{n−1}) = (f'/(n·f))·y`, the derivation is diagonal —
`D(Σ aᵢyⁱ) = Σ [D(aᵢ) + aᵢ·(i·f'/(n·f))]·yⁱ`, mixing no `y`-powers. -/
abbrev appA_radicalDeriv := @RadElem.radDeriv

/-- **Appendix A §1, p.74** (validation): over `α = ℚ(x)`, `n = 2`, `f = x³+1`, the radical
generator squares to the radicand, `y·y = f` (`native_decide`). -/
abbrev appA_radGen_sq_eq_radicand := @radGen_sq_eq_radicand

/-- **Appendix A §1, p.74** (validation): over `α = ℚ(x)`, `n = 2`, `f = x³+1`,
`D(y) = (3x²/(2(x³+1)))·y` — the diagonal derivation on the generator (`native_decide`). -/
abbrev appA_radDeriv_radGen_eq := @radDeriv_radGen_eq

/-! ## The `Tᵢ` decoupling (App. A §1) -/

/-- **The per-`y`-power projection** `Tᵢ` (Trager, Appendix A §1): `radProj i` keeps the `yⁱ`
coefficient. The diagonality of `radDeriv` is exactly the statement that `D` commutes with each
`Tᵢ`, so `∫(g₀ + g₁y)` splits into `∫g₀` and `∫g₁y` independently. -/
abbrev appA_Ti_projection := @RadElem.radProj

/-- **Appendix A §1** (the decoupling theorem): `D` commutes with the `Tᵢ` projection —
`radProj i (radDeriv p) = radDeriv (radProj i p)` on the `mixedElem` witness (`native_decide`),
so the integral of a sum of `y`-powers splits power-by-power. -/
abbrev appA_radDeriv_decouples := @radDeriv_decouples

/-! ## Case 1 — `C/(Vᵏy)`, `θ' = 1` (App. A §2.1) -/

/-- **Case 1 cofactor** (Trager, Appendix A §2.1, p.75–76): `CPoly.radCase1Cofactor` solves the
Hermite congruence `(1−k)V'fB ≡ C (mod V)` via the fuel-free Bézout solver `cdiophantine`, giving
the numerator `B` of the lowered term `Bf/(V^{k−1}y)`. -/
abbrev appA_case1_cofactor := @CPoly.radCase1Cofactor

/-- **Case 1 residual** (Trager, Appendix A §2.1, p.76): `CPoly.radCase1Residual` returns the residual
numerator `D` at multiplicity `k−1` after subtracting `(Bf/(V^{k−1}y))'` from `C/(Vᵏy)`. -/
abbrev appA_case1_residual := @CPoly.radCase1Residual

/-- **Appendix A §2.1, p.76** (validation): the Case-1 cleared Hermite identity
`(Bf/(V^{k−1}y))' − C/(Vᵏy) = D/(V^{k−1}y)` holds for `y = √(x−1)`-style data
(`native_decide`). -/
abbrev appA_case1_cleared_identity := @case1_cleared_identity

/-! ## Case 2 — `C/(Wᵏy)`, `W ∣ f` squarefree, `n = 2` (App. A §2.2) -/

/-- **Case 2 cofactor** (Trager, Appendix A §2.2, p.76–77, `n = 2`): `CPoly.radCase2Cofactor` solves
the `radDeriv`-validated congruence `B·(½−k)W'h ≡ C (mod W)` (`h = f/W`; the bracket `½−k =
1−k−eⱼ/n` is Trager's at `eⱼ = 1, n = 2`) via `cdiophantine`, clearing `f`-factors from
denominators. -/
abbrev appA_case2_cofactor := @CPoly.radCase2Cofactor

/-- **Case 2 residual** (Trager, Appendix A §2.2, p.77, `n = 2`): `CPoly.radCase2Residual` returns the
residual numerator `D` from the cleared identity `B·(½−k)W'h − C + W·(B'h + ½Bh') = W·D`. -/
abbrev appA_case2_residual := @CPoly.radCase2Residual

/-- **Appendix A §2.2, p.77** (validation): the Case-2 cleared identity
`B·(½−k)W'h − C + W·(B'h + ½Bh') = W·D` holds for the `C/(Wᵏy)` reduction (`native_decide`). -/
abbrev appA_case2_cleared_identity := @case2_cleared_identity

/-! ## Case 3 — `C/y`, `θ' = 1` (App. A §2.3) -/

/-- **Case 3 cofactor** (Trager, Appendix A §2.3, p.77–78): `CPoly.radCase3Cofactor` does the
degree-lowering leading-coefficient match `c_{j+m} = (j+1 + lcf(g))b`,
`b = lcf(C)/((j+1)+lcf(g))`, giving the numerator `B` for the `C/y` reduction. -/
abbrev appA_case3_cofactor := @CPoly.radCase3Cofactor

/-- **Case 3 residual** (Trager, Appendix A §2.3, p.78): `CPoly.radCase3Residual` returns the residual
numerator `D` from the cleared identity `B'f + Bg − C = D` with `deg D < deg C`. -/
abbrev appA_case3_residual := @CPoly.radCase3Residual

/-- **Appendix A §2.3, p.78** (validation): the Case-3 cleared identity `B'f + Bg − C = D` holds
for the `C/y` reduction (`native_decide`). -/
abbrev appA_case3_cleared_identity := @case3_cleared_identity

/-! ## `θ = log v` cofactor (App. A §2.3, eq. 5) -/

/-- **`θ = log v` cofactor** (Trager, Appendix A §2.3, eq. 5, p.78): `CPoly.radCase3CofactorGen` does
the `C/y` degree-lowering with the `v'/v`-weighted bracket `(j+1)·θ' + lcf(g)` and the full
monomial derivative `cmonomialDeriv [θ']` for `B'`, validated on a genuine 2-level tower
`ℚ(x)[log x]`, `y = √(log x)`. -/
abbrev appA_logTheta_cofactor := @CPoly.radCase3CofactorGen

/-- **Appendix A §2.3, eq. 5, p.78** (validation): the `θ = log v` cleared identity holds on the
`ℚ(x)[log x]`, `y = √(log x)` tower (`native_decide`). -/
abbrev appA_logTheta_cleared_identity := @logCase_cleared_identity

/-! ## `θ = exp v` cofactor — the `C/(θᵏy)` step (App. A §2.4) -/

/-- **`θ = exp v` cofactor** (Trager, Appendix A §2.4, p.79): `CPoly.radExpCofactor` is the `C/(θᵏy)`
step where `θ ∣ θ'`, matching constant (θ-degree-`0`) terms `c₀ = b₀g₀ − k·v'·b₀·f₀`
(constant-`b₀` slice `b₀ = c₀/(g₀ − kv'f₀)`). -/
abbrev appA_expTheta_cofactor := @CPoly.radExpCofactor

/-- **`θ = exp v` residual** (Trager, Appendix A §2.4, p.79): `CPoly.radExpResidual` returns the
residual `D` from the cleared identity `(B'f + Bg − kv'Bf) − C = θ·D`. -/
abbrev appA_expTheta_residual := @CPoly.radExpResidual

/-- **Appendix A §2.4, p.79** (validation): the `θ = exp v` cleared identity
`(B'f + Bg − kv'Bf) − C = θ·D` holds on the exponential tower `ℚ(x)[eˣ]`, `y = √(eˣ+1)`
(`native_decide`). -/
abbrev appA_expTheta_cleared_identity := @expCase_cleared_identity

/-! ## The end-to-end rational-part drivers (App. A §2, iterated) -/

/-- **Fuel-free iterated Case-1 reduction** (Trager, Appendix A §2.1, iterated):
`radReduceCase1IterateWf` runs the single-step `k → k−1` Hermite reduction to completion without
runtime fuel, accumulating each cofactor
contribution `Bⱼf/(V^{kⱼ−1}y)` into a running numerator `vNum`, with the master identity
`∫ C/(V^{k₀}y) = vNum/(V^{k₀−1}y) + ∫ Crem/(Vy)`. -/
abbrev appA_case1_iterate := @DensePoly.radReduceCase1IterateWf

/-- **The fuel-free simple-radical rational-part driver** `radIntegrateCase1Wf` (Trager, Appendix A §2):
wraps `radReduceCase1IterateWf`, decoupling the `R/y` integrand, running the iterated Case-1 reduction,
and assembling the accumulated rational part `v` without runtime fuel. -/
abbrev appA_radIntegrateCase1 := @DensePoly.radIntegrateCase1Wf

/-- The Case-1 driver run `radIntegrateCase1Wf cderiv V f g 3 C` on `∫ 1/((x−1)³√x)`. -/
def appA_sqrtxRun : DensePoly ℚ × DensePoly ℚ :=
  radIntegrateCase1Wf cderiv sqrtxV sqrtxF sqrtx 3 sqrtxC

/-- The driver's rational part for `∫ 1/((x−1)³√x)` lifted to `RadElem (DenseFrac ℚ)`. -/
def appA_sqrtxVlift : RadElem (DenseFrac ℚ) :=
  [CCommRing.zero, CField.div (CFrac.ofPoly appA_sqrtxRun.2) (CFrac.ofPoly (cmul sqrtxV2 sqrtxF))]

/-- The rational-part target for `∫ 1/((x−1)³√x)` lifted to `RadElem (DenseFrac ℚ)`. -/
def appA_sqrtxRatLift : RadElem (DenseFrac ℚ) :=
  [CCommRing.zero,
    CField.sub (CField.div (CFrac.ofPoly sqrtxC) (CFrac.ofPoly (cmul sqrtxV3 sqrtxF)))
      (CField.div (CFrac.ofPoly appA_sqrtxRun.1) (CFrac.ofPoly (cmul sqrtxV sqrtxF)))]

/-- **Appendix A §2** (the driver capstone, `native_decide`): for `y² = x`, `V = x−1`, `k₀ = 3`,
`C₀ = 1` (the integrand `1/((x−1)³√x)`), the driver's accumulated rational part `v` satisfies
`D(v) = C₀/(V³y) − Crem/(Vy)` checked with the actual diagonal derivation `radDeriv 2 x` over the
genuine radical extension `(ℚ(x))[y]/(y²−x)` — i.e. the driver actually integrates the rational
part. -/
theorem appA_sqrtxDriver_integrates :
    DensePoly.cisZero (DensePoly.csub (radDeriv 2 sqrtxFqx appA_sqrtxVlift) appA_sqrtxRatLift) = true := by
  native_decide

/-- The Case-1 driver run on `∫ 1/((x−1)³√(x³+1))`. -/
def appA_cubeRun : DensePoly ℚ × DensePoly ℚ :=
  radIntegrateCase1Wf cderiv cubeV cubeF cube 3 cubeC

/-- The driver's rational part for `∫ 1/((x−1)³√(x³+1))` lifted to `RadElem (DenseFrac ℚ)`. -/
def appA_cubeVlift : RadElem (DenseFrac ℚ) :=
  [CCommRing.zero, CField.div (CFrac.ofPoly appA_cubeRun.2) (CFrac.ofPoly (cmul (cpow cubeV 2) cubeF))]

/-- The rational-part target for `∫ 1/((x−1)³√(x³+1))` lifted to `RadElem (DenseFrac ℚ)`. -/
def appA_cubeRatLift : RadElem (DenseFrac ℚ) :=
  [CCommRing.zero,
    CField.sub (CField.div (CFrac.ofPoly cubeC) (CFrac.ofPoly (cmul (cpow cubeV 3) cubeF)))
      (CField.div (CFrac.ofPoly appA_cubeRun.1) (CFrac.ofPoly (cmul cubeV cubeF)))]

/-- **Appendix A §2** (the driver capstone on a second curve, `native_decide`): for `y² = x³+1`,
`V = x−1`, the driver's accumulated `v` satisfies the analogous `D(v) = rational-part` identity
with `radDeriv 2 (x³+1)` over `(ℚ(x))[y]/(y²−(x³+1))`. -/
theorem appA_cubeDriver_integrates :
    DensePoly.cisZero (DensePoly.csub (radDeriv 2 cubeFqx appA_cubeVlift) appA_cubeRatLift) = true := by
  native_decide

/-- **Appendix A §2.2** (the Case-2 driver capstone, `native_decide`): the `C/(Wᵏy)` Case-2
reduction integrates end-to-end, `D(v) = rational-part`, validated with the actual `radDeriv` on
the genuine radical extension (`ComputableRadicalCase2`). -/
abbrev appA_case2cDriver_integrates := @case2cDriver_integrates

/-- **Fuel-free multi-case rational-part driver** (Trager, Appendix A §2, iterated):
`radIntegrateRationalWf` squarefree-decomposes the rational denominator, splits each factor into its
`V`-part and `W`-part, partial-fractions the numerator, and dispatches every summand to the fuel-free
Case-1 or Case-2 reduction without runtime fuel. -/
abbrev appA_radIntegrateRational := @DensePoly.radIntegrateRationalWf

/-- The multi-case dispatch run `radIntegrateRationalWf ρ R B` on `∫ 1/((x−1)²x²·√x)`. -/
def appA_mcRun : List (Bool × DensePoly ℚ × ℕ × DensePoly ℚ × DensePoly ℚ × DensePoly ℚ) :=
  DensePoly.radIntegrateRationalWf mcRho mcR mcB

/-- **Appendix A §2** (`native_decide`): on `∫ 1/((x−1)²x²·√x)` the dispatcher classifies the mixed
denominator into one `V` factor and one `W` factor, both of multiplicity `2`. -/
theorem appA_mcRun_classification :
    (appA_mcRun.map (fun r => r.1), appA_mcRun.map (fun r => r.2.2.1)) = ([true, false], [2, 2]) := by
  native_decide

/-- Pull the `V`-factor reduction `(Bᵢ, eᵢ, Nᵢ, vNumᵢ, Cremᵢ)` out of `appA_mcRun`. -/
def appA_mcV : DensePoly ℚ × ℕ × DensePoly ℚ × DensePoly ℚ × DensePoly ℚ :=
  (appA_mcRun.headD (true, [], 0, [], [], [])).2

/-- Pull the `W`-factor reduction `(Bᵢ, eᵢ, Nᵢ, vNumᵢ, Cremᵢ)` out of `appA_mcRun`. -/
def appA_mcW : DensePoly ℚ × ℕ × DensePoly ℚ × DensePoly ℚ × DensePoly ℚ :=
  (appA_mcRun.getD 1 (false, [], 0, [], [], [])).2

/-- The assembled total rational part `v = v_V + v_W` lifted to `RadElem (DenseFrac ℚ)`. -/
def appA_mcVlift : RadElem (DenseFrac ℚ) :=
  DensePoly.cadd
    [CCommRing.zero, CField.div (CFrac.ofPoly appA_mcV.2.2.2.1)
      (CFrac.ofPoly (cmul (cpow appA_mcV.1 (appA_mcV.2.1 - 1)) mcRho))]
    [CCommRing.zero, CField.div (CFrac.ofPoly appA_mcW.2.2.2.1)
      (CFrac.ofPoly (cmul (cpow appA_mcW.1 appA_mcW.2.1) mcRho))]

/-- The integrand's total rational part after subtracting the two `k = 1` leftovers. -/
def appA_mcRatLift : RadElem (DenseFrac ℚ) :=
  DensePoly.cadd
    [CCommRing.zero, CField.sub
      (CField.div (CFrac.ofPoly appA_mcV.2.2.1) (CFrac.ofPoly (cmul (cpow appA_mcV.1 appA_mcV.2.1) mcRho)))
      (CField.div (CFrac.ofPoly appA_mcV.2.2.2.2) (CFrac.ofPoly (cmul appA_mcV.1 mcRho)))]
    [CCommRing.zero, CField.sub
      (CField.div (CFrac.ofPoly appA_mcW.2.2.1) (CFrac.ofPoly (cmul (cpow appA_mcW.1 appA_mcW.2.1) mcRho)))
      (CField.div (CFrac.ofPoly appA_mcW.2.2.2.2) (CFrac.ofPoly (cmul appA_mcW.1 mcRho)))]

/-- **Appendix A §2** (multi-case capstone, `native_decide`): on `∫ 1/((x−1)²x²√x)`, the dispatcher
classifies the mixed denominator into one `V` factor and one `W` factor, assembles the rational part,
and the actual radical derivation satisfies `D(v) = rational-part` after subtracting the two `k = 1`
leftovers. -/
theorem appA_multiCaseDriver_integrates :
    DensePoly.cisZero (DensePoly.csub (radDeriv 2 mcRhoQx appA_mcVlift) appA_mcRatLift) = true := by native_decide

end DeepWiki.Tiaf
