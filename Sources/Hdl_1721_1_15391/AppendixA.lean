import DeepWiki.SymbolicIntegration.ComputableRadicalExtension
import DeepWiki.SymbolicIntegration.ComputableRadicalCase2
import DeepWiki.SymbolicIntegration.ComputableRadicalWellFounded
import Sources.Hdl_1721_1_15391.Source

/-! # Trager catalog — Appendix A: Simple Radical Extensions
Trager's practical reductions for a simple radical extension `F(y)` with `yⁿ = f ∈ F` (`F` a
differential field, char 0) — the most common algebraic case. The `DeepWiki.SymbolicIntegration`
library renders the appendix's **rational part** as computable algorithms over the generic
ℚ(x) = `QFunNZG ℚ` carrier (`ComputableRadicalExtension` / `ComputableRadicalCase2` /
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
  a Risch first-order ODE) is the deferred `cRischDEGWf` glue `[deferred]`.
App. A §2.4 `θ = exp v`: the `C/y` sub-case (eq. 6) and the *lower* (non-leading,
  non-constant) coefficient ODE solves of the `θ = log v` / `θ = exp v` variants
  (Risch first-order ODE for each coefficient) `[deferred]`.
App. A: the radical degree `n ≥ 3` (only `n = 2` validated end-to-end; the carrier `radMul` /
  `radDeriv` are generic in `n`, but the Case-2 bracket `1−k−eⱼ/n` and the drivers are
  exercised only at `n = 2`) `[deferred]`. -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.RadElem
open DeepWiki.SymbolicIntegration.CPolyG

namespace DeepWiki.Tiaf

/-! ## The simple-radical carrier and the diagonal derivation (App. A §1) -/

/-- **The simple-radical-extension carrier** (Trager, Appendix A §1, p.73): an element of
`F(y)`, `yⁿ = f`, is a coefficient list `[a₀,…,a_{n−1}]` for `Σ aᵢyⁱ` in `α[y]/(yⁿ − f)`. The
library's `RadElem α = List α` (the degree `n` and radicand `f` are carried by the operations).
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

/-- **Case 1 cofactor** (Trager, Appendix A §2.1, p.75–76): `radCase1Cofactor` solves the
Hermite congruence `(1−k)V'fB ≡ C (mod V)` via the generic Bézout solver `cdiophantineG`, giving
the numerator `B` of the lowered term `Bf/(V^{k−1}y)`. -/
abbrev appA_case1_cofactor := @radCase1Cofactor

/-- **Case 1 residual** (Trager, Appendix A §2.1, p.76): `radCase1Residual` returns the residual
numerator `D` at multiplicity `k−1` after subtracting `(Bf/(V^{k−1}y))'` from `C/(Vᵏy)`. -/
abbrev appA_case1_residual := @radCase1Residual

/-- **Appendix A §2.1, p.76** (validation): the Case-1 cleared Hermite identity
`(Bf/(V^{k−1}y))' − C/(Vᵏy) = D/(V^{k−1}y)` holds for `y = √(x−1)`-style data
(`native_decide`). -/
abbrev appA_case1_cleared_identity := @case1_cleared_identity

/-! ## Case 2 — `C/(Wᵏy)`, `W ∣ f` squarefree, `n = 2` (App. A §2.2) -/

/-- **Case 2 cofactor** (Trager, Appendix A §2.2, p.76–77, `n = 2`): `radCase2Cofactor` solves
the `radDeriv`-validated congruence `B·(½−k)W'h ≡ C (mod W)` (`h = f/W`; the bracket `½−k =
1−k−eⱼ/n` is Trager's at `eⱼ = 1, n = 2`) via `cdiophantineG`, clearing `f`-factors from
denominators. -/
abbrev appA_case2_cofactor := @radCase2Cofactor

/-- **Case 2 residual** (Trager, Appendix A §2.2, p.77, `n = 2`): `radCase2Residual` returns the
residual numerator `D` from the cleared identity `B·(½−k)W'h − C + W·(B'h + ½Bh') = W·D`. -/
abbrev appA_case2_residual := @radCase2Residual

/-- **Appendix A §2.2, p.77** (validation): the Case-2 cleared identity
`B·(½−k)W'h − C + W·(B'h + ½Bh') = W·D` holds for the `C/(Wᵏy)` reduction (`native_decide`). -/
abbrev appA_case2_cleared_identity := @case2_cleared_identity

/-! ## Case 3 — `C/y`, `θ' = 1` (App. A §2.3) -/

/-- **Case 3 cofactor** (Trager, Appendix A §2.3, p.77–78): `radCase3Cofactor` does the
degree-lowering leading-coefficient match `c_{j+m} = (j+1 + lcf(g))b`,
`b = lcf(C)/((j+1)+lcf(g))`, giving the numerator `B` for the `C/y` reduction. -/
abbrev appA_case3_cofactor := @radCase3Cofactor

/-- **Case 3 residual** (Trager, Appendix A §2.3, p.78): `radCase3Residual` returns the residual
numerator `D` from the cleared identity `B'f + Bg − C = D` with `deg D < deg C`. -/
abbrev appA_case3_residual := @radCase3Residual

/-- **Appendix A §2.3, p.78** (validation): the Case-3 cleared identity `B'f + Bg − C = D` holds
for the `C/y` reduction (`native_decide`). -/
abbrev appA_case3_cleared_identity := @case3_cleared_identity

/-! ## `θ = log v` cofactor (App. A §2.3, eq. 5) -/

/-- **`θ = log v` cofactor** (Trager, Appendix A §2.3, eq. 5, p.78): `radCase3CofactorGen` does
the `C/y` degree-lowering with the `v'/v`-weighted bracket `(j+1)·θ' + lcf(g)` and the full
monomial derivative `cmonomialDeriv [θ']` for `B'`, validated on a genuine 2-level tower
`ℚ(x)[log x]`, `y = √(log x)`. -/
abbrev appA_logTheta_cofactor := @radCase3CofactorGen

/-- **Appendix A §2.3, eq. 5, p.78** (validation): the `θ = log v` cleared identity holds on the
`ℚ(x)[log x]`, `y = √(log x)` tower (`native_decide`). -/
abbrev appA_logTheta_cleared_identity := @logCase_cleared_identity

/-! ## `θ = exp v` cofactor — the `C/(θᵏy)` step (App. A §2.4) -/

/-- **`θ = exp v` cofactor** (Trager, Appendix A §2.4, p.79): `radExpCofactor` is the `C/(θᵏy)`
step where `θ ∣ θ'`, matching constant (θ-degree-`0`) terms `c₀ = b₀g₀ − k·v'·b₀·f₀`
(constant-`b₀` slice `b₀ = c₀/(g₀ − kv'f₀)`). -/
abbrev appA_expTheta_cofactor := @radExpCofactor

/-- **`θ = exp v` residual** (Trager, Appendix A §2.4, p.79): `radExpResidual` returns the
residual `D` from the cleared identity `(B'f + Bg − kv'Bf) − C = θ·D`. -/
abbrev appA_expTheta_residual := @radExpResidual

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
abbrev appA_case1_iterate := @CPolyG.radReduceCase1IterateWf

/-- **The fuel-free simple-radical rational-part driver** `radIntegrateCase1Wf` (Trager, Appendix A §2):
wraps `radReduceCase1IterateWf`, decoupling the `R/y` integrand, running the iterated Case-1 reduction,
and assembling the accumulated rational part `v` without runtime fuel. -/
abbrev appA_radIntegrateCase1 := @CPolyG.radIntegrateCase1Wf

/-- **Appendix A §2** (the fuel-free driver capstone, `native_decide`): for `y² = x`, `V = x−1`, `k₀ = 3`,
`C₀ = 1` (the integrand `1/((x−1)³√x)`), the Wf driver's accumulated rational part `v` satisfies
`D(v) = C₀/(V³y) − Crem/(Vy)` checked with the actual diagonal derivation `radDeriv 2 x` over the
genuine radical extension `(ℚ(x))[y]/(y²−x)` — i.e. the driver actually integrates the rational
part. -/
abbrev appA_sqrtxDriver_integrates := @sqrtxDriverWf_integrates

/-- **Appendix A §2** (the fuel-free driver capstone on a second curve, `native_decide`): for `y² = x³+1`,
`V = x−1`, the Wf driver's accumulated `v` satisfies the analogous `D(v) =
rational-part` identity with `radDeriv 2 (x³+1)` over `(ℚ(x))[y]/(y²−(x³+1))`. -/
abbrev appA_cubeDriver_integrates := @cubeDriverWf_integrates

/-- **Appendix A §2.2** (the Case-2 driver capstone, `native_decide`): the `C/(Wᵏy)` Case-2
reduction integrates end-to-end, `D(v) = rational-part`, validated with the actual `radDeriv` on
the genuine radical extension (`ComputableRadicalCase2`). -/
abbrev appA_case2cDriver_integrates := @case2cDriver_integrates

/-- **Fuel-free multi-case rational-part driver** (Trager, Appendix A §2, iterated):
`radIntegrateRationalWf` squarefree-decomposes the rational denominator, splits each factor into its
`V`-part and `W`-part, partial-fractions the numerator, and dispatches every summand to the fuel-free
Case-1 or Case-2 reduction without runtime fuel. -/
abbrev appA_radIntegrateRational := @CPolyG.radIntegrateRationalWf

/-- **Appendix A §2** (fuel-free multi-case capstone, `native_decide`): on
`∫ 1/((x−1)²x²√x)`, the Wf dispatcher classifies the mixed denominator into one `V` factor and one `W`
factor, assembles the rational part, and the actual radical derivation satisfies `D(v) = rational-part`
after subtracting the two `k = 1` leftovers. -/
abbrev appA_multiCaseDriver_integrates := @mcDriverWf_integrates

end DeepWiki.Tiaf
