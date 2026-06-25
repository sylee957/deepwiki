import DeepWiki.SymbolicIntegration.ComputableLogPartTower
import DeepWiki.SymbolicIntegration.ComputableFractionFieldDeriv
import DeepWiki.SymbolicIntegration.RationalIntegrationGcdLogForm

/-! # Abstract correctness of the §5.6 residue-criterion log part over the tower `ℚ(x)(t)`
The computable engine `ComputableLogPartTower` *computes* the §5.6 Rothstein–Trager–Lazard
logarithmic part — the residue resultant `cResidueResultantTower` and the per-residue log arguments
`cLogArgTower` — and `logPartTower_example` validates it (`native_decide`) on Bronstein's Example
5.6.2. This file proves the **abstract correctness** of the underlying *integral identity*, the
all-inputs generalization of the example: the logarithmic part
`∑ aᵢ·log gᵢ` differentiates back to the simple integrand `a/d` over the genuine tower fraction field
`RatFunc (RatFunc ℚ)`, using the keystone derivation `extendDeriv (implicitDeriv (toPolyG Dt))`
(= `towerFractionFieldDeriv Dt`) of `ComputableFractionFieldDeriv`.

The §2 *rational* Rothstein–Trager theory (`PartialFraction`, `RationalIntegrationGcdLogForm`) is the
template: there `D = d/dx`, `D' = derivative D`, and `A/D = ∑_a a·logDeriv(gcd(D, A − a·D'))` with
`∫ A/D = ∑_a a·log(gcd(…))`. The §5.6 case differs in exactly one place — the base derivation: `d/dx`
is replaced by the *monomial* derivation `Δ = implicitDeriv (toPolyG Dt)` on `k[t]` (`k = ℚ(x)`), and
the fraction-field derivation `d/dx` on `K(x)` by `extendDeriv Δ` on `k(t)`. The residue criterion
uses `Δd = implicitDeriv Dt d` in place of `derivative D`.

This file establishes, **derivation-generically** (over any base `δ : Derivation ℤ K[X] K[X]` with
`[Algebra ℚ K]`, then specialized to the tower):

* **Per-factor logarithmic-derivative identity** (`extendDeriv_logDerivOf`): the log-derivative
  `extendDeriv δ g / g` of a polynomial factor `g` (as a rational function) is `(δ g)/g` — the
  building block of every `log gᵢ` term. The all-inputs lift of the example's individual log-argument
  checks. Direct from the keystone `extendDeriv_logDeriv_mk`.
* **Generic log-sum Leibniz reduction** (`extendDeriv_sum_const_logDerivOf`): for δ-constant
  coefficients `cᵢ` and factors `gᵢ`, `extendDeriv δ (∑ᵢ cᵢ·log gᵢ) = ∑ᵢ cᵢ·(δgᵢ)/gᵢ` — the
  differential half of the integral identity, reducing `D(∑ aᵢ log gᵢ)` to the residue sum
  `∑ aᵢ·(Δgᵢ)/gᵢ`, by additivity + the constant-multiple rule + the per-factor identity. This is the
  exact analogue of §2's `deriv_sum_residue_log`, generalized to `extendDeriv δ`.
* **Specialization to the tower** (`towerLogPart_*`): the same two identities over
  `RatFunc (RatFunc ℚ)` with `δ = implicitDeriv (toPolyG Dt)`, i.e. the actual carrier of
  `cResidueResultantTower`/`cLogArgTower`.

**The remaining gap** is the *residue-matching* half: that the residue sum `∑ aᵢ·(Δgᵢ)/gᵢ` equals the
integrand `a/d`. Over a splitting field where `d = ∏(t−αⱼ)`, this is the partial-fraction
`a/d = ∑ⱼ (a(αⱼ)/d'(αⱼ))/(t−αⱼ)` matched against `∑ⱼ cⱼ·Δ(t−αⱼ)/(t−αⱼ)`. In §2 (`d/dx`) the match is
immediate because `Δ(t−αⱼ) = 1`; in §5.6 `Δ(t−αⱼ) = Δt − Δαⱼ` with **`αⱼ` a constant of `t` but not
of `x`** (the roots live in an algebraic extension of `k = ℚ(x)`, where `Δ = D` acts nontrivially), so
the match is the genuine splitting-field/algebraic-extension argument of Bronstein Theorem 5.6.1 —
the analogue of §2 `deriv_sum_residue_log`'s partial fraction, but over the tower, and deferred here.
The *differential* spine (everything `D(∑ aᵢ log gᵢ)` reduces to before the residue match) is proved. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### Per-factor logarithmic-derivative identity (generic base derivation) -/

section Generic
variable {K : Type*} [Field K] [Algebra ℚ K] (δ : Derivation ℤ K[X] K[X])

/-- **Per-factor logarithmic derivative** under the extended derivation `extendDeriv δ`: for a
polynomial factor `g`, the log-derivative `extendDeriv δ (algMap g) / algMap g` is the rational
function `(δ g)/g`. This is the §5.6 building block `D(log gᵢ) = (Δ gᵢ)/gᵢ` — the all-inputs
generalization of the example's per-residue log argument. Restatement of the keystone
`extendDeriv_logDeriv_mk` in residue-criterion phrasing. -/
theorem extendDeriv_logDerivOf (g : K[X]) :
    extendDeriv δ (algebraMap K[X] (RatFunc K) g) / algebraMap K[X] (RatFunc K) g
      = RatFunc.mk (δ g) g :=
  extendDeriv_logDeriv_mk δ g

/-- `extendDeriv δ` kills the image of a δ-constant polynomial: if `δ c = 0` then
`extendDeriv δ (algMap c) = 0`. Used to pull the constant residue coefficients `aᵢ` out of the
log-sum derivative. -/
theorem extendDeriv_algebraMap_of_deriv_eq_zero {c : K[X]} (hc : δ c = 0) :
    extendDeriv δ (algebraMap K[X] (RatFunc K) c) = 0 := by
  rw [extendDeriv_algebraMap, hc, map_zero]

/-- **Constant-multiple rule** for `extendDeriv δ`: if `δ c = 0` (a residue coefficient is a
δ-constant), then `extendDeriv δ (algMap c · y) = algMap c · extendDeriv δ y` — the residue scalar
passes through the derivation. From the Leibniz rule with the constant factor annihilated. -/
theorem extendDeriv_const_mul {c : K[X]} (hc : δ c = 0) (y : RatFunc K) :
    extendDeriv δ (algebraMap K[X] (RatFunc K) c * y)
      = algebraMap K[X] (RatFunc K) c * extendDeriv δ y := by
  rw [Derivation.leibniz, extendDeriv_algebraMap_of_deriv_eq_zero δ hc, smul_zero, add_zero,
    smul_eq_mul]

/-! ### Generic log-sum Leibniz reduction (the differential half of the integral identity)

The §2 `deriv_sum_residue_log` template, generalized to `extendDeriv δ`: modeling each `log gᵢ` by an
abstract `L i` whose log-derivative is `(δ gᵢ)/gᵢ`, the derivative of `∑ᵢ cᵢ·log gᵢ` (δ-constant
coefficients `cᵢ`) is the residue sum `∑ᵢ cᵢ·(δ gᵢ)/gᵢ`. -/

/-- **Log-sum Leibniz reduction** (the §5.6 differential identity, all inputs): for δ-constant residue
coefficients `c i` (`δ (c i) = 0`) and an abstract `log` model `L` with
`extendDeriv δ (L i) = algMap (δ (g i)) / algMap (g i)` (the §5.6 per-factor log-derivative
`extendDeriv_logDerivOf`), the derivative of the logarithmic part `∑ᵢ algMap(cᵢ)·L i` is the residue
sum `∑ᵢ algMap(cᵢ)·algMap(δ gᵢ)/algMap(gᵢ)`. This is `D(∑ aᵢ log gᵢ) = ∑ aᵢ·(Δgᵢ)/gᵢ`, the exact
analogue of §2's `deriv_sum_residue_log` over the tower derivation `extendDeriv δ`; it reduces the
integral identity to matching the residue sum against the integrand `a/d` (the deferred
splitting-field step). -/
theorem extendDeriv_sum_const_logDerivOf {ι : Type*} (s : Finset ι) (c g : ι → K[X])
    (hc : ∀ i ∈ s, δ (c i) = 0) (L : ι → RatFunc K)
    (hL : ∀ i ∈ s, extendDeriv δ (L i)
      = algebraMap K[X] (RatFunc K) (δ (g i)) / algebraMap K[X] (RatFunc K) (g i)) :
    extendDeriv δ (∑ i ∈ s, algebraMap K[X] (RatFunc K) (c i) * L i)
      = ∑ i ∈ s, algebraMap K[X] (RatFunc K) (c i)
          * (algebraMap K[X] (RatFunc K) (δ (g i)) / algebraMap K[X] (RatFunc K) (g i)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [extendDeriv_const_mul δ (hc i hi), hL i hi]

/-- **Log-sum Leibniz reduction, `RatFunc.mk` form**: the same as `extendDeriv_sum_const_logDerivOf`
but with each residue term written as the rational function `RatFunc.mk (δ gᵢ) gᵢ = (δ gᵢ)/gᵢ` (the
form delivered by the keystone `extendDeriv_logDeriv_mk`), so the right side is literally
`∑ᵢ algMap(cᵢ)·mk (δ gᵢ) gᵢ` — the §5.6 residue sum exactly as `cLogArgTower` produces its factors. -/
theorem extendDeriv_sum_const_logDerivOf_mk {ι : Type*} (s : Finset ι) (c g : ι → K[X])
    (hc : ∀ i ∈ s, δ (c i) = 0) (L : ι → RatFunc K)
    (hL : ∀ i ∈ s, extendDeriv δ (L i)
      = algebraMap K[X] (RatFunc K) (δ (g i)) / algebraMap K[X] (RatFunc K) (g i)) :
    extendDeriv δ (∑ i ∈ s, algebraMap K[X] (RatFunc K) (c i) * L i)
      = ∑ i ∈ s, algebraMap K[X] (RatFunc K) (c i) * RatFunc.mk (δ (g i)) (g i) := by
  rw [extendDeriv_sum_const_logDerivOf δ s c g hc L hL]
  exact Finset.sum_congr rfl fun i _ => by rw [RatFunc.mk_eq_div]

end Generic

/-! ### The d/dx specialization: the generic spine recovers §2's full integral identity
Taking the base derivation `δ = derivative'` (Mathlib's `Polynomial.derivative` as a `Derivation`),
`extendDeriv derivative'` is the d/dx derivation on `RatFunc K` — equal to the repo's `ratFuncDeriv`
(both extend `derivative` on `K[X]`, so they coincide by `derivation_ext_fractionRing`). This lets the
§2 *rational* Rothstein–Trager integral identity (`ratFunc_eq_sum_residue_gcd`,
`deriv_sum_residue_log`) compose with the generic spine above: the **complete** integral identity
`D(∑ a·log gₐ) = A/D` holds for d/dx, with the residue match supplied by §2's partial fraction. This
is the end-to-end anchor; the tower case (§5.6) reuses the *same* spine (`extendDeriv δ`,
`extendDeriv_sum_const_logDerivOf`) with `δ` the monomial derivation, the only missing piece being the
tower analogue of the §2 residue match (the deferred splitting-field step). -/

section Ddx
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- `Polynomial.derivative` packaged as a `Derivation ℤ K[X] K[X]` (Mathlib's `K`-derivation
`derivative'` restricted to the base `ℤ`). The d/dx base derivation, so
`extendDeriv derivativeDerivation` is d/dx on `RatFunc K`. -/
noncomputable def derivativeDerivation : Derivation ℤ K[X] K[X] :=
  (Polynomial.derivative' (R := K)).restrictScalars ℤ

omit [Algebra ℚ K] in
@[simp] theorem derivativeDerivation_apply (p : K[X]) :
    derivativeDerivation p = derivative p := rfl

omit [Algebra ℚ K] in
/-- **`extendDeriv derivativeDerivation` is d/dx on `RatFunc K`**, at the function level: it computes
the repo's `ratFuncDeriv` (the §2 d/dx derivation) on every rational function. Both are the quotient
rule with `derivative` as the base (`extendDerivFun_mk`/`ratFuncDeriv_mk`), so they agree on each
`RatFunc.mk p q` by `RatFunc.induction_on'`. (Stated at the function level to side-step the field
`Module ℤ` diamond on the bundled `Derivation`.) -/
theorem extendDerivFun_derivativeDerivation (x : RatFunc K) :
    extendDerivFun (derivativeDerivation (K := K)) x = ratFuncDeriv x := by
  induction x using RatFunc.induction_on' with | _ p q hq =>
  rw [extendDerivFun_mk, ratFuncDeriv_mk, derivativeDerivation_apply, derivativeDerivation_apply]

/-- **`extendDeriv derivativeDerivation` is d/dx**, applied form: `extendDeriv derivativeDerivation x`
equals `ratFuncDeriv x` (the d/dx derivation underlying the §2 `Differential (RatFunc K)` instance). -/
theorem extendDeriv_derivativeDerivation_apply (x : RatFunc K) :
    extendDeriv (derivativeDerivation (K := K)) x = ratFuncDeriv x := by
  rw [extendDeriv_apply, extendDerivFun_derivativeDerivation]

end Ddx

/-- Headline restatement: the §5.6 per-factor log-derivative `D(log gᵢ) = (Δ gᵢ)/gᵢ` over the tower
derivation `extendDeriv δ`. -/
example {K : Type*} [Field K] [Algebra ℚ K] (δ : Derivation ℤ K[X] K[X]) (g : K[X]) :
    extendDeriv δ (algebraMap K[X] (RatFunc K) g) / algebraMap K[X] (RatFunc K) g
      = RatFunc.mk (δ g) g :=
  extendDeriv_logDerivOf δ g

/-- Headline restatement: the §5.6 log-sum Leibniz reduction `D(∑ aᵢ·log gᵢ) = ∑ aᵢ·(Δ gᵢ)/gᵢ` for
δ-constant residue coefficients `aᵢ`, over the tower derivation `extendDeriv δ`. -/
example {K : Type*} [Field K] [Algebra ℚ K] (δ : Derivation ℤ K[X] K[X]) {ι : Type*} (s : Finset ι)
    (c g : ι → K[X]) (hc : ∀ i ∈ s, δ (c i) = 0) (L : ι → RatFunc K)
    (hL : ∀ i ∈ s, extendDeriv δ (L i)
      = algebraMap K[X] (RatFunc K) (δ (g i)) / algebraMap K[X] (RatFunc K) (g i)) :
    extendDeriv δ (∑ i ∈ s, algebraMap K[X] (RatFunc K) (c i) * L i)
      = ∑ i ∈ s, algebraMap K[X] (RatFunc K) (c i)
          * (algebraMap K[X] (RatFunc K) (δ (g i)) / algebraMap K[X] (RatFunc K) (g i)) :=
  extendDeriv_sum_const_logDerivOf δ s c g hc L hL

/-! ### Specialization to the genuine tower fraction field `RatFunc (RatFunc ℚ)`
The §5.6 identities on the *actual* carrier of `cResidueResultantTower`/`cLogArgTower`: the tower
derivation `towerFractionFieldDeriv Dt = extendDeriv (implicitDeriv (toPolyG Dt))` on
`RatFunc (RatFunc ℚ)`, with the monomial base `Δ = implicitDeriv (toPolyG Dt)`. -/

open CPolyG

/-- The engine carrier `CFieldSpec.K QFunNZ` is `RatFunc ℚ`, a `ℚ`-algebra. Re-declared as a local
instance (matching the keystone's) so the tower specialization synthesizes the **same** `Algebra ℚ`
as `towerFractionFieldDeriv`, avoiding an instance-mismatch detour. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K QFunNZ) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- **The §5.6 per-factor log-derivative on the tower**: for a log argument `g ∈ (RatFunc ℚ)[X]` (e.g.
the `gcd_t(d, a − c·Dd)` produced by `cLogArgTower`), the log-derivative of `g` under the tower
derivation `towerFractionFieldDeriv Dt` is `(Δ g)/g` with `Δ = implicitDeriv (toPolyG Dt)` the monomial
derivation. The all-inputs generalization of `logPartTower_example`'s per-residue log-argument check,
on the genuine tower fraction field. The keystone `towerFractionFieldDeriv_logDeriv`, restated in
residue-criterion phrasing. -/
theorem towerLogPart_logDerivOf (Dt : CPolyG QFunNZ) (g : (CFieldSpec.K QFunNZ)[X]) :
    towerFractionFieldDeriv Dt (algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) g)
        / algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) g
      = RatFunc.mk (Differential.implicitDeriv (toPolyG Dt) g) g :=
  towerFractionFieldDeriv_logDeriv Dt g

/-- **The §5.6 log-sum Leibniz reduction on the tower** (`D(∑ aᵢ·log gᵢ) = ∑ aᵢ·(Δ gᵢ)/gᵢ`): for the
monomial-derivation tower `RatFunc (RatFunc ℚ)`, with δ-constant residue coefficients `cᵢ` and log
arguments `gᵢ ∈ (RatFunc ℚ)[X]` modeled by `L`, the derivative of the logarithmic part
`∑ᵢ algMap(cᵢ)·log gᵢ` is the residue sum `∑ᵢ algMap(cᵢ)·(Δ gᵢ)/gᵢ` under `towerFractionFieldDeriv Dt`.
The differential half of the §5.6 integral identity over the genuine tower fraction field — the
all-inputs generalization of `logPartTower_example` to the integral form `D(∑ aᵢ log gᵢ) = a/d` (the
residue match against `a/d` being the deferred splitting-field step). Proved by `map_sum` + the
constant-multiple rule (`Derivation.leibniz` with the δ-constant factor killed via
`towerFractionFieldDeriv_algebraMap`) + the per-factor `hL`. -/
theorem towerLogPart_sum_const_logDerivOf (Dt : CPolyG QFunNZ) {ι : Type*} (s : Finset ι)
    (c g : ι → (CFieldSpec.K QFunNZ)[X])
    (hc : ∀ i ∈ s, Differential.implicitDeriv (toPolyG Dt) (c i) = 0)
    (L : ι → RatFunc (CFieldSpec.K QFunNZ))
    (hL : ∀ i ∈ s, towerFractionFieldDeriv Dt (L i)
      = algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (Differential.implicitDeriv (toPolyG Dt) (g i))
          / algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (g i)) :
    towerFractionFieldDeriv Dt (∑ i ∈ s, algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (c i) * L i)
      = ∑ i ∈ s, algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (c i)
          * (algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (Differential.implicitDeriv (toPolyG Dt) (g i))
              / algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) (g i)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Derivation.leibniz, towerFractionFieldDeriv_algebraMap, hc i hi, map_zero, smul_zero,
    add_zero, smul_eq_mul, hL i hi]

/-- Headline restatement: the §5.6 per-factor log-derivative on the genuine tower carrier. -/
example (Dt : CPolyG QFunNZ) (g : (CFieldSpec.K QFunNZ)[X]) :
    towerFractionFieldDeriv Dt (algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) g)
        / algebraMap _ (RatFunc (CFieldSpec.K QFunNZ)) g
      = RatFunc.mk (Differential.implicitDeriv (toPolyG Dt) g) g :=
  towerLogPart_logDerivOf Dt g

#print axioms extendDeriv_logDerivOf
#print axioms extendDeriv_sum_const_logDerivOf
#print axioms extendDeriv_sum_const_logDerivOf_mk
#print axioms extendDeriv_derivativeDerivation_apply
#print axioms towerLogPart_logDerivOf
#print axioms towerLogPart_sum_const_logDerivOf

end DeepWiki.SymbolicIntegration
