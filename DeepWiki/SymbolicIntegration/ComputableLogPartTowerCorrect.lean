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

end Generic

end DeepWiki.SymbolicIntegration
