import DeepWiki.SymbolicIntegration.ComputableLogPartTowerSoundness
import DeepWiki.SymbolicIntegration.ComputableRadicalLogSoundness
import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.ResidueMultiplicity
import DeepWiki.SymbolicIntegration.MonomialExtensions

/-! # The Rothstein–Trager residue-MATCH correctness (Bronstein Thm 5.6.1, abstract)

`ComputableLogPartTowerSoundness` reduced the checker-free normal-part one-shot to a single hypothesis
`hmatch` — the **residue match**: that the integrator's logarithmic part `∑ᵢ cᵢ·D(log vᵢ)` (over the tower
with the monomial derivation `D = cmonomialDeriv Dt`, so `D(t−α) = Dt − α′`, NOT `1`) sums to the simple
integrand `a/d` over `RatFunc (CFieldSpec.K α)`. The residues `cᵢ` are the roots of the Rothstein–Trager
resultant `R(z) = res_t(d, a − z·Dd)` (PROVEN: `roots_residueResultantTowerG_eq_residues`) and each
`vᵢ = gcd_t(d, a − cᵢ·Dd)`.

The base-field analogue is `ratFunc_eq_sum_residue_grouped` (`PartialFraction`): for `D = ∏(X−α)`
squarefree and the *standard* polynomial derivative (`(X−α)′ = 1`),
`A/D = ∑_a a·logDeriv(∏_{res(α)=a}(X−α))`. The ★ subtlety the prompt flags (the same gap as the algebraic
`isRadicalLogIntegral_of_residue_match`): over a monomial `D(t−α) = Dt − α′ ≠ 1`, so the Lagrange
identity does NOT transport verbatim — the residue `c` at `α` must **absorb** the `Dt − α′` factor
(Bronstein Thm 5.6.1, the *differentiated* RT criterion).

This file builds the residue-match identity incrementally — small, individually-committed lemmas — toward
discharging the `hmatch` hypothesis of `logResidueSumG_eq_of_residue_match`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

namespace ResidueMatchTower

/-! ### Step 1 (reused): the monomial derivative of a linear factor `t − C α`

Over the tower derivation `D = extendDeriv (implicitDeriv v)` with `v = toPolyG Dt`, the implicit
derivative of a linear factor is `implicitDeriv v (X − C α) = v − C α′` — `MonomialExtensions`'
`implicitDeriv_X_sub_C` (the §3.4 root-characterization crux). This is the structural source of the ★
absorption: the log-derivative of `t − α` is `(v − C α′)/(t − α)`, NOT `1/(t − α)`. -/

variable {K : Type*} [Field K] [Differential K]

/-! ### Step 2: the monomial log-derivative of a linear factor in `K(t)`

Under the extended monomial derivation `extendDeriv (implicitDeriv v)`, the log-derivative of the linear
factor `t − α` reads `(v − C α′)/(t − α)` over `RatFunc K` — the ★ absorption made explicit: it is
`(Dt − α′)/(t − α)`, NOT `1/(t − α)`. Combines `extendDeriv_logDeriv` with `implicitDeriv_X_sub_C`. -/

/-- **The monomial log-derivative of a linear factor** — over `extendDeriv (implicitDeriv v)`,
`D(t−α)/(t−α) = algebraMap(v − C α′) / algebraMap(t − α)` in `RatFunc K`. The Rothstein–Trager monomial
absorption made explicit at the per-factor level: the log-derivative is `(Dt − α′)/(t − α)`, not `1/(t − α)`.
By `extendDeriv_logDeriv` (the generic logarithmic-derivative reading) and `implicitDeriv_X_sub_C`. -/
theorem extendDeriv_implicitDeriv_logDeriv_X_sub_C [Algebra ℚ K] (v : K[X]) (α : K) :
    extendDeriv (Differential.implicitDeriv v) (algebraMap K[X] (RatFunc K) (X - C α))
        / algebraMap K[X] (RatFunc K) (X - C α)
      = algebraMap K[X] (RatFunc K) (v - C (α′)) / algebraMap K[X] (RatFunc K) (X - C α) := by
  rw [extendDeriv_logDeriv, implicitDeriv_X_sub_C]

/-! ### Step 3a: the ★ absorption identity at a simple root of `d`

The crux of Bronstein Thm 5.6.1. At a root `α` of the (squarefree) denominator `d`, the monomial
derivative `Dd = implicitDeriv v d` evaluates to `(Dd)(α) = d′(α)·(v(α) − α′)` — the `v(α) − α′` factor
that the residue `cᵢ = a(α)/(Dd)(α)` divides out is exactly what makes `cᵢ·D(t−α)/(t−α)` carry residue
`a(α)/d′(α)` at the place `t−α`, so the monomial RT sum telescopes to `a/d` despite `D(t−α) ≠ 1`.

Proof: `implicitDeriv v d = mapCoeffs d + v·(derivative d)`, so `(Dd)(α) = (mapCoeffs d)(α) +
v(α)·d′(α)`. Mathlib's `deriv_aeval_eq` gives `(d(α))′ = (mapCoeffs d)(α) + d′(α)·α′`; since `d(α) = 0`
its LHS is `0′ = 0`, so `(mapCoeffs d)(α) = −d′(α)·α′`, and the two combine to `d′(α)·(v(α) − α′)`. -/

/-- **`eval` of `mapCoeffs d` at a root of `d`** — for `d(α) = 0`, `(mapCoeffs d)(α) = −d′(α)·α′` over a
differential field `K`. From Mathlib's `deriv_aeval_eq` `(d(α))′ = (mapCoeffs d)(α) + d′(α)·α′` with the
LHS `(0)′ = 0`. The half of the absorption coming from the coefficient derivation `κ_D`. -/
theorem eval_mapCoeffs_of_isRoot (d : K[X]) (α : K) (hα : d.eval α = 0) :
    (Differential.mapCoeffs d).eval α = -((derivative d).eval α * α′) := by
  have h := Differential.deriv_aeval_eq (A := K) (R := K) α d
  simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] at h
  rw [hα] at h
  -- `(0)′ = 0` since the derivation is additive
  rw [show (0 : K)′ = 0 from map_zero _] at h
  -- `0 = (mapCoeffs d)(α) + d′(α)·α′`, so `(mapCoeffs d)(α) = −d′(α)·α′`
  linear_combination -h

/-- **★ The absorption identity at a simple root** (Bronstein Thm 5.6.1) — for `d(α) = 0`, the monomial
derivative `Dd = implicitDeriv v d` evaluates to `(Dd)(α) = d′(α)·(v(α) − α′)`. The residue
`cᵢ = a(α)/(Dd)(α)` divides out this `v(α) − α′`, so `cᵢ·(v − C α′)/(t−α)` carries residue `a(α)/d′(α)`
at `t−α` — the place-wise content making the monomial RT sum reassemble `a/d`. From
`implicitDeriv = mapCoeffs + v·derivative` and `eval_mapCoeffs_of_isRoot`. -/
theorem eval_implicitDeriv_of_isRoot (v d : K[X]) (α : K) (hα : d.eval α = 0) :
    (Differential.implicitDeriv v d).eval α = (derivative d).eval α * (v.eval α - α′) := by
  rw [Differential.implicitDeriv]
  simp only [Derivation.add_apply, Derivation.coe_smul, Pi.smul_apply, smul_eq_mul,
    Derivation.coe_restrictScalars, derivative'_apply, eval_add, eval_mul]
  rw [eval_mapCoeffs_of_isRoot d α hα]
  ring

end ResidueMatchTower

end DeepWiki.SymbolicIntegration
