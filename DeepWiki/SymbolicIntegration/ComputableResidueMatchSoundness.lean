import DeepWiki.SymbolicIntegration.ComputableLogPartTowerSoundness
import DeepWiki.SymbolicIntegration.ComputableRadicalLogSoundness
import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.ResidueMultiplicity

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

/-! ### Step 1: the monomial log-derivative of a linear factor `t − C α`

Over the tower derivation `D = extendDeriv (implicitDeriv v)` with `v = toPolyG Dt`, the implicit
derivative of a linear factor is `implicitDeriv v (X − C α) = v − C α′` (Mathlib `implicitDeriv_X`,
`implicitDeriv_C`). This is the structural source of the ★ absorption: the log-derivative of `t − α` is
`(v − C α′)/(t − α)`, NOT `1/(t − α)`. -/

variable {K : Type*} [Field K] [Differential K]

/-- **The implicit derivative of a linear factor** `implicitDeriv v (X − C α) = v − C α′` over a
differential base field `K`. The structural source of the Rothstein–Trager monomial absorption: `D(t−α)`
is `Dt − α′`, not `1`. By `implicitDeriv_X` and `implicitDeriv_C` (Mathlib). -/
theorem implicitDeriv_X_sub_C (v : K[X]) (α : K) :
    Differential.implicitDeriv v (X - C α) = v - C (α′) := by
  rw [map_sub, Differential.implicitDeriv_X, Differential.implicitDeriv_C]

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

end ResidueMatchTower

end DeepWiki.SymbolicIntegration
