import DeepWiki.SymbolicIntegration.Computable.MonomialDeriv
import DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors

/-! # Algebraic Hermite degree bounds

Leading-degree estimates for the Hermite numerator relation `a = c·D(f) + e·f + g`, including the
`N - δ` form used by the algebraic Hermite completeness reduction. -/

open Polynomial Differential
open scoped Differential

namespace DeepWiki.SymbolicIntegration.AlgebraicHermite

section DegreeBound

variable {k : Type*} [Field k] [Differential k]

/-- The per-component degree bound `hermiteBoundN da δ db = da + δ + 1 − db` (as `ℤ`, so a negative
value forces `fᵢ = 0`). -/
def hermiteBoundN (da δ db : ℕ) : ℤ := (da : ℤ) + (δ : ℤ) + 1 - (db : ℤ)

/-- The candidate top degree `hermiteCandTopDegree v c f = deg(c) + deg(f) + max(0, deg(v) − 1)`, the
degree of the dominant term `c·D(f)` (`D = implicitDeriv v`). -/
def hermiteCandTopDegree (v c f : k[X]) : ℕ :=
  c.natDegree + f.natDegree + max 0 (v.natDegree - 1)

/-- In `a = c·D(f) + e·f + g` (`D = implicitDeriv v`) with the lower terms bounded by
`hermiteCandTopDegree v c f`, the degree of `a` is at most `hermiteCandTopDegree v c f`. -/
theorem natDegree_le_hermiteCandTopDegree {v a c e f g : k[X]}
    (heq : a = c * Differential.implicitDeriv v f + e * f + g)
    (hef : (e * f).natDegree ≤ hermiteCandTopDegree v c f)
    (hg : g.natDegree ≤ hermiteCandTopDegree v c f) :
    a.natDegree ≤ hermiteCandTopDegree v c f := by
  rw [heq]
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ hef)) hg)
  calc (c * Differential.implicitDeriv v f).natDegree
      ≤ c.natDegree + (Differential.implicitDeriv v f).natDegree := natDegree_mul_le
    _ ≤ c.natDegree + (f.natDegree + max 0 (v.natDegree - 1)) := by
        gcongr; exact natDegree_implicitDeriv_le v f
    _ = hermiteCandTopDegree v c f := by rw [hermiteCandTopDegree]; ring

/-- The Hermite degree bound, sharp top-coefficient form: in `a = c·D(f) + e·f + g` with the lower
terms bounded, if `a.coeff (hermiteCandTopDegree v c f) ≠ 0` then
`deg(f) ≤ deg(a) − deg(c) − max(0, deg(v) − 1)`. -/
theorem natDegree_hermiteNum_le_of_topCoeff_ne_zero {v a c e f g : k[X]}
    (heq : a = c * Differential.implicitDeriv v f + e * f + g)
    (hef : (e * f).natDegree ≤ hermiteCandTopDegree v c f)
    (hg : g.natDegree ≤ hermiteCandTopDegree v c f)
    (htop : a.coeff (hermiteCandTopDegree v c f) ≠ 0) :
    f.natDegree ≤ a.natDegree - c.natDegree - max 0 (v.natDegree - 1) := by
  have hub := natDegree_le_hermiteCandTopDegree heq hef hg
  have hda : a.natDegree = hermiteCandTopDegree v c f :=
    le_antisymm hub (le_natDegree_of_ne_zero htop)
  rw [hda, hermiteCandTopDegree]; omega

/-- The Hermite degree bound in `N − δ` form: with `deg(c) = deg(b)` and `deg(v) = δ`,
`(deg f : ℤ) ≤ hermiteBoundN (deg a) δ (deg b) − δ`. -/
theorem natDegree_hermiteNum_le {v a c e f g b : k[X]} (δ : ℕ)
    (heq : a = c * Differential.implicitDeriv v f + e * f + g)
    (hef : (e * f).natDegree ≤ hermiteCandTopDegree v c f)
    (hg : g.natDegree ≤ hermiteCandTopDegree v c f)
    (htop : a.coeff (hermiteCandTopDegree v c f) ≠ 0)
    (hδ : v.natDegree = δ)
    (hcdeg : c.natDegree = b.natDegree) :
    (f.natDegree : ℤ) ≤ hermiteBoundN a.natDegree δ b.natDegree - (δ : ℤ) := by
  have hub := natDegree_le_hermiteCandTopDegree heq hef hg
  have hda : a.natDegree = c.natDegree + f.natDegree + max 0 (v.natDegree - 1) :=
    le_antisymm hub (by simpa [hermiteCandTopDegree] using le_natDegree_of_ne_zero htop)
  have hmax : ((max 0 (v.natDegree - 1) : ℕ) : ℤ) = max 0 ((δ : ℤ) - 1) := by
    rw [hδ]; push_cast; omega
  have hdaℤ : (a.natDegree : ℤ)
      = (b.natDegree : ℤ) + (f.natDegree : ℤ) + max 0 ((δ : ℤ) - 1) := by
    have : (a.natDegree : ℤ)
        = (c.natDegree : ℤ) + (f.natDegree : ℤ) + ((max 0 (v.natDegree - 1) : ℕ) : ℤ) := by
      exact_mod_cast hda
    rw [this, hmax, hcdeg]
  rw [hermiteBoundN]; omega

end DegreeBound

/-! ## Operational witness — the degree bound is non-vacuous over `ℚ[X]` -/

section Witness

open scoped Differential

/-- Over the constant field `ℚ`, `implicitDeriv (X²) X = X²` (the `mapCoeffs` term vanishes). -/
theorem implicitDeriv_X2_X :
    Differential.implicitDeriv (X ^ 2 : ℚ[X]) X = X ^ 2 := by
  rw [Differential.implicitDeriv, derivative']
  simp [Differential.mapCoeffs]

/-- The Hermite degree bound fires on the concrete relation `X² = 1·D(X)` over `ℚ[X]`:
`deg X = 1 ≤ 1`. -/
theorem hermite_degree_bound_witness :
    (X : ℚ[X]).natDegree
      ≤ (X ^ 2 : ℚ[X]).natDegree - (1 : ℚ[X]).natDegree
        - max 0 ((X ^ 2 : ℚ[X]).natDegree - 1) := by
  have heq : (X ^ 2 : ℚ[X])
      = (1 : ℚ[X]) * Differential.implicitDeriv (X ^ 2 : ℚ[X]) X + 0 * X + 0 := by
    rw [implicitDeriv_X2_X]; ring
  have hcand : AlgebraicHermite.hermiteCandTopDegree (X ^ 2 : ℚ[X]) 1 X = 2 := by
    simp [AlgebraicHermite.hermiteCandTopDegree, natDegree_X]
  have htop : (X ^ 2 : ℚ[X]).coeff (AlgebraicHermite.hermiteCandTopDegree (X ^ 2 : ℚ[X]) 1 X) ≠ 0 := by
    rw [hcand]; simp
  have hef : ((0 : ℚ[X]) * X).natDegree
      ≤ AlgebraicHermite.hermiteCandTopDegree (X ^ 2 : ℚ[X]) 1 X := by simp
  have hg : (0 : ℚ[X]).natDegree ≤ AlgebraicHermite.hermiteCandTopDegree (X ^ 2 : ℚ[X]) 1 X := by simp
  exact AlgebraicHermite.natDegree_hermiteNum_le_of_topCoeff_ne_zero heq hef hg htop

end Witness

/-! ### Axiom audit -/

#print axioms natDegree_le_hermiteCandTopDegree
#print axioms natDegree_hermiteNum_le_of_topCoeff_ne_zero
#print axioms natDegree_hermiteNum_le
#print axioms hermite_degree_bound_witness

end DeepWiki.SymbolicIntegration.AlgebraicHermite
