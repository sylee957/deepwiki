import DeepWiki.TimeSeries.StationaryProcesses
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-! # The autocovariance covariance matrix (toward the converse of Theorem 1.5.2)
For an autocovariance candidate `κ : ℤ → ℝ`, the finite covariance matrix
`[κ(i − j)]_{i,j ∈ I}`. When `κ` is even and non-negative definite this matrix is
symmetric and positive semidefinite — the input to the multivariate Gaussian used
to build a stationary Gaussian process with autocovariance `κ`. -/

namespace DeepWiki.TimeSeries

open Matrix

variable {κ : ℤ → ℝ}

/-- The covariance matrix `[κ(i − j)]` of a stationary process with autocovariance
`κ`, indexed by a finite set `I` of times. -/
def acvfCovMatrix (κ : ℤ → ℝ) (I : Finset ℤ) : Matrix I I ℝ :=
  .of fun i j => κ ((i : ℤ) - (j : ℤ))

@[simp] theorem acvfCovMatrix_apply (I : Finset ℤ) (i j : I) :
    acvfCovMatrix κ I i j = κ ((i : ℤ) - (j : ℤ)) := rfl

/-- Restricting the covariance matrix to a sub-index set is the covariance matrix of
that sub-set (consistency, for the projective family). -/
theorem acvfCovMatrix_submatrix {I J : Finset ℤ} (hJI : J ⊆ I) :
    (acvfCovMatrix κ I).submatrix (fun i : J => ⟨i, hJI i.2⟩) (fun i : J => ⟨i, hJI i.2⟩)
      = acvfCovMatrix κ J := rfl

/-- For an even, non-negative-definite `κ`, the covariance matrix `[κ(i − j)]` is
positive semidefinite (and symmetric). -/
theorem posSemidef_acvfCovMatrix (heven : ∀ h : ℤ, κ (-h) = κ h)
    (hnd : IsNonnegDefinite κ) (I : Finset ℤ) : (acvfCovMatrix κ I).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun x => ?_⟩
  · simp only [acvfCovMatrix_apply, star_trivial]
    rw [show ((j : ℤ) - i) = -((i : ℤ) - j) by ring, heven]
  · rw [dot_mulVec_eq_sum_sum]
    simp only [Pi.star_apply, star_trivial, acvfCovMatrix_apply]
    rw [show (∑ j : I, ∑ i : I, x i * κ ((i : ℤ) - j) * x j)
          = ∑ k, ∑ l, x (I.equivFin.symm k) * x (I.equivFin.symm l)
              * κ ((↑(I.equivFin.symm k) : ℤ) - ↑(I.equivFin.symm l)) from ?_]
    · exact hnd I.card (fun k => x (I.equivFin.symm k)) (fun k => (↑(I.equivFin.symm k) : ℤ))
    · rw [Finset.sum_comm,
          ← Equiv.sum_comp I.equivFin.symm
            (fun i : I => ∑ j : I, x i * κ ((i : ℤ) - j) * x j)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Equiv.sum_comp I.equivFin.symm
            (fun j : I => x (I.equivFin.symm k) * κ ((↑(I.equivFin.symm k) : ℤ) - j) * x j)]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring

end DeepWiki.TimeSeries
