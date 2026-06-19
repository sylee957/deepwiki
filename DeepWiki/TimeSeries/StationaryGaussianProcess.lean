import DeepWiki.TimeSeries.StationaryProcesses
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily
import DeepWiki.MeasureTheory.KolmogorovExtension
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

/-! ## The Gaussian projective family with autocovariance `κ` -/

open MeasureTheory ProbabilityTheory NormedSpace WithLp

/-- The finite-dimensional centered Gaussian distribution with covariance matrix
`[κ(i − j)]`, as a measure on `I → ℝ` (the form used by the Kolmogorov extension). -/
noncomputable def gaussianProjectiveFamily (κ : ℤ → ℝ) (I : Finset ℤ) : Measure (I → ℝ) :=
  multivariateGaussian 0 (acvfCovMatrix κ I) |>.map (MeasurableEquiv.toLp 2 (I → ℝ)).symm

/-- `gaussianProjectiveFamily κ I` is, up to the `ofLp` equivalence, the centered
multivariate Gaussian with covariance `acvfCovMatrix κ I`. -/
lemma measurePreserving_ofLp_gaussianProjectiveFamily (κ : ℤ → ℝ) (I : Finset ℤ) :
    MeasurePreserving ofLp (multivariateGaussian 0 (acvfCovMatrix κ I))
      (gaussianProjectiveFamily κ I) where
  measurable := by fun_prop
  map_eq := rfl

instance isGaussian_gaussianProjectiveFamily (κ : ℤ → ℝ) (I : Finset ℤ) :
    IsGaussian (gaussianProjectiveFamily κ I) := by
  rw [gaussianProjectiveFamily,
    show ⇑(MeasurableEquiv.toLp 2 (I → ℝ)).symm = ⇑(EuclideanSpace.equiv I ℝ) from rfl]
  infer_instance

/-- For an even, non-negative-definite `κ`, the family `gaussianProjectiveFamily κ`
is a projective measure family (consistent under restriction) — the hypothesis of
the Kolmogorov extension theorem. -/
lemma isProjectiveMeasureFamily_gaussianProjectiveFamily
    (heven : ∀ h : ℤ, κ (-h) = κ h) (hnd : IsNonnegDefinite κ) :
    IsProjectiveMeasureFamily (α := fun _ : ℤ => ℝ) (gaussianProjectiveFamily κ) := by
  intro I J hJI
  nth_rw 2 [gaussianProjectiveFamily]
  rw [Measure.map_map]
  · have : (Finset.restrict₂ (π := fun _ : ℤ => ℝ) hJI ∘ (MeasurableEquiv.toLp 2 (I → ℝ)).symm)
        = ofLp ∘ (EuclideanSpace.restrict₂ hJI) := by ext; simp
    rw [this, ((measurePreserving_ofLp_gaussianProjectiveFamily κ J).comp
        (measurePreserving_restrict₂_multivariateGaussian
          (posSemidef_acvfCovMatrix heven hnd I) hJI)).map_eq]
  · exact Finset.measurable_restrict₂ _
  · fun_prop

/-! ## The stationary Gaussian process measure (Kolmogorov extension) -/

/-- The law on `ℤ → ℝ` of a process whose finite-dimensional distributions are the
centered Gaussians with covariance `[κ(i − j)]`, obtained by applying the Kolmogorov
extension theorem to `gaussianProjectiveFamily κ`. Requires `κ` even and
non-negative definite. -/
noncomputable def stationaryGaussianMeasure (heven : ∀ h : ℤ, κ (-h) = κ h)
    (hnd : IsNonnegDefinite κ) : Measure (ℤ → ℝ) :=
  projectiveLimit (gaussianProjectiveFamily κ)
    (isProjectiveMeasureFamily_gaussianProjectiveFamily heven hnd)

/-- `stationaryGaussianMeasure` is the projective limit of the Gaussian family: its
finite-dimensional marginals are exactly `gaussianProjectiveFamily κ`. -/
lemma isProjectiveLimit_stationaryGaussianMeasure (heven : ∀ h : ℤ, κ (-h) = κ h)
    (hnd : IsNonnegDefinite κ) :
    IsProjectiveLimit (stationaryGaussianMeasure heven hnd) (gaussianProjectiveFamily κ) :=
  isProjectiveLimit_projectiveLimit _

instance isProbabilityMeasure_stationaryGaussianMeasure (heven : ∀ h : ℤ, κ (-h) = κ h)
    (hnd : IsNonnegDefinite κ) : IsProbabilityMeasure (stationaryGaussianMeasure heven hnd) :=
  isProbabilityMeasure_projectiveLimit _

end DeepWiki.TimeSeries
