import DeepWiki.TimeSeries.StationaryProcesses
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
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

/-- The covariance of two coordinate evaluations under `gaussianProjectiveFamily κ I`
is `κ(i − j)`. -/
lemma covariance_eval_gaussianProjectiveFamily (heven : ∀ h : ℤ, κ (-h) = κ h)
    (hnd : IsNonnegDefinite κ) (I : Finset ℤ) (i j : I) :
    cov[fun x => x i, fun x => x j; gaussianProjectiveFamily κ I] = κ ((i : ℤ) - j) := by
  rw [gaussianProjectiveFamily, covariance_map_equiv,
    show ((fun x : I → ℝ => x i) ∘ ⇑(MeasurableEquiv.toLp 2 (I → ℝ)).symm)
        = (fun y : EuclideanSpace ℝ I => y i) from rfl,
    show ((fun x : I → ℝ => x j) ∘ ⇑(MeasurableEquiv.toLp 2 (I → ℝ)).symm)
        = (fun y : EuclideanSpace ℝ I => y j) from rfl,
    covariance_eval_multivariateGaussian (posSemidef_acvfCovMatrix heven hnd I),
    acvfCovMatrix_apply]

/-- Integration against `gaussianProjectiveFamily κ I` reduces to the multivariate
Gaussian via the `ofLp` equivalence. -/
lemma integral_gaussianProjectiveFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Finset ℤ) (f : (I → ℝ) → E) :
    ∫ x, f x ∂(gaussianProjectiveFamily κ I)
      = ∫ x, f (ofLp x) ∂(multivariateGaussian 0 (acvfCovMatrix κ I)) := by
  simp [gaussianProjectiveFamily, integral_map_equiv]

/-- `gaussianProjectiveFamily κ I` is centered: `∫ x = 0`. -/
@[simp] lemma integral_id_gaussianProjectiveFamily (I : Finset ℤ) :
    ∫ x, x ∂(gaussianProjectiveFamily κ I) = 0 := by
  rw [integral_gaussianProjectiveFamily, ← PiLp.coe_continuousLinearEquiv 2 ℝ,
    ContinuousLinearEquiv.integral_comp_id_comm, integral_id_multivariateGaussian, map_zero]

/-- Each coordinate has mean zero under `gaussianProjectiveFamily κ I`. -/
@[simp] lemma integral_eval_gaussianProjectiveFamily (I : Finset ℤ) (i : I) :
    ∫ x, x i ∂(gaussianProjectiveFamily κ I) = 0 := by
  conv => enter [1, 2]; change fun x => ContinuousLinearMap.proj (R := ℝ) i x
  rw [ContinuousLinearMap.integral_comp_id_comm, integral_id_gaussianProjectiveFamily, map_zero]
  exact IsGaussian.integrable_id

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

/-- The autocovariance of the coordinate process under `stationaryGaussianMeasure` is
`κ`: `Cov(ω ↦ ω r, ω ↦ ω s) = κ(r − s)`. The covariance is pushed through the
projective-limit marginal over `{r, s}` to the finite-dimensional Gaussian. -/
lemma covariance_coordinate_stationaryGaussianMeasure (heven : ∀ h : ℤ, κ (-h) = κ h)
    (hnd : IsNonnegDefinite κ) (r s : ℤ) :
    cov[fun ω => ω r, fun ω => ω s; stationaryGaussianMeasure heven hnd] = κ (r - s) := by
  have hr : r ∈ ({r, s} : Finset ℤ) := Finset.mem_insert_self r {s}
  have hs : s ∈ ({r, s} : Finset ℤ) := Finset.mem_insert_of_mem (Finset.mem_singleton_self s)
  have hpl := isProjectiveLimit_stationaryGaussianMeasure heven hnd ({r, s} : Finset ℤ)
  have key := covariance_eval_gaussianProjectiveFamily heven hnd ({r, s} : Finset ℤ) ⟨r, hr⟩ ⟨s, hs⟩
  rw [← hpl, covariance_map (measurable_pi_apply _).aestronglyMeasurable
      (measurable_pi_apply _).aestronglyMeasurable (by fun_prop)] at key
  exact key

/-- The coordinate process `t ↦ ω t` under `stationaryGaussianMeasure` is a Gaussian
process: every finite-dimensional marginal is multivariate Gaussian (Def 1.3.4). -/
lemma isGaussianProcess_stationaryGaussianMeasure (heven : ∀ h : ℤ, κ (-h) = κ h)
    (hnd : IsNonnegDefinite κ) :
    IsGaussianProcess (fun (t : ℤ) (ω : ℤ → ℝ) => ω t) (stationaryGaussianMeasure heven hnd) := by
  refine ⟨fun I => ⟨?_⟩⟩
  rw [show (stationaryGaussianMeasure heven hnd).map (fun ω => I.restrict (fun t => ω t))
        = gaussianProjectiveFamily κ I from isProjectiveLimit_stationaryGaussianMeasure heven hnd I]
  infer_instance

/-- The coordinate process under `stationaryGaussianMeasure` has mean zero. -/
lemma integral_eval_stationaryGaussianMeasure (heven : ∀ h : ℤ, κ (-h) = κ h)
    (hnd : IsNonnegDefinite κ) (t : ℤ) :
    ∫ ω, ω t ∂(stationaryGaussianMeasure heven hnd) = 0 := by
  have ht : t ∈ ({t} : Finset ℤ) := Finset.mem_singleton_self t
  have hpl := isProjectiveLimit_stationaryGaussianMeasure heven hnd ({t} : Finset ℤ)
  rw [show (∫ ω, ω t ∂(stationaryGaussianMeasure heven hnd))
        = ∫ x, x ⟨t, ht⟩ ∂(gaussianProjectiveFamily κ {t}) from ?_]
  · exact integral_eval_gaussianProjectiveFamily (κ := κ) {t} ⟨t, ht⟩
  · rw [← hpl]
    exact (integral_map
      (Finset.measurable_restrict (X := fun _ : ℤ => ℝ) ({t} : Finset ℤ)).aemeasurable
      (measurable_pi_apply (⟨t, ht⟩ : ({t} : Finset ℤ))).aestronglyMeasurable).symm

/-- **Theorem 1.5.2 converse (witness)**: the coordinate process `t ↦ ω t` under
`stationaryGaussianMeasure` is weakly stationary (when `κ` is even and non-negative
definite). -/
lemma isWeaklyStationary_stationaryGaussianMeasure (heven : ∀ h : ℤ, κ (-h) = κ h)
    (hnd : IsNonnegDefinite κ) :
    IsWeaklyStationary (fun (t : ℤ) (ω : ℤ → ℝ) => ω t) (stationaryGaussianMeasure heven hnd) where
  memLp t := ((isGaussianProcess_stationaryGaussianMeasure heven hnd).hasGaussianLaw_eval t).memLp_two
  mean_const s t := by
    simp only [mean]
    rw [integral_eval_stationaryGaussianMeasure heven hnd s,
      integral_eval_stationaryGaussianMeasure heven hnd t]
  acvf_shift r s h := by
    rw [covariance_coordinate_stationaryGaussianMeasure heven hnd r s,
      covariance_coordinate_stationaryGaussianMeasure heven hnd (r + h) (s + h)]
    congr 1
    ring

/-- **Theorem 1.5.2 converse**: the autocovariance of the witness process is `κ`. -/
lemma acvfStat_stationaryGaussianMeasure (heven : ∀ h : ℤ, κ (-h) = κ h)
    (hnd : IsNonnegDefinite κ) (h : ℤ) :
    acvfStat (fun (t : ℤ) (ω : ℤ → ℝ) => ω t) (stationaryGaussianMeasure heven hnd) h = κ h := by
  rw [acvfStat_apply, covariance_coordinate_stationaryGaussianMeasure]
  congr 1
  ring

/-- **Theorem 1.5.2 (converse)**: every even, non-negative-definite function
`κ : ℤ → ℝ` is the autocovariance function of a (Gaussian) weakly stationary
process — namely the coordinate process under `stationaryGaussianMeasure`. -/
theorem exists_isWeaklyStationary_acvfStat_eq (heven : ∀ h : ℤ, κ (-h) = κ h)
    (hnd : IsNonnegDefinite κ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (X : ℤ → Ω → ℝ),
      IsWeaklyStationary X μ ∧ ∀ h, acvfStat X μ h = κ h :=
  ⟨ℤ → ℝ, inferInstance, stationaryGaussianMeasure heven hnd, fun t ω => ω t,
    isWeaklyStationary_stationaryGaussianMeasure heven hnd,
    acvfStat_stationaryGaussianMeasure heven hnd⟩

/-- **Theorem 1.5.2** (full characterization): a function `κ : ℤ → ℝ` is the
autocovariance function of a stationary process if and only if it is even and
non-negative definite. -/
theorem isACVF_iff_even_and_isNonnegDefinite (κ : ℤ → ℝ) :
    (∃ (μ : Measure (ℤ → ℝ)) (X : ℤ → (ℤ → ℝ) → ℝ), IsProbabilityMeasure μ ∧
        IsWeaklyStationary X μ ∧ ∀ h, acvfStat X μ h = κ h)
      ↔ (∀ h, κ (-h) = κ h) ∧ IsNonnegDefinite κ := by
  constructor
  · rintro ⟨μ, X, hμ, hstat, hacvf⟩
    haveI := hμ
    have hfun : acvfStat X μ = κ := funext hacvf
    obtain ⟨heven, hnd⟩ := hstat.even_and_isNonnegDefinite_acvfStat
    rw [hfun] at heven hnd
    exact ⟨fun h => (heven h).symm, hnd⟩
  · rintro ⟨heven, hnd⟩
    exact ⟨stationaryGaussianMeasure heven hnd, fun t ω => ω t, inferInstance,
      isWeaklyStationary_stationaryGaussianMeasure heven hnd,
      acvfStat_stationaryGaussianMeasure heven hnd⟩

end DeepWiki.TimeSeries
