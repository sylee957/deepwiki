import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! # Stochastic processes, the autocovariance function, and stationarity
A (real-valued, ℤ-indexed) stochastic process `X : ℤ → Ω → ℝ` over a probability
space, its mean function and autocovariance function (Def 1.3.1), and weak
(second-order) and strict stationarity (Def 1.3.2, 1.3.3). The elementary
properties of the autocovariance function of a stationary process (§1.5):
`γ(0) ≥ 0`, evenness `γ(−h) = γ(h)`, the bound `|γ(h)| ≤ γ(0)`, and non-negative
definiteness. -/

namespace DeepWiki.TimeSeries

open MeasureTheory ProbabilityTheory

/-- **Definition 1.2.1**: a stochastic process is a family `(Xₜ)_{t ∈ T}` of random variables
(measurable maps `Ω → 𝒳`) on a probability space, indexed by an *arbitrary* set `T` — by
Remark 1, `T` is often `ℤ`, `ℕ`, `[0,∞)` or `ℝ` but need not be a subset of `ℝ`, and the
values need not be real. Modeled as bare functions `T → Ω → 𝒳` (measurability supplied as a
hypothesis where used); the discrete-time real theory below is the case `T = ℤ`, `𝒳 = ℝ`. -/
abbrev Process (T Ω 𝒳 : Type*) := T → Ω → 𝒳

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℤ → Ω → ℝ}

/-! ## Mean and autocovariance -/

/-- The mean function `m_X(t) = E[Xₜ]` of a process. -/
noncomputable def mean (X : ℤ → Ω → ℝ) (μ : Measure Ω) (t : ℤ) : ℝ := ∫ ω, X t ω ∂μ

/-- **Definition 1.3.1**: the autocovariance function `γ_X(r,s) = Cov(Xᵣ, Xₛ)`. -/
noncomputable def acvf (X : ℤ → Ω → ℝ) (μ : Measure Ω) (r s : ℤ) : ℝ := cov[X r, X s; μ]

@[simp] theorem acvf_apply (X : ℤ → Ω → ℝ) (μ : Measure Ω) (r s : ℤ) :
    acvf X μ r s = cov[X r, X s; μ] := rfl

/-- The autocovariance is symmetric in its two arguments: `γ(r,s) = γ(s,r)`. -/
theorem acvf_comm (X : ℤ → Ω → ℝ) (μ : Measure Ω) (r s : ℤ) :
    acvf X μ r s = acvf X μ s r := by
  simp only [acvf_apply]; exact covariance_comm (X r) (X s)

/-! ## Stationarity -/

/-- **Definition 1.3.2**: (weak / second-order) stationarity — each `Xₜ` is square
integrable, the mean `E[Xₜ]` is constant in `t`, and the autocovariance
`Cov(Xᵣ, Xₛ)` is invariant under a common shift `r,s ↦ r+h, s+h` (so it depends
only on the lag `r − s`). -/
structure IsWeaklyStationary (X : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- (i) Each `Xₜ` is square integrable, `E|Xₜ|² < ∞`. -/
  memLp : ∀ t : ℤ, MemLp (X t) 2 μ
  /-- (ii) The mean `E[Xₜ]` is constant in `t`. -/
  mean_const : ∀ s t : ℤ, mean X μ s = mean X μ t
  /-- (iii) The autocovariance is invariant under a common shift, `γ(r,s) = γ(r+h, s+h)`. -/
  acvf_shift : ∀ r s h : ℤ, cov[X r, X s; μ] = cov[X (r + h), X (s + h); μ]

/-- **Definition 1.3.3**: strict stationarity — every finite-dimensional joint
distribution is shift-invariant: the law of `(X_{t₁}, …, X_{tₖ})` equals the law
of `(X_{t₁+h}, …, X_{tₖ+h})`. -/
def IsStrictlyStationary (X : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ (k : ℕ) (t : Fin k → ℤ) (h : ℤ),
    μ.map (fun ω i => X (t i) ω) = μ.map (fun ω i => X (t i + h) ω)

/-- The autocovariance of a stationary process as a function of the lag alone:
`γ_X(h) = Cov(X_{t+h}, Xₜ) = Cov(X_h, X₀)` (Remark 2 after Definition 1.3.2). -/
noncomputable def acvfStat (X : ℤ → Ω → ℝ) (μ : Measure Ω) (h : ℤ) : ℝ := cov[X h, X 0; μ]

theorem acvfStat_apply (X : ℤ → Ω → ℝ) (μ : Measure Ω) (h : ℤ) :
    acvfStat X μ h = cov[X h, X 0; μ] := rfl

/-- For a stationary process, the two-argument autocovariance depends only on the
lag: `Cov(Xᵣ, Xₛ) = γ(r − s)` (Remark 2). -/
theorem IsWeaklyStationary.acvf_eq_acvfStat (hX : IsWeaklyStationary X μ) (r s : ℤ) :
    cov[X r, X s; μ] = acvfStat X μ (r - s) := by
  have hs := hX.acvf_shift r s (-s)
  have e1 : r + -s = r - s := by ring
  have e2 : s + -s = (0 : ℤ) := by ring
  rw [e1, e2] at hs
  rw [acvfStat_apply]
  exact hs

/-! ## Problem 1.11: sums of uncorrelated stationary processes -/

/-- The covariance of two summed processes splits when the cross-covariances vanish:
`Cov(Xₚ + Yₚ, X_q + Y_q) = Cov(Xₚ, X_q) + Cov(Yₚ, Y_q)` when `Cov(Xᵣ, Yₛ) = 0`. -/
private theorem cov_add_add_of_uncorrelated [IsFiniteMeasure μ] {X Y : ℤ → Ω → ℝ}
    (hX : ∀ t, MemLp (X t) 2 μ) (hY : ∀ t, MemLp (Y t) 2 μ)
    (hXY : ∀ r s : ℤ, cov[X r, Y s; μ] = 0) (p q : ℤ) :
    cov[X p + Y p, X q + Y q; μ] = cov[X p, X q; μ] + cov[Y p, Y q; μ] := by
  rw [covariance_add_left (hX p) (hY p) ((hX q).add (hY q)),
      covariance_add_right (hX p) (hX q) (hY q),
      covariance_add_right (hY p) (hX q) (hY q),
      hXY p q, covariance_comm (Y p) (X q), hXY q p]
  ring

/-- **Problem 1.11**: the sum of two uncorrelated weakly stationary processes — `X`, `Y`
stationary with `Cov(Xᵣ, Yₛ) = 0` for all `r, s` — is weakly stationary. -/
theorem IsWeaklyStationary.add_of_uncorrelated [IsFiniteMeasure μ] {X Y : ℤ → Ω → ℝ}
    (hX : IsWeaklyStationary X μ) (hY : IsWeaklyStationary Y μ)
    (hXY : ∀ r s : ℤ, cov[X r, Y s; μ] = 0) :
    IsWeaklyStationary (fun t ω => X t ω + Y t ω) μ where
  memLp t := (hX.memLp t).add (hY.memLp t)
  mean_const s t := by
    simp only [mean]
    rw [integral_add ((hX.memLp s).integrable (by norm_num))
          ((hY.memLp s).integrable (by norm_num)),
        integral_add ((hX.memLp t).integrable (by norm_num))
          ((hY.memLp t).integrable (by norm_num))]
    have hmX := hX.mean_const s t
    have hmY := hY.mean_const s t
    simp only [mean] at hmX hmY
    rw [hmX, hmY]
  acvf_shift r s h := by
    show cov[X r + Y r, X s + Y s; μ]
      = cov[X (r + h) + Y (r + h), X (s + h) + Y (s + h); μ]
    rw [cov_add_add_of_uncorrelated hX.memLp hY.memLp hXY,
        cov_add_add_of_uncorrelated hX.memLp hY.memLp hXY,
        hX.acvf_shift r s h, hY.acvf_shift r s h]

/-- **Problem 1.11**: the autocovariance of the sum of uncorrelated processes is the sum of
the autocovariances, `γ_{X+Y}(h) = γ_X(h) + γ_Y(h)`. -/
theorem acvfStat_add_of_uncorrelated [IsFiniteMeasure μ] {X Y : ℤ → Ω → ℝ}
    (hX : ∀ t, MemLp (X t) 2 μ) (hY : ∀ t, MemLp (Y t) 2 μ)
    (hXY : ∀ r s : ℤ, cov[X r, Y s; μ] = 0) (h : ℤ) :
    acvfStat (fun t ω => X t ω + Y t ω) μ h = acvfStat X μ h + acvfStat Y μ h := by
  simp only [acvfStat_apply]
  exact cov_add_add_of_uncorrelated hX hY hXY h 0

/-- A function `κ : ℤ → ℝ` is **non-negative definite** if
`∑ᵢⱼ aᵢ aⱼ κ(tᵢ − tⱼ) ≥ 0` for every finite collection of integer points `t i`
and reals `a i`. -/
def IsNonnegDefinite (κ : ℤ → ℝ) : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (t : Fin n → ℤ), 0 ≤ ∑ i, ∑ j, a i * a j * κ (t i - t j)

/-! ## Properties of the autocovariance function (§1.5) -/

/-- `γ(0) = Var(X₀) ≥ 0`: the autocovariance at lag 0 is non-negative. -/
theorem IsWeaklyStationary.acvfStat_zero_nonneg (hX : IsWeaklyStationary X μ) :
    0 ≤ acvfStat X μ 0 := by
  rw [acvfStat_apply, covariance_self (hX.memLp 0).aestronglyMeasurable.aemeasurable]
  exact variance_nonneg _ _

/-- `γ(−h) = γ(h)`: the autocovariance function of a stationary process is even. -/
theorem IsWeaklyStationary.acvfStat_neg (hX : IsWeaklyStationary X μ) (h : ℤ) :
    acvfStat X μ (-h) = acvfStat X μ h := by
  have hs := hX.acvf_shift (-h) 0 h
  have e1 : -h + h = (0 : ℤ) := by ring
  have e2 : (0 : ℤ) + h = h := by ring
  rw [e1, e2] at hs
  rw [acvfStat_apply, acvfStat_apply, hs, covariance_comm]

/-- `Finset` form of non-negative definiteness: `∑_{i,j ∈ s} xᵢ xⱼ κ(i − j) ≥ 0`
for any finite set of integer points `s` and reals `x`. -/
theorem IsNonnegDefinite.finset {κ : ℤ → ℝ} (h : IsNonnegDefinite κ) (s : Finset ℤ)
    (x : ℤ → ℝ) : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, x i * x j * κ (i - j) := by
  have key := h s.card (fun k => x ↑(s.equivFin.symm k)) (fun k => (↑(s.equivFin.symm k) : ℤ))
  rw [show (∑ i ∈ s, ∑ j ∈ s, x i * x j * κ (i - j))
        = ∑ k, ∑ l, x ↑(s.equivFin.symm k) * x ↑(s.equivFin.symm l)
            * κ (↑(s.equivFin.symm k) - ↑(s.equivFin.symm l)) from ?_]
  · exact key
  · rw [← Finset.sum_coe_sort s (fun i => ∑ j ∈ s, x i * x j * κ (i - j)),
        ← Equiv.sum_comp s.equivFin.symm
          (fun i : s => ∑ j ∈ s, x ↑i * x j * κ (↑i - j))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_coe_sort s
          (fun j => x ↑(s.equivFin.symm k) * x j * κ (↑(s.equivFin.symm k) - j)),
        ← Equiv.sum_comp s.equivFin.symm]

/-- **Non-negative definiteness** (§1.5): for any finite collection of lags `t i`
and reals `a i`, `∑ᵢⱼ aᵢ aⱼ γ(tᵢ − tⱼ) ≥ 0`. It is the variance of the linear
combination `∑ᵢ aᵢ X_{tᵢ}`, expanded by bilinearity of the covariance. -/
theorem IsWeaklyStationary.nonneg_definite [IsProbabilityMeasure μ]
    (hX : IsWeaklyStationary X μ) {n : ℕ} (a : Fin n → ℝ) (t : Fin n → ℤ) :
    0 ≤ ∑ i, ∑ j, a i * a j * acvfStat X μ (t i - t j) := by
  set Y : Fin n → Ω → ℝ := fun i ω => a i * X (t i) ω with hYdef
  have hYmem : ∀ i, MemLp (Y i) 2 μ := fun i => (hX.memLp (t i)).const_mul (a i)
  have hSmem : MemLp (fun ω => ∑ i, Y i ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ => hYmem i)
  have hexp : cov[fun ω => ∑ i, Y i ω, fun ω => ∑ j, Y j ω; μ]
      = ∑ i, ∑ j, a i * a j * acvfStat X μ (t i - t j) := by
    rw [covariance_fun_sum_fun_sum hYmem hYmem]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [hYdef]
    rw [covariance_const_mul_left, covariance_const_mul_right, hX.acvf_eq_acvfStat]
    ring
  have hnn : (0 : ℝ) ≤ cov[fun ω => ∑ i, Y i ω, fun ω => ∑ j, Y j ω; μ] := by
    rw [covariance_self hSmem.aestronglyMeasurable.aemeasurable]
    exact variance_nonneg _ _
  rw [hexp] at hnn
  exact hnn

/-- The autocovariance function of a stationary process is non-negative definite. -/
theorem IsWeaklyStationary.isNonnegDefinite_acvfStat [IsProbabilityMeasure μ]
    (hX : IsWeaklyStationary X μ) : IsNonnegDefinite (acvfStat X μ) :=
  fun _ a t => hX.nonneg_definite a t

/-- Characterization of autocovariance functions, forward direction: the
autocovariance function of a stationary process is even and non-negative definite.
(The converse — that every even, non-negative-definite function is the ACVF of some
stationary process — is obtained by constructing a Gaussian process via Kolmogorov's
existence theorem, and is not formalized here.) -/
theorem IsWeaklyStationary.even_and_isNonnegDefinite_acvfStat [IsProbabilityMeasure μ]
    (hX : IsWeaklyStationary X μ) :
    (∀ h : ℤ, acvfStat X μ h = acvfStat X μ (-h)) ∧ IsNonnegDefinite (acvfStat X μ) :=
  ⟨fun h => (hX.acvfStat_neg h).symm, hX.isNonnegDefinite_acvfStat⟩

/-- `|γ(h)| ≤ γ(0)`: the autocovariance is dominated by its value at lag 0. Derived
from non-negative definiteness at two points via the discriminant of the
non-negative quadratic `λ ↦ γ(0)λ² + 2γ(h)λ + γ(0)`. -/
theorem IsWeaklyStationary.abs_acvfStat_le [IsProbabilityMeasure μ]
    (hX : IsWeaklyStationary X μ) (h : ℤ) : |acvfStat X μ h| ≤ acvfStat X μ 0 := by
  have hq : ∀ lam : ℝ,
      0 ≤ acvfStat X μ 0 * (lam * lam) + 2 * acvfStat X μ h * lam + acvfStat X μ 0 := by
    intro lam
    have hnd := hX.nonneg_definite ![lam, 1] ![h, 0]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      sub_self, sub_zero, zero_sub] at hnd
    rw [hX.acvfStat_neg] at hnd
    nlinarith [hnd]
  have hd := discrim_le_zero hq
  simp only [discrim] at hd
  have hsq : acvfStat X μ h ^ 2 ≤ acvfStat X μ 0 ^ 2 := by nlinarith [hd]
  exact abs_le_of_sq_le_sq hsq hX.acvfStat_zero_nonneg

end DeepWiki.TimeSeries
