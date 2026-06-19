import DeepWiki.TimeSeries.StationaryProcesses
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! # Worked examples of stochastic processes (§1.2–§1.3)
Realizations (Def 1.2.2) and the cosine process `Xₜ = A cos(θt) + B sin(θt)`
(Example 1.3.1): a stationary process with autocovariance `σ² cos(θh)`. -/

namespace DeepWiki.TimeSeries

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Definition 1.2.2**: a realization (sample path) of a process `X` at the
outcome `ω` is the function `t ↦ Xₜ(ω)`. -/
def realization (X : ℤ → Ω → ℝ) (ω : Ω) : ℤ → ℝ := fun t => X t ω

/-- **Example 1.2.1**: the sinusoid with random phase and amplitude
`Xₜ = r⁻¹ · A · cos(νt + Θ)`, where the amplitude `A ≥ 0` and the phase `Θ` (independent
of `A`, uniform on `[0, 2π]`) are random; `ν ≥ 0` and `r > 0` are constants. A
continuous-time process `ℝ → Ω → ℝ`. -/
noncomputable def sinusoidProcess (r ν : ℝ) (A Θ : Ω → ℝ) : ℝ → Ω → ℝ :=
  fun t ω => r⁻¹ * A ω * Real.cos (ν * t + Θ ω)

/-- **Example 1.2.4**: the Bienaymé–Galton–Watson branching process: `X₀ = x` (the initial
population) and `X_{t+1} = ∑_{j < Xₜ} Z t j`, the total offspring of the `Xₜ` individuals
of generation `t`, where `Z t j` are the (iid, `ℕ`-valued) offspring counts. -/
def branchingProcess (x : ℕ) (Z : ℕ → ℕ → Ω → ℕ) : ℕ → Ω → ℕ
  | 0 => fun _ => x
  | (t + 1) => fun ω => ∑ j ∈ Finset.range (branchingProcess x Z t ω), Z t j ω

/-- Bilinear expansion of the covariance of two linear combinations of `A`, `B`. -/
private theorem covariance_lin_comb [IsFiniteMeasure μ] {A B : Ω → ℝ}
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) (c₁ d₁ c₂ d₂ : ℝ) :
    cov[c₁ • A + d₁ • B, c₂ • A + d₂ • B; μ]
      = c₁ * c₂ * cov[A, A; μ] + c₁ * d₂ * cov[A, B; μ]
        + d₁ * c₂ * cov[B, A; μ] + d₁ * d₂ * cov[B, B; μ] := by
  rw [covariance_add_left (hA.const_smul c₁) (hB.const_smul d₁)
        ((hA.const_smul c₂).add (hB.const_smul d₂)),
      covariance_add_right (hA.const_smul c₁) (hA.const_smul c₂) (hB.const_smul d₂),
      covariance_add_right (hB.const_smul d₁) (hA.const_smul c₂) (hB.const_smul d₂),
      covariance_smul_left, covariance_smul_left, covariance_smul_left, covariance_smul_left,
      covariance_smul_right, covariance_smul_right, covariance_smul_right, covariance_smul_right]
  ring

/-- **Example 1.3.1**: the cosine process `Xₜ = A cos(θt) + B sin(θt)`, with `A`, `B`
uncorrelated, mean zero, and common variance. -/
noncomputable def cosProcess (A B : Ω → ℝ) (θ : ℝ) : ℤ → Ω → ℝ :=
  fun t => Real.cos (θ * (t : ℝ)) • A + Real.sin (θ * (t : ℝ)) • B

/-- **Example 1.3.1**: the autocovariance of the cosine process is
`γ(r,s) = σ² cos(θ(r − s))` (with `σ² = Var A = Var B` and `A`, `B` uncorrelated). -/
theorem cosProcess_acvf [IsFiniteMeasure μ] {A B : Ω → ℝ} {θ σ2 : ℝ}
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ)
    (hVA : cov[A, A; μ] = σ2) (hVB : cov[B, B; μ] = σ2) (hAB : cov[A, B; μ] = 0)
    (r s : ℤ) :
    acvf (cosProcess A B θ) μ r s = σ2 * Real.cos (θ * ((r : ℝ) - (s : ℝ))) := by
  simp only [acvf, cosProcess]
  rw [covariance_lin_comb hA hB, hVA, hVB, hAB, covariance_comm B A, hAB, mul_sub, Real.cos_sub]
  ring

/-- **Example 1.3.1**: the cosine process is (covariance) stationary — its
autocovariance is invariant under a common time shift. -/
theorem cosProcess_acvf_shift [IsFiniteMeasure μ] {A B : Ω → ℝ} {θ σ2 : ℝ}
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ)
    (hVA : cov[A, A; μ] = σ2) (hVB : cov[B, B; μ] = σ2) (hAB : cov[A, B; μ] = 0)
    (r s h : ℤ) :
    acvf (cosProcess A B θ) μ r s = acvf (cosProcess A B θ) μ (r + h) (s + h) := by
  rw [cosProcess_acvf hA hB hVA hVB hAB, cosProcess_acvf hA hB hVA hVB hAB]
  congr 2
  push_cast
  ring

/-! ## The random walk (Example 1.3.4) -/

/-- **Example 1.3.4**: the random walk `Sₜ = X₁ + ⋯ + Xₜ` of a sequence `{Xₜ}`. -/
noncomputable def randomWalk (X : ℤ → Ω → ℝ) : ℤ → Ω → ℝ :=
  fun t => ∑ i ∈ Finset.Icc 1 t, X i

/-- For a zero-mean uncorrelated sequence with variance `σ²`, the random walk has
`Var(Sₜ) = Cov(Sₜ, Sₜ) = card(Icc 1 t) · σ²` — increasing in `t`. -/
theorem randomWalk_self_covariance [IsFiniteMeasure μ] {X : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (huc : ∀ i j, cov[X i, X j; μ] = if i = j then σ2 else 0)
    (t : ℤ) :
    cov[randomWalk X t, randomWalk X t; μ] = (Finset.Icc 1 t).card • σ2 := by
  simp only [randomWalk]
  rw [covariance_sum_sum' (fun i _ => hX i) (fun j _ => hX j)]
  calc ∑ i ∈ Finset.Icc 1 t, ∑ j ∈ Finset.Icc 1 t, cov[X i, X j; μ]
      = ∑ i ∈ Finset.Icc 1 t, ∑ j ∈ Finset.Icc 1 t, (if i = j then σ2 else 0) := by
        simp only [huc]
    _ = ∑ _i ∈ Finset.Icc 1 t, σ2 := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.sum_ite_eq (Finset.Icc 1 t) i (fun _ => σ2), if_pos hi]
    _ = (Finset.Icc 1 t).card • σ2 := by rw [Finset.sum_const]

/-- **Example 1.3.4**: the random walk of a zero-mean uncorrelated sequence with
`σ² > 0` is **not** (covariance) stationary, because `Var(Sₜ)` grows with `t`. -/
theorem randomWalk_not_stationary [IsFiniteMeasure μ] {X : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (huc : ∀ i j, cov[X i, X j; μ] = if i = j then σ2 else 0)
    (hσ : 0 < σ2) : ¬ IsWeaklyStationary (randomWalk X) μ := by
  intro hstat
  have hshift := hstat.acvf_shift 1 1 1
  rw [show (1 : ℤ) + 1 = 2 from by norm_num,
      randomWalk_self_covariance hX huc, randomWalk_self_covariance hX huc] at hshift
  have c1 : (Finset.Icc (1 : ℤ) 1).card = 1 := by rw [Int.card_Icc]; rfl
  have c2 : (Finset.Icc (1 : ℤ) 2).card = 2 := by rw [Int.card_Icc]; rfl
  rw [c1, c2, one_smul, two_smul] at hshift
  linarith [hσ]

/-! ## The MA(1) process (Example 1.3.2) -/

/-- Bilinear expansion of `cov[U + θ•V, W + θ•Y]`. -/
private theorem cov_two_two [IsFiniteMeasure μ] {U V W Y : Ω → ℝ}
    (hU : MemLp U 2 μ) (hV : MemLp V 2 μ) (hW : MemLp W 2 μ) (hY : MemLp Y 2 μ) (θ : ℝ) :
    cov[U + θ • V, W + θ • Y; μ]
      = cov[U, W; μ] + θ * cov[U, Y; μ] + θ * cov[V, W; μ] + θ ^ 2 * cov[V, Y; μ] := by
  rw [covariance_add_left hU (hV.const_smul θ) (hW.add (hY.const_smul θ)),
      covariance_add_right hU hW (hY.const_smul θ),
      covariance_add_right (hV.const_smul θ) hW (hY.const_smul θ),
      covariance_smul_right, covariance_smul_left, covariance_smul_left, covariance_smul_right]
  ring

/-- **Example 1.3.2**: the moving-average process `Xₜ = Zₜ + θ Zₜ₋₁` (MA(1)). -/
noncomputable def maProcess1 (Z : ℤ → Ω → ℝ) (θ : ℝ) : ℤ → Ω → ℝ :=
  fun t => Z t + θ • Z (t - 1)

variable {Z : ℤ → Ω → ℝ} {θ σ2 : ℝ}

/-- **Example 1.3.2**: the MA(1) variance is `γ(0) = (1 + θ²) σ²`. -/
theorem maProcess1_acvf_zero [IsFiniteMeasure μ]
    (hZ : ∀ i, MemLp (Z i) 2 μ) (huc : ∀ i j, cov[Z i, Z j; μ] = if i = j then σ2 else 0)
    (s : ℤ) : cov[maProcess1 Z θ s, maProcess1 Z θ s; μ] = (1 + θ ^ 2) * σ2 := by
  simp only [maProcess1]
  rw [cov_two_two (hZ s) (hZ (s - 1)) (hZ s) (hZ (s - 1)),
      huc s s, huc s (s - 1), huc (s - 1) s, huc (s - 1) (s - 1),
      if_pos rfl, if_pos rfl, if_neg (by omega : (s : ℤ) ≠ s - 1),
      if_neg (by omega : (s : ℤ) - 1 ≠ s)]
  ring

/-- **Example 1.3.2**: the MA(1) lag-1 autocovariance is `γ(1) = θ σ²`. -/
theorem maProcess1_acvf_one [IsFiniteMeasure μ]
    (hZ : ∀ i, MemLp (Z i) 2 μ) (huc : ∀ i j, cov[Z i, Z j; μ] = if i = j then σ2 else 0)
    (s : ℤ) : cov[maProcess1 Z θ (s + 1), maProcess1 Z θ s; μ] = θ * σ2 := by
  simp only [maProcess1]
  rw [cov_two_two (hZ (s + 1)) (hZ (s + 1 - 1)) (hZ s) (hZ (s - 1)),
      huc (s + 1) s, huc (s + 1) (s - 1), huc (s + 1 - 1) s, huc (s + 1 - 1) (s - 1),
      if_neg (by omega : (s : ℤ) + 1 ≠ s), if_neg (by omega : (s : ℤ) + 1 ≠ s - 1),
      if_pos (by omega : (s : ℤ) + 1 - 1 = s), if_neg (by omega : (s : ℤ) + 1 - 1 ≠ s - 1)]
  ring

/-- **Example 1.3.2**: the MA(1) autocovariance vanishes at lags `≥ 2`. -/
theorem maProcess1_acvf_ge_two [IsFiniteMeasure μ]
    (hZ : ∀ i, MemLp (Z i) 2 μ) (huc : ∀ i j, cov[Z i, Z j; μ] = if i = j then σ2 else 0)
    (s h : ℤ) (hh : 2 ≤ h) : cov[maProcess1 Z θ (s + h), maProcess1 Z θ s; μ] = 0 := by
  simp only [maProcess1]
  rw [cov_two_two (hZ (s + h)) (hZ (s + h - 1)) (hZ s) (hZ (s - 1)),
      huc (s + h) s, huc (s + h) (s - 1), huc (s + h - 1) s, huc (s + h - 1) (s - 1),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  ring

/-! ## A covariance-stationary series with non-constant mean (Example 1.3.3) -/

/-- **Example 1.3.3**: the process `Xₜ = Zₜ + 1{t odd}` — its autocovariance depends
only on the lag, but its mean alternates with the parity of `t`. -/
noncomputable def parityShift (Z : ℤ → Ω → ℝ) : ℤ → Ω → ℝ :=
  fun t ω => Z t ω + (if Odd t then 1 else 0)

/-- The mean of the parity-shifted process picks up `1` at odd times. -/
theorem parityShift_mean [IsProbabilityMeasure μ] (hZ : ∀ t, Integrable (Z t) μ) (t : ℤ) :
    mean (parityShift Z) μ t = mean Z μ t + (if Odd t then 1 else 0) := by
  simp only [mean, parityShift]
  rw [integral_add (hZ t) (integrable_const _), integral_const]
  simp

/-- **Example 1.3.3**: the parity-shifted process is **not** (covariance) stationary,
because its mean is not constant — even though its autocovariance is lag-only. -/
theorem parityShift_not_stationary [IsProbabilityMeasure μ]
    (hZ : ∀ t, Integrable (Z t) μ) (hZmean : mean Z μ 0 = mean Z μ 1) :
    ¬ IsWeaklyStationary (parityShift Z) μ := by
  intro hstat
  have h := hstat.mean_const 0 1
  rw [parityShift_mean hZ, parityShift_mean hZ,
      if_neg (by decide : ¬ Odd (0 : ℤ)), if_pos (by decide : Odd (1 : ℤ)), hZmean] at h
  linarith

end DeepWiki.TimeSeries
