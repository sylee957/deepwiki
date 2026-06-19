import DeepWiki.TimeSeries.StationaryProcesses
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Bernoulli
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

/-- **Example 1.2.2** (the binary process): there exists a probability space carrying an
iid sequence `(Xₜ)` of fair `±1` coin flips — each `Xₜ` has the Bernoulli law
`P(Xₜ = 1) = P(Xₜ = -1) = 1/2` (1.2.3, 1.2.4). Its existence (not evident from the
finite-dimensional laws alone) is guaranteed by Kolmogorov's theorem; concretely it is the
coordinate process on the infinite product of the fair Bernoulli measure on `{1, -1}`. -/
theorem exists_iidBinaryProcess :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℤ → Ω → ℝ),
      (∀ t, Measurable (X t)) ∧
      (∀ t, HasLaw (X t)
        (bernoulliMeasure (1 : ℝ) (-1) ⟨1 / 2, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩) P) ∧
      iIndepFun X P ∧ IsProbabilityMeasure P :=
  exists_iid ℤ (bernoulliMeasure (1 : ℝ) (-1) ⟨1 / 2, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩)

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

/-! ## Problem 1.7(b): the constant process -/

/-- **Problem 1.7(b)**: the (degenerate) constant process `Xₜ = a + b·Z`, the same
random variable for every `t`. -/
noncomputable def constProcess (a b : ℝ) (Z : Ω → ℝ) : ℤ → Ω → ℝ := fun _ ω => a + b * Z ω

/-- The autocovariance of `Xₜ = a + b·Z` is `b²·Var(Z)` at every pair of times. -/
theorem constProcess_acvf [IsProbabilityMeasure μ] {a b : ℝ} {Z : Ω → ℝ}
    (hZ : MemLp Z 2 μ) (r s : ℤ) :
    acvf (constProcess a b Z) μ r s = b ^ 2 * cov[Z, Z; μ] := by
  have hint : Integrable (fun ω => b * Z ω) μ := (hZ.integrable (by norm_num)).const_mul b
  show cov[fun ω => a + b * Z ω, fun ω => a + b * Z ω; μ] = b ^ 2 * cov[Z, Z; μ]
  rw [covariance_const_add_left hint, covariance_const_add_right hint,
      covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- **Problem 1.7(b)**: the constant process `Xₜ = a + b·Z` is (weakly) stationary — its
mean and autocovariance are trivially shift-invariant since `Xₜ` does not depend on `t`. -/
theorem constProcess_isWeaklyStationary [IsFiniteMeasure μ] {a b : ℝ} {Z : Ω → ℝ}
    (hZ : MemLp Z 2 μ) : IsWeaklyStationary (constProcess a b Z) μ where
  memLp _ := (memLp_const a).add (hZ.const_mul b)
  mean_const _ _ := rfl
  acvf_shift _ _ _ := rfl

/-- The lag-only autocovariance of the constant process is `b²·Var(Z)` at every lag. -/
theorem constProcess_acvfStat [IsProbabilityMeasure μ] {a b : ℝ} {Z : Ω → ℝ}
    (hZ : MemLp Z 2 μ) (h : ℤ) :
    acvfStat (constProcess a b Z) μ h = b ^ 2 * cov[Z, Z; μ] := by
  rw [acvfStat_apply]; exact constProcess_acvf hZ h 0

/-! ## Problem 1.7(e): a deterministically modulated single variable -/

/-- **Problem 1.7(e)**: the process `Xₜ = Z·cos(ct)` — a single random variable `Z`
modulated by the deterministic factor `cos(ct)`. -/
noncomputable def cosScaleProcess (c : ℝ) (Z : Ω → ℝ) : ℤ → Ω → ℝ :=
  fun t ω => Real.cos (c * (t : ℝ)) * Z ω

/-- The autocovariance of `Xₜ = Z·cos(ct)` is `cos(cr)·cos(cs)·Var(Z)`. -/
theorem cosScaleProcess_cov [IsProbabilityMeasure μ] {c : ℝ} {Z : Ω → ℝ} (r s : ℤ) :
    cov[cosScaleProcess c Z r, cosScaleProcess c Z s; μ]
      = Real.cos (c * (r : ℝ)) * Real.cos (c * (s : ℝ)) * cov[Z, Z; μ] := by
  show cov[fun ω => Real.cos (c * (r : ℝ)) * Z ω, fun ω => Real.cos (c * (s : ℝ)) * Z ω; μ] = _
  rw [covariance_const_mul_left, covariance_const_mul_right]; ring

/-- **Problem 1.7(e)**: `Xₜ = Z·cos(ct)` is **not** (covariance) stationary when `cos²c ≠ 1`
and `Var(Z) > 0` — its variance `cos²(ct)·Var(Z)` is not constant in `t`. -/
theorem cosScaleProcess_not_stationary [IsProbabilityMeasure μ] {c : ℝ} {Z : Ω → ℝ}
    (hc : Real.cos c ^ 2 ≠ 1) (hpos : 0 < cov[Z, Z; μ]) :
    ¬ IsWeaklyStationary (cosScaleProcess c Z) μ := by
  intro hstat
  have h := hstat.acvf_shift 0 0 1
  rw [cosScaleProcess_cov, cosScaleProcess_cov] at h
  push_cast at h
  simp only [mul_zero, Real.cos_zero, mul_one, one_mul] at h
  -- h : cov[Z, Z; μ] = Real.cos c * Real.cos c * cov[Z, Z; μ]
  apply hc
  have hcc : Real.cos c * Real.cos c = 1 := by
    have key : cov[Z, Z; μ] * (1 - Real.cos c * Real.cos c) = 0 := by linear_combination h
    rcases mul_eq_zero.mp key with h1 | h2
    · exact absurd h1 hpos.ne'
    · linarith
  rw [sq]; exact hcc

/-! ## Problem 1.7(a): the MA(2)-type process -/

/-- Bilinear expansion of `cov[b•U + c•V, b•W + c•Y]` over four functions. -/
private theorem cov_bc_four [IsFiniteMeasure μ] {U V W Y : Ω → ℝ}
    (hU : MemLp U 2 μ) (hV : MemLp V 2 μ) (hW : MemLp W 2 μ) (hY : MemLp Y 2 μ) (b c : ℝ) :
    cov[b • U + c • V, b • W + c • Y; μ]
      = b * b * cov[U, W; μ] + b * c * cov[U, Y; μ]
        + c * b * cov[V, W; μ] + c * c * cov[V, Y; μ] := by
  rw [covariance_add_left (hU.const_smul b) (hV.const_smul c)
        ((hW.const_smul b).add (hY.const_smul c)),
      covariance_add_right (hU.const_smul b) (hW.const_smul b) (hY.const_smul c),
      covariance_add_right (hV.const_smul c) (hW.const_smul b) (hY.const_smul c),
      covariance_smul_left, covariance_smul_left, covariance_smul_left, covariance_smul_left,
      covariance_smul_right, covariance_smul_right, covariance_smul_right, covariance_smul_right]
  ring

/-- **Problem 1.7(a)**: the process `Xₜ = a + b Zₜ + c Zₜ₋₂` (mean `a`, MA(2)-type). -/
noncomputable def maProcess2 (a b c : ℝ) (Z : ℤ → Ω → ℝ) : ℤ → Ω → ℝ :=
  fun t ω => a + (b • Z t + c • Z (t - 2)) ω

/-- The autocovariance of `Xₜ = a + bZₜ + cZₜ₋₂` (the constant `a` drops out). -/
theorem maProcess2_cov [IsProbabilityMeasure μ] {a b c σ2 : ℝ} {Z : ℤ → Ω → ℝ}
    (hZ : ∀ i, MemLp (Z i) 2 μ) (huc : ∀ i j, cov[Z i, Z j; μ] = if i = j then σ2 else 0)
    (r s : ℤ) :
    cov[maProcess2 a b c Z r, maProcess2 a b c Z s; μ]
      = b * b * (if r = s then σ2 else 0) + b * c * (if r = s - 2 then σ2 else 0)
        + c * b * (if r - 2 = s then σ2 else 0) + c * c * (if r - 2 = s - 2 then σ2 else 0) := by
  have hL : ∀ t : ℤ, Integrable (b • Z t + c • Z (t - 2)) μ := fun t =>
    (((hZ t).const_smul b).add ((hZ (t - 2)).const_smul c)).integrable (by norm_num)
  show cov[fun ω => a + (b • Z r + c • Z (r - 2)) ω,
      fun ω => a + (b • Z s + c • Z (s - 2)) ω; μ] = _
  rw [covariance_const_add_left (hL r), covariance_const_add_right (hL s),
      cov_bc_four (hZ r) (hZ (r - 2)) (hZ s) (hZ (s - 2)),
      huc r s, huc r (s - 2), huc (r - 2) s, huc (r - 2) (s - 2)]

/-- **Problem 1.7(a)**: the MA(2)-type variance `γ(0) = (b² + c²) σ²`. -/
theorem maProcess2_acvf_zero [IsProbabilityMeasure μ] {a b c σ2 : ℝ} {Z : ℤ → Ω → ℝ}
    (hZ : ∀ i, MemLp (Z i) 2 μ) (huc : ∀ i j, cov[Z i, Z j; μ] = if i = j then σ2 else 0)
    (s : ℤ) : cov[maProcess2 a b c Z s, maProcess2 a b c Z s; μ] = (b ^ 2 + c ^ 2) * σ2 := by
  rw [maProcess2_cov hZ huc, if_pos (rfl : s = s), if_neg (show ¬(s = s - 2) by omega),
    if_neg (show ¬(s - 2 = s) by omega), if_pos (rfl : s - 2 = s - 2)]
  ring

/-- **Problem 1.7(a)**: the lag-1 autocovariance vanishes, `γ(1) = 0`. -/
theorem maProcess2_acvf_one [IsProbabilityMeasure μ] {a b c σ2 : ℝ} {Z : ℤ → Ω → ℝ}
    (hZ : ∀ i, MemLp (Z i) 2 μ) (huc : ∀ i j, cov[Z i, Z j; μ] = if i = j then σ2 else 0)
    (s : ℤ) : cov[maProcess2 a b c Z (s + 1), maProcess2 a b c Z s; μ] = 0 := by
  rw [maProcess2_cov hZ huc, if_neg (show ¬(s + 1 = s) by omega),
    if_neg (show ¬(s + 1 = s - 2) by omega), if_neg (show ¬(s + 1 - 2 = s) by omega),
    if_neg (show ¬(s + 1 - 2 = s - 2) by omega)]
  ring

/-- **Problem 1.7(a)**: the lag-2 autocovariance `γ(2) = b c σ²`. -/
theorem maProcess2_acvf_two [IsProbabilityMeasure μ] {a b c σ2 : ℝ} {Z : ℤ → Ω → ℝ}
    (hZ : ∀ i, MemLp (Z i) 2 μ) (huc : ∀ i j, cov[Z i, Z j; μ] = if i = j then σ2 else 0)
    (s : ℤ) : cov[maProcess2 a b c Z (s + 2), maProcess2 a b c Z s; μ] = b * c * σ2 := by
  rw [maProcess2_cov hZ huc, if_neg (show ¬(s + 2 = s) by omega),
    if_neg (show ¬(s + 2 = s - 2) by omega), if_pos (show s + 2 - 2 = s by omega),
    if_neg (show ¬(s + 2 - 2 = s - 2) by omega)]
  ring

/-- **Problem 1.7(a)**: the autocovariance vanishes at lags `≥ 3`. -/
theorem maProcess2_acvf_ge_three [IsProbabilityMeasure μ] {a b c σ2 : ℝ} {Z : ℤ → Ω → ℝ}
    (hZ : ∀ i, MemLp (Z i) 2 μ) (huc : ∀ i j, cov[Z i, Z j; μ] = if i = j then σ2 else 0)
    (s h : ℤ) (hh : 3 ≤ h) :
    cov[maProcess2 a b c Z (s + h), maProcess2 a b c Z s; μ] = 0 := by
  rw [maProcess2_cov hZ huc, if_neg (show ¬(s + h = s) by omega),
    if_neg (show ¬(s + h = s - 2) by omega), if_neg (show ¬(s + h - 2 = s) by omega),
    if_neg (show ¬(s + h - 2 = s - 2) by omega)]
  ring

end DeepWiki.TimeSeries
