import DeepWiki.TimeSeries.LinearProcess

/-! # A finite linear filter acting on an `L²` linear process
Applying a finite linear filter `∑ₖ cₖ Bᵏ` to the `MA(∞)` linear process `Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ` produces
again a linear process, with the *convolved* weights `(c ⋆ ψ)_m = ∑ₖ cₖ ψ_{m−k}`:
`∑ₖ cₖ X_{t−k} = ∑_m (∑ₖ cₖ ψ_{m−k}) Z_{t−m}`. This is the operator-level step behind the ARMA
equation `φ(B) X = θ(B) Z` (forward Theorem 3.1.1). -/

namespace DeepWiki.TimeSeries

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A scaled, `k`-shifted linear process as a convergent series in the convolution index `m = j + k`:
`∑_m (c · ψ_{m−k}) Z_{t−m} = c · X_{t−k}` (reindex `j ↦ m = j + k` of `c · ∑ⱼ ψⱼ Z_{(t−k)−j}`). -/
theorem hasSum_smul_shift_linearProcessLp {ψ : ℤ → ℝ} (hψ : Summable ψ) {Z : ℤ → Lp ℝ 2 μ}
    {C : ℝ} (hZb : ∀ t, ‖Z t‖ ≤ C) (c : ℝ) (k t : ℤ) :
    HasSum (fun m : ℤ => (c * ψ (m - k)) • Z (t - m)) (c • linearProcessLp ψ Z (t - k)) := by
  refine (Equiv.hasSum_iff (Equiv.addRight k)).mp ?_
  have heq : (fun m : ℤ => (c * ψ (m - k)) • Z (t - m)) ∘ (Equiv.addRight k)
      = fun j => c • (ψ j • Z (t - k - j)) := by
    funext j
    simp only [Function.comp_apply, Equiv.coe_addRight]
    rw [show j + k - k = j from by ring, show t - (j + k) = t - k - j from by ring, smul_smul]
  rw [heq]
  exact (hasSum_linearProcessLp hψ hZb (t - k)).const_smul c

/-- **A finite linear filter on a linear process is a linear process with convolved weights:**
`∑_{k ∈ s} cₖ X_{t−k} = ∑_m (∑_{k ∈ s} cₖ ψ_{m−k}) Z_{t−m}`, i.e. applying `∑ₖ cₖ Bᵏ` to
`Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ` gives the linear process with the convolved weight sequence `m ↦ ∑ₖ cₖ ψ_{m−k}`. -/
theorem linearProcessLp_filter {ψ : ℤ → ℝ} (hψ : Summable ψ) {Z : ℤ → Lp ℝ 2 μ}
    {C : ℝ} (hZb : ∀ t, ‖Z t‖ ≤ C) (c : ℤ → ℝ) (s : Finset ℤ) (t : ℤ) :
    ∑ k ∈ s, c k • linearProcessLp ψ Z (t - k)
      = linearProcessLp (fun m => ∑ k ∈ s, c k * ψ (m - k)) Z t := by
  have hχ : Summable (fun m => ∑ k ∈ s, c k * ψ (m - k)) :=
    summable_sum fun k _ => (((Equiv.subRight k).summable_iff).mpr hψ).mul_left (c k)
  have hLHS : HasSum (fun m => ∑ k ∈ s, (c k * ψ (m - k)) • Z (t - m))
      (∑ k ∈ s, c k • linearProcessLp ψ Z (t - k)) :=
    hasSum_sum fun k _ => hasSum_smul_shift_linearProcessLp hψ hZb (c k) k t
  refine (hLHS.congr_fun fun m => ?_).unique (hasSum_linearProcessLp hχ hZb t)
  rw [Finset.sum_smul]

/-- **Finite linear filter, `ℕ`-indexed form:** `∑_{k<N} cₖ X_{t−k} = ∑_m (∑_{k<N} cₖ ψ_{m−k}) Z_{t−m}`
— the `range N` version of `linearProcessLp_filter`, matching a polynomial filter `∑_{k=0}^{p} φₖ Bᵏ`
(`c = φ.coeff`, `N = deg φ + 1`). -/
theorem linearProcessLp_filter_range {ψ : ℤ → ℝ} (hψ : Summable ψ) {Z : ℤ → Lp ℝ 2 μ}
    {C : ℝ} (hZb : ∀ t, ‖Z t‖ ≤ C) (c : ℕ → ℝ) (N : ℕ) (t : ℤ) :
    ∑ k ∈ Finset.range N, c k • linearProcessLp ψ Z (t - k)
      = linearProcessLp (fun m => ∑ k ∈ Finset.range N, c k * ψ (m - k)) Z t := by
  have hχ : Summable (fun m => ∑ k ∈ Finset.range N, c k * ψ (m - (k : ℤ))) :=
    summable_sum fun k _ => (((Equiv.subRight (k : ℤ)).summable_iff).mpr hψ).mul_left (c k)
  have hLHS : HasSum (fun m => ∑ k ∈ Finset.range N, (c k * ψ (m - (k : ℤ))) • Z (t - m))
      (∑ k ∈ Finset.range N, c k • linearProcessLp ψ Z (t - (k : ℤ))) :=
    hasSum_sum fun k _ => hasSum_smul_shift_linearProcessLp hψ hZb (c k) (k : ℤ) t
  refine (hLHS.congr_fun fun m => ?_).unique (hasSum_linearProcessLp hχ hZb t)
  rw [Finset.sum_smul]

end DeepWiki.TimeSeries
