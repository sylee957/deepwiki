import DeepWiki.TimeSeries.LinearProcess
import DeepWiki.TimeSeries.LinearProcessExamples
import DeepWiki.TimeSeries.ArmaProcesses

/-! # The linear process over ARMA white noise (Theorem 3.2.1)
Combining the `L²` linear-process autocovariance with the white-noise → `L²` bridge: a linear
process `Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ` driven by a genuine `WN(0,σ²)` (Definition 3.1.1) has the Theorem 3.2.1
autocovariance `γ(h) = σ² ∑ₖ ψₖ ψ_{k+h}`. This is the fully book-faithful endpoint: it starts from
the book's `IsWhiteNoise` predicate, not an abstract `L²`-orthogonality hypothesis. -/

namespace DeepWiki.TimeSeries

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Theorem 3.2.1 for a book `WN(0,σ²)`:** a linear process `Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ` (`∑ⱼ |ψⱼ| < ∞`)
driven by white noise `Z` (Definition 3.1.1, square-integrable and uniformly `L²`-bounded after
embedding) has autocovariance `γ(h) = ⟪X_{t+h}, Xₜ⟫ = σ² ∑ₖ ψₖ ψ_{k+h}`. -/
theorem isWhiteNoise_linearProcess_acvf [IsProbabilityMeasure μ] {ψ : ℤ → ℝ} (hψ : Summable ψ)
    {Z : ℤ → Ω → ℝ} (hmem : ∀ t, MemLp (Z t) 2 μ) {σ2 : ℝ} (hwn : IsWhiteNoise Z μ σ2)
    {C : ℝ} (hZb : ∀ t, ‖toLpSeq Z hmem t‖ ≤ C) (t h : ℤ) :
    inner ℝ (linearProcessLp ψ (toLpSeq Z hmem) (t + h)) (linearProcessLp ψ (toLpSeq Z hmem) t)
      = σ2 * ∑' k, ψ k * ψ (k + h) :=
  linearProcessLp_inner_toLpSeq hψ hmem hZb (hwn.integral_mul hmem) t h

/-- **§3.3 Second Method (homogeneous difference equation):** if the `φ`-convolution of the weights
vanishes pointwise — `ψⱼ · ∑ₖ φₖ ψ_{j+(h−k)} = 0` for every `j` (which holds for `h > deg θ`, since
`∑ₖ φₖ ψ_{m−k} = θ_m = 0` for `m > deg θ` and `ψⱼ = 0` for `j < 0`) — then the linear-process
autocovariance `γ(m) = σ² ∑ⱼ ψⱼ ψ_{j+m}` satisfies the homogeneous recursion
`∑_{k=0}^p φₖ γ(h−k) = 0`. -/
theorem acvf_homogeneous {ψ : ℤ → ℝ} (hψ : Summable ψ) (φ : Polynomial ℝ) (σ2 : ℝ) (h : ℤ)
    (hvanish : ∀ j : ℤ,
      ψ j * ∑ k ∈ Finset.range (φ.natDegree + 1), φ.coeff k * ψ (j + (h - k)) = 0) :
    ∑ k ∈ Finset.range (φ.natDegree + 1),
      φ.coeff k * (σ2 * ∑' j : ℤ, ψ j * ψ (j + (h - k))) = 0 := by
  have hzero : ∑ k ∈ Finset.range (φ.natDegree + 1),
      φ.coeff k * ∑' j : ℤ, ψ j * ψ (j + (h - k)) = 0 := by
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (f := fun (k : ℕ) (j : ℤ) => φ.coeff k * (ψ j * ψ (j + (h - k))))
      fun k _ => (summable_mul_shift hψ (h - k)).mul_left (φ.coeff k)]
    refine (tsum_congr fun j => ?_).trans tsum_zero
    rw [← hvanish j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [show (∑ k ∈ Finset.range (φ.natDegree + 1), φ.coeff k * (σ2 * ∑' j : ℤ, ψ j * ψ (j + (h - k))))
      = σ2 * ∑ k ∈ Finset.range (φ.natDegree + 1), φ.coeff k * ∑' j : ℤ, ψ j * ψ (j + (h - k)) from by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring, hzero, mul_zero]

/-- **§3.3 Second Method for a causal `ARMA(p,q)`:** if the `ψ`-weights are summable (the causal
`∑ⱼ |ψⱼ| < ∞`), one-sided (`ψⱼ = 0` for `j < 0`), and satisfy the recursion-vanishing
`∑ₖ φₖ ψ_{m−k} = 0` for every `m > q` (eq 3.3.3 with `θ_m = 0`, `q = deg θ`), then the autocovariance
`γ(m) = σ² ∑ⱼ ψⱼ ψ_{j+m}` satisfies the homogeneous difference equation `∑_{k=0}^p φₖ γ(h−k) = 0` at
every lag `h > q`. The summability is the analytic content that causality (`φ ≠ 0` on `|z| ≤ 1`)
would supply (here a hypothesis, as that estimate is out of scope). -/
theorem arma_acvf_homogeneous {ψ : ℤ → ℝ} (hψ : Summable ψ) (φ : Polynomial ℝ) (σ2 : ℝ) {q : ℕ}
    (hpos : ∀ j : ℤ, j < 0 → ψ j = 0)
    (hrec : ∀ m : ℤ, (q : ℤ) < m →
      ∑ k ∈ Finset.range (φ.natDegree + 1), φ.coeff k * ψ (m - k) = 0)
    {h : ℤ} (hh : (q : ℤ) < h) :
    ∑ k ∈ Finset.range (φ.natDegree + 1),
      φ.coeff k * (σ2 * ∑' j : ℤ, ψ j * ψ (j + (h - k))) = 0 := by
  refine acvf_homogeneous hψ φ σ2 h fun j => ?_
  rcases lt_or_ge j 0 with hj | hj
  · rw [hpos j hj, zero_mul]
  · have hconv : ∑ k ∈ Finset.range (φ.natDegree + 1), φ.coeff k * ψ (j + (h - k)) = 0 := by
      simp_rw [show ∀ k : ℕ, j + (h - (k : ℤ)) = (j + h) - k from fun k => by ring]
      exact hrec (j + h) (by omega)
    rw [hconv, mul_zero]

/-- **Example 3.2.1 (faithful `MA(q) = MA(∞)`):** the `L²` linear process built from the finite
`MA(q)` filter over embedded square-integrable noise agrees, almost everywhere, with the book's
`MA(q)` process `θ(B) Z = ∑_{j=0}^q θⱼ Zₜ₋ⱼ` — connecting the abstract `Lp` `MA(∞)` construction to
the random-variable process. -/
theorem coeFn_linearProcessLp_maqFilter {Z : ℤ → Ω → ℝ} (hmem : ∀ t, MemLp (Z t) 2 μ)
    (θ : Polynomial ℝ) (t : ℤ) :
    (linearProcessLp (maqFilter θ) (toLpSeq Z hmem) t : Ω → ℝ) =ᵐ[μ] (lagPoly θ Z) t := by
  rw [linearProcessLp_maqFilter_eq, lagPoly_apply]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have h : ∀ i ∈ Finset.range (θ.natDegree + 1),
      (⇑(θ.coeff i • toLpSeq Z hmem (t - i)) : Ω → ℝ) =ᵐ[μ] θ.coeff i • Z (t - i) :=
    fun i _ => (Lp.coeFn_smul _ _).trans ((MemLp.coeFn_toLp _).const_smul (θ.coeff i))
  filter_upwards [(Filter.eventually_all_finset _).mpr fun i hi => h i hi] with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => hω i hi

/-- **Theorem 3.2.1 for a finite `MA(q)`:** the genuine `MA(q)` process `Xₜ = ∑_{j=0}^q θⱼ Zₜ₋ⱼ` over
white noise `Z ~ WN(0, σ²)` has autocovariance `γ(h) = σ² ∑_{k=0}^{q−h} θₖ θ_{k+h}` for `0 ≤ h` (and
`γ(h) = 0` for `h > q`) — the classical closed form, from the white-noise linear-process acvf
(`isWhiteNoise_linearProcess_acvf`) and the explicit filter sum (`maqFilter_tsum_mul_shift_eq`). -/
theorem maq_linearProcess_acvf [IsProbabilityMeasure μ] (θ : Polynomial ℝ) {Z : ℤ → Ω → ℝ}
    (hmem : ∀ t, MemLp (Z t) 2 μ) {σ2 : ℝ} (hwn : IsWhiteNoise Z μ σ2) {C : ℝ}
    (hZb : ∀ t, ‖toLpSeq Z hmem t‖ ≤ C) (t : ℤ) {h : ℤ} (hh : 0 ≤ h) :
    inner ℝ (linearProcessLp (maqFilter θ) (toLpSeq Z hmem) (t + h))
        (linearProcessLp (maqFilter θ) (toLpSeq Z hmem) t)
      = σ2 * ∑ k ∈ Finset.range (θ.natDegree + 1), θ.coeff k * θ.coeff (k + h.toNat) := by
  rw [isWhiteNoise_linearProcess_acvf (summable_maqFilter θ) hmem hwn hZb,
    maqFilter_tsum_mul_shift_eq θ hh]

end DeepWiki.TimeSeries
