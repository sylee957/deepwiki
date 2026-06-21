import DeepWiki.TimeSeries.CausalPolyDisk
import DeepWiki.TimeSeries.LinearProcessArma
import DeepWiki.TimeSeries.LinearProcessFilter

/-! # Causal `ARMA` autocovariance solves the homogeneous AR recursion (§3.3, Second Method)
The analytic payoff. For a *causal* `ARMA(p,q)` (`φ(z) ≠ 0` on `|z| ≤ 1`) the `MA(∞)` weights
`ψⱼ = Re (θ/φ)ⱼ` are *genuinely summable* — this is the `∑ⱼ |ψⱼ| < ∞` proven analytically in
`CausalPolyDisk`, no longer a hypothesis — one-sided (`ψⱼ = 0` for `j < 0`), and satisfy the
recursion `∑ₖ φₖ ψ_{m−k} = 0` for `m > q` (eq 3.3.3, the real part of the coefficient-uniqueness
identity `∑_{i+j=m} φᵢ ψⱼ = θ_m`). Feeding these to `arma_acvf_homogeneous` discharges its
summability hypothesis, giving the homogeneous difference equation `∑ₖ φₖ γ(h−k) = 0` (`h > q`) for
the genuine causal-`ARMA` autocovariance `γ(h) = σ² ∑ⱼ ψⱼ ψ_{j+h}`. -/

namespace DeepWiki.TimeSeries

open scoped Polynomial

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Causal `ARMA(p,q)` `MA(∞)` weights (shared construction):** for a causal AR polynomial `φ`
(`IsCausalPoly`), there exist real, summable, one-sided weights `ψ` (the real parts of the Taylor
coefficients of `θ/φ`) satisfying the recursion `∑_{k=0}^p φₖ ψ_{m−k} = 0` for every `m > q = deg θ`
— the real part of the coefficient-uniqueness identity `∑_{i+j=m} φᵢ ψⱼ = θ_m`
(`conv_coeff_div_eq_coeff`), with summability the analytic `∑ⱼ |ψⱼ| < ∞` of `CausalPolyDisk`. The
weight construction shared by the §3.3 autocovariance results. -/
theorem exists_causal_arma_weights {φ θ : ℝ[X]} (hφ : IsCausalPoly φ) :
    ∃ ψ : ℤ → ℝ, Summable ψ ∧ (∀ j : ℤ, j < 0 → ψ j = 0) ∧
      ∀ m : ℤ, (θ.natDegree : ℤ) < m →
        ∑ k ∈ Finset.range (φ.natDegree + 1), φ.coeff k * ψ (m - k) = 0 := by
  obtain ⟨R, hR1, hsum, hrec⟩ := conv_coeff_div_eq_coeff (φ := φ) (θ := θ) hφ
  set p := cauchyPowerSeries (fun w : ℂ => Polynomial.aeval w θ * (Polynomial.aeval w φ)⁻¹) 0 R
    with hp
  -- real `MA(∞)` weights: the real parts of the Taylor coefficients of `θ/φ`
  set ρ : ℕ → ℝ := fun n => (p.coeff n).re with hρ
  have hρsum : Summable ρ :=
    Summable.of_norm_bounded hsum fun n => by
      rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm (p.coeff n)
  -- one-sided extension to `ℤ`
  set ψ : ℤ → ℝ := fun n => if 0 ≤ n then ρ n.toNat else 0 with hψ
  have hψval : ∀ n : ℤ, ψ n = if 0 ≤ n then ρ n.toNat else 0 := fun _ => rfl
  have hψ0 : ∀ j : ℤ, j < 0 → ψ j = 0 := fun j hj => by
    rw [hψval]; exact if_neg (not_le.mpr hj)
  have hψsum : Summable ψ := by
    have hcond : ∀ x ∉ Set.range ((↑) : ℕ → ℤ), ψ x = 0 := fun x hx => by
      rw [hψval]; exact if_neg fun hx0 => hx ⟨x.toNat, Int.toNat_of_nonneg hx0⟩
    refine (Function.Injective.summable_iff Nat.cast_injective hcond).mp ?_
    refine hρsum.congr fun n => ?_
    rw [Function.comp_apply, hψval, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]
  -- real part of the coefficient-uniqueness recursion (eq 3.3.3): `∑_{i+j=m} φᵢ ψⱼ = θ_m`
  have hreal : ∀ m' : ℕ, ∑ q ∈ Finset.antidiagonal m', φ.coeff q.1 * ρ q.2 = θ.coeff m' := by
    intro m'
    have key := congrArg (⇑Complex.reCLM) (hrec m')
    simp only [map_sum, map_smul, Complex.reCLM_apply, smul_eq_mul, Complex.ofReal_re] at key
    simpa only [hρ] using key
  -- recast in the `range (deg φ + 1)`, `ℤ`-indexed form `arma_acvf_homogeneous` consumes
  have hψrec : ∀ m : ℤ, (θ.natDegree : ℤ) < m →
      ∑ k ∈ Finset.range (φ.natDegree + 1), φ.coeff k * ψ (m - k) = 0 := by
    intro m hm
    obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = (M : ℤ) :=
      ⟨m.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hMq : θ.natDegree < M := by exact_mod_cast hm
    have hθM : θ.coeff M = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hMq
    have hM0 : ∑ k ∈ Finset.range (M + 1), φ.coeff k * ρ (M - k) = 0 := by
      rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => φ.coeff i * ρ j) M]
      exact (hreal M).trans hθM
    have hg1_zero_deg : ∀ k ∈ Finset.range (φ.natDegree + M + 1),
        k ∉ Finset.range (φ.natDegree + 1) → φ.coeff k * ψ ((M : ℤ) - ↑k) = 0 := by
      intro k _ hk
      rw [Finset.mem_range, not_lt] at hk
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
    have hg1_zero_M : ∀ k ∈ Finset.range (φ.natDegree + M + 1),
        k ∉ Finset.range (M + 1) → φ.coeff k * ψ ((M : ℤ) - ↑k) = 0 := by
      intro k _ hk
      rw [Finset.mem_range, not_lt] at hk
      rw [hψval, if_neg (show ¬ (0 : ℤ) ≤ (M : ℤ) - ↑k by omega), mul_zero]
    have hg2_eq : ∀ k ∈ Finset.range (M + 1),
        φ.coeff k * ρ (M - k) = φ.coeff k * ψ ((M : ℤ) - ↑k) := by
      intro k hk
      rw [Finset.mem_range, Nat.lt_succ_iff] at hk
      congr 1
      rw [hψval, if_pos (show (0 : ℤ) ≤ (M : ℤ) - ↑k by omega)]
      congr 1
      omega
    calc ∑ k ∈ Finset.range (φ.natDegree + 1), φ.coeff k * ψ ((M : ℤ) - ↑k)
        = ∑ k ∈ Finset.range (φ.natDegree + M + 1), φ.coeff k * ψ ((M : ℤ) - ↑k) :=
          Finset.sum_subset (by intro x hx; rw [Finset.mem_range] at hx ⊢; omega) hg1_zero_deg
      _ = ∑ k ∈ Finset.range (M + 1), φ.coeff k * ψ ((M : ℤ) - ↑k) :=
          (Finset.sum_subset (by intro x hx; rw [Finset.mem_range] at hx ⊢; omega) hg1_zero_M).symm
      _ = ∑ k ∈ Finset.range (M + 1), φ.coeff k * ρ (M - k) :=
          (Finset.sum_congr rfl hg2_eq).symm
      _ = 0 := hM0
  exact ⟨ψ, hψsum, hψ0, hψrec⟩

/-- **Causal `ARMA(p,q)` autocovariance solves the homogeneous AR recursion (§3.3):** the
linear-process autocovariance `γ(h) = σ² ∑ⱼ ψⱼ ψ_{j+h}` of a causal ARMA satisfies
`∑_{k=0}^p φₖ γ(h−k) = 0` at every lag `h > q = deg θ`. The weight summability — a hypothesis in
`arma_acvf_homogeneous` — is *discharged* by the analytic `∑ⱼ |ψⱼ| < ∞` of `CausalPolyDisk`. -/
theorem causal_arma_acvf_homogeneous {φ θ : ℝ[X]} (hφ : IsCausalPoly φ) (σ2 : ℝ)
    {h : ℤ} (hh : (θ.natDegree : ℤ) < h) :
    ∃ ψ : ℤ → ℝ, Summable ψ ∧ (∀ j : ℤ, j < 0 → ψ j = 0) ∧
      ∑ k ∈ Finset.range (φ.natDegree + 1),
        φ.coeff k * (σ2 * ∑' j : ℤ, ψ j * ψ (j + (h - k))) = 0 := by
  obtain ⟨ψ, hψsum, hψ0, hψrec⟩ := exists_causal_arma_weights (θ := θ) hφ
  exact ⟨ψ, hψsum, hψ0, arma_acvf_homogeneous hψsum φ σ2 hψ0 hψrec hh⟩

/-- **Example 3.2.3 / Theorem 3.2.1 + §3.3 for the genuine `L²` causal-`ARMA` process:** for a causal
ARMA over genuine white noise `Z` (Definition 3.1.1, square-integrable and `L²`-bounded after
embedding), there exist real, summable, one-sided `MA(∞)` weights `ψ` such that the linear process
`Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ` (`linearProcessLp`) has the Theorem 3.2.1 autocovariance
`⟪X_{t+k}, Xₜ⟫ = σ² ∑ⱼ ψⱼ ψ_{j+k}`, and that autocovariance satisfies the §3.3 homogeneous AR
recursion `∑_{k=0}^p φₖ γ(h−k) = 0` for `h > q`. Both the summability (the analytic `∑ⱼ |ψⱼ| < ∞`)
and the recursion follow from causality alone — the full `L²`-process form of the closed §3.3
result. -/
theorem causal_arma_linearProcess_acvf_homogeneous [IsProbabilityMeasure μ] {φ θ : ℝ[X]}
    (hφ : IsCausalPoly φ) {Z : ℤ → Ω → ℝ} (hmem : ∀ t, MemLp (Z t) 2 μ) {σ2 : ℝ}
    (hwn : IsWhiteNoise Z μ σ2) {C : ℝ} (hZb : ∀ t, ‖toLpSeq Z hmem t‖ ≤ C)
    {h : ℤ} (hh : (θ.natDegree : ℤ) < h) :
    ∃ ψ : ℤ → ℝ, Summable ψ ∧ (∀ j : ℤ, j < 0 → ψ j = 0) ∧
      (∀ t k : ℤ, inner ℝ (linearProcessLp ψ (toLpSeq Z hmem) (t + k))
          (linearProcessLp ψ (toLpSeq Z hmem) t) = σ2 * ∑' j : ℤ, ψ j * ψ (j + k)) ∧
      ∑ k ∈ Finset.range (φ.natDegree + 1),
        φ.coeff k * (σ2 * ∑' j : ℤ, ψ j * ψ (j + (h - k))) = 0 := by
  obtain ⟨ψ, hψsum, hψ0, hψrec⟩ := exists_causal_arma_weights (θ := θ) hφ
  exact ⟨ψ, hψsum, hψ0,
    fun t k => isWhiteNoise_linearProcess_acvf hψsum hmem hwn hZb t k,
    arma_acvf_homogeneous hψsum φ σ2 hψ0 hψrec hh⟩

/-- **Forward Theorem 3.1.1 (causal ⟹ the `MA(∞)` process solves the ARMA equation):** for a causal
ARMA, the `L²` linear process `Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ` built from the genuine `MA(∞)` weights `ψ = θ/φ`
(`armaPsi`, real and summable) satisfies the ARMA difference equation `φ(B) X = θ(B) Z`:
`∑_{k=0}^p φₖ X_{t−k} = ∑_{j=0}^q θⱼ Z_{t−j}`. The filter `φ(B)` turns `X` into the linear process
with the convolved weights `∑ₖ φₖ ψ_{·−k}`, which the recursion `eq 3.3.3` identifies with the finite
`MA(q)` filter `maqFilter θ` — collapsing to `θ(B) Z`. -/
theorem causal_arma_linearProcessLp_arma_eq {φ θ : ℝ[X]} (hφ : IsCausalPoly φ)
    {Z : ℤ → Lp ℝ 2 μ} {C : ℝ} (hZb : ∀ t, ‖Z t‖ ≤ C) :
    ∃ ψ : ℤ → ℝ, Summable ψ ∧ (∀ j : ℤ, j < 0 → ψ j = 0) ∧
      ∀ t : ℤ, ∑ k ∈ Finset.range (φ.natDegree + 1), φ.coeff k • linearProcessLp ψ Z (t - k)
        = ∑ j ∈ Finset.range (θ.natDegree + 1), θ.coeff j • Z (t - j) := by
  set ψ : ℤ → ℝ := fun n => if 0 ≤ n then PowerSeries.coeff n.toNat (armaPsi φ θ) else 0 with hψdef
  have hψval : ∀ n : ℤ, ψ n = if 0 ≤ n then PowerSeries.coeff n.toNat (armaPsi φ θ) else 0 :=
    fun _ => rfl
  have hψ0 : ∀ j : ℤ, j < 0 → ψ j = 0 := fun j hj => by rw [hψval]; exact if_neg (not_le.mpr hj)
  have hψsum : Summable ψ := by
    have hcond : ∀ x ∉ Set.range ((↑) : ℕ → ℤ), ψ x = 0 := fun x hx => by
      rw [hψval]; exact if_neg fun hx0 => hx ⟨x.toNat, Int.toNat_of_nonneg hx0⟩
    refine (Function.Injective.summable_iff Nat.cast_injective hcond).mp ?_
    refine (summable_armaPsi_coeff (θ := θ) hφ).congr fun n => ?_
    rw [Function.comp_apply, hψval, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]
  have hφc : PowerSeries.constantCoeff (φ : PowerSeries ℝ) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe]
    exact fun h0 => hφ 0 (by simp)
      (by rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero, h0, map_zero])
  -- the `φ`-convolution of the `ψ`-weights is the finite `MA(q)` filter `maqFilter θ` (eq 3.3.3)
  have hconv : ∀ m : ℤ,
      ∑ k ∈ Finset.range (φ.natDegree + 1), φ.coeff k * ψ (m - k) = maqFilter θ m := by
    intro m
    rcases lt_or_ge m 0 with hm | hm
    · rw [maqFilter_neg θ hm]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hψval, if_neg (show ¬ (0 : ℤ) ≤ m - ↑k by omega), mul_zero]
    · obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = (M : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
      rw [maqFilter_natCast]
      have hg1 : ∀ k ∈ Finset.range (φ.natDegree + M + 1), k ∉ Finset.range (φ.natDegree + 1) →
          φ.coeff k * ψ ((M : ℤ) - ↑k) = 0 := fun k _ hk => by
        rw [Finset.mem_range, not_lt] at hk
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      have hg2 : ∀ k ∈ Finset.range (φ.natDegree + M + 1), k ∉ Finset.range (M + 1) →
          φ.coeff k * ψ ((M : ℤ) - ↑k) = 0 := fun k _ hk => by
        rw [Finset.mem_range, not_lt] at hk
        rw [hψval, if_neg (show ¬ (0 : ℤ) ≤ (M : ℤ) - ↑k by omega), mul_zero]
      have hval : ∀ k ∈ Finset.range (M + 1),
          φ.coeff k * PowerSeries.coeff (M - k) (armaPsi φ θ) = φ.coeff k * ψ ((M : ℤ) - ↑k) :=
        fun k hk => by
          rw [Finset.mem_range, Nat.lt_succ_iff] at hk
          rw [hψval, if_pos (show (0 : ℤ) ≤ (M : ℤ) - ↑k by omega),
            show ((M : ℤ) - ↑k).toNat = M - k from by omega]
      calc ∑ k ∈ Finset.range (φ.natDegree + 1), φ.coeff k * ψ ((M : ℤ) - ↑k)
          = ∑ k ∈ Finset.range (φ.natDegree + M + 1), φ.coeff k * ψ ((M : ℤ) - ↑k) :=
            Finset.sum_subset (by intro x hx; rw [Finset.mem_range] at hx ⊢; omega) hg1
        _ = ∑ k ∈ Finset.range (M + 1), φ.coeff k * ψ ((M : ℤ) - ↑k) :=
            (Finset.sum_subset (by intro x hx; rw [Finset.mem_range] at hx ⊢; omega) hg2).symm
        _ = ∑ k ∈ Finset.range (M + 1), φ.coeff k * PowerSeries.coeff (M - k) (armaPsi φ θ) :=
            (Finset.sum_congr rfl hval).symm
        _ = θ.coeff M := armaPsi_coeff_recursion hφc M
  refine ⟨ψ, hψsum, hψ0, fun t => ?_⟩
  rw [linearProcessLp_filter_range hψsum hZb φ.coeff (φ.natDegree + 1) t,
    show (fun m => ∑ k ∈ Finset.range (φ.natDegree + 1), φ.coeff k * ψ (m - k)) = maqFilter θ from
      funext hconv, linearProcessLp_maqFilter_eq]

/-- **Theorem 3.1.2, forward direction** (invertible ⟹ the `AR(∞)` inversion solves the ARMA
equation): for an invertible ARMA, the `AR(∞)` weights `π = φ/θ` give a process `Wₜ = ∑ⱼ πⱼ Xₜ₋ⱼ`
satisfying `θ(B) W = φ(B) X`, i.e. `∑_{k=0}^q θₖ W_{t−k} = ∑_{j=0}^p φⱼ X_{t−j}`. The exact dual of
`causal_arma_linearProcessLp_arma_eq` under `φ ↔ θ` (`IsInvertiblePoly θ` is definitionally the same
`≠ 0 on |z| ≤ 1` condition as `IsCausalPoly θ`); combined with the ARMA equation this recovers the
noise `Zₜ = ∑ⱼ πⱼ Xₜ₋ⱼ`. -/
theorem invertible_arma_linearProcessLp_arInv_eq {φ θ : ℝ[X]} (hθ : IsInvertiblePoly θ)
    {X : ℤ → Lp ℝ 2 μ} {C : ℝ} (hXb : ∀ t, ‖X t‖ ≤ C) :
    ∃ π : ℤ → ℝ, Summable π ∧ (∀ j : ℤ, j < 0 → π j = 0) ∧
      ∀ t : ℤ, ∑ k ∈ Finset.range (θ.natDegree + 1), θ.coeff k • linearProcessLp π X (t - k)
        = ∑ j ∈ Finset.range (φ.natDegree + 1), φ.coeff j • X (t - j) :=
  causal_arma_linearProcessLp_arma_eq (φ := θ) (θ := φ) hθ hXb

/-- **§8.1 (eq 8.1.5, the Yule–Walker variance equation):** for a causal `AR(p)` process
`Xₜ = ∑ⱼ ψⱼ Zₜ₋ⱼ` (`φ(B) X = Z`, `Z ~ WN(0, σ²)`), the autocovariance and the innovation variance
satisfy `∑_{k=0}^p φₖ γ(−k) = σ² ψ₀` — the `Z ⊥ past` relation, from applying `⟪·, Xₜ⟫` to the AR
equation `∑ₖ φₖ X_{t−k} = Zₜ`: `∑ₖ φₖ ⟪X_{t−k}, Xₜ⟫ = ⟪Zₜ, Xₜ⟫ = σ² ψ₀`. For the normalized
`φ(0) = 1` (so `ψ₀ = 1`) and `γ(−k) = γ(k)`, this is the book's `σ² = γ(0) − ∑_{k≥1} φ'ₖ γ(k)`. -/
theorem ar_yule_walker_variance {φ : ℝ[X]} (hφ : IsCausalPoly φ) {Z : ℤ → Lp ℝ 2 μ} {C σ2 : ℝ}
    (hZb : ∀ t, ‖Z t‖ ≤ C) (hZorth : ∀ a b, inner ℝ (Z a) (Z b) = if a = b then σ2 else 0) (t : ℤ) :
    ∃ ψ : ℤ → ℝ, Summable ψ ∧ (∀ j : ℤ, j < 0 → ψ j = 0) ∧
      ∑ k ∈ Finset.range (φ.natDegree + 1),
        φ.coeff k * (σ2 * ∑' j : ℤ, ψ j * ψ (j + -(k : ℤ))) = σ2 * ψ 0 := by
  obtain ⟨ψ, hψ, hψ0, hop⟩ := causal_arma_linearProcessLp_arma_eq (φ := φ) (θ := 1) hφ hZb
  refine ⟨ψ, hψ, hψ0, ?_⟩
  have hopt := hop t
  simp only [Polynomial.natDegree_one, zero_add, Finset.range_one, Finset.sum_singleton,
    Polynomial.coeff_one, ↓reduceIte, one_smul, Nat.cast_zero, sub_zero] at hopt
  have key := congrArg (fun w => (inner ℝ w (linearProcessLp ψ Z t) : ℝ)) hopt
  simp only [sum_inner, real_inner_smul_left] at key
  rw [real_inner_comm (linearProcessLp ψ Z t) (Z t),
    linearProcessLp_inner_single hψ hZb hZorth t t, sub_self] at key
  rw [← key]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show t - (k : ℤ) = t + -(k : ℤ) from by ring,
    linearProcessLp_inner hψ hZb hZorth t (-(k : ℤ))]

end DeepWiki.TimeSeries
