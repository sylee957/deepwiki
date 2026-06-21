import DeepWiki.TimeSeries.CausalPolyDisk
import DeepWiki.TimeSeries.LinearProcessArma

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

/-- **Causal `ARMA(p,q)` autocovariance solves the homogeneous AR recursion (§3.3):** for a causal
AR polynomial `φ` (`IsCausalPoly`), there exist real, summable, one-sided `MA(∞)` weights `ψ` (the
real parts of the Taylor coefficients of `θ/φ`) such that the linear-process autocovariance
`γ(h) = σ² ∑ⱼ ψⱼ ψ_{j+h}` satisfies `∑_{k=0}^p φₖ γ(h−k) = 0` at every lag `h > q = deg θ`. The
weight summability — a hypothesis in `arma_acvf_homogeneous` — is here *discharged* by the analytic
`∑ⱼ |ψⱼ| < ∞` of `CausalPolyDisk`. -/
theorem causal_arma_acvf_homogeneous {φ θ : ℝ[X]} (hφ : IsCausalPoly φ) (σ2 : ℝ)
    {h : ℤ} (hh : (θ.natDegree : ℤ) < h) :
    ∃ ψ : ℤ → ℝ, Summable ψ ∧ (∀ j : ℤ, j < 0 → ψ j = 0) ∧
      ∑ k ∈ Finset.range (φ.natDegree + 1),
        φ.coeff k * (σ2 * ∑' j : ℤ, ψ j * ψ (j + (h - k))) = 0 := by
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
  exact ⟨ψ, hψsum, hψ0, arma_acvf_homogeneous hψsum φ σ2 hψ0 hψrec hh⟩

end DeepWiki.TimeSeries
