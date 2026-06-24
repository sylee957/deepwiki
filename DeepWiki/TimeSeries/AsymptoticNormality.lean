import DeepWiki.TimeSeries.MultivariateCLT

/-! # Asymptotic normality (Brockwell–Davis §6.4)
A real sequence `Xₙ` is **asymptotically normal** `AN(aₙ, bₙ²)` if the standardized `(Xₙ − aₙ)/bₙ`
converges in distribution to the standard normal. Equivalently (Lévy's continuity theorem) the
characteristic function of the standardized sequence converges pointwise to that of `N(0,1)`; this
characteristic-function form is taken as the definition, so the predicate is self-contained (no
reference Gaussian variable). The library's `TendstoInDistribution`-form central limit theorems feed it
through `IsAsymptoticallyNormal.of_tendstoInDistribution`. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Matrix RealInnerProductSpace

namespace DeepWiki.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Asymptotic normality** `AN(aₙ, bₙ²)`: the characteristic function of the standardized sequence
`(Xₙ − aₙ)/bₙ` converges pointwise to that of `N(0,1)`. -/
def IsAsymptoticallyNormal (X : ℕ → Ω → ℝ) (a b : ℕ → ℝ) (μ : Measure Ω) : Prop :=
  ∀ s : ℝ, Tendsto (fun n => charFun (μ.map fun ω => (X n ω - a n) / b n) s) atTop
    (𝓝 (charFun (gaussianReal 0 1) s))

/-- **Convergence in distribution of the standardized sequence to `N(0,1)` gives asymptotic normality**:
the bridge from the library's `TendstoInDistribution`-form CLTs to the `AN` predicate (Lévy's continuity
theorem, `ProbabilityMeasure.tendsto_iff_tendsto_charFun`). -/
theorem IsAsymptoticallyNormal.of_tendstoInDistribution [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    {a b : ℕ → ℝ} {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {G : Ω' → ℝ} (hG : HasLaw G (gaussianReal 0 1) P')
    (h : TendstoInDistribution (fun n ω => (X n ω - a n) / b n) atTop G (fun _ => μ) P') :
    IsAsymptoticallyNormal X a b μ := by
  intro s
  rw [← hG.map_eq]
  exact ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp h.tendsto s

/-- **Asymptotic normality is preserved under positive scaling**: if `Xₙ` is `AN(aₙ, bₙ²)` then `c · Xₙ`
is `AN(c·aₙ, (c·bₙ)²)` for `c > 0` (the standardized sequence is unchanged). -/
theorem IsAsymptoticallyNormal.const_mul_pos {X : ℕ → Ω → ℝ} {a b : ℕ → ℝ}
    (h : IsAsymptoticallyNormal X a b μ) {c : ℝ} (hc : 0 < c) :
    IsAsymptoticallyNormal (fun n ω => c * X n ω) (fun n => c * a n) (fun n => c * b n) μ := by
  intro s
  refine (h s).congr fun n => ?_
  have heq : (fun ω => (X n ω - a n) / b n) = fun ω => (c * X n ω - c * a n) / (c * b n) := by
    funext ω; rw [← mul_sub, mul_div_mul_left _ _ hc.ne']
  rw [heq]

/-- **Asymptotic normality is preserved under an additive shift**: if `Xₙ` is `AN(aₙ, bₙ²)` then
`Xₙ + dₙ` is `AN(aₙ + dₙ, bₙ²)` (the standardized sequence is unchanged). -/
theorem IsAsymptoticallyNormal.add_const {X : ℕ → Ω → ℝ} {a b : ℕ → ℝ}
    (h : IsAsymptoticallyNormal X a b μ) (d : ℕ → ℝ) :
    IsAsymptoticallyNormal (fun n ω => X n ω + d n) (fun n => a n + d n) b μ := by
  intro s
  refine (h s).congr fun n => ?_
  have heq : (fun ω => (X n ω - a n) / b n) = fun ω => (X n ω + d n - (a n + d n)) / b n := by
    funext ω; rw [add_sub_add_right_eq_sub]
  rw [heq]

/-- **Asymptotic normality from convergence in distribution to a non-degenerate Gaussian:** if `Yₙ ⇒ G`
with `G ~ N(0, v)` and `v > 0`, then `Yₙ` is `AN(0, v)` — the standardized `Yₙ / √v` converges to `N(0,1)`.
The companion of `of_tendstoInDistribution` for a limit whose variance need not be `1` (the standardizer
`gaussianReal_map_div_const`: `N(0,v)` pushed through `· / √v` is `N(0,1)`). -/
theorem IsAsymptoticallyNormal.of_tendstoInDistribution_gaussianReal [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {G : Ω' → ℝ} {v : ℝ} (hv : 0 < v) (hG : HasLaw G (gaussianReal 0 v.toNNReal) P')
    (h : TendstoInDistribution Y atTop G (fun _ => μ) P') :
    IsAsymptoticallyNormal Y (fun _ => 0) (fun _ => Real.sqrt v) μ := by
  have hdiv : HasLaw (· / Real.sqrt v) (gaussianReal 0 1) (gaussianReal 0 v.toNNReal) :=
    ⟨by fun_prop, by
      rw [gaussianReal_map_div_const, zero_div]
      congr 1
      apply NNReal.coe_injective
      rw [NNReal.coe_div, NNReal.coe_mk, Real.sq_sqrt hv.le, Real.coe_toNNReal v hv.le,
        NNReal.coe_one, div_self hv.ne']⟩
  refine IsAsymptoticallyNormal.of_tendstoInDistribution (hdiv.fun_comp hG) ?_
  have hcomp := h.continuous_comp (g := (· / Real.sqrt v)) (continuous_id.div_const _)
  simpa [Function.comp_def, sub_zero] using hcomp

/-- **Asymptotic normality of a sequence of random vectors** (Brockwell–Davis Definition 6.4.2,
Cramér–Wold form): the `ℝᵏ`-valued sequence `Xₙ` is `AN(aₙ, Sₙ)` if every nondegenerate linear
projection `λ ⬝ᵥ Xₙ` (`λ ⬝ᵥ Sₙ λ > 0`) is one-dimensionally asymptotically normal
`AN(λ ⬝ᵥ aₙ, λ ⬝ᵥ Sₙ λ)`. -/
def IsAsymptoticallyNormalVec {k : ℕ} (X : ℕ → Ω → Fin k → ℝ) (a : ℕ → Fin k → ℝ)
    (S : ℕ → Matrix (Fin k) (Fin k) ℝ) (μ : Measure Ω) : Prop :=
  ∀ lam : Fin k → ℝ, (∀ n, 0 < lam ⬝ᵥ (S n *ᵥ lam)) →
    IsAsymptoticallyNormal (fun n ω => lam ⬝ᵥ X n ω) (fun n => lam ⬝ᵥ a n)
      (fun n => Real.sqrt (lam ⬝ᵥ (S n *ᵥ lam))) μ

/-- **Linear images of asymptotically normal vectors are asymptotically normal** (Brockwell–Davis
Proposition 6.4.2): if `Xₙ` is `AN(aₙ, Sₙ)` then `B Xₙ` is `AN(B aₙ, B Sₙ Bᵀ)` for any matrix `B`. Each
projection `λ ⬝ᵥ (B Xₙ) = (Bᵀ λ) ⬝ᵥ Xₙ` is the `(Bᵀ λ)`-projection of `Xₙ`, hence asymptotically normal. -/
theorem IsAsymptoticallyNormalVec.matrix_mulVec {k m : ℕ} {X : ℕ → Ω → Fin k → ℝ} {a : ℕ → Fin k → ℝ}
    {S : ℕ → Matrix (Fin k) (Fin k) ℝ} (h : IsAsymptoticallyNormalVec X a S μ)
    (B : Matrix (Fin m) (Fin k) ℝ) :
    IsAsymptoticallyNormalVec (fun n ω => B *ᵥ X n ω) (fun n => B *ᵥ a n)
      (fun n => B * S n * Bᵀ) μ := by
  intro lam hlam
  have hproj : ∀ v : Fin k → ℝ, lam ⬝ᵥ (B *ᵥ v) = (Bᵀ *ᵥ lam) ⬝ᵥ v := fun v => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have hquad : ∀ n, lam ⬝ᵥ ((B * S n * Bᵀ) *ᵥ lam) = (Bᵀ *ᵥ lam) ⬝ᵥ (S n *ᵥ (Bᵀ *ᵥ lam)) := fun n => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hproj]
  have hcond : ∀ n, 0 < (Bᵀ *ᵥ lam) ⬝ᵥ (S n *ᵥ (Bᵀ *ᵥ lam)) := fun n => (hquad n) ▸ hlam n
  have key := h (Bᵀ *ᵥ lam) hcond
  simp only [hproj, hquad]
  exact key

/-- **Asymptotic normality of vectors is preserved under a constant shift** (the affine part of
Prop 6.4.2): if `Xₙ` is `AN(aₙ, Sₙ)` then `Xₙ + d` is `AN(aₙ + d, Sₙ)`. Each projection
`λ ⬝ᵥ (Xₙ + d) = λ ⬝ᵥ Xₙ + λ ⬝ᵥ d` is a shifted 1-D asymptotically normal sequence. -/
theorem IsAsymptoticallyNormalVec.add_const {k : ℕ} {X : ℕ → Ω → Fin k → ℝ} {a : ℕ → Fin k → ℝ}
    {S : ℕ → Matrix (Fin k) (Fin k) ℝ} (h : IsAsymptoticallyNormalVec X a S μ) (d : Fin k → ℝ) :
    IsAsymptoticallyNormalVec (fun n ω => X n ω + d) (fun n => a n + d) S μ := by
  intro lam hlam
  have key := (h lam hlam).add_const fun _ => lam ⬝ᵥ d
  simp only [dotProduct_add]
  exact key

/-- **Marginals of an asymptotically-Gaussian vector are asymptotically normal:** if `Xₙ` converges in
distribution to `V ~ multivariateGaussian 0 S` (`S` positive semidefinite) and a direction `lam` has
positive variance `lam ⬝ᵥ S lam`, then the scalar projection `⟪Xₙ, lam⟫` is asymptotically normal
`AN(0, lam ⬝ᵥ S lam)`. The projection `⟪·, lam⟫` is continuous (continuous mapping gives
`⟪Xₙ, lam⟫ ⇒ ⟪V, lam⟫`) and `⟪V, lam⟫ ~ N(0, lam ⬝ᵥ S lam)` (`map_inner_multivariateGaussian`); the
non-degenerate-Gaussian bridge then standardizes. The per-direction core of the AN-vec ⟵ multivariate-CLT
connection. -/
theorem isAsymptoticallyNormal_inner_of_tendstoInDistribution {k : ℕ} [IsProbabilityMeasure μ]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : ℕ → Ω → EuclideanSpace ℝ (Fin k)} {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosSemidef)
    {V : Ω' → EuclideanSpace ℝ (Fin k)} (hV : HasLaw V (multivariateGaussian 0 S) P')
    (h : TendstoInDistribution X atTop V (fun _ => μ) P') (lam : EuclideanSpace ℝ (Fin k))
    (hpos : 0 < lam ⬝ᵥ S *ᵥ lam) :
    IsAsymptoticallyNormal (fun n ω => (⟪X n ω, lam⟫ : ℝ)) (fun _ => 0)
      (fun _ => Real.sqrt (lam ⬝ᵥ S *ᵥ lam)) μ := by
  have hproj : HasLaw (fun x : EuclideanSpace ℝ (Fin k) => (⟪x, lam⟫ : ℝ))
      (gaussianReal 0 (lam ⬝ᵥ S *ᵥ lam).toNNReal) (multivariateGaussian 0 S) :=
    ⟨by fun_prop, map_inner_multivariateGaussian hS lam⟩
  refine IsAsymptoticallyNormal.of_tendstoInDistribution_gaussianReal hpos (hproj.fun_comp hV) ?_
  simpa [Function.comp_def] using h.continuous_comp (g := fun x => (⟪x, lam⟫ : ℝ)) (by fun_prop)

/-- **Every linear combination of the normalized i.i.d. vector sum is asymptotically normal:** for
centered i.i.d. `L²` random vectors `Z` with covariance `S`, each projection
`⟪(√n)⁻¹ ∑ₖ Zₖ, lam⟫` is asymptotically normal `AN(0, lam ⬝ᵥ S lam)` (whenever that variance is positive).
The multivariate CLT (`multivariate_iid_clt`, with the canonical identity Gaussian witness) fed through the
marginal-AN bridge — the projection form of the multivariate CLT, the engine for delta-method applications
such as the sample coefficient of variation. -/
theorem isAsymptoticallyNormal_inner_iid_clt {k : ℕ} [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → EuclideanSpace ℝ (Fin k)} {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosSemidef)
    (hZmem : ∀ i, MemLp (Z i) 2 μ) (hindep : iIndepFun Z μ)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) μ μ) (hcenter : ∫ ω, Z 0 ω ∂μ = 0)
    (hcov : ∀ t : EuclideanSpace ℝ (Fin k), ∫ ω, (⟪Z 0 ω, t⟫ : ℝ) ^ 2 ∂μ = t ⬝ᵥ S *ᵥ t)
    (lam : EuclideanSpace ℝ (Fin k)) (hpos : 0 < lam ⬝ᵥ S *ᵥ lam) :
    IsAsymptoticallyNormal (fun n ω => (⟪(√n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Z k ω, lam⟫ : ℝ))
      (fun _ => 0) (fun _ => Real.sqrt (lam ⬝ᵥ S *ᵥ lam)) μ := by
  have hV : HasLaw (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
      (multivariateGaussian 0 S) (multivariateGaussian 0 S) := ⟨aemeasurable_id, Measure.map_id⟩
  exact isAsymptoticallyNormal_inner_of_tendstoInDistribution hS hV
    (multivariate_iid_clt hS hZmem hindep hident hcenter hcov hV) lam hpos

end DeepWiki.TimeSeries
