import DeepWiki.TimeSeries.MultivariateCLT

/-! # Asymptotic normality (Brockwell–Davis §6.4)
A real sequence `Xₙ` is **asymptotically normal** `AN(aₙ, bₙ²)` if the standardized `(Xₙ − aₙ)/bₙ`
converges in distribution to the standard normal. Equivalently (Lévy's continuity theorem) the
characteristic function of the standardized sequence converges pointwise to that of `N(0,1)`; this
characteristic-function form is taken as the definition, so the predicate is self-contained (no
reference Gaussian variable). The library's `TendstoInDistribution`-form central limit theorems feed it
through `IsAsymptoticallyNormal.of_tendstoInDistribution`. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Matrix

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

end DeepWiki.TimeSeries
