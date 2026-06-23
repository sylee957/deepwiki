import DeepWiki.NetworkCalculus.WorstCaseLPTandemChainRateLatency
import DeepWiki.NetworkCalculus.TandemLinearProgramWitness

/-! # The LP optimum vs the exact tandem worst-case delay (the unification, adjudicated)
Two encodings of the single-flow tandem worst case meet here:

* `worstCaseChainDelay` (= `hDev(γ_{r,b}, β_{minR,∑T})`), the **exact** worst-case
  end-to-end delay over real trajectories, with closed form `(∑ₕTₕ) + b/(minₕRₕ)`
  (`worstCaseChainDelay_tokenBucketNN_rateLatencyNN`); and
* `TandemLP.programOptimum (Feasible N) delay`, the optimum of the §11.1.2 finite LP
  on **sampled boundary dates**, with value `objectiveValue N Rmin = (∑ₕRₕTₕ + b)/(Rmin − r)`
  on the homogeneous tandem (`tandem_programOptimum_homogeneous`).

The unification is a **one-sided** identity: the LP optimum *upper-bounds* the exact
worst case, `exact ≤ LP`, and the two **coincide exactly when the source rate is null**
(`r = 0`).  For `r > 0` the §11.1.2 LP, which constrains only a single sampled backlogged
window with the strict-service curve and the token bucket, is a genuine **relaxation** that
*strictly* over-estimates (`worstCaseChainDelay_lt_programOptimum`): e.g. one server `R=2,
T=1, r=1, b=2` has exact delay `T + b/R = 2` but LP optimum `(RT+b)/(R−r) = 4`.  This is the
well-documented LP-relaxation gap; the genuinely *tight* end-to-end value is the analytic
`hDev` of part (1), not the sampled LP.  The exact `programOptimum = worstCaseChainDelay`
identity for `r > 0` would need the §11.1.3 trajectory-reconstruction that tightens the
sampled LP to the analytic optimum — `[infra]`, adjudicated below. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal BigOperators

/-! ## The arithmetic of the relaxation gap (`exact ≤ LP`) -/

/-- **The exact worst case is at most the LP objective** (the pure-arithmetic relaxation
inequality): for a stable single server `0 ≤ r < R`, `T + b/R ≤ (R·T + b)/(R − r)` — the
sampled-window LP value dominates the analytic `hDev`. -/
theorem exact_delay_le_objectiveValue_arith {R T r b : ℝ}
    (hR : 0 < R) (hr0 : 0 ≤ r) (hrR : r < R) (hT : 0 ≤ T) (hb : 0 ≤ b) :
    T + b / R ≤ (R * T + b) / (R - r) := by
  have he : T + b / R = (R * T + b) / R := by field_simp
  rw [he, div_le_div_iff₀ hR (by linarith : (0:ℝ) < R - r)]
  nlinarith [mul_nonneg hr0 hT, mul_nonneg hr0 hb, mul_pos hR hR]

/-- **The exact worst case is strictly below the LP objective when the source rate is
positive** (the relaxation is strict for `r > 0`): with `0 < r < R` and a positive burst
`0 < b`, `T + b/R < (R·T + b)/(R − r)`. -/
theorem exact_delay_lt_objectiveValue_arith {R T r b : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hrR : r < R) (hT : 0 ≤ T) (hb : 0 < b) :
    T + b / R < (R * T + b) / (R - r) := by
  have he : T + b / R = (R * T + b) / R := by field_simp
  rw [he, div_lt_div_iff₀ hR (by linarith : (0:ℝ) < R - r)]
  nlinarith [mul_nonneg hr.le hT, mul_pos hr hb, mul_pos hR hR]

/-- **The LP value equals the exact worst case exactly when the source rate is null**
(`r = 0`): `(R·T + b)/(R − 0) = T + b/R`, the only case the sampled LP is already tight. -/
theorem objectiveValue_eq_exact_delay_arith {R T b : ℝ} (hR : 0 < R) :
    (R * T + b) / (R - 0) = T + b / R := by
  rw [sub_zero]
  field_simp

/-! ## The single-server bridge: exact `worstCaseChainDelay` vs LP `programOptimum` -/

/-- The single-server tandem instance `(r, b, R, T)` for the §11.1.2 LP. -/
def singleServerTandem (r b R T : ℝ) : TandemLP.Tandem 1 where
  burst := b
  rate0 := r
  rate := ![R]
  lat := ![T]

/-- The single-server LP objective value is `(R·T + b)/(R − r)` (the SFA / sampled-window
end-to-end bound). -/
theorem objectiveValue_singleServerTandem (r b R T : ℝ) :
    TandemLP.objectiveValue (singleServerTandem r b R T) R = (R * T + b) / (R - r) := by
  simp [TandemLP.objectiveValue, singleServerTandem]

/-- **The single-server LP optimum is the SFA value `(R·T + b)/(R − r)`** — the witness
attainment `tandem_programOptimum_one` evaluated on `singleServerTandem`. -/
theorem programOptimum_singleServerTandem {r b R T : ℝ}
    (hR : 0 < R) (hr0 : 0 ≤ r) (hT : 0 ≤ T) (hb : 0 ≤ b) (hstab : r < R) :
    programOptimum (TandemLP.Feasible (singleServerTandem r b R T))
        (fun v => ((TandemLP.delay v : ℝ) : EReal))
      = (((R * T + b) / (R - r) : ℝ) : EReal) := by
  rw [TandemLP.tandem_programOptimum_one (singleServerTandem r b R T) hR hr0
    (by simp [singleServerTandem]) (by simp [singleServerTandem]; exact hT) (by simpa [singleServerTandem])
    (by simpa [singleServerTandem]), objectiveValue_singleServerTandem]

/-- The exact single-server worst-case delay `worstCaseChainDelay … []` is `T + b/R`
(part (1) on the empty downstream chain). -/
theorem worstCaseChainDelay_singleServer (r b R T : ℝ≥0)
    (hb : 0 < b) (hR : 0 < R) (hrR : r ≤ R) :
    worstCaseChainDelay (tokenBucketArrival r b) (rateLatencyNN R T) []
      = (((T + b / R : ℝ≥0)) : ℝ≥0∞) := by
  have h := worstCaseChainDelay_tokenBucketNN_rateLatencyNN r b R T [] hb
    (by simpa using hR) (by simpa using hrR)
  simpa using h

/-! ## The bridge (the one-sided unification) -/

/-- **The exact worst-case delay is at most the §11.1.2 LP optimum** (the unification, `≤`
direction): the analytic `worstCaseChainDelay` (`= T + b/R`) is dominated by the sampled LP
`programOptimum` (`= (R·T+b)/(R−r)`), as `EReal`-cast values.  So the two worst-case
encodings agree up to the LP relaxation: the finite LP is a sound *upper bound* on the exact
trajectory worst case. -/
theorem worstCaseChainDelay_le_programOptimum (r b R T : ℝ≥0)
    (hb : 0 < b) (hR : 0 < R) (hstab : r < R) :
    ((worstCaseChainDelay (tokenBucketArrival r b) (rateLatencyNN R T) [] : ℝ≥0∞) : EReal)
      ≤ programOptimum (TandemLP.Feasible (singleServerTandem r b R T))
          (fun v => ((TandemLP.delay v : ℝ) : EReal)) := by
  rw [worstCaseChainDelay_singleServer r b R T hb hR hstab.le,
    programOptimum_singleServerTandem (by exact_mod_cast hR) r.coe_nonneg T.coe_nonneg
      b.coe_nonneg (by exact_mod_cast hstab),
    EReal.coe_nnreal_eq_coe_real, EReal.coe_le_coe_iff]
  push_cast
  exact exact_delay_le_objectiveValue_arith (by exact_mod_cast hR) r.coe_nonneg
    (by exact_mod_cast hstab) T.coe_nonneg b.coe_nonneg

/-- **The exact worst case is strictly below the LP optimum when `r > 0`** (the relaxation is
strict): for a positive source rate `0 < r < R` and burst `0 < b`, the analytic worst-case
delay is *strictly* less than the LP optimum.  So `programOptimum = worstCaseChainDelay`
*fails* for `r > 0` — the §11.1.2 LP genuinely over-estimates. -/
theorem worstCaseChainDelay_lt_programOptimum (r b R T : ℝ≥0)
    (hb : 0 < b) (hR : 0 < R) (hr : 0 < r) (hstab : r < R) :
    ((worstCaseChainDelay (tokenBucketArrival r b) (rateLatencyNN R T) [] : ℝ≥0∞) : EReal)
      < programOptimum (TandemLP.Feasible (singleServerTandem r b R T))
          (fun v => ((TandemLP.delay v : ℝ) : EReal)) := by
  rw [worstCaseChainDelay_singleServer r b R T hb hR hstab.le,
    programOptimum_singleServerTandem (by exact_mod_cast hR) r.coe_nonneg T.coe_nonneg
      b.coe_nonneg (by exact_mod_cast hstab),
    EReal.coe_nnreal_eq_coe_real, EReal.coe_lt_coe_iff]
  push_cast
  exact exact_delay_lt_objectiveValue_arith (by exact_mod_cast hR) (by exact_mod_cast hr)
    (by exact_mod_cast hstab) T.coe_nonneg (by exact_mod_cast hb)

/-- **The two worst-case encodings coincide exactly when the source rate is null** (`r = 0`):
the exact `worstCaseChainDelay` *equals* the §11.1.2 LP `programOptimum`, both `= T + b/R`.
This is the only regime in which the sampled LP is already tight against the analytic worst
case (a non-bursty arrival has no burst to over-account in the single-window sample). -/
theorem worstCaseChainDelay_eq_programOptimum_of_rate0 (b R T : ℝ≥0)
    (hb : 0 < b) (hR : 0 < R) :
    ((worstCaseChainDelay (tokenBucketArrival 0 b) (rateLatencyNN R T) [] : ℝ≥0∞) : EReal)
      = programOptimum (TandemLP.Feasible (singleServerTandem 0 b R T))
          (fun v => ((TandemLP.delay v : ℝ) : EReal)) := by
  rw [worstCaseChainDelay_singleServer 0 b R T hb hR hR.le,
    programOptimum_singleServerTandem (by exact_mod_cast hR) le_rfl T.coe_nonneg
      b.coe_nonneg (by exact_mod_cast hR),
    EReal.coe_nnreal_eq_coe_real, EReal.coe_eq_coe_iff]
  push_cast
  exact (objectiveValue_eq_exact_delay_arith (by exact_mod_cast hR)).symm

/-- **The numeric relaxation gap** (the concrete witness, `R=2, T=1, r=1, b=2`): the exact
worst-case delay is `T + b/R = 2` while the §11.1.2 LP optimum is `(R·T+b)/(R−r) = 4`, twice
as large — a strict, two-fold over-estimate. -/
theorem programOptimum_eq_two_mul_worstCaseChainDelay_witness :
    ((worstCaseChainDelay (tokenBucketArrival 1 2) (rateLatencyNN 2 1) [] : ℝ≥0∞) : EReal) = 2 ∧
    programOptimum (TandemLP.Feasible (singleServerTandem 1 2 2 1))
        (fun v => ((TandemLP.delay v : ℝ) : EReal)) = 4 := by
  refine ⟨?_, ?_⟩
  · rw [worstCaseChainDelay_singleServer 1 2 2 1 (by norm_num) (by norm_num) (by norm_num),
      EReal.coe_nnreal_eq_coe_real]
    norm_num
    rfl
  · rw [programOptimum_singleServerTandem (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
    norm_num
    rfl

/-! ## Restatements (the theorems say what the book says) -/

-- The single-server exact worst case is at most the LP optimum (the sound `≤` unification).
example (r b R T : ℝ≥0) (hb : 0 < b) (hR : 0 < R) (hstab : r < R) :
    ((worstCaseChainDelay (tokenBucketArrival r b) (rateLatencyNN R T) [] : ℝ≥0∞) : EReal)
      ≤ programOptimum (TandemLP.Feasible (singleServerTandem r b R T))
          (fun v => ((TandemLP.delay v : ℝ) : EReal)) :=
  worstCaseChainDelay_le_programOptimum r b R T hb hR hstab

-- The LP optimum strictly exceeds the exact worst case for a bursty positive-rate flow.
example (r b R T : ℝ≥0) (hb : 0 < b) (hR : 0 < R) (hr : 0 < r) (hstab : r < R) :
    ((worstCaseChainDelay (tokenBucketArrival r b) (rateLatencyNN R T) [] : ℝ≥0∞) : EReal)
      < programOptimum (TandemLP.Feasible (singleServerTandem r b R T))
          (fun v => ((TandemLP.delay v : ℝ) : EReal)) :=
  worstCaseChainDelay_lt_programOptimum r b R T hb hR hr hstab

/-! ## ADJUDICATION — why the full `programOptimum = worstCaseChainDelay` identity is `[infra]`

Two faithful encodings of the single-flow tandem worst case live in the library:

* `worstCaseChainDelay` — the supremum of the realized delay over the **infinite set of real
  trajectories** `(A_in, A_out)` (`ChainServed`, the min-plus convolution service model).  It
  is provably the analytic optimum `hDev(γ_{r,b}, β_{minR,∑T}) = (∑T) + b/(minR)` (part (1)).

* `TandemLP.programOptimum (Feasible N) delay` — the supremum over the **finite §11.1.2 LP
  feasible polytope**: a single sampled backlogged window per server with the rate-latency
  *strict-service* constraint `Rₕ(wₕ − Tₕ) ≤ Aₕ − Dₕ` and one token-bucket source constraint
  `A₀ − Aₙ ≤ b + r·(t₀ − tₙ)`.  Its optimum is the SFA value `(∑RₕTₕ + b)/(Rmin − r)`
  (`tandem_programOptimum_homogeneous`).

The bridge here proves the genuine, non-trivial relation between them: `exact ≤ LP`, with
equality **iff `r = 0`** and a strict gap (`worstCaseChainDelay_lt_programOptimum`,
witnessed two-fold in `programOptimum_eq_two_mul_worstCaseChainDelay_witness`) whenever
`r > 0`.  The §11.1.2 LP as encoded is therefore a *sound over-approximation*, not an exact
encoding: its single-window source constraint bounds the whole burst against one window's
growth, which a real bursty trajectory cannot realize — the burst is paid once analytically
(`hDev`) but charged per-window in the sampled LP.

The exact `programOptimum = worstCaseChainDelay` identity for `r > 0` is **false for this LP
as written** (the strict gap above is a theorem).  Recovering an *exact* finite program would
require the §11.1.3 multi-window / trajectory-reconstruction refinement that adds the
inter-window arrival constraints tightening the polytope down to the analytic `hDev` optimum
— an extremal/existence construction over a parameterized vertex family, `[infra]`, not a
closed-form lemma.  The honest, tight deliverable is part (1)'s analytic closed form together
with this one-sided unification and its strict-gap adjudication. -/

end DeepWiki
