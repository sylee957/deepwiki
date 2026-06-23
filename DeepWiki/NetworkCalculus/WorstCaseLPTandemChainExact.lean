import DeepWiki.NetworkCalculus.WorstCaseLPTandemChainBridge

/-! # The EXACT (relaxation-free) tandem worst-case program (§11.1.3)
The §11.1.2 `TandemLP` is provably a *relaxation* — its `programOptimum` strictly
over-estimates the true worst case for a positive source rate
(`worstCaseChainDelay_lt_programOptimum`).  This file packages the **exact**
worst-case program, whose optimum *equals* the true worst-case delay (the analytic
`hDev`, closed form `(∑ₕTₕ) + b/(minₕRₕ)`), not the SFA over-estimate.

The key observation: `worstCaseChainDelay` is *already* a `⨆` over the feasible set
of real trajectories `(A_in, A_out)` constrained by `ChainServed`.  That is exactly
the shape of the generic `programOptimum Feasible obj` (`WorstCaseLP.lean`).  So the
exact worst case **is** a program optimum — `exactChainOptimum = worstCaseChainDelay`
— over the *full* (relaxation-free) network-calculus constraint set, distinct from
`TandemLP.programOptimum`'s sampled-and-relaxed polytope.  Through part (1)
(`worstCaseChainDelay_eq_hDev_minConvChain`) and the rate-latency closed form this
gives a single statement *exact LP optimum = worst case = `(∑T) + b/(minR)`*.

Part (2) carries the exact identity down to a genuinely finite-dimensional encoding
for the single server (`n = 1`): a finite `ExactServerVars`/`ExactServerFeasible`
polytope whose `programOptimum` is exactly `T + b/R` (NOT the relaxed `(RT+b)/(R−r)`),
because it carries the tight burst-against-the-backlog-window constraint the §11.1.2
LP dropped.  The general-`n` finite encoding is adjudicated at the foot of the file. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal BigOperators

/-! ## The `ℝ≥0∞`-to-`EReal` supremum bridge

`programOptimum` is `EReal`-valued; `worstCaseChainDelay` is an `ℝ≥0∞`-valued `⨆`.
The coercion `ℝ≥0∞ → EReal` commutes with a *nonempty* `⨆` (it disagrees on the
empty index, where `ℝ≥0∞`'s `⨆ = 0` but `EReal`'s `⨆ = ⊥ = −∞`), so we state the
bridge with `[Nonempty ι]`. -/

/-- `(⨆ i, f i : ℝ≥0∞)` cast to `EReal` equals `⨆ i, (f i : EReal)` for a **nonempty**
index (the cast `ℝ≥0∞ → EReal` preserves nonempty suprema; on the empty index the two
sides are `0` vs `−∞`). -/
theorem coe_ennreal_iSup {ι : Type*} [Nonempty ι] (f : ι → ℝ≥0∞) :
    ((⨆ i, f i : ℝ≥0∞) : EReal) = ⨆ i, ((f i : ℝ≥0∞) : EReal) := by
  refine le_antisymm ?_
    (iSup_le fun i => EReal.coe_ennreal_le_coe_ennreal_iff.mpr (le_iSup f i))
  set g : ι → EReal := fun i => ((f i : ℝ≥0∞) : EReal) with hg
  have hnn : (0 : EReal) ≤ ⨆ i, g i :=
    le_trans (EReal.coe_ennreal_nonneg _) (le_iSup g (Classical.arbitrary ι))
  rw [← EReal.coe_toENNReal hnn, EReal.coe_ennreal_le_coe_ennreal_iff]
  refine iSup_le fun i => ?_
  have hfi : f i = (g i).toENNReal := by rw [hg]; simp [EReal.toENNReal_coe]
  rw [hfi]
  exact EReal.toENNReal_le_toENNReal (le_iSup g i)

/-! ## Part (1): the exact worst case AS a `programOptimum`

The exact worst-case delay is the optimum of a program whose **feasible
configurations are the real trajectories** `(A_in, A_out)` and whose **objective is
the realized delay** — the full, relaxation-free network-calculus constraint set
(`ExactChainFeasible`), in contrast to `TandemLP.Feasible`'s sampled, relaxed
polytope. -/

/-- **The exact (relaxation-free) feasible set**: a trajectory pair `p = (A_in, A_out)`
is exact-feasible for the source `α` and the chain `β₀ :: βs` when `A_in` is monotone,
`α`-arrival-constrained, and served by the *entire* chain into `A_out` (`ChainServed`,
the min-plus convolution service model — no sampling, no window relaxation).  These are
exactly the constraints of `worstCaseChainDelay`'s supremand. -/
def ExactChainFeasible (α : ℝ≥0 → ℝ≥0) (β₀ : ℝ≥0 → ℝ≥0∞) (βs : List (ℝ≥0 → ℝ≥0∞))
    (p : (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0)) : Prop :=
  Monotone p.1 ∧
    IsMaximalArrivalBound (Deviation.liftENN p.1) (Deviation.liftENN α) ∧
    ChainServed β₀ βs p.1 p.2

/-- **The exact chain worst-case program optimum**: the generic `programOptimum`
over the exact-feasible trajectory set with the realized-delay objective, valued in
`EReal`.  This is the §11.1.3 *relaxation-free* program — distinct from the §11.1.2
`TandemLP.programOptimum`, which is a sampled relaxation that strictly over-estimates. -/
noncomputable def exactChainOptimum (α : ℝ≥0 → ℝ≥0) (β₀ : ℝ≥0 → ℝ≥0∞)
    (βs : List (ℝ≥0 → ℝ≥0∞)) : EReal :=
  programOptimum (ExactChainFeasible α β₀ βs)
    (fun p => ((Deviation.delay p.1 p.2 : ℝ≥0∞) : EReal))

/-- **The exact program optimum is the worst-case delay** (part (1), the repackaging):
`exactChainOptimum = worstCaseChainDelay`, cast to `EReal`.  The two are the *same*
nonempty supremum — `worstCaseChainDelay`'s `⨆` over `{p // Feasible p}` and
`programOptimum`'s `⨆` over the same subtype with the cast objective — so the exact
worst case literally *is* a program optimum.  Needs the servers null at the origin so
the greedy trajectory exists and the feasible set is nonempty. -/
theorem exactChainOptimum_eq_worstCaseChainDelay {α : ℝ≥0 → ℝ≥0} {β₀ : ℝ≥0 → ℝ≥0∞}
    {βs : List (ℝ≥0 → ℝ≥0∞)} (hαmono : Monotone α) (hαsub : IsSubadditive α)
    (hβ₀0 : β₀ 0 = 0) (hβs0 : ∀ γ ∈ βs, γ 0 = 0) :
    exactChainOptimum α β₀ βs = ((worstCaseChainDelay α β₀ βs : ℝ≥0∞) : EReal) := by
  -- nonemptiness: the greedy chain trajectory is feasible
  obtain ⟨A_out, hserv, _⟩ := exists_chainServed_greedy β₀ βs hβ₀0 hβs0 α
  have harr : IsMaximalArrivalBound (Deviation.liftENN α) (Deviation.liftENN α) :=
    isMaximalArrivalBound_self_of_subadditive hαsub.liftENN
  -- the feasible subtype (in `worstCaseChainDelay`'s inlined spelling) is nonempty
  haveI hne : Nonempty {p : (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0) // Monotone p.1 ∧
      IsMaximalArrivalBound (Deviation.liftENN p.1) (Deviation.liftENN α) ∧
      ChainServed β₀ βs p.1 p.2} :=
    ⟨⟨(α, A_out), hαmono, harr, hserv⟩⟩
  rw [exactChainOptimum, programOptimum, worstCaseChainDelay, coe_ennreal_iSup]
  rfl

/-- **The exact program optimum is the horizontal deviation** `hDev(α, β₀ ∗ β₁ ∗ ⋯)`
(part (1) chained through `worstCaseChainDelay_eq_hDev_minConvChain`): the optimum of
the relaxation-free trajectory program is the analytic closed form, not a sampled
over-estimate. -/
theorem exactChainOptimum_eq_hDev_minConvChain {α : ℝ≥0 → ℝ≥0} {β₀ : ℝ≥0 → ℝ≥0∞}
    {βs : List (ℝ≥0 → ℝ≥0∞)} (hαmono : Monotone α) (hα0 : IsNullAtOrigin α)
    (hαsub : IsSubadditive α) (hβ₀mono : Monotone β₀) (hβsmono : ∀ γ ∈ βs, Monotone γ)
    (hβ₀0 : β₀ 0 = 0) (hβs0 : ∀ γ ∈ βs, γ 0 = 0) :
    exactChainOptimum α β₀ βs
      = ((hDev (Deviation.liftENN α) (minConvChain β₀ βs) : ℝ≥0∞) : EReal) := by
  rw [exactChainOptimum_eq_worstCaseChainDelay hαmono hαsub hβ₀0 hβs0,
    worstCaseChainDelay_eq_hDev_minConvChain hαmono hα0 hαsub hβ₀mono hβsmono hβ₀0 hβs0]

/-- **The exact LP optimum of a heterogeneous rate-latency tandem is `(∑ₕTₕ) + b/(minₕRₕ)`**
(part (1) end to end): for a token-bucket source `γ_{r,b}` (`b > 0`, `r ≤ minR`) crossing
the rate-latency chain `β_{R₀,T₀} :: [β_{R₁,T₁}, …]`, the *exact, relaxation-free*
program optimum is the true tight closed form — `exact LP optimum = worst case =
(∑T) + b/(minR)` as a single statement, with no SFA over-estimate. -/
theorem exactChainOptimum_tokenBucketNN_rateLatencyNN (r b R₀ T₀ : ℝ≥0)
    (ps : List (ℝ≥0 × ℝ≥0)) (hb : 0 < b)
    (hRmin : 0 < ps.foldr (fun p R => p.1 ⊓ R) R₀)
    (hrR : r ≤ ps.foldr (fun p R => p.1 ⊓ R) R₀) :
    exactChainOptimum (tokenBucketArrival r b) (rateLatencyNN R₀ T₀)
        (ps.map (fun p => rateLatencyNN p.1 p.2))
      = ((((T₀ + (ps.map Prod.snd).sum) + b / (ps.foldr (fun p R => p.1 ⊓ R) R₀)
          : ℝ≥0) : ℝ≥0∞) : EReal) := by
  rw [exactChainOptimum_eq_worstCaseChainDelay (tokenBucketArrival_mono r b)
      (tokenBucketArrival_subadditive r b) (rateLatencyNN_zero_eq R₀ T₀)
      (fun γ hγ => by
        obtain ⟨p, _, hp⟩ := List.mem_map.mp hγ
        exact hp ▸ rateLatencyNN_zero_eq p.1 p.2),
    worstCaseChainDelay_tokenBucketNN_rateLatencyNN r b R₀ T₀ ps hb hRmin hrR]

/-! ## Restatements (the theorems say what the book says) -/

-- The exact (relaxation-free) program optimum is the worst-case delay, as `EReal` values.
example {α : ℝ≥0 → ℝ≥0} {β₀ : ℝ≥0 → ℝ≥0∞} {βs : List (ℝ≥0 → ℝ≥0∞)}
    (hαmono : Monotone α) (hαsub : IsSubadditive α) (hβ₀0 : β₀ 0 = 0)
    (hβs0 : ∀ γ ∈ βs, γ 0 = 0) :
    exactChainOptimum α β₀ βs = ((worstCaseChainDelay α β₀ βs : ℝ≥0∞) : EReal) :=
  exactChainOptimum_eq_worstCaseChainDelay hαmono hαsub hβ₀0 hβs0

-- The exact single-server program optimum is `T + b/R` (not the relaxed `(RT+b)/(R−r)`).
example (r b R T : ℝ≥0) (hb : 0 < b) (hR : 0 < R) (hrR : r ≤ R) :
    exactChainOptimum (tokenBucketArrival r b) (rateLatencyNN R T) []
      = (((T + b / R : ℝ≥0) : ℝ≥0∞) : EReal) := by
  have h := exactChainOptimum_tokenBucketNN_rateLatencyNN r b R T [] hb
    (by simpa using hR) (by simpa using hrR)
  simpa using h

/-! ## Part (2): a genuinely finite-dimensional EXACT single-server LP

The §11.1.2 `TandemLP` is a relaxation because its single source constraint charges
the whole burst `b` over the *outer* window `[t n, t 0]`; on one server that gives the
loose `(R·T + b)/(R − r)`.  The §11.1.3 *exact* single-server LP separates the bit of
interest's **arrival date** `u` from the backlog-start `s`, charging the token bucket
only over `[s, u]`.  This `4`-real polytope (`ExactServerVars`: `s ≤ u ≤ d`, arrival
increment `q`) has the same realized delay `d − u`, and its optimum is exactly the
tight `T + b/R` — no relaxation gap.

The tightening is the date split: with `delay = d − u = T + q/R − (u − s)` and the
token bucket `q ≤ b + r·(u − s)`,
`delay ≤ T + b/R − (u − s)·(1 − r/R) ≤ T + b/R`, attained at `u = s`.  The relaxed LP
collapses `u = s` away, paying `b/(R − r)` instead of `b/R`. -/

/-- **The variables of the exact single-server LP** (§11.1.3, one server): the
backlog-start date `s`, the bit-of-interest **arrival** date `u` (separated from `s` —
this is the tightening the §11.1.2 LP loses), the **departure** date `d`, and the
arrival increment `q = A u − A s` of the bit above the backlog-start level. -/
structure ExactServerVars where
  /-- Start of the backlogged period. -/
  s : ℝ
  /-- Arrival date of the bit of interest (`s ≤ u`). -/
  u : ℝ
  /-- Departure date of the bit of interest (`u ≤ d`). -/
  d : ℝ
  /-- Arrival increment `A u − A s` of the bit above the backlog-start level. -/
  q : ℝ

/-- **The exact single-server feasible polytope** for a token-bucket source `γ_{r,b}`
crossing a rate-latency strict server `β_{R,T}`:

* **date ordering** `s ≤ u` (bit arrives no earlier than backlog start) and `u ≤ d`
  (departs after arriving);
* **arrival increment nonneg** `0 ≤ q`;
* **token bucket on `[s, u]`** `q ≤ b + r·(u − s)`: the bit's arrival increment is
  `γ_{r,b}`-constrained over the *sub-window up to its own arrival* (the tight
  §11.1.3 form, not the §11.1.2 outer-window relaxation);
* **strict service** `R·((d − s) − T) ≤ q`: the bit at increment `q` departs no later
  than when the rate-latency strict-service guarantee `R·((·) − T)` reaches `q`. -/
def ExactServerFeasible (r b R T : ℝ) (v : ExactServerVars) : Prop :=
  v.s ≤ v.u ∧ v.u ≤ v.d ∧ 0 ≤ v.q ∧
    v.q ≤ b + r * (v.u - v.s) ∧
    R * ((v.d - v.s) - T) ≤ v.q

/-- The realized end-to-end **delay** of a single-server exact point: the time the bit
spends from arrival `u` to departure `d`. -/
def exactServerDelay (v : ExactServerVars) : ℝ := v.d - v.u

/-- **Soundness** (the `≤` half of exactness): every feasible single-server point has
delay at most `T + b/R`.  The date split plus the token bucket give
`delay = T + q/R − (u − s) ≤ T + b/R − (u − s)·(1 − r/R) ≤ T + b/R` for a stable
source `0 ≤ r ≤ R`. -/
theorem exactServerDelay_le {r b R T : ℝ} {v : ExactServerVars}
    (hR : 0 < R) (hrR : r ≤ R) (hv : ExactServerFeasible r b R T v) :
    exactServerDelay v ≤ T + b / R := by
  obtain ⟨hsu, _, _, htb, hserv⟩ := hv
  rw [exactServerDelay]
  -- reduce to `R·(d − u) ≤ R·T + b`, then linear arithmetic
  have key : R * (v.d - v.u) ≤ R * T + b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrR) (sub_nonneg.mpr hsu), hserv, htb]
  have he : T + b / R = (R * T + b) / R := by field_simp
  rw [he, le_div_iff₀ hR, mul_comm]
  linarith [key]

/-- The **worst-case feasible point**: the bit arrives at the backlog start (`u = s = 0`)
inside the full burst (`q = b`) and departs after latency-plus-burst-service
(`d = T + b/R`).  Realizes delay exactly `T + b/R`. -/
noncomputable def exactServerWitness (b R T : ℝ) : ExactServerVars where
  s := 0
  u := 0
  d := T + b / R
  q := b

/-- The witness is **feasible** for any stable source (`0 ≤ r`, `0 < R`, `0 ≤ b`,
`0 ≤ T`): the bit takes the whole burst at the start and the service guarantee is met
with equality. -/
theorem exactServerFeasible_witness {r b R T : ℝ}
    (hR : 0 < R) (hb : 0 ≤ b) (hT : 0 ≤ T) :
    ExactServerFeasible r b R T (exactServerWitness b R T) := by
  refine ⟨le_rfl, ?_, hb, ?_, ?_⟩
  · simp only [exactServerWitness]; positivity
  · simp only [exactServerWitness]; linarith
  · simp only [exactServerWitness, sub_zero, add_sub_cancel_left]
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self (ne_of_gt hR), mul_one]

/-- The witness **realizes** delay `T + b/R`. -/
theorem exactServerDelay_witness (b R T : ℝ) :
    exactServerDelay (exactServerWitness b R T) = T + b / R := by
  simp [exactServerDelay, exactServerWitness]

/-- **The exact single-server LP optimum is `T + b/R`** (§11.1.3, the relaxation-free
single server): the `programOptimum` of the exact finite polytope equals the true tight
worst-case delay — *not* the §11.1.2 relaxation's `(R·T + b)/(R − r)`.  Soundness bounds
every feasible point by `T + b/R` (`exactServerDelay_le`) and the witness attains it
(`exactServerFeasible_witness` + `exactServerDelay_witness`).  This is the finite-LP
counterpart of `exactChainOptimum … [] = T + b/R`. -/
theorem programOptimum_exactServer {r b R T : ℝ}
    (hR : 0 < R) (hrR : r ≤ R) (hb : 0 ≤ b) (hT : 0 ≤ T) :
    programOptimum (ExactServerFeasible r b R T)
        (fun v => ((exactServerDelay v : ℝ) : EReal))
      = (((T + b / R : ℝ) : EReal)) := by
  apply le_antisymm
  · refine programOptimum_le fun v hv => ?_
    exact EReal.coe_le_coe_iff.mpr (exactServerDelay_le hR hrR hv)
  · rw [show (((T + b / R : ℝ) : EReal)) = ((exactServerDelay (exactServerWitness b R T) : ℝ) : EReal)
      from by rw [exactServerDelay_witness]]
    exact le_programOptimum (obj := fun v => ((exactServerDelay v : ℝ) : EReal))
      (exactServerFeasible_witness hR hb hT)

/-- **The exact single-server LP optimum equals the exact analytic optimum**
(part (1) ∘ part (2)): the finite §11.1.3 polytope's `programOptimum` *is* the
relaxation-free trajectory program's optimum `exactChainOptimum … []`, both equal to
`T + b/R` — a single bridge from the finite LP to the analytic worst case. -/
theorem programOptimum_exactServer_eq_exactChainOptimum (r b R T : ℝ≥0)
    (hb : 0 < b) (hR : 0 < R) (hrR : r ≤ R) :
    programOptimum (ExactServerFeasible r b R T)
        (fun v => ((exactServerDelay v : ℝ) : EReal))
      = exactChainOptimum (tokenBucketArrival r b) (rateLatencyNN R T) [] := by
  have hrhs : exactChainOptimum (tokenBucketArrival r b) (rateLatencyNN R T) []
      = (((T + b / R : ℝ≥0) : ℝ≥0∞) : EReal) := by
    have h := exactChainOptimum_tokenBucketNN_rateLatencyNN r b R T [] hb
      (by simpa using hR) (by simpa using hrR)
    simpa using h
  rw [programOptimum_exactServer (by exact_mod_cast hR)
      (by exact_mod_cast hrR) b.coe_nonneg T.coe_nonneg, hrhs,
    EReal.coe_nnreal_eq_coe_real]
  push_cast
  rfl

/-! ## Restatements of Part (2) -/

-- The exact single-server finite LP optimum is the tight `T + b/R`, not the SFA value.
example (r b R T : ℝ) (hR : 0 < R) (hrR : r ≤ R) (hb : 0 ≤ b) (hT : 0 ≤ T) :
    programOptimum (ExactServerFeasible r b R T)
        (fun v => ((exactServerDelay v : ℝ) : EReal))
      = (((T + b / R : ℝ) : EReal)) :=
  programOptimum_exactServer hR hrR hb hT

/-! ## Part (3): the general-`n` exact finite LP via the chain collapse

For a single flow, the §11.1.3 PMOO content *is* the chain collapse: the cascade
`β_{R₀,T₀} ∗ ⋯ ∗ β_{Rₙ,Tₙ} = β_{minR, ∑T}` (`minConvChain_rateLatencyNN`) is already
the tight end-to-end service curve.  So the **general-`n` exact finite LP is the
single-server polytope `ExactServerFeasible` at the collapsed parameters
`(∑ₕTₕ, minₕRₕ)`** — its optimum is `(∑T) + b/(minR)`, the exact heterogeneous tandem
worst case, *not* the SFA bottleneck objective.  This is `programOptimum_exactServer`
fed the collapsed `(R, T)`, bridged to part (1)'s analytic `exactChainOptimum`. -/

/-- **The general-`n` exact finite LP optimum equals the exact analytic tandem optimum**:
the single-server polytope at the *collapsed* parameters `(∑Tₕ, minₕRₕ)` has
`programOptimum = exactChainOptimum` of the whole rate-latency chain, both
`(∑T) + b/(minR)`.  This realizes the heterogeneous `n`-server worst case as a finite LP
(the chain-collapse / PMOO route — exact for a single flow), distinct from the SFA
relaxation.  Writing `Rmin = ps.foldr (⊓) R₀`, `Tsum = T₀ + ∑ₕ Tₕ`. -/
theorem programOptimum_exactServer_collapsed_eq_exactChainOptimum (r b R₀ T₀ : ℝ≥0)
    (ps : List (ℝ≥0 × ℝ≥0)) (Rmin Tsum : ℝ≥0)
    (hRmindef : Rmin = ps.foldr (fun p R => p.1 ⊓ R) R₀)
    (hTsumdef : Tsum = T₀ + (ps.map Prod.snd).sum)
    (hb : 0 < b) (hRmin : 0 < Rmin) (hrR : r ≤ Rmin) :
    programOptimum
        (ExactServerFeasible (r : ℝ) (b : ℝ) (Rmin : ℝ) (Tsum : ℝ))
        (fun v => ((exactServerDelay v : ℝ) : EReal))
      = exactChainOptimum (tokenBucketArrival r b) (rateLatencyNN R₀ T₀)
          (ps.map (fun p => rateLatencyNN p.1 p.2)) := by
  -- LHS via the finite single-server optimum at the collapsed (ℝ-cast) parameters
  rw [programOptimum_exactServer (by exact_mod_cast hRmin) (by exact_mod_cast hrR)
      b.coe_nonneg Tsum.coe_nonneg]
  -- RHS via part (1)'s analytic closed form, then fold the collapsed parameters back
  have hchain := exactChainOptimum_tokenBucketNN_rateLatencyNN r b R₀ T₀ ps hb
    (hRmindef ▸ hRmin) (hRmindef ▸ hrR)
  rw [← hRmindef, ← hTsumdef] at hchain
  rw [hchain, EReal.coe_nnreal_eq_coe_real, EReal.coe_eq_coe_iff, NNReal.coe_add,
    NNReal.coe_div]

/-- **The exact `n`-server finite LP optimum is `(∑T) + b/(minR)`** (the explicit closed
form, general heterogeneous tandem): the collapsed single-server polytope optimum is the
true tight value.  The finite-LP statement of `worstCaseChainDelay_tokenBucketNN_rateLatencyNN`. -/
theorem programOptimum_exactServer_collapsed_eq (r b R₀ T₀ : ℝ≥0)
    (ps : List (ℝ≥0 × ℝ≥0)) (Rmin Tsum : ℝ≥0)
    (hRmindef : Rmin = ps.foldr (fun p R => p.1 ⊓ R) R₀)
    (hTsumdef : Tsum = T₀ + (ps.map Prod.snd).sum)
    (hb : 0 < b) (hRmin : 0 < Rmin) (hrR : r ≤ Rmin) :
    programOptimum
        (ExactServerFeasible (r : ℝ) (b : ℝ) (Rmin : ℝ) (Tsum : ℝ))
        (fun v => ((exactServerDelay v : ℝ) : EReal))
      = ((((Tsum + b / Rmin : ℝ≥0)) : ℝ≥0∞) : EReal) := by
  rw [programOptimum_exactServer_collapsed_eq_exactChainOptimum r b R₀ T₀ ps Rmin Tsum
      hRmindef hTsumdef hb hRmin hrR]
  have hchain := exactChainOptimum_tokenBucketNN_rateLatencyNN r b R₀ T₀ ps hb
    (hRmindef ▸ hRmin) (hRmindef ▸ hrR)
  rw [← hRmindef, ← hTsumdef] at hchain
  exact hchain

/-! ## Restatements of Part (3) -/

-- The exact TWO-server finite LP optimum is `(T₀+T₁) + b/(R₁⊓R₀)`, the true tight value.
example (r b R₀ T₀ R₁ T₁ : ℝ≥0) (hb : 0 < b) (hRmin : 0 < R₁ ⊓ R₀) (hrR : r ≤ R₁ ⊓ R₀) :
    programOptimum (ExactServerFeasible (r : ℝ) (b : ℝ) ((R₁ ⊓ R₀ : ℝ≥0) : ℝ)
        ((T₀ + T₁ : ℝ≥0) : ℝ))
        (fun v => ((exactServerDelay v : ℝ) : EReal))
      = ((((T₀ + T₁) + b / (R₁ ⊓ R₀) : ℝ≥0) : ℝ≥0∞) : EReal) :=
  programOptimum_exactServer_collapsed_eq r b R₀ T₀ [(R₁, T₁)] (R₁ ⊓ R₀) (T₀ + T₁)
    (by simp) (by simp) hb hRmin hrR

/-! ## ADJUDICATION — what is exact, and what the per-server finite encoding still needs

**Exact (proven here), `r > 0` included:**

* Part (1) — the *relaxation-free* program `exactChainOptimum` (the supremum over the
  full infinite trajectory set `ChainServed`, no sampling) **equals** `worstCaseChainDelay`
  (`exactChainOptimum_eq_worstCaseChainDelay`), hence the analytic `hDev` and the closed
  form `(∑T) + b/(minR)` (`exactChainOptimum_tokenBucketNN_rateLatencyNN`).  This is the
  honest "exact LP optimum = worst case = closed form" as one statement, for *any* source
  rate — unlike the §11.1.2 `TandemLP`, which strictly over-estimates for `r > 0`
  (`worstCaseChainDelay_lt_programOptimum`).

* Part (2) — a genuinely **finite-dimensional** exact LP for one server: the 4-real
  polytope `ExactServerFeasible` whose `programOptimum` is exactly `T + b/R`
  (`programOptimum_exactServer`), with the §11.1.3 date-split (arrival `u` separated from
  backlog-start `s`) that the §11.1.2 LP collapsed.  Bridged to part (1)
  (`programOptimum_exactServer_eq_exactChainOptimum`).

* Part (3) — the general-`n` heterogeneous exact finite LP via the **chain collapse**:
  the single-server polytope at `(∑Tₕ, minₕRₕ)` is the exact `n`-server program
  (`programOptimum_exactServer_collapsed_eq`, `= (∑T) + b/(minR)`), since for a single
  flow the concatenation `β₀ ∗ ⋯ ∗ βₙ = β_{minR,∑T}` is already tight (PMOO is exact).
  The two-server explicit instance is the restatement above.

**Scoped (`[infra]`) — a *per-server-windowed* finite LP for general `n`:** part (3)'s
finite LP collapses the chain to one server *before* sampling, so it has a single window,
not one window per server.  A per-server-windowed exact polytope (variables `s, u`, a
departure date `dₕ` per server, per-server strict-service `Rₕ((dₕ − d_{h−1}) − Tₕ) ≤ qₕ`,
flow conservation, objective `d_{n−1} − u`) requires proving that the *latest-departure*
vertex of that polytope realizes the global combined service `β_{minR,∑T}` — i.e. that the
per-window slacks telescope to the collapsed bound with equality at the bottleneck.  That
is the §11.1.3 trajectory-reconstruction (an extremal-vertex existence argument over the
per-server window family), and is exactly the obstruction documented for the SFA witness in
`TandemLinearProgramWitness`'s `## NON-ATTAINMENT`.  The collapse route (part (3)) sidesteps
it and is mathematically the tight single-flow result; the windowed encoding is the same
optimum re-derived through per-server vertices, deferred. -/

end DeepWiki
