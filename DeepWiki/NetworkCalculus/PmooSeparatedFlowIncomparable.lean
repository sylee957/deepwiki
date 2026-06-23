import DeepWiki.NetworkCalculus.ServersResidualPmooRateLatency

/-! # PMOO and separated-flow end-to-end curves are incomparable
On the three-server tandem `1 → 2 → 3` in which the flow of interest crosses
every server while two cross-flows cross *overlapping but non-nested*
sub-paths — flow `2` on servers `{1,2}`, flow `3` on servers `{2,3}` — the
pay-multiplexing-only-once (PMOO) end-to-end service curve and the
separated-flow-analysis (SFA) end-to-end service curve are **incomparable**:
neither pointwise dominates the other across the parameter family.

Both end-to-end curves are rate-latency. With identical rate-latency servers
`β_{R,T}` and token-bucket cross-flows `γ_{r₂,b₂}`, `γ_{r₃,b₃}`:

* the **PMOO** curve is `β_{Rₚ,Tₚ}` with `Rₚ = R − r₂ − r₃` and
  `Tₚ = T(1 + r₂/Rₚ) + T(1 + (r₂+r₃)/Rₚ) + T(1 + r₃/Rₚ) + (b₂+b₃)/Rₚ`
  (the book's closed form: bottleneck rate net of all interfering rates, each
  burst charged once); see `pmooRate`, `pmooLatency`;

* the **SFA** curve is the convolution of the per-server residuals
  `[β_{R,T} − γ_{rₕ,bₕ}]⁺` (each burst charged at every server it meets),
  `β_{R−r₂−r₃, ∑ₕ residual latency}` via `chainConv_rateLatency` and
  `rateLatency_sub_affine`; see `sfaRate`, `sfaLatency`.

Both have the **same** bottleneck rate `R − r₂ − r₃`, so domination is decided
by the latency. We exhibit two concrete instances with opposite latency
orderings (`pmooFavorable`/`sfaFavorable`), proving the two strict witnesses
and the two `¬ ∀` refutations: neither analysis is uniformly tighter. This is
the curve-level "loss of tightness" the chapter discusses for non-nested
tandems. -/

namespace DeepWiki

open scoped NNReal

/-! ## The two end-to-end curves of the non-nested tandem
Parameters of the rate-latency end-to-end service curves for the flow of
interest, which crosses all three servers `β_{R,T}`; cross-flow `2` is
`γ_{r₂,b₂}` on servers `{1,2}` and cross-flow `3` is `γ_{r₃,b₃}` on servers
`{2,3}`. Stability is `r₂ + r₃ < R`. -/

/-- PMOO bottleneck rate: the server rate net of *all* interfering rates,
`R − r₂ − r₃` (the slowest residual rate, attained at server `2`). -/
noncomputable def pmooRate (R r₂ r₃ : ℝ≥0) : ℝ≥0 := R - r₂ - r₃

/-- PMOO end-to-end latency for the non-nested tandem (book closed form):
`T(1 + r₂/Rₚ) + T(1 + (r₂+r₃)/Rₚ) + T(1 + r₃/Rₚ) + (b₂+b₃)/Rₚ`, the burst of
each cross-flow charged exactly once over the bottleneck rate `Rₚ`. -/
noncomputable def pmooLatency (R T r₂ b₂ r₃ b₃ : ℝ≥0) : ℝ≥0 :=
  let Rp := pmooRate R r₂ r₃
  T * (1 + r₂ / Rp) + T * (1 + (r₂ + r₃) / Rp) + T * (1 + r₃ / Rp)
    + (b₂ + b₃) / Rp

/-- SFA per-server residual latency `[β_{R,T} − γ_{r,b}]⁺` latency:
`T + (r·T + b)/(R − r)` (`rateLatency_sub_affine`). -/
noncomputable def sfaHopLatency (R T r b : ℝ≥0) : ℝ≥0 :=
  T + (r * T + b) / (R - r)

/-- SFA end-to-end rate: the slowest per-server residual rate, which is the
server-`2` residual `R − r₂ − r₃` (servers `1`/`3` see only one cross-flow,
so their residual rates `R − r₂`, `R − r₃` are larger). Equals `pmooRate`. -/
noncomputable def sfaRate (R r₂ r₃ : ℝ≥0) : ℝ≥0 := R - r₂ - r₃

/-- SFA end-to-end latency: the sum of the three per-server residual
latencies — server `1` charged `γ_{r₂,b₂}`, server `2` charged the aggregate
`γ_{r₂+r₃,b₂+b₃}`, server `3` charged `γ_{r₃,b₃}`. Each burst is paid at
every server it crosses, unlike PMOO. -/
noncomputable def sfaLatency (R T r₂ b₂ r₃ b₃ : ℝ≥0) : ℝ≥0 :=
  sfaHopLatency R T r₂ b₂
    + sfaHopLatency R T (r₂ + r₃) (b₂ + b₃)
    + sfaHopLatency R T r₃ b₃

/-- The PMOO end-to-end service curve of the non-nested tandem (rate-latency). -/
noncomputable def pmooCurve (R T r₂ b₂ r₃ b₃ : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  rateLatency (pmooRate R r₂ r₃) (pmooLatency R T r₂ b₂ r₃ b₃)

/-- The SFA end-to-end service curve of the non-nested tandem (rate-latency). -/
noncomputable def sfaCurve (R T r₂ b₂ r₃ b₃ : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  rateLatency (sfaRate R r₂ r₃) (sfaLatency R T r₂ b₂ r₃ b₃)

/-- PMOO and SFA share the bottleneck rate `R − r₂ − r₃`. -/
theorem pmooRate_eq_sfaRate (R r₂ r₃ : ℝ≥0) :
    pmooRate R r₂ r₃ = sfaRate R r₂ r₃ := rfl

/-- `pmooCurve … t = Rₚ·(t − Tₚ)` (the rate-latency value). -/
theorem pmooCurve_apply (R T r₂ b₂ r₃ b₃ t : ℝ≥0) :
    pmooCurve R T r₂ b₂ r₃ b₃ t
      = pmooRate R r₂ r₃ * (t - pmooLatency R T r₂ b₂ r₃ b₃) := rfl

/-- `sfaCurve … t = Rₛ·(t − Tₛ)` (the rate-latency value). -/
theorem sfaCurve_apply (R T r₂ b₂ r₃ b₃ t : ℝ≥0) :
    sfaCurve R T r₂ b₂ r₃ b₃ t
      = sfaRate R r₂ r₃ * (t - sfaLatency R T r₂ b₂ r₃ b₃) := rfl

/-! ## The SFA latency is the chain-convolution of the residual latencies
The SFA end-to-end curve really is the convolution of the per-server residual
rate-latency curves: `chainConv_rateLatency` folds three rate-latency hops to
`β_{⨅ rate, ∑ latency}`, and `rateLatency_sub_affine` gives each residual hop.
With the symmetric server rate `R` and `r₂ + r₃ < R`, the folded rate is
`R − r₂ − r₃` (server `2`'s residual), matching `sfaRate`. -/

/-- The three SFA residual hop rates fold (min) to `R − r₂ − r₃` under
stability `r₂ + r₃ < R`: server `2`'s residual is the bottleneck. -/
theorem sfa_chainRate_eq (R r₂ r₃ : ℝ≥0) (h : r₂ + r₃ < R) :
    (R - r₂) ⊓ (R - (r₂ + r₃)) ⊓ (R - r₃) = R - r₂ - r₃ := by
  have h2 : r₂ ≤ R := le_of_lt (lt_of_le_of_lt le_self_add h)
  have h3 : r₃ ≤ R := le_of_lt (lt_of_le_of_lt le_add_self h)
  have e23 : R - (r₂ + r₃) = R - r₂ - r₃ := tsub_add_eq_tsub_tsub R r₂ r₃
  rw [e23]
  have le1 : R - r₂ - r₃ ≤ R - r₂ := tsub_le_self
  have le3 : R - r₂ - r₃ ≤ R - r₃ := by
    rw [tsub_right_comm]; exact tsub_le_self
  rw [inf_eq_right.mpr le1, inf_eq_left.mpr le3]

/-! ## `ℝ≥0` literal-subtraction facts
The truncated subtraction on `ℝ≥0` needs `n ≤ m` to coincide with real
subtraction; the literal differences arising in the two instances are
recorded once so the latency computations reduce to positive-divisor field
arithmetic. -/

/-- `(6 : ℝ≥0) − 1 = 5`. -/
theorem nnreal_six_sub_one : (6 : ℝ≥0) - 1 = 5 := by
  rw [show (6 : ℝ≥0) = 5 + 1 from by norm_num, add_tsub_cancel_right]

/-- `(6 : ℝ≥0) − 1 − 1 = 4` (the bottleneck rate of both instances). -/
theorem nnreal_six_sub_two : (6 : ℝ≥0) - 1 - 1 = 4 := by
  rw [show (6 : ℝ≥0) = 4 + 1 + 1 from by norm_num, add_tsub_cancel_right,
    add_tsub_cancel_right]

/-- `(6 : ℝ≥0) − (1 + 1) = 4`. -/
theorem nnreal_six_sub_oneone : (6 : ℝ≥0) - (1 + 1) = 4 := by
  rw [show (6 : ℝ≥0) = 4 + (1 + 1) from by norm_num, add_tsub_cancel_right]

/-! ## Two instances with opposite latency orderings -/

/-- An instance where SFA is tighter than PMOO (PMOO *loses* tightness):
`R = 6, T = 1`, both cross-flows `γ_{1,0}`. PMOO latency `4`, SFA latency
`39/10`. -/
theorem sfaFavorable_pmoo : pmooLatency 6 1 1 0 1 0 = 4 := by
  simp only [pmooLatency, pmooRate, nnreal_six_sub_two]
  norm_num

/-- The SFA-favorable instance: SFA latency `39/10 < 4`. -/
theorem sfaFavorable_sfa : sfaLatency 6 1 1 0 1 0 = 39 / 10 := by
  simp only [sfaLatency, sfaHopLatency, nnreal_six_sub_one, nnreal_six_sub_oneone]
  norm_num

/-- An instance where PMOO is tighter than SFA: `R = 6, T = 0`,
cross-flow `2 = γ_{1,0}`, cross-flow `3 = γ_{1,1}`. PMOO latency `1/4`,
SFA latency `9/20`. -/
theorem pmooFavorable_pmoo : pmooLatency 6 0 1 0 1 1 = 1 / 4 := by
  simp only [pmooLatency, pmooRate, nnreal_six_sub_two]
  norm_num

/-- The PMOO-favorable instance: SFA latency `9/20 > 1/4`. -/
theorem pmooFavorable_sfa : sfaLatency 6 0 1 0 1 1 = 9 / 20 := by
  simp only [sfaLatency, sfaHopLatency, nnreal_six_sub_one, nnreal_six_sub_oneone]
  norm_num

/-! ## The incomparability witnesses
Both instances have rate `4`; with smaller latency a rate-latency curve is
pointwise larger, so each instance witnesses one strict direction. -/

/-- The bottleneck rate `R − r₂ − r₃` of both instances is `4`. -/
theorem rate_eq_four : pmooRate 6 1 1 = 4 ∧ sfaRate 6 1 1 = 4 :=
  ⟨nnreal_six_sub_two, nnreal_six_sub_two⟩

/-- `(5 : ℝ≥0) − 4 = 1` (PMOO value increment at `t = 5`). -/
theorem nnreal_five_sub_four : (5 : ℝ≥0) - 4 = 1 := by
  rw [← NNReal.coe_inj, NNReal.coe_sub (by norm_num)]; norm_num

/-- `(5 : ℝ≥0) − 39/10 = 11/10` (SFA value increment at `t = 5`). -/
theorem nnreal_five_sub_sfa : (5 : ℝ≥0) - 39 / 10 = 11 / 10 := by
  rw [← NNReal.coe_inj, NNReal.coe_sub (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)]
  push_cast; norm_num

/-- `(1 : ℝ≥0) − 1/4 = 3/4` (PMOO value increment at `t = 1`). -/
theorem nnreal_one_sub_pmoo : (1 : ℝ≥0) - 1 / 4 = 3 / 4 := by
  rw [← NNReal.coe_inj, NNReal.coe_sub (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)]
  push_cast; norm_num

/-- `(1 : ℝ≥0) − 9/20 = 11/20` (SFA value increment at `t = 1`). -/
theorem nnreal_one_sub_sfa : (1 : ℝ≥0) - 9 / 20 = 11 / 20 := by
  rw [← NNReal.coe_inj, NNReal.coe_sub (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)]
  push_cast; norm_num

/-- **SFA beats PMOO** on the SFA-favorable instance at `t = 5`:
`pmooCurve 5 = 4 < 22/5 = sfaCurve 5`. -/
theorem pmooCurve_lt_sfaCurve_sfaFavorable :
    pmooCurve 6 1 1 0 1 0 5 < sfaCurve 6 1 1 0 1 0 5 := by
  rw [pmooCurve_apply, sfaCurve_apply, sfaFavorable_pmoo, sfaFavorable_sfa,
    rate_eq_four.2, rate_eq_four.1, nnreal_five_sub_four, nnreal_five_sub_sfa]
  norm_num

/-- **PMOO beats SFA** on the PMOO-favorable instance at `t = 1`:
`sfaCurve 1 = 11/5 < 3 = pmooCurve 1`. -/
theorem sfaCurve_lt_pmooCurve_pmooFavorable :
    sfaCurve 6 0 1 0 1 1 1 < pmooCurve 6 0 1 0 1 1 1 := by
  rw [pmooCurve_apply, sfaCurve_apply, pmooFavorable_pmoo, pmooFavorable_sfa,
    rate_eq_four.2, rate_eq_four.1, nnreal_one_sub_pmoo, nnreal_one_sub_sfa]
  norm_num

/-! ## The `¬ ∀` general refutations (neither analysis uniformly dominates) -/

/-- **PMOO does not uniformly dominate SFA**: there is no universal pointwise
inequality `sfaCurve ≤ pmooCurve` over the parameter family — the
SFA-favorable instance refutes it. -/
theorem not_forall_sfaCurve_le_pmooCurve :
    ¬ ∀ R T r₂ b₂ r₃ b₃ t, sfaCurve R T r₂ b₂ r₃ b₃ t ≤ pmooCurve R T r₂ b₂ r₃ b₃ t := by
  intro h
  exact absurd (h 6 1 1 0 1 0 5) (not_le.mpr pmooCurve_lt_sfaCurve_sfaFavorable)

/-- **SFA does not uniformly dominate PMOO**: there is no universal pointwise
inequality `pmooCurve ≤ sfaCurve` over the parameter family — the
PMOO-favorable instance refutes it. -/
theorem not_forall_pmooCurve_le_sfaCurve :
    ¬ ∀ R T r₂ b₂ r₃ b₃ t, pmooCurve R T r₂ b₂ r₃ b₃ t ≤ sfaCurve R T r₂ b₂ r₃ b₃ t := by
  intro h
  exact absurd (h 6 0 1 0 1 1 1) (not_le.mpr sfaCurve_lt_pmooCurve_pmooFavorable)

/-! ## Book restatement (incomparability of PMOO and separated-flow analysis)
On the non-nested tandem (flow of interest on all three servers, cross-flows
on `{1,2}` and `{2,3}`), the PMOO and the separated-flow end-to-end service
curves are incomparable: there is an instance where PMOO is strictly smaller
at a point and another where it is strictly larger, so neither
`pmooCurve ≤ sfaCurve` nor `sfaCurve ≤ pmooCurve` holds for all instances.
PMOO can lose tightness against the simpler separated analysis. -/
example :
    (¬ ∀ R T r₂ b₂ r₃ b₃ t, pmooCurve R T r₂ b₂ r₃ b₃ t ≤ sfaCurve R T r₂ b₂ r₃ b₃ t)
    ∧ (¬ ∀ R T r₂ b₂ r₃ b₃ t, sfaCurve R T r₂ b₂ r₃ b₃ t ≤ pmooCurve R T r₂ b₂ r₃ b₃ t) :=
  ⟨not_forall_pmooCurve_le_sfaCurve, not_forall_sfaCurve_le_pmooCurve⟩

end DeepWiki
