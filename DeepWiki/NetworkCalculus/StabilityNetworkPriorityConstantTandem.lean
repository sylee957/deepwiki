import DeepWiki.NetworkCalculus.StabilityNetworkPriorityConstant
import DeepWiki.NetworkCalculus.StabilityNetworkTrajectory
import DeepWiki.NetworkCalculus.StabilityNetwork
import DeepWiki.NetworkCalculus.RealCurvesRates

/-! # Theorem 12.3 (static priority / FDF), shared-path tandem
The network-level static-priority stability theorem for the **shared-path tandem**: all flows `ι`
(priority-ordered by `<`) traverse the same line of `m` SP rate-latency servers; each flow a token
bucket at ingress; total local stability `∑ⱼ rⱼ < R^(k)` at every hop. Then every hop is globally
stable. The proof is the static-priority analogue of the GPS tandem
(`GpsTandem.isGloballyStable_sharedPath_tandem`): instead of GPS's argmin *peeling*, it inducts on
the **priority order** — the strictly-higher-priority flows `j < i` are bounded first (well-founded
induction on `<` over the finite flow set), so their per-hop bursts feed flow `i`'s SP residual
`β_{R k − ∑_{j<i} rⱼ, ·}` (`isMaximalArrivalBound_spPath_tokenBucket`), and flow `i` stays below its
residual rate because `∑_{j≤i} rⱼ ≤ ∑ⱼ rⱼ < R^(k)`. The per-flow bounds aggregate to local stability
against each server (`Network.isGloballyStable_of_perFlow_bounds`). Helpers live in the `SpTandem`
sub-namespace. The variable-per-server-population general SP network (the list-path↔hop bridge) is
the remaining generalization. -/

namespace DeepWiki.SpTandem

open scoped Classical NNReal ENNReal BigOperators
open DeepWiki

/-- A shared-path static-priority tandem: all flows `ι` (priority-ordered by `<`) traverse the
same `m` SP servers; hop `k`'s aggregate offers strict rate-latency `β_{R k,T k}`; each flow is
token-bucket `γ_{r i,b i}` at ingress; total local stability `∑ⱼ rⱼ < R k` at every hop. -/
structure Tandem (ι : Type*) [Fintype ι] [LinearOrder ι] (m : ℕ) where
  /-- The per-hop static-priority server relations (over the full flow set). -/
  Sf : ℕ → (ι → Curve) → (ι → Curve) → Prop
  /-- Per-hop rate of the aggregate service. -/
  R : ℕ → ℝ≥0
  /-- Per-hop latency of the aggregate service. -/
  T : ℕ → ℝ≥0
  /-- Per-flow rate at ingress. -/
  r : ι → ℝ≥0
  /-- Per-flow burst at ingress. -/
  b : ι → ℝ≥0
  /-- The trajectory: `traj k` is the per-flow input vector at hop `k`. -/
  traj : ℕ → (ι → Curve)
  /-- Each hop's server is per-flow causal. -/
  hcaus : ∀ k, IsCausalN (Sf k)
  /-- Each hop's aggregate offers strict rate-latency service `β_{R k, T k}`. -/
  hβf : ∀ k, IsStrictMinimalServiceCurve (rateLatency (R k) (T k)) (aggregateServer (Sf k))
  /-- Each hop's server obeys the preemptive static-priority freeze. -/
  hSP : ∀ k, IsStaticPriorityServerN (Sf k)
  /-- The shared-path chaining: hop `k`'s output is hop `(k+1)`'s input. -/
  hchain : ∀ k, k < m → Sf k (traj k) (traj (k + 1))
  /-- Each flow is token-bucket constrained at ingress. -/
  harr0 : ∀ i, IsMaximalArrivalBound (⇑(traj 0 i)) (fun t => r i * t + b i)
  /-- Total aggregate local stability at every hop. -/
  hstab : ∀ k, ∑ j, r j < R k

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- Flow `i` has a per-hop token-bucket arrival bound of rate `r i` at every hop. -/
def FlowBound (t : Tandem ι m) (i : ι) : Prop :=
  ∃ B : ℕ → ℝ≥0, ∀ k, k ≤ m → IsMaximalArrivalBound (⇑(t.traj k i)) (fun s => t.r i * s + B k)

/-- The higher-priority rate sum `∑_{j<i} rⱼ` is below `R k` (it is `≤ ∑ⱼ rⱼ < R k`). -/
theorem hp_rate_lt (t : Tandem ι m) (i : ι) (k : ℕ) :
    (∑ j ∈ Finset.univ.filter (fun j => j < i), t.r j) < t.R k :=
  lt_of_le_of_lt (Finset.sum_le_sum_of_subset (Finset.subset_univ _)) (t.hstab k)

/-- `∑_{j≤i} rⱼ = rᵢ + ∑_{j<i} rⱼ`. -/
theorem sum_le_eq (t : Tandem ι m) (i : ι) :
    (∑ j ∈ Finset.univ.filter (fun j => j ≤ i), t.r j)
      = t.r i + ∑ j ∈ Finset.univ.filter (fun j => j < i), t.r j := by
  rw [show Finset.univ.filter (fun j => j ≤ i)
      = insert i (Finset.univ.filter (fun j => j < i)) by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      le_iff_lt_or_eq]; tauto,
    Finset.sum_insert (by simp)]

/-- Flow `i`'s rate is below the higher-priority-reduced rate `R k − ∑_{j<i} rⱼ`. -/
theorem rate_lt_residual (t : Tandem ι m) (i : ι) (k : ℕ) :
    t.r i < t.R k - ∑ j ∈ Finset.univ.filter (fun j => j < i), t.r j := by
  rw [lt_tsub_iff_right]
  calc t.r i + ∑ j ∈ Finset.univ.filter (fun j => j < i), t.r j
      = ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), t.r j := (sum_le_eq t i).symm
    _ ≤ ∑ j, t.r j := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ < t.R k := t.hstab k

/-- **The priority-order induction**: every flow is `FlowBound`. Strong induction on the priority
order `<` (well-founded on the finite flow set): the strictly-higher-priority flows `j < i` are
`FlowBound` by the IH, so their per-hop bursts feed the SP residual, and the SP per-flow path
arrival bound (`isMaximalArrivalBound_spPath_tokenBucket`) bounds flow `i`. -/
theorem allFlowBound (t : Tandem ι m) (i : ι) : FlowBound t i := by
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    -- choose each higher-priority flow's per-hop burst function (junk off `{j < i}`)
    have hch : ∀ j : ι, ∃ Bj : ℕ → ℝ≥0, j < i →
        ∀ k, k ≤ m → IsMaximalArrivalBound (⇑(t.traj k j)) (fun s => t.r j * s + Bj k) := by
      intro j
      by_cases hj : j < i
      · obtain ⟨Bj, hBj⟩ := ih j hj; exact ⟨Bj, fun _ => hBj⟩
      · exact ⟨0, fun h => absurd h hj⟩
    choose B hB using hch
    -- apply the SP per-flow arrival-bound lemma with `bHP k j := B j k`
    have hmab := isMaximalArrivalBound_spPath_tokenBucket
      (ι := ι) (n := m) (Sf := t.Sf) (i := i) (r := t.r i) (b := t.b i)
      (R := t.R) (T := t.T) (rHP := t.r) (bHP := fun k j => B j k)
      t.hcaus t.hβf t.hSP (fun k => hp_rate_lt t i k) (fun k => t.traj k i) ?_ (t.harr0 i)
      (fun k _ => le_of_lt (rate_lt_residual t i k))
    · exact ⟨fun k => t.b i + t.r i * ∑ j ∈ Finset.range k,
        (t.R j * t.T j + ∑ l ∈ Finset.univ.filter (fun l => l < i), B l j)
          / (t.R j - ∑ l ∈ Finset.univ.filter (fun l => l < i), t.r l), hmab⟩
    · -- hchain: the residual-with-higher-priority-bound carries `traj k i → traj (k+1) i`
      intro k hk
      refine ⟨t.traj k, t.traj (k + 1), ⟨t.hchain k hk, ?_⟩, rfl, rfl⟩
      intro j hj
      exact hB j hj k (le_of_lt hk)

/-- The SP tandem as a `Network (Fin m) ι`. -/
noncomputable def toNetwork (t : Tandem ι m) : Network (Fin m) ι where
  paths := fun _ => List.finRange m
  arrival := fun i => t.traj 0 i
  arrivalCurve := fun i => fun s => t.r i * s + t.b i
  service := fun h => rateLatency (t.R h.val) (t.T h.val)

/-- In the tandem network every flow crosses every server. -/
theorem toNetwork_flowsThrough (t : Tandem ι m) (h : Fin m) :
    (toNetwork t).flowsThrough h = Finset.univ := by
  ext i; simp only [Network.mem_flowsThrough, toNetwork, Finset.mem_univ, List.mem_finRange]

/-- **Theorem 12.3, shared-path tandem**: a locally stable shared-path static-priority tandem is
globally stable at every hop — each server's aggregate has a bounded backlogged period. Assembled
by the priority-order induction (`allFlowBound`) feeding `Network.isGloballyStable_of_perFlow_bounds`
(the per-flow token buckets have rate `rᵢ`, so their aggregate has rate `∑ᵢ rᵢ < R^(h)`). -/
theorem isGloballyStable_sharedPath_tandem (t : Tandem ι m) :
    ∀ h : Fin m, IsGloballyStableServer
      (⇑(∑ i, t.traj h.val i)) (⇑(∑ i, t.traj (h.val + 1) i)) := by
  have hAll : ∀ (h : Fin m) (i : ι), ∃ B : ℝ≥0,
      IsMaximalArrivalBound (⇑(t.traj h.val i)) (fun s => t.r i * s + B) := fun h i => by
    obtain ⟨B, hB⟩ := allFlowBound t i
    exact ⟨B h.val, hB h.val (le_of_lt h.isLt)⟩
  choose B hB using hAll
  set σ : Fin m → ι → ℝ≥0 → ℝ≥0 := fun h i => fun s => t.r i * s + B h i with hσdef
  refine (toNetwork t).isGloballyStable_of_perFlow_bounds (S := fun h => t.Sf h.val)
    (Ain := fun h i => t.traj h.val i) (Dout := fun h i => t.traj (h.val + 1) i) (σ := σ)
    (fun h => t.hcaus h.val) (fun h => t.hβf h.val) (fun h => t.hchain h.val h.isLt)
    (fun h i => hB h i) ?_
  intro h
  show IsLocallyStableServer (fun s => ∑ i, σ h i s) (rateLatency (t.R h.val) (t.T h.val))
  have hcurve : (fun s => ∑ i, σ h i s) = fun s => (∑ i, t.r i) * s + ∑ i, B h i := by
    funext s; simp only [hσdef]; rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [hcurve]
  show longTermArrivalRate (fun s => (∑ i, t.r i) * s + ∑ i, B h i)
    < longTermServiceRate (rateLatency (t.R h.val) (t.T h.val))
  rw [longTermArrivalRate_affine, longTermServiceRate_rateLatency]
  exact_mod_cast t.hstab h.val

/-! ## Book restatement (Theorem 12.3, shared-path tandem)
A locally stable shared-path static-priority tandem — all flows on the same `m`-hop line, each
hop a strict rate-latency aggregate service under preemptive priority, each flow a token bucket
at ingress, total local stability `∑ᵢ rᵢ < R^(h)` — is globally stable at every hop. -/
example (t : Tandem ι m) (h : Fin m) :
    IsGloballyStableServer
      (⇑(∑ i, t.traj h.val i)) (⇑(∑ i, t.traj (h.val + 1) i)) :=
  isGloballyStable_sharedPath_tandem t h

end DeepWiki.SpTandem
