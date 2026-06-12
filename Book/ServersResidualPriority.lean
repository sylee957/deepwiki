import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Book.ServersResidual
import Book.ServiceCurvePackets

/-! # Static-priority residual service
A preemptive static-priority server freezes a flow while strictly
higher-priority data is backlogged. With a *left-continuous* strict
aggregate service curve `β` and arrival curves on the higher-priority
flows only, flow `i` receives the strict residual
`[β − ∑_{j<i} αⱼ]⁺↑`. Left-continuity of `β` is the repair this needs:
the book's proof equates the flow's backlog at the start of the
higher-priority busy period, which an instantaneous service burst at
that instant can break; anchoring just inside the period and passing
`β` through its left limit closes the gap. For `β` not left-continuous
the statement fails — settled by the step-`β` witness ladder ending in
`not_forall_add_residualCurve_le_of_isStaticPriority`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Set Topology Filter

/-- **Preemptive static priority**: while the strictly-higher-priority
aggregate is backlogged throughout the closed interval `[s, t]`, flow
`i` receives nothing on `(s, t]` (`j < i` means `j` has higher
priority). -/
def IsStaticPriority {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A D : ι → ℝ≥0 → ℝ≥0) : Prop :=
  ∀ i : ι, ∀ s t : ℝ≥0, s ≤ t →
    (∀ u ∈ Set.Icc s t,
      (∑ j ∈ Finset.univ.filter (fun j => j < i), D j u)
        < ∑ j ∈ Finset.univ.filter (fun j => j < i), A j u) →
    D i t = D i s

/-- **Static-priority `n`-server**: every served family obeys the
preemptive priority freeze. -/
def IsStaticPriorityServerN {ι : Type*} [Fintype ι] [LinearOrder ι]
    (S : (ι → Curve) → (ι → Curve) → Prop) : Prop :=
  ∀ As Ds, S As Ds →
    IsStaticPriority (fun j => ⇑(As j)) (fun j => ⇑(Ds j))

/-- **Static-priority residual service**: under preemptive SP with a
left-continuous strict aggregate curve `β` and `αⱼ`-constrained
higher-priority arrivals, flow `i` obeys the strict service inequality
for `[β − ∑_{j<i} αⱼ]⁺↑` on its backlogged periods. -/
theorem add_residualCurve_le_of_isStaticPriority {ι : Type*} [Fintype ι]
    [LinearOrder ι] {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hβlc : IsLeftContinuous β)
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    (hSP : IsStaticPriority (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    {i : ι} (harr : ∀ j, j < i → IsMaximalArrivalBound ⇑(As j) (α j))
    {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t)) :
    (Ds i) s
      + residualCurve β
          (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α j v)
          (t - s)
      ≤ (Ds i) t := by
  set F : Finset ι := Finset.univ.filter (fun j => j < i) with hF
  set L : Finset ι := (Finset.univ.erase i) \ F with hL
  have hcH : ∀ x, (∑ j ∈ F, (Ds j) x) ≤ ∑ j ∈ F, (As j) x := fun x =>
    Finset.sum_le_sum fun j _ => hc j x
  set p : ℝ≥0 := start (fun x => ∑ j ∈ F, (As j) x)
    (fun x => ∑ j ∈ F, (Ds j) x) s with hpdef
  have hps : p ≤ s := start_le _ _ s
  have hpt : p ≤ t := hps.trans hst
  -- the higher-priority aggregate is backlogged on `(p, s]`
  have hblH : IsBacklogged (fun x => ∑ j ∈ F, (As j) x)
      (fun x => ∑ j ∈ F, (Ds j) x) (Set.Ioc p s) :=
    isBacklogged_Ioc_start hcH s
  -- and at equality at `p`
  have hpeq : (∑ j ∈ F, (As j) p) = ∑ j ∈ F, (Ds j) p :=
    apply_start_eq
      (isLeftContinuous_sum _ fun j _ => (As j).leftCont)
      (isLeftContinuous_sum _ fun j _ => (Ds j).leftCont)
      (by show (∑ j ∈ F, (As j) 0) = ∑ j ∈ F, (Ds j) 0
          exact Finset.sum_congr rfl fun j _ =>
            ((As j).zero : (As j) 0 = 0).trans
              ((Ds j).zero : (Ds j) 0 = 0).symm)
      hcH s
  -- higher-priority arrival increments
  have hHinc : ∀ x v : ℝ≥0,
      (∑ j ∈ F, (As j) (x + v)) ≤ (∑ j ∈ F, (As j) x) + ∑ j ∈ F, α j v := by
    intro x v
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    exact (isMaximalArrivalBound_iff_increment _ _).mp
      (harr j (Finset.mem_filter.mp hj).2) x v
  -- a strict prefix transfers to any superset of flows
  have hsplit : ∀ G : Finset ι, F ⊆ G → ∀ u : ℝ≥0,
      (∑ j ∈ F, (Ds j) u) < (∑ j ∈ F, (As j) u) →
      (∑ j ∈ G, (Ds j) u) < ∑ j ∈ G, (As j) u := by
    intro G hFG u hH
    calc (∑ j ∈ G, (Ds j) u)
        = (∑ j ∈ G \ F, (Ds j) u) + ∑ j ∈ F, (Ds j) u :=
          (Finset.sum_sdiff hFG).symm
      _ < (∑ j ∈ G \ F, (As j) u) + ∑ j ∈ F, (As j) u :=
          add_lt_add_of_le_of_lt
            (Finset.sum_le_sum fun j _ => hc j u) hH
      _ = ∑ j ∈ G, (As j) u := Finset.sum_sdiff hFG
  -- the full aggregate is backlogged on `(p, t]`
  have hblF : IsBacklogged (fun x => ∑ j, (As j) x)
      (fun x => ∑ j, (Ds j) x) (Set.Ioc p t) := by
    intro u hu
    rcases le_or_gt u s with hus | hus
    · exact hsplit Finset.univ (Finset.subset_univ F) u (hblH u ⟨hu.1, hus⟩)
    · exact isBacklogged_sum_of_isBacklogged (fun j _ x => hc j x) (Finset.mem_univ i)
        hbl u ⟨hus, hu.2⟩
  -- lower-priority flows are frozen on `(p, t]`
  have hfreezeLow : ∀ k ∈ L, ∀ s' w : ℝ≥0, p < s' → s' ≤ w → w ≤ t →
      (Ds k) w = (Ds k) s' := by
    intro k hk s' w hps' hs'w hwt
    have hik : i < k := by
      obtain ⟨hker, hknF⟩ := Finset.mem_sdiff.mp hk
      have hne : k ≠ i := (Finset.mem_erase.mp hker).1
      have hnlt : ¬ k < i := fun hlt => hknF
        (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hlt⟩)
      exact lt_of_le_of_ne (not_lt.mp hnlt) (Ne.symm hne)
    refine hSP k s' w hs'w fun u hu => ?_
    have hFk : F ⊆ Finset.univ.filter (fun j => j < k) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
        lt_trans (Finset.mem_filter.mp hj).2 hik⟩
    have hu' : u ∈ Set.Ioc p t :=
      ⟨lt_of_lt_of_le hps' hu.1, hu.2.trans hwt⟩
    rcases le_or_gt u s with hus | hus
    · exact hsplit _ hFk u (hblH u ⟨hu'.1, hus⟩)
    · have hiFk : i ∈ Finset.univ.filter (fun j => j < k) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hik⟩
      exact Finset.sum_lt_sum (fun j _ => hc j u)
        ⟨i, hiFk, hbl u ⟨hus, hu'.2⟩⟩
  -- flow `i` is frozen on `(p, s]`, hence `Dᵢ s ≤ Dᵢ s'` on `(p, t]`
  have hDis : ∀ s' : ℝ≥0, p < s' → s' ≤ t → (Ds i) s ≤ (Ds i) s' := by
    intro s' hps' hs't
    rcases le_or_gt s' s with h1 | h1
    · exact le_of_eq (hSP i s' s h1 fun u hu =>
        hblH u ⟨lt_of_lt_of_le hps' hu.1, hu.2⟩)
    · exact (Ds i).mono h1.le
  -- the full-aggregate decomposition over `{i} ∪ F ∪ L`
  have hdecomp : ∀ g : ι → ℝ≥0,
      (∑ j, g j) = (g i + ∑ j ∈ F, g j) + ∑ j ∈ L, g j := by
    intro g
    have hFsub : F ⊆ Finset.univ.erase i := by
      intro j hj
      exact Finset.mem_erase.mpr
        ⟨ne_of_lt (Finset.mem_filter.mp hj).2, Finset.mem_univ j⟩
    rw [← Finset.add_sum_erase _ g (Finset.mem_univ i),
      ← Finset.sum_sdiff hFsub, add_comm
        (∑ j ∈ Finset.univ.erase i \ F, g j) (∑ j ∈ F, g j), ← add_assoc]
  -- every shift up to `t − p` is covered
  have hkey : ∀ σ : ℝ≥0, σ ≤ t - p →
      β σ - (∑ j ∈ F, α j σ) ≤ (Ds i) t - (Ds i) s := by
    intro σ hσ
    rcases eq_zero_or_pos σ with rfl | hσpos
    · rw [beta_zero_eq_of_strict hstrict, zero_tsub]
      exact zero_le'
    set w : ℝ≥0 := p + σ with hw
    have hwt : w ≤ t := by
      calc p + σ ≤ p + (t - p) := add_le_add le_rfl hσ
        _ = t := add_tsub_cancel_of_le hpt
    -- the anchored bound, for every anchor `s' ∈ (p, w]`
    have hanch : ∀ s' : ℝ≥0, p < s' → s' ≤ w →
        β (w - s') ≤ (∑ j ∈ F, α j σ) + ((Ds i) t - (Ds i) s) := by
      intro s' hps' hs'w
      have hs't : s' ≤ t := hs'w.trans hwt
      have hstr := hstrict s' w hs'w fun u hu =>
        hblF u ⟨lt_trans hps' hu.1, hu.2.trans hwt⟩
      rw [hdecomp (fun j => (Ds j) s'), hdecomp (fun j => (Ds j) w)] at hstr
      have hstr' : ((Ds i) s'
            + ((∑ j ∈ F, (Ds j) s') + ∑ j ∈ L, (Ds j) s')) + β (w - s')
          ≤ (Ds i) w + ((∑ j ∈ F, (Ds j) w) + ∑ j ∈ L, (Ds j) w) := by
        rw [← add_assoc ((Ds i) s'), ← add_assoc ((Ds i) w)]
        exact hstr
      have hcross : (∑ j ∈ F, (Ds j) w) + ∑ j ∈ L, (Ds j) w
          ≤ ((∑ j ∈ F, (Ds j) s') + ∑ j ∈ L, (Ds j) s')
            + ∑ j ∈ F, α j σ := by
        have hH : (∑ j ∈ F, (Ds j) w) ≤ (∑ j ∈ F, (Ds j) s')
            + ∑ j ∈ F, α j σ := by
          calc (∑ j ∈ F, (Ds j) w) ≤ ∑ j ∈ F, (As j) w := hcH w
            _ ≤ (∑ j ∈ F, (As j) p) + ∑ j ∈ F, α j σ := hHinc p σ
            _ = (∑ j ∈ F, (Ds j) p) + ∑ j ∈ F, α j σ := by rw [hpeq]
            _ ≤ (∑ j ∈ F, (Ds j) s') + ∑ j ∈ F, α j σ :=
                add_le_add (Finset.sum_le_sum fun j _ =>
                  (Ds j).mono hps'.le) le_rfl
        have hLfr : (∑ j ∈ L, (Ds j) w) = ∑ j ∈ L, (Ds j) s' :=
          Finset.sum_congr rfl fun k hk =>
            hfreezeLow k hk s' w hps' hs'w hwt
        calc (∑ j ∈ F, (Ds j) w) + ∑ j ∈ L, (Ds j) w
            = (∑ j ∈ F, (Ds j) w) + ∑ j ∈ L, (Ds j) s' := by rw [hLfr]
          _ ≤ ((∑ j ∈ F, (Ds j) s') + ∑ j ∈ F, α j σ)
              + ∑ j ∈ L, (Ds j) s' := add_le_add hH le_rfl
          _ = ((∑ j ∈ F, (Ds j) s') + ∑ j ∈ L, (Ds j) s')
              + ∑ j ∈ F, α j σ := by ring
      have hcore := tsub_le_of_aggregate_step hstr' hcross
        ((Ds i).mono hwt) ((Ds i).mono hs't)
      have hcore' : β (w - s') - (∑ j ∈ F, α j σ)
          ≤ (Ds i) t - (Ds i) s :=
        le_trans hcore (tsub_le_tsub_left (hDis s' hps' hs't) _)
      exact tsub_le_iff_left.mp hcore'
    -- pass `β` through its left limit at `σ = w − p`
    have hlim : β σ ≤ (∑ j ∈ F, α j σ) + ((Ds i) t - (Ds i) s) := by
      have hne : (𝓝[<] σ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hσpos⟩
      refine le_of_tendsto (hβlc σ).tendsto ?_
      filter_upwards [Ioo_mem_nhdsLT hσpos] with σ' hσ'
      have hσw : σ' ≤ w := le_trans hσ'.2.le le_add_self
      have hps' : p < w - σ' := by
        rw [hw, add_tsub_assoc_of_le hσ'.2.le]
        exact lt_add_of_pos_right p (tsub_pos_of_lt hσ'.2)
      have happ := hanch (w - σ') hps' tsub_le_self
      rwa [tsub_tsub_cancel_of_le hσw] at happ
    exact tsub_le_iff_left.mpr hlim
  -- collect the supremum and conclude
  have hsup : residualCurve β (fun v => ∑ j ∈ F, α j v) (t - s)
      ≤ (Ds i) t - (Ds i) s :=
    ciSup_le fun v => hkey v.1 (v.2.trans (tsub_le_tsub_left hps t))
  calc (Ds i) s + residualCurve β (fun v => ∑ j ∈ F, α j v) (t - s)
      ≤ (Ds i) s + ((Ds i) t - (Ds i) s) := add_le_add le_rfl hsup
    _ = (Ds i) t := add_tsub_cancel_of_le ((Ds i).mono hst)

/-- Relation form: an SP `n`-server with a left-continuous strict
aggregate curve, restricted to pairs with constrained higher-priority
arrivals, offers `[β − ∑_{j<i} αⱼ]⁺↑` as a strict service curve to the
residual server of flow `i`. -/
theorem isStrictMinimalServiceCurve_residualServer_of_isStaticPriority
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S) (hβlc : IsLeftContinuous β)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hSP : IsStaticPriorityServerN S) :
    IsStrictMinimalServiceCurve
      (residualCurve β
        (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α j v))
      (residualServer (fun As Ds => S As Ds ∧
        ∀ j, j < i → IsMaximalArrivalBound ⇑(As j) (α j)) i) := by
  rintro Ai Di ⟨As, Ds, ⟨hp, harr⟩, rfl, rfl⟩ s t hst hbl
  refine add_residualCurve_le_of_isStaticPriority
    (fun j => hcaus As Ds hp j) hβlc ?_ (hSP As Ds hp) harr hst hbl
  exact hβ.sum_strict hp

/-! ## Book restatement (static priority)
A preemptive SP `n`-server offering a (left-continuous) strict service
curve `β` whose higher-priority flows have arrival curves `αⱼ`: flow `i`
receives `βᵢ = [β − ∑_{j<i} αⱼ]⁺↑` as a strict service curve — no
constraint on flow `i` itself or on lower-priority flows is used. (The
book omits the left-continuity of `β`, which its proof needs at the
start of the higher-priority busy period.) -/
example {ι : Type*} [Fintype ι] [LinearOrder ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0} {i : ι}
    (hSrv : IsServerN S) (hβlc : IsLeftContinuous β)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hSP : IsStaticPriorityServerN S) :
    IsStrictMinimalServiceCurve
      (residualCurve β
        (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α j v))
      (residualServer (fun As Ds => S As Ds ∧
        ∀ j, j < i → IsMaximalArrivalCurve ⇑(As j) (α j)) i) := by
  have h := isStrictMinimalServiceCurve_residualServer_of_isStaticPriority
    (α := α) (i := i) hSrv.1 hβlc hβ hSP
  intro Ai Di hpair
  obtain ⟨As, Ds, ⟨hp, harr⟩, hA, hD⟩ := hpair
  exact h Ai Di ⟨As, Ds, ⟨hp, fun j hj => (harr j hj).2⟩, hA, hD⟩

/-! ## The left-continuity of `β` is necessary
The witness: two flows under preemptive priority served exactly one
unit at each integer instant `0, …, 12` — all to the low-priority flow
except the units at `2, 3, 4` — against the right-continuous step
`β = 1_{d≥1}`. Every backlogged window of length at least `1` contains
an integer service instant, so the aggregate strict inequality holds;
but the high-priority burst arrives at `1⁺` and its backlogged pair
`(1, 2]` receives nothing, while `residualCurve β 0` serves `β(1) = 1`. -/

/-- The step service curve `1_{d≥1}` — not left-continuous at `1`. -/
noncomputable def spWitnessBeta : ℝ≥0 → ℝ≥0 := fun d => if d < 1 then 0 else 1

/-- High-priority witness departures: one unit at each of `2, 3, 4`. -/
noncomputable def spWitnessDHigh : Curve :=
  ∑ k ∈ ({2, 3, 4} : Finset ℕ), stepCurve (k : ℝ≥0) 1

/-- Low-priority witness departures: one unit at each of
`0, 1, 5, …, 12`. -/
noncomputable def spWitnessDLow : Curve :=
  ∑ k ∈ ({0, 1} ∪ Finset.Icc 5 12 : Finset ℕ), stepCurve (k : ℝ≥0) 1

/-- The witness aggregate serves one unit at every integer in
`0, …, 12`. -/
theorem spWitness_agg_apply (u : ℝ≥0) :
    spWitnessDHigh u + spWitnessDLow u
      = (((Finset.range 13).filter
          (fun k : ℕ => (k : ℝ≥0) < u)).card : ℝ≥0) := by
  rw [spWitnessDHigh, spWitnessDLow, sum_stepCurve_apply,
    sum_stepCurve_apply, ← Nat.cast_add, ← Finset.card_union_of_disjoint
      (((by decide : Disjoint ({2, 3, 4} : Finset ℕ)
          ({0, 1} ∪ Finset.Icc 5 12))).mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  congr 2
  rw [← Finset.filter_union]
  congr 1
  decide

/-- The step `β` is monotone (it is only left-discontinuous). -/
theorem spWitnessBeta_mono : Monotone spWitnessBeta := by
  intro a b hab
  simp only [spWitnessBeta]
  by_cases ha : a < 1
  · by_cases hb : b < 1
    · rw [if_pos ha, if_pos hb]
    · rw [if_pos ha, if_neg hb]
      exact zero_le'
  · rw [if_neg ha, if_neg (fun hb => ha (lt_of_le_of_lt hab hb))]

/-- The high-priority witness has departed nothing by time `2`. -/
theorem spWitnessDHigh_eq_zero {u : ℝ≥0} (hu : u ≤ 2) :
    spWitnessDHigh u = 0 := by
  have hempty : ({2, 3, 4} : Finset ℕ).filter
      (fun k : ℕ => (k : ℝ≥0) < u) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro k hk
    fin_cases hk
    all_goals
      push_cast
      exact not_lt.mpr (le_trans hu (by norm_num))
  rw [spWitnessDHigh, sum_stepCurve_apply, hempty]
  simp

/-- The witness pairs are causal. -/
theorem spWitness_causal :
    ∀ j : Fin 2, (![spWitnessDHigh, spWitnessDLow] j)
      ≤ (![stepCurve 1 3, stepCurve 0 10] j) := by
  intro j
  fin_cases j
  · intro u
    show spWitnessDHigh u ≤ stepCurve 1 3 u
    rw [spWitnessDHigh, sum_stepCurve_apply, stepCurve_apply]
    by_cases h1 : (1 : ℝ≥0) < u
    · rw [if_pos h1]
      calc ((({2, 3, 4} : Finset ℕ).filter
            (fun k : ℕ => (k : ℝ≥0) < u)).card : ℝ≥0)
          ≤ ((({2, 3, 4} : Finset ℕ).card : ℕ) : ℝ≥0) := by
            exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        _ = 3 := by norm_num
    · have hempty : ({2, 3, 4} : Finset ℕ).filter
          (fun k : ℕ => (k : ℝ≥0) < u) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro k hk
        fin_cases hk
        all_goals
          push_cast
          exact not_lt.mpr (le_trans (not_lt.mp h1) (by norm_num))
      rw [if_neg h1, hempty]
      simp
  · intro u
    show spWitnessDLow u ≤ stepCurve 0 10 u
    rw [spWitnessDLow, sum_stepCurve_apply, stepCurve_apply]
    by_cases h0 : (0 : ℝ≥0) < u
    · rw [if_pos h0]
      calc ((( ({0, 1} ∪ Finset.Icc 5 12 : Finset ℕ)).filter
            (fun k : ℕ => (k : ℝ≥0) < u)).card : ℝ≥0)
          ≤ ((({0, 1} ∪ Finset.Icc 5 12 : Finset ℕ).card : ℕ) : ℝ≥0) := by
            exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        _ = 10 := by
            rw [show ({0, 1} ∪ Finset.Icc 5 12 : Finset ℕ).card = 10
              from by decide]
            norm_num
    · have hempty : (({0, 1} ∪ Finset.Icc 5 12 : Finset ℕ)).filter
          (fun k : ℕ => (k : ℝ≥0) < u) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun k _ hlt =>
          h0 (lt_of_le_of_lt zero_le' hlt)
      rw [if_neg h0, hempty]
      simp

/-- The witness aggregate obeys the strict step inequality: every
backlogged window of length at least `1` contains a service instant. -/
theorem spWitness_strict : ∀ s t : ℝ≥0, s ≤ t →
    IsBacklogged
      (fun x => ∑ j, (![stepCurve 1 3, stepCurve 0 10] j) x)
      (fun x => ∑ j, (![spWitnessDHigh, spWitnessDLow] j) x)
      (Set.Ioc s t) →
    (∑ j, (![spWitnessDHigh, spWitnessDLow] j) s) + spWitnessBeta (t - s)
      ≤ ∑ j, (![spWitnessDHigh, spWitnessDLow] j) t := by
  intro s t hst hbl
  have hsum : ∀ x : ℝ≥0, (∑ j, (![spWitnessDHigh, spWitnessDLow] j) x)
      = (((Finset.range 13).filter
          (fun k : ℕ => (k : ℝ≥0) < x)).card : ℝ≥0) := by
    intro x
    rw [Fin.sum_univ_two]
    exact spWitness_agg_apply x
  have hmono : ((Finset.range 13).filter
        (fun k : ℕ => (k : ℝ≥0) < s)).card
      ≤ ((Finset.range 13).filter (fun k : ℕ => (k : ℝ≥0) < t)).card :=
    Finset.card_le_card (Finset.monotone_filter_right _
      (fun k _ hk => lt_of_lt_of_le hk hst))
  by_cases hlen : t - s < 1
  · rw [hsum, hsum, show spWitnessBeta (t - s) = 0 from if_pos hlen,
      add_zero]
    exact_mod_cast hmono
  · have h1ts : (1 : ℝ≥0) ≤ t - s := not_lt.mp hlen
    have hs1t : s + 1 ≤ t := by
      calc s + 1 ≤ s + (t - s) := add_le_add le_rfl h1ts
        _ = t := add_tsub_cancel_of_le hst
    have hslt : s < t := lt_of_lt_of_le (lt_add_of_pos_right s one_pos) hs1t
    have ht12 : t ≤ 12 := by
      by_contra hcon
      push Not at hcon
      have hb : (∑ j, (![spWitnessDHigh, spWitnessDLow] j) t)
          < ∑ j, (![stepCurve 1 3, stepCurve 0 10] j) t :=
        hbl t ⟨hslt, le_rfl⟩
      rw [hsum,
        show (((Finset.range 13).filter
            (fun k : ℕ => (k : ℝ≥0) < t)).card : ℝ≥0) = 13 from by
          rw [Finset.filter_true_of_mem fun k hk => ?_, Finset.card_range]
          · norm_num
          · have hk13 : (k : ℝ≥0) ≤ 12 := by
              have := Finset.mem_range.mp hk
              exact_mod_cast Nat.lt_succ_iff.mp this
            exact lt_of_le_of_lt hk13 hcon,
        show (∑ j, (![stepCurve 1 3, stepCurve 0 10] j) t) = 13 from by
          rw [Fin.sum_univ_two]
          show stepCurve 1 3 t + stepCurve 0 10 t = 13
          rw [stepCurve_apply, stepCurve_apply,
            if_pos (lt_trans (by norm_num : (1:ℝ≥0) < 12) hcon),
            if_pos (lt_trans (by norm_num : (0:ℝ≥0) < 12) hcon)]
          norm_num] at hb
      exact absurd hb (lt_irrefl 13)
    set k₀ : ℕ := ⌈s⌉₊ with hk₀def
    have hsk₀ : s ≤ (k₀ : ℝ≥0) := Nat.le_ceil s
    have hk₀t : (k₀ : ℝ≥0) < t :=
      lt_of_lt_of_le (Nat.ceil_lt_add_one zero_le') hs1t
    have hk₀range : k₀ ∈ Finset.range 13 := by
      rw [Finset.mem_range]
      have h13 : (k₀ : ℝ≥0) < 13 :=
        lt_of_lt_of_le hk₀t (le_trans ht12 (by norm_num))
      exact_mod_cast h13
    rw [hsum, hsum, show spWitnessBeta (t - s) = 1 from if_neg hlen]
    have hss : (Finset.range 13).filter (fun k : ℕ => (k : ℝ≥0) < s)
        ⊂ (Finset.range 13).filter (fun k : ℕ => (k : ℝ≥0) < t) := by
      refine (Finset.ssubset_iff_of_subset
        (Finset.monotone_filter_right _
          (fun k _ hk => lt_of_lt_of_le hk hst))).mpr ?_
      exact ⟨k₀, Finset.mem_filter.mpr ⟨hk₀range, hk₀t⟩, fun hmem =>
        absurd (Finset.mem_filter.mp hmem).2 (not_lt.mpr hsk₀)⟩
    have hcard := Finset.card_lt_card hss
    exact_mod_cast Nat.succ_le_of_lt hcard

/-- The witness family is served by static priority: the premise is
vacuous for the high-priority flow and pins the freeze window inside
`(1, 4]` for the low one. -/
theorem spWitness_staticPriority :
    IsStaticPriority (fun j => ⇑(![stepCurve 1 3, stepCurve 0 10] j))
      (fun j => ⇑(![spWitnessDHigh, spWitnessDLow] j)) := by
  intro i s t hst hprem
  fin_cases i
  · exfalso
    simp only [Fin.mk_zero] at hprem
    have h := hprem s ⟨le_rfl, hst⟩
    rw [show (Finset.univ.filter (fun j : Fin 2 => j < 0)) = ∅ from by
      decide] at h
    simp at h
  · simp only [Fin.mk_one] at hprem
    have hfilter : (Finset.univ.filter (fun j : Fin 2 => j < 1)) = {0} := by
      decide
    have hs1 : (1 : ℝ≥0) < s := by
      have h := hprem s ⟨le_rfl, hst⟩
      rw [hfilter, Finset.sum_singleton, Finset.sum_singleton] at h
      by_contra hcon
      push Not at hcon
      rw [show (![stepCurve 1 3, stepCurve 0 10] 0) s = 0 from by
        show stepCurve 1 3 s = 0
        rw [stepCurve_apply, if_neg (not_lt.mpr hcon)]] at h
      exact absurd h (not_lt.mpr zero_le')
    have ht4 : t ≤ 4 := by
      have h := hprem t ⟨hst, le_rfl⟩
      rw [hfilter, Finset.sum_singleton, Finset.sum_singleton] at h
      by_contra hcon
      push Not at hcon
      rw [show (![spWitnessDHigh, spWitnessDLow] 0) t = 3 from by
          show spWitnessDHigh t = 3
          rw [spWitnessDHigh, sum_stepCurve_apply,
            Finset.filter_true_of_mem fun k hk => ?_]
          · norm_num
          · have : (k : ℝ≥0) ≤ 4 := by fin_cases hk <;> norm_num
            exact lt_of_le_of_lt this hcon,
        show (![stepCurve 1 3, stepCurve 0 10] 0) t = 3 from by
          show stepCurve 1 3 t = 3
          rw [stepCurve_apply,
            if_pos (lt_trans (by norm_num : (1:ℝ≥0) < 4) hcon)]] at h
      exact absurd h (lt_irrefl 3)
    have heval : ∀ u : ℝ≥0, 1 < u → u ≤ 4 → spWitnessDLow u = 2 := by
      intro u h1 h4
      rw [spWitnessDLow, sum_stepCurve_apply,
        show (({0, 1} ∪ Finset.Icc 5 12 : Finset ℕ)).filter
            (fun k : ℕ => (k : ℝ≥0) < u) = {0, 1} from by
          ext k
          rw [Finset.mem_filter, Finset.mem_union]
          constructor
          · rintro ⟨hk | hk, hlt⟩
            · exact hk
            · exfalso
              have h5 : (5 : ℝ≥0) ≤ (k : ℝ≥0) := by
                exact_mod_cast (Finset.mem_Icc.mp hk).1
              exact absurd hlt
                (not_lt.mpr (le_trans (le_trans h4 (by norm_num)) h5))
          · intro hk
            refine ⟨Or.inl hk, ?_⟩
            have h1k : (k : ℝ≥0) ≤ 1 := by
              fin_cases hk <;> norm_num
            exact lt_of_le_of_lt h1k h1]
      norm_num
    show spWitnessDLow t = spWitnessDLow s
    rw [heval t (lt_of_lt_of_le hs1 hst) ht4,
      heval s hs1 (le_trans hst ht4)]

/-- The step `β` is not left-continuous at `1` — the witness separates
exactly the repaired hypothesis. -/
theorem not_isLeftContinuous_spWitnessBeta :
    ¬ IsLeftContinuous spWitnessBeta := by
  intro h
  have hne : (𝓝[<] (1 : ℝ≥0)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, one_pos⟩
  have h0 : Filter.Tendsto spWitnessBeta (𝓝[<] (1 : ℝ≥0)) (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact (if_pos hv).symm
  have huniq := tendsto_nhds_unique (h 1).tendsto h0
  rw [show spWitnessBeta 1 = 1 from if_neg (lt_irrefl 1)] at huniq
  exact one_ne_zero huniq

/-- The residual conclusion fails at the witness: on the pair `(1, 2)`
the high-priority flow gains nothing while the residual demands one
unit. -/
theorem not_add_residualCurve_le_spWitness :
    ¬ (spWitnessDHigh 1 + residualCurve spWitnessBeta
        (fun v => ∑ j ∈ (Finset.univ : Finset (Fin 2)).filter
          (fun j => j < (0 : Fin 2)), (fun _ _ => (0 : ℝ≥0)) j v)
        ((2 : ℝ≥0) - 1)
      ≤ spWitnessDHigh 2) := by
  intro hbad
  rw [spWitnessDHigh_eq_zero (by norm_num : (1 : ℝ≥0) ≤ 2),
    spWitnessDHigh_eq_zero le_rfl, zero_add] at hbad
  have hres : (1 : ℝ≥0) ≤ residualCurve spWitnessBeta
      (fun v => ∑ j ∈ (Finset.univ : Finset (Fin 2)).filter
        (fun j => j < (0 : Fin 2)), (fun _ _ => (0 : ℝ≥0)) j v)
      ((2 : ℝ≥0) - 1) := by
    have h21 : (2 : ℝ≥0) - 1 = 1 := tsub_eq_of_eq_add (by norm_num)
    rw [h21]
    have hb := tsub_le_residualCurve
      (β := spWitnessBeta)
      (α := fun v => ∑ j ∈ (Finset.univ : Finset (Fin 2)).filter
        (fun j => j < (0 : Fin 2)), (fun _ _ => (0 : ℝ≥0)) j v)
      (closureBddAbove_tsub_of_monotone spWitnessBeta_mono)
      (le_refl (1 : ℝ≥0))
    refine le_trans (le_of_eq ?_) hb
    show (1 : ℝ≥0) = spWitnessBeta 1
        - (∑ j ∈ (Finset.univ : Finset (Fin 2)).filter
            (fun j => j < (0 : Fin 2)), (0 : ℝ≥0))
    rw [show spWitnessBeta 1 = 1 from if_neg (lt_irrefl 1),
      Finset.sum_const_zero, tsub_zero]
  exact absurd (le_trans hres hbad) (by norm_num)

/-- **The book's static-priority residual fails without left-continuity
of `β`**: the universally quantified statement mirroring
`add_residualCurve_le_of_isStaticPriority` with `hβlc` removed is
false. -/
theorem not_forall_add_residualCurve_le_of_isStaticPriority :
    ¬ ∀ (ι : Type) [Fintype ι] [LinearOrder ι]
      (As Ds : ι → Curve) (β : ℝ≥0 → ℝ≥0) (α : ι → ℝ≥0 → ℝ≥0),
      (∀ j, Ds j ≤ As j) →
      (∀ s t, s ≤ t →
        IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
          (Set.Ioc s t) →
        (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t) →
      IsStaticPriority (fun j => ⇑(As j)) (fun j => ⇑(Ds j)) →
      ∀ i, (∀ j, j < i → IsMaximalArrivalBound ⇑(As j) (α j)) →
      ∀ s t : ℝ≥0, s ≤ t →
      IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t) →
      (Ds i) s + residualCurve β
        (fun v => ∑ j ∈ Finset.univ.filter (fun j => j < i), α j v) (t - s)
      ≤ (Ds i) t := by
  intro h
  have hbad := h (Fin 2) ![stepCurve 1 3, stepCurve 0 10]
    ![spWitnessDHigh, spWitnessDLow] spWitnessBeta (fun _ _ => 0)
    spWitness_causal spWitness_strict spWitness_staticPriority 0
    (fun j hj => absurd hj (not_lt.mpr (Fin.zero_le j)))
    1 2 (by norm_num)
    (fun u hu => by
      show spWitnessDHigh u < stepCurve 1 3 u
      rw [spWitnessDHigh_eq_zero hu.2, stepCurve_apply, if_pos hu.1]
      norm_num)
  exact not_add_residualCurve_le_spWitness hbad

end DeepWiki
