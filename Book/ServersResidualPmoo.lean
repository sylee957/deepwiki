import Book.ServersResidual

/-! # Pay multiplexing only once
Two strict servers in tandem under blind multiplexing: computing the
tagged flow's residual directly across the tandem pays the
cross-traffic burst once — `(β₁ ∗ β₂ − ∑_{j≠i} αⱼ)⁺`, with no
closure — where the modular per-server composition pays it at every
hop. The start of the second server's backlogged period cascades to
a start of the first, and the strict bounds chain across the two
windows. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The PMOO residual `(β₁ ∗ β₂ − α)⁺`: the tandem convolution less
the cross-traffic, clamped — no non-decreasing closure. -/
noncomputable def pmooResidual (β₁ β₂ α : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun v => minConvProj β₁ β₂ v - α v

/-- `pmooResidual β₁ β₂ α v` is the clamped difference at `v`. -/
@[simp] theorem pmooResidual_apply (β₁ β₂ α : ℝ≥0 → ℝ≥0) (v : ℝ≥0) :
    pmooResidual β₁ β₂ α v = minConvProj β₁ β₂ v - α v := rfl

/-- `pmooResidual β₁ β₂ α 0 = 0` for `β₁, β₂` null at the origin. -/
theorem pmooResidual_zero_eq {β₁ β₂ : ℝ≥0 → ℝ≥0} (α : ℝ≥0 → ℝ≥0)
    (hβ₁ : β₁ 0 = 0) (hβ₂ : β₂ 0 = 0) :
    pmooResidual β₁ β₂ α 0 = 0 := by
  rw [pmooResidual_apply, minConvProj_zero_eq, hβ₁, hβ₂, add_zero,
    zero_tsub]

/-- The PMOO residual stays below the tandem convolution. -/
theorem pmooResidual_le_minConvProj (β₁ β₂ α : ℝ≥0 → ℝ≥0) (v : ℝ≥0) :
    pmooResidual β₁ β₂ α v ≤ minConvProj β₁ β₂ v :=
  tsub_le_self

/-- **Pay multiplexing only once, anchored form**: across a tandem of
two strict servers, the tagged flow gains the PMOO residual from the
cascaded start `u = Start₁(Start₂(t))` — the second server's strict
bound runs from `s = Start₂(t)`, the first server's from `u`, every
flow is fully served at both starts, and each cross flow pays its
arrival curve once, over `(u, t]`. -/
theorem add_pmooResidual_le_of_strict_tandem {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    {As Bs Ds : ι → Curve} {β₁ β₂ : ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0}
    (hc₁ : ∀ j, Bs j ≤ As j) (hc₂ : ∀ j, Ds j ≤ Bs j)
    (hstrict₁ : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Bs j) x)
        (Set.Ioc s t) →
      (∑ j, (Bs j) s) + β₁ (t - s) ≤ ∑ j, (Bs j) t)
    (hstrict₂ : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (Bs j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β₂ (t - s) ≤ ∑ j, (Ds j) t)
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(As j) (α j))
    (t : ℝ≥0) :
    (As i) (start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Bs j) x)
        (start (fun x => ∑ j, (Bs j) x) (fun x => ∑ j, (Ds j) x) t))
      + pmooResidual β₁ β₂
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v)
          (t - start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Bs j) x)
            (start (fun x => ∑ j, (Bs j) x)
              (fun x => ∑ j, (Ds j) x) t))
      ≤ (Ds i) t := by
  set s := start (fun x => ∑ j, (Bs j) x) (fun x => ∑ j, (Ds j) x) t
    with hsdef
  set u := start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Bs j) x) s
    with hudef
  have hst : s ≤ t := start_le _ _ t
  have hus : u ≤ s := start_le _ _ s
  have hut : u ≤ t := hus.trans hst
  have h2 := hstrict₂ s t hst (isBacklogged_Ioc_start
    (fun x => Finset.sum_le_sum fun j _ => hc₂ j x) t)
  have h1 := hstrict₁ u s hus (isBacklogged_Ioc_start
    (fun x => Finset.sum_le_sum fun j _ => hc₁ j x) s)
  -- every flow is fully served at both starts
  have heq2 : ∀ j, (Ds j) s = (Bs j) s := Curve.apply_start_sum_eq hc₂ t
  have heq1 : ∀ j, (Bs j) u = (As j) u := Curve.apply_start_sum_eq hc₁ s
  have hE2 : (∑ j, (Ds j) s) = ∑ j, (Bs j) s :=
    Finset.sum_congr rfl fun j _ => heq2 j
  have hE1 : (∑ j, (Bs j) u) = ∑ j, (As j) u :=
    Finset.sum_congr rfl fun j _ => heq1 j
  -- the cross-traffic through the tandem, paid once over `(u, t]`
  have hcross : (∑ j ∈ Finset.univ.erase i, (Ds j) t)
      ≤ (∑ j ∈ Finset.univ.erase i, (As j) u)
        + ∑ j ∈ Finset.univ.erase i, α j (t - u) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    have harr' : (As j) t ≤ (As j) u + α j (t - u) := by
      have h := (isMaximalArrivalBound_iff_increment _ _).mp
        (harr j (Finset.ne_of_mem_erase hj)) u (t - u)
      rwa [add_tsub_cancel_of_le hut] at h
    exact le_trans (le_trans (hc₂ j t) (hc₁ j t)) harr'
  -- the convolution split across the two windows
  have hconv : minConvProj β₁ β₂ (t - u) ≤ β₁ (s - u) + β₂ (t - s) :=
    minConvProj_le_add (by
      rw [add_comm]
      exact tsub_add_tsub_cancel hst hus)
  -- the totals split over the tagged flow and the rest
  have hSDt : (∑ j, (Ds j) t)
      = (Ds i) t + ∑ j ∈ Finset.univ.erase i, (Ds j) t :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hSAu : (∑ j, (As j) u)
      = (As i) u + ∑ j ∈ Finset.univ.erase i, (As j) u :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  -- the anchor floor, independent of the chain
  have hfloor : (As i) u ≤ (Ds i) t :=
    calc (As i) u = (Bs i) u := (heq1 i).symm
      _ ≤ (Bs i) s := (Bs i).mono hus
      _ = (Ds i) s := (heq2 i).symm
      _ ≤ (Ds i) t := (Ds i).mono hst
  rw [pmooResidual_apply]
  rcases le_or_gt (∑ j ∈ Finset.univ.erase i, α j (t - u))
      (minConvProj β₁ β₂ (t - u)) with hcase | hcase
  · -- below the clamp: the linear chain over `ℝ`
    rw [← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hcase]
    have h2R := NNReal.coe_le_coe.mpr h2
    have h1R := NNReal.coe_le_coe.mpr h1
    have hE2R := congrArg NNReal.toReal hE2
    have hE1R := congrArg NNReal.toReal hE1
    have hcrossR := NNReal.coe_le_coe.mpr hcross
    have hconvR := NNReal.coe_le_coe.mpr hconv
    have hSDtR := congrArg NNReal.toReal hSDt
    have hSAuR := congrArg NNReal.toReal hSAu
    push_cast at h2R h1R hE2R hE1R hcrossR hconvR hSDtR hSAuR
    linarith
  · -- past the clamp: the residual vanishes and the floor remains
    rw [tsub_eq_zero_of_le hcase.le, add_zero]
    exact hfloor

/-- **Pay multiplexing only once**: across a tandem of two strict
servers under blind multiplexing, the tagged flow is min-plus served
at `(β₁ ∗ β₂ − ∑_{j≠i} αⱼ)⁺` — the cross-traffic burst is paid once,
where the per-server modular composition pays it at each hop. -/
theorem minConv_pmooResidual_le_of_strict_tandem {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {As Bs Ds : ι → Curve} {β₁ β₂ : ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0}
    (hc₁ : ∀ j, Bs j ≤ As j) (hc₂ : ∀ j, Ds j ≤ Bs j)
    (hstrict₁ : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Bs j) x)
        (Set.Ioc s t) →
      (∑ j, (Bs j) s) + β₁ (t - s) ≤ ∑ j, (Bs j) t)
    (hstrict₂ : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (Bs j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β₂ (t - s) ≤ ∑ j, (Ds j) t)
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(As j) (α j))
    (t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As i))
        (Deviation.liftENN (pmooResidual β₁ β₂
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v))) t
      ≤ ((Ds i) t : ℝ≥0∞) := by
  have hkey := add_pmooResidual_le_of_strict_tandem hc₁ hc₂
    hstrict₁ hstrict₂ harr t
  have hut : start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Bs j) x)
      (start (fun x => ∑ j, (Bs j) x) (fun x => ∑ j, (Ds j) x) t)
      ≤ t :=
    le_trans (start_le _ _ _) (start_le _ _ t)
  refine le_trans (minConv_le_add _ _ (add_tsub_cancel_of_le hut)) ?_
  exact_mod_cast hkey

/-- Relation form: composing two `n`-servers with strict aggregate
curves into a tandem and constraining the cross-traffic arrivals,
the residual server of the tagged flow offers the PMOO residual as a
min-plus service curve. -/
theorem isMinimalServiceCurve_pmooResidual_of_strict_tandem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S₁ S₂ : (ι → Curve) → (ι → Curve) → Prop} {β₁ β₂ : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus₁ : IsCausalN S₁) (hcaus₂ : IsCausalN S₂)
    (hβ₁ : IsStrictMinimalServiceCurve β₁ (aggregateServer S₁))
    (hβ₂ : IsStrictMinimalServiceCurve β₂ (aggregateServer S₂)) :
    IsMinimalServiceCurve
      (liftEReal (pmooResidual β₁ β₂
        (fun v => ∑ j ∈ Finset.univ.erase i, α j v)))
      (residualServer (fun A D =>
        (∃ B, S₁ A B ∧ S₂ B D)
          ∧ ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(A j) (α j)) i) := by
  rintro Ai Di ⟨As, Ds, ⟨⟨Bs, hp₁, hp₂⟩, harr⟩, rfl, rfl⟩ t
  have h := minConv_pmooResidual_le_of_strict_tandem
    (fun j => hcaus₁ As Bs hp₁ j) (fun j => hcaus₂ Bs Ds hp₂ j)
    (hβ₁.sum_strict hp₁) (hβ₂.sum_strict hp₂) harr t
  rw [show Deviation.liftENN (pmooResidual β₁ β₂
        (fun v => ∑ j ∈ Finset.univ.erase i, α j v))
      = Deviation.toENN (liftEReal (pmooResidual β₁ β₂
        (fun v => ∑ j ∈ Finset.univ.erase i, α j v)))
    from (Deviation.toENN_liftEReal _).symm] at h
  rw [curveEReal_apply]
  exact (Deviation.minConv_toENN_le_coe_iff (As i)
    (isNonneg_liftEReal _) ((Ds i) t) t).mp h

/-! ## Book restatement (the pay-multiplexing-only-once phenomenon)
Two flows crossing two strict servers in tandem under blind
multiplexing: direct computation over the trajectories gives flow
`2` the min-plus service curve `β̃₂ = (β⁽¹⁾ ∗ β⁽²⁾ − α₁)⁺` — the
multiplexing with flow `1` appears once, while composing the
per-server residuals pays the burst of flow `1` at each server. The
book notes this cannot be reached by concatenating and then taking
the residual, since the concatenation curve is not strict —
formalized here for `n` flows with the cross-traffic summed. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    {As Bs Ds : ι → Curve} {β₁ β₂ : ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0}
    (hc₁ : ∀ j, Bs j ≤ As j) (hc₂ : ∀ j, Ds j ≤ Bs j)
    (hstrict₁ : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Bs j) x)
        (Set.Ioc s t) →
      (∑ j, (Bs j) s) + β₁ (t - s) ≤ ∑ j, (Bs j) t)
    (hstrict₂ : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (Bs j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β₂ (t - s) ≤ ∑ j, (Ds j) t)
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalCurve ⇑(As j) (α j))
    (t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(As i))
        (Deviation.liftENN (pmooResidual β₁ β₂
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v))) t
      ≤ ((Ds i) t : ℝ≥0∞) :=
  minConv_pmooResidual_le_of_strict_tandem hc₁ hc₂ hstrict₁ hstrict₂
    (fun j hj => (harr j hj).2) t

end DeepWiki
