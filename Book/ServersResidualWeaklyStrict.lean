import Book.ServersResidual

/-! # Weakly strict residual from a weakly strict aggregate
The two-flow composition theorem of the hierarchy chapter,
generalized to `n` flows: under arbitrary multiplexing with a weakly
strict aggregate `β` and arrival curves on every flow, flow `i` is
offered the *weakly strict* residual
`[[β − ∑_{j≠i} αⱼ]⁺↑ ⊘̄ αᵢ]⁺↑` (`residualCurveDeconv`) — the
deconvolution pays flow `i`'s own arrivals across the gap between its
start and the aggregate's. The book notes the curve is not tight and
not used in practice. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The deconvolved residual `[[β − αc]⁺↑ ⊘̄ αi]⁺↑`: the residual of
the cross-traffic `αc`, deconvolved by the own-arrival curve `αi`,
then closed non-decreasingly. -/
noncomputable def residualCurveDeconv (β αc αi : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  ndClosure (maxDeconv (residualCurve β αc) αi)

/-- `residualCurveDeconv β αc αi t` is the supremum of the deconvolved
residuals up to `t`. -/
theorem residualCurveDeconv_apply (β αc αi : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    residualCurveDeconv β αc αi t
      = ⨆ v : {v : ℝ≥0 // v ≤ t},
          maxDeconv (residualCurve β αc) αi v.1 := rfl

/-- `residualCurveDeconv β αc αi 0` is the deconvolution at the
origin. -/
theorem residualCurveDeconv_zero_eq (β αc αi : ℝ≥0 → ℝ≥0) :
    residualCurveDeconv β αc αi 0
      = maxDeconv (residualCurve β αc) αi 0 := by
  refine le_antisymm (ciSup_le fun v => ?_) ?_
  · show maxDeconv (residualCurve β αc) αi v.1
        ≤ maxDeconv (residualCurve β αc) αi 0
    rw [show v.1 = 0 from le_antisymm v.2 zero_le']
  · refine le_ciSup_of_le
      ⟨maxDeconv (residualCurve β αc) αi 0, ?_⟩ ⟨0, le_rfl⟩ le_rfl
    rintro y ⟨v, rfl⟩
    show maxDeconv (residualCurve β αc) αi v.1
        ≤ maxDeconv (residualCurve β αc) αi 0
    rw [show v.1 = 0 from le_antisymm v.2 zero_le']

/-- Intro: each deconvolved residual below `t` bounds
`residualCurveDeconv β αc αi t` from below (under
prefix-boundedness). -/
theorem maxDeconv_le_residualCurveDeconv {β αc αi : ℝ≥0 → ℝ≥0}
    (hbdd : ClosureBddAbove (maxDeconv (residualCurve β αc) αi))
    {v t : ℝ≥0} (hvt : v ≤ t) :
    maxDeconv (residualCurve β αc) αi v
      ≤ residualCurveDeconv β αc αi t :=
  le_ciSup_of_le (hbdd t) ⟨v, hvt⟩ le_rfl

/-- Elim: `residualCurveDeconv β αc αi t ≤ x` from the pointwise
deconvolution bounds on `[0, t]`. -/
theorem residualCurveDeconv_le {β αc αi : ℝ≥0 → ℝ≥0} {x t : ℝ≥0}
    (h : ∀ v, v ≤ t → maxDeconv (residualCurve β αc) αi v ≤ x) :
    residualCurveDeconv β αc αi t ≤ x :=
  ciSup_le fun v => h v.1 v.2

/-- `residualCurveDeconv β αc αi` is monotone (under
prefix-boundedness). -/
theorem residualCurveDeconv_mono {β αc αi : ℝ≥0 → ℝ≥0}
    (hbdd : ClosureBddAbove (maxDeconv (residualCurve β αc) αi)) :
    Monotone (residualCurveDeconv β αc αi) :=
  ndClosure_mono _ hbdd

/-- For non-decreasing `β` the deconvolved residuals are
prefix-bounded: the `s = 0` term of each deconvolution is dominated
by the residual, which `β t` dominates. -/
theorem closureBddAbove_maxDeconv_of_monotone {β αc αi : ℝ≥0 → ℝ≥0}
    (hβ : Monotone β) :
    ClosureBddAbove (maxDeconv (residualCurve β αc) αi) := fun t =>
  ⟨β t, by
    rintro y ⟨v, rfl⟩
    refine le_trans (maxDeconv_le_sub _ _ v.1 0) ?_
    refine le_trans tsub_le_self ?_
    rw [add_zero]
    exact residualCurve_le fun w hw =>
      le_trans tsub_le_self (hβ (hw.trans v.2))⟩

/-- `residualCurveDeconv β αc αi` is monotone for non-decreasing
`β`. -/
theorem residualCurveDeconv_mono_of_monotone {β αc αi : ℝ≥0 → ℝ≥0}
    (hβ : Monotone β) : Monotone (residualCurveDeconv β αc αi) :=
  residualCurveDeconv_mono (closureBddAbove_maxDeconv_of_monotone hβ)

/-- **Weakly strict residual service**: under a weakly strict
aggregate with every flow arrival-constrained, flow `i` gains the
deconvolved residual from its own start — the aggregate start sits
earlier, the residual accrues from there, and the deconvolution pays
flow `i`'s arrivals across the gap. -/
theorem add_residualCurveDeconv_le_of_wstrict_aggregate {ι : Type*}
    [Fintype ι]
    {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hws : ∀ w, (∑ j, (Ds j)
        (start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x) w))
      + β (w - start (fun x => ∑ j, (As j) x)
          (fun x => ∑ j, (Ds j) x) w)
      ≤ ∑ j, (Ds j) w)
    {i : ι} (harr : ∀ j, IsMaximalArrivalBound ⇑(As j) (α j))
    (t : ℝ≥0) :
    (Ds i) (start ⇑(As i) ⇑(Ds i) t)
      + residualCurveDeconv β
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v) (α i)
          (t - start ⇑(As i) ⇑(Ds i) t)
      ≤ (Ds i) t := by
  have hs1t : start ⇑(As i) ⇑(Ds i) t ≤ t := start_le _ _ t
  have h0agg : (∑ j, (As j) 0) = ∑ j, (Ds j) 0 :=
    (Curve.sum_zero_eq As).trans (Curve.sum_zero_eq Ds).symm
  -- the aggregate start sits at or before flow `i`'s
  have hagg_le : start (fun x => ∑ j, (As j) x)
      (fun x => ∑ j, (Ds j) x) t ≤ start ⇑(As i) ⇑(Ds i) t :=
    start_le_of_isBacklogged
      (isBacklogged_sum_of_isBacklogged (fun j _ x => hc j x)
        (Finset.mem_univ i) (isBacklogged_Ioc_start (hc i) t))
  -- per-flow equality at the aggregate start
  have hfloweq : ∀ j, (Ds j) (start (fun x => ∑ j, (As j) x)
      (fun x => ∑ j, (Ds j) x) t) = (As j)
      (start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x) t) :=
    Curve.apply_start_sum_eq hc t
  -- flow `i`'s arrivals across the gap
  have hgap : (As i) (start ⇑(As i) ⇑(Ds i) t)
      ≤ (Ds i) (start (fun x => ∑ j, (As j) x)
          (fun x => ∑ j, (Ds j) x) t)
        + α i (start ⇑(As i) ⇑(Ds i) t
            - start (fun x => ∑ j, (As j) x)
              (fun x => ∑ j, (Ds j) x) t) := by
    have hinc := (isMaximalArrivalBound_iff_increment _ _).mp (harr i)
      (start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x) t)
      (start ⇑(As i) ⇑(Ds i) t
        - start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x) t)
    rw [add_tsub_cancel_of_le hagg_le] at hinc
    rw [hfloweq i]
    exact hinc
  -- every closure term is covered
  have hv : ∀ w : ℝ≥0, w ≤ t - start ⇑(As i) ⇑(Ds i) t →
      maxDeconv (residualCurve β
        (fun v => ∑ j ∈ Finset.univ.erase i, α j v)) (α i) w
      ≤ (Ds i) t - (Ds i) (start ⇑(As i) ⇑(Ds i) t) := by
    intro w hw
    have hvt : start ⇑(As i) ⇑(Ds i) t + w ≤ t := by
      have h1 : start ⇑(As i) ⇑(Ds i) t + w
          ≤ start ⇑(As i) ⇑(Ds i) t + (t - start ⇑(As i) ⇑(Ds i) t) :=
        add_le_add le_rfl hw
      rwa [add_tsub_cancel_of_le hs1t] at h1
    -- the aggregate start is constant up to `t`
    have hconst : start (fun x => ∑ j, (As j) x)
        (fun x => ∑ j, (Ds j) x) (start ⇑(As i) ⇑(Ds i) t + w)
        = start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x) t :=
      start_eq_start_of_le h0agg (hagg_le.trans le_self_add) hvt
    have hres := add_residualCurve_start_le_of_wstrict_aggregate
      (i := i) hc hws (fun j _ => harr j)
      (start ⇑(As i) ⇑(Ds i) t + w)
    rw [hconst] at hres
    -- the deconvolution term at the gap
    have hdec := maxDeconv_le_sub
      (residualCurve β (fun v => ∑ j ∈ Finset.univ.erase i, α j v))
      (α i) w
      (start ⇑(As i) ⇑(Ds i) t
        - start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x) t)
    rw [show w + (start ⇑(As i) ⇑(Ds i) t
        - start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x) t)
        = (start ⇑(As i) ⇑(Ds i) t + w)
          - start (fun x => ∑ j, (As j) x)
            (fun x => ∑ j, (Ds j) x) t from by
      rw [add_comm, tsub_add_eq_add_tsub hagg_le]] at hdec
    refine le_trans hdec ?_
    -- (X − a) ≤ D_i t − D_i s₁ from the chain, in ℝ
    rw [tsub_le_iff_left]
    have hD1A : (Ds i) (start ⇑(As i) ⇑(Ds i) t)
        ≤ (As i) (start ⇑(As i) ⇑(Ds i) t) :=
      hc i _
    have hmono1 : (Ds i) (start ⇑(As i) ⇑(Ds i) t) ≤ (Ds i) t :=
      (Ds i).mono hs1t
    have hmonovt : (Ds i) (start ⇑(As i) ⇑(Ds i) t + w) ≤ (Ds i) t :=
      (Ds i).mono hvt
    rw [← NNReal.coe_le_coe, NNReal.coe_add, NNReal.coe_sub hmono1]
    have hresR := NNReal.coe_le_coe.mpr hres
    have hgapR := NNReal.coe_le_coe.mpr (hD1A.trans hgap)
    have hmonoR := NNReal.coe_le_coe.mpr hmonovt
    push_cast at hresR hgapR hmonoR
    linarith
  -- collect the closure
  have hsup : residualCurveDeconv β
      (fun v => ∑ j ∈ Finset.univ.erase i, α j v) (α i)
      (t - start ⇑(As i) ⇑(Ds i) t)
      ≤ (Ds i) t - (Ds i) (start ⇑(As i) ⇑(Ds i) t) := by
    exact residualCurveDeconv_le hv
  calc (Ds i) (start ⇑(As i) ⇑(Ds i) t)
      + residualCurveDeconv β _ (α i) (t - start ⇑(As i) ⇑(Ds i) t)
      ≤ (Ds i) (start ⇑(As i) ⇑(Ds i) t)
        + ((Ds i) t - (Ds i) (start ⇑(As i) ⇑(Ds i) t)) :=
        add_le_add le_rfl hsup
    _ = (Ds i) t := add_tsub_cancel_of_le ((Ds i).mono hs1t)

/-- Relation form: an `n`-server with a weakly strict aggregate curve
and every flow arrival-constrained offers flow `i` the deconvolved
residual as a *weakly strict* service curve on the residual server. -/
theorem isWeaklyStrictMinimalServiceCurve_residualServer_of_wstrict
    {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S)
    (hβ : IsWeaklyStrictMinimalServiceCurve β (aggregateServer S)) :
    IsWeaklyStrictMinimalServiceCurve
      (residualCurveDeconv β
        (fun v => ∑ j ∈ Finset.univ.erase i, α j v) (α i))
      (residualServer (fun A D => S A D ∧
        ∀ j, IsMaximalArrivalBound ⇑(A j) (α j)) i) := by
  rintro Ai Di ⟨As, Ds, ⟨hp, harr⟩, rfl, rfl⟩ t
  exact add_residualCurveDeconv_le_of_wstrict_aggregate
    (fun j => hcaus As Ds hp j) (hβ.sum_wstrict hp) harr t

/-! ## Book restatement (the two-flow weakly strict composition)
A two-server offering a weakly strict service curve `β`, with two
flows of respective arrival curves `α₁, α₂`, under arbitrary
multiplexing, offers flow `1` the weakly strict service curve
`β₁ = [[β − α₂]⁺↑ ⊘̄ α₁]⁺↑` — formalized here for `n` flows with the
cross-traffic summed, the book's statement being the case `n = 2`.
The curve is not tight and, the book notes, not used in practice.
First pair-level with the arrival-curve bundles
`IsMaximalArrivalCurve` (monotonicity passed down as `.2`), then in
relation form. -/
example {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0}
    (hSrv : IsServerN S)
    (hβ : IsWeaklyStrictMinimalServiceCurve β (aggregateServer S))
    {As Ds : ι → Curve} (hp : S As Ds)
    {i : ι} (harr : ∀ j, IsMaximalArrivalCurve ⇑(As j) (α j))
    (t : ℝ≥0) :
    (Ds i) (start ⇑(As i) ⇑(Ds i) t)
      + residualCurveDeconv β
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v) (α i)
          (t - start ⇑(As i) ⇑(Ds i) t)
      ≤ (Ds i) t :=
  add_residualCurveDeconv_le_of_wstrict_aggregate
    (fun j => hSrv.1 As Ds hp j) (hβ.sum_wstrict hp)
    (fun j => (harr j).2) t
example {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0} {i : ι}
    (hSrv : IsServerN S)
    (hβ : IsWeaklyStrictMinimalServiceCurve β (aggregateServer S)) :
    IsWeaklyStrictMinimalServiceCurve
      (residualCurveDeconv β
        (fun v => ∑ j ∈ Finset.univ.erase i, α j v) (α i))
      (residualServer (fun A D => S A D ∧
        ∀ j, IsMaximalArrivalBound ⇑(A j) (α j)) i) :=
  isWeaklyStrictMinimalServiceCurve_residualServer_of_wstrict
    hSrv.1 hβ

end DeepWiki
