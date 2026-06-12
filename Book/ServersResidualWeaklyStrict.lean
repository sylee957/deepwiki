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

/-- `residualCurveDeconv β αc αi t` unfolds to its closure form. -/
theorem residualCurveDeconv_apply (β αc αi : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    residualCurveDeconv β αc αi t
      = ndClosure (maxDeconv (residualCurve β αc) αi) t := rfl

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
  have h0agg : (∑ j, (As j) 0) = ∑ j, (Ds j) 0 := by
    have hA : (∑ j, (As j) 0) = 0 :=
      Finset.sum_eq_zero fun j _ => ((As j).zero : (As j) 0 = 0)
    have hD : (∑ j, (Ds j) 0) = 0 :=
      Finset.sum_eq_zero fun j _ => ((Ds j).zero : (Ds j) 0 = 0)
    rw [hA, hD]
  -- the aggregate start sits at or before flow `i`'s
  have hagg_le : start (fun x => ∑ j, (As j) x)
      (fun x => ∑ j, (Ds j) x) t ≤ start ⇑(As i) ⇑(Ds i) t := by
    unfold start
    refine csSup_le_csSup ⟨t, fun x hx => hx.1⟩
      ⟨0, zero_le', h0agg⟩ ?_
    rintro u ⟨hut, hequ⟩
    refine ⟨hut, ?_⟩
    exact ((Finset.sum_eq_sum_iff_of_le
      (fun j _ => hc j u)).mp hequ.symm i (Finset.mem_univ i)).symm
  -- per-flow equality at the aggregate start
  have hfloweq : ∀ j, (Ds j) (start (fun x => ∑ j, (As j) x)
      (fun x => ∑ j, (Ds j) x) t) = (As j)
      (start (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x) t) :=
    apply_start_sum_eq (fun j x => hc j x)
      (fun j => (As j).leftCont) (fun j => (Ds j).leftCont)
      (fun j => ((As j).zero : (As j) 0 = 0).trans
        ((Ds j).zero : (Ds j) 0 = 0).symm) t
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
    rw [residualCurveDeconv_apply]
    exact ciSup_le fun w => hv w.1 w.2
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
The curve is not tight and, the book notes, not used in practice. -/
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
