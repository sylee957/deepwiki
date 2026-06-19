import DeepWiki.NetworkCalculus.ServersResidual

/-! # Deficit-round-robin residual service
DRR serves flows in rounds: each round adds the flow's quantum `Qᵢ` to
its deficit counter and serves head packets while the counter covers
them, so the counter stays below the flow's maximal packet size. On a
backlogged period the round count couples a service guarantee for the
flow with a service bound for every other flow, and a strict aggregate
curve turns the coupling into the strict residual
`[Qᵢ/F·β − (Qᵢ(L−ℓᵢᵘ) + (F−Qᵢ)(Qᵢ+ℓᵢᵘ))/F]⁺` (`drrResidual`). The
book's sharpening for packet lengths and quanta that are multiples of
a basic unit `ε` is the same theorem at `ℓⱼᵘ − ε`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **Deficit round robin**: on each backlogged period of flow `i`
there is a round count `p` — the complete service rounds dedicated to
flow `i` within it — granting flow `i` at least `p·Qᵢ − ℓᵢᵘ` (its
quanta minus the leftover deficit) while every other flow takes at
most `(p+1)·Qⱼ + ℓⱼᵘ` (one extra round, the deficit overshoot counted
once). -/
def IsDrr {ι : Type*} (Q lmax : ι → ℝ≥0) (A D : ι → ℝ≥0 → ℝ≥0) :
    Prop :=
  ∀ i : ι, ∀ s t : ℝ≥0, s ≤ t →
    IsBacklogged (A i) (D i) (Set.Ioc s t) →
    ∃ p : ℕ,
      (D i s + (p : ℝ≥0) * Q i ≤ D i t + lmax i)
      ∧ ∀ j, j ≠ i →
        D j t ≤ D j s + (((p : ℝ≥0) + 1) * Q j + lmax j)

/-- **DRR `n`-server**: every served family obeys the round-count
coupling. -/
def IsDrrServerN {ι : Type*} (Q lmax : ι → ℝ≥0)
    (S : (ι → Curve) → (ι → Curve) → Prop) : Prop :=
  ∀ As Ds, S As Ds →
    IsDrr Q lmax (fun j => ⇑(As j)) (fun j => ⇑(Ds j))

/-- `(∑ j, f j) − f i` is the exact erased sum: summands make the
truncated difference honest. -/
theorem sum_tsub_eq_sum_erase {ι : Type*} [Fintype ι]
    (f : ι → ℝ≥0) (i : ι) :
    (∑ j, f j) - f i = ∑ j ∈ Finset.univ.erase i, f j := by
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)]
  exact tsub_eq_of_eq_add (by rw [add_comm])

/-- The DRR residual curve: flow `i`'s quantum share of `β`, minus the
round-robin price of the other flows' rounds and its own leftover
deficit. -/
noncomputable def drrResidual {ι : Type*} [Fintype ι]
    (Q lmax : ι → ℝ≥0) (i : ι) (β : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun τ => (Q i / ∑ j, Q j) * β τ
    - (Q i * ((∑ j, lmax j) - lmax i)
      + ((∑ j, Q j) - Q i) * (Q i + lmax i)) / ∑ j, Q j

/-- `drrResidual Q lmax i β τ` unfolds to its closed form. -/
@[simp] theorem drrResidual_apply {ι : Type*} [Fintype ι]
    (Q lmax : ι → ℝ≥0) (i : ι) (β : ℝ≥0 → ℝ≥0) (τ : ℝ≥0) :
    drrResidual Q lmax i β τ
      = (Q i / ∑ j, Q j) * β τ
        - (Q i * ((∑ j, lmax j) - lmax i)
          + ((∑ j, Q j) - Q i) * (Q i + lmax i)) / ∑ j, Q j := rfl

/-- `drrResidual Q lmax i β 0 = 0` when `β 0 = 0`. -/
theorem drrResidual_zero_eq {ι : Type*} [Fintype ι]
    {Q lmax : ι → ℝ≥0} {i : ι} {β : ℝ≥0 → ℝ≥0} (hβ0 : β 0 = 0) :
    drrResidual Q lmax i β 0 = 0 := by
  rw [drrResidual_apply, hβ0, mul_zero, zero_tsub]

/-- **DRR residual service**: under DRR with a strict aggregate `β`,
flow `i` obeys the strict service inequality for
`[Qᵢ/F·β − (Qᵢ(L−ℓᵢᵘ) + (F−Qᵢ)(Qᵢ+ℓᵢᵘ))/F]⁺` on its backlogged
periods, with `F = ∑ Qⱼ` and `L = ∑ ℓⱼᵘ` — no arrival curves are
needed. -/
theorem add_drrResidual_le_of_isDrr {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0} {Q lmax : ι → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    (hdrr : IsDrr Q lmax (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    {i : ι} {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t)) :
    (Ds i) s + drrResidual Q lmax i β (t - s) ≤ (Ds i) t := by
  rw [drrResidual_apply]
  obtain ⟨p, hown, hcross⟩ := hdrr i s t hst hbl
  have hstr := hstrict s t hst
    (isBacklogged_sum_of_isBacklogged (fun j _ x => hc j x)
      (Finset.mem_univ i) hbl)
  -- decompose the aggregate over `{i}` and the rest
  rw [← Finset.add_sum_erase Finset.univ (fun j => (Ds j) s)
      (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ (fun j => (Ds j) t)
      (Finset.mem_univ i)] at hstr
  -- the constants are exact truncated differences
  have hQle : Q i ≤ ∑ j, Q j :=
    Finset.single_le_sum (fun j _ => zero_le) (Finset.mem_univ i)
  have hlle : lmax i ≤ ∑ j, lmax j :=
    Finset.single_le_sum (fun j _ => zero_le) (Finset.mem_univ i)
  have hQerase := sum_tsub_eq_sum_erase Q i
  have hlerase := sum_tsub_eq_sum_erase lmax i
  rcases eq_zero_or_pos (∑ j, Q j) with hF | hF
  · -- no quanta at all: the residual is `0 − …`
    rw [hF, div_zero, zero_mul, zero_tsub, add_zero]
    exact (Ds i).mono hst
  -- the three coupled facts, in `ℝ`
  have hownR : ((Ds i) s : ℝ) + (p : ℝ) * ((Q i : ℝ≥0) : ℝ)
      ≤ ((Ds i) t : ℝ) + ((lmax i : ℝ≥0) : ℝ) := by
    exact_mod_cast hown
  have hcrossR :
      ((∑ j ∈ Finset.univ.erase i, (Ds j) t : ℝ≥0) : ℝ)
        ≤ ((∑ j ∈ Finset.univ.erase i, (Ds j) s : ℝ≥0) : ℝ)
          + (((p : ℝ) + 1)
              * ((∑ j ∈ Finset.univ.erase i, Q j : ℝ≥0) : ℝ)
            + ((∑ j ∈ Finset.univ.erase i, lmax j : ℝ≥0) : ℝ)) := by
    have h : (∑ j ∈ Finset.univ.erase i, (Ds j) t)
        ≤ ∑ j ∈ Finset.univ.erase i,
            ((Ds j) s + (((p : ℝ≥0) + 1) * Q j + lmax j)) :=
      Finset.sum_le_sum fun j hj =>
        hcross j (Finset.ne_of_mem_erase hj)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum] at h
    exact_mod_cast h
  have hstrR : (((Ds i) s : ℝ)
        + ((∑ j ∈ Finset.univ.erase i, (Ds j) s : ℝ≥0) : ℝ))
        + ((β (t - s) : ℝ≥0) : ℝ)
      ≤ ((Ds i) t : ℝ)
        + ((∑ j ∈ Finset.univ.erase i, (Ds j) t : ℝ≥0) : ℝ) := by
    exact_mod_cast hstr
  -- eliminate the round count
  have hkeyR : ((Q i : ℝ≥0) : ℝ) * ((β (t - s) : ℝ≥0) : ℝ)
      ≤ (((Q i : ℝ≥0) : ℝ)
          + ((∑ j ∈ Finset.univ.erase i, Q j : ℝ≥0) : ℝ))
          * (((Ds i) t : ℝ) - ((Ds i) s : ℝ))
        + (((Q i : ℝ≥0) : ℝ)
            * ((∑ j ∈ Finset.univ.erase i, lmax j : ℝ≥0) : ℝ)
          + ((∑ j ∈ Finset.univ.erase i, Q j : ℝ≥0) : ℝ)
            * (((Q i : ℝ≥0) : ℝ) + ((lmax i : ℝ≥0) : ℝ))) := by
    have hβbound : ((β (t - s) : ℝ≥0) : ℝ)
        ≤ (((Ds i) t : ℝ) - ((Ds i) s : ℝ))
          + (((p : ℝ) + 1)
              * ((∑ j ∈ Finset.univ.erase i, Q j : ℝ≥0) : ℝ)
            + ((∑ j ∈ Finset.univ.erase i, lmax j : ℝ≥0) : ℝ)) := by
      linarith
    have hm1 := mul_le_mul_of_nonneg_left hβbound (Q i).coe_nonneg
    have hm2 := mul_le_mul_of_nonneg_left
      (show (p : ℝ) * ((Q i : ℝ≥0) : ℝ)
          ≤ (((Ds i) t : ℝ) - ((Ds i) s : ℝ)) + ((lmax i : ℝ≥0) : ℝ)
        from by linarith)
      (∑ j ∈ Finset.univ.erase i, Q j : ℝ≥0).coe_nonneg
    ring_nf at hm1 hm2 ⊢
    linarith
  -- rewrite the truncated constants as the exact erased sums
  rw [hQerase, hlerase]
  rcases le_total ((Q i / ∑ j, Q j) * β (t - s))
      ((Q i * ∑ j ∈ Finset.univ.erase i, lmax j
        + (∑ j ∈ Finset.univ.erase i, Q j) * (Q i + lmax i))
        / ∑ j, Q j) with hd | hd
  · -- the residual vanishes
    rw [tsub_eq_zero_of_le hd, add_zero]
    exact (Ds i).mono hst
  · -- clear the division through `F > 0`
    have hFpos : (0 : ℝ) < ((∑ j, Q j : ℝ≥0) : ℝ) := by
      exact_mod_cast hF
    have hFsplitR : ((∑ j, Q j : ℝ≥0) : ℝ)
        = ((Q i : ℝ≥0) : ℝ)
          + ((∑ j ∈ Finset.univ.erase i, Q j : ℝ≥0) : ℝ) := by
      rw [← NNReal.coe_add]
      exact congrArg _ (Finset.add_sum_erase Finset.univ Q
        (Finset.mem_univ i)).symm
    rw [← NNReal.coe_le_coe, NNReal.coe_add, NNReal.coe_sub hd]
    push_cast at hkeyR hFpos hFsplitR ⊢
    rw [div_mul_eq_mul_div, div_sub_div_same]
    have hfinal : (((Q i : ℝ) * (β (t - s) : ℝ))
          - ((Q i : ℝ) * ∑ j ∈ Finset.univ.erase i, ((lmax j : ℝ))
            + (∑ j ∈ Finset.univ.erase i, ((Q j : ℝ)))
              * ((Q i : ℝ) + (lmax i : ℝ))))
          / ∑ j, ((Q j : ℝ))
        ≤ ((Ds i) t : ℝ) - ((Ds i) s : ℝ) := by
      rw [div_le_iff₀ hFpos, hFsplitR]
      ring_nf
      ring_nf at hkeyR
      linarith
    linarith

/-- Relation form: a DRR `n`-server with a strict aggregate curve
offers each flow the quantum-proportional strict residual on the
residual server, without arrival-curve hypotheses. -/
theorem isStrictMinimalServiceCurve_drrResidual_of_isDrr
    {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {Q lmax : ι → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hdrr : IsDrrServerN Q lmax S) :
    IsStrictMinimalServiceCurve (drrResidual Q lmax i β)
      (residualServer S i) := by
  rintro Ai Di ⟨As, Ds, hp, rfl, rfl⟩ s t hst hbl
  exact add_drrResidual_le_of_isDrr (fun j => hcaus As Ds hp j)
    (hβ.sum_strict hp) (hdrr As Ds hp) hst hbl

/-! ## Book restatement (DRR residual service)
An `n`-server offering a strict service curve `β` under DRR, with
maximum packet sizes `ℓᵢᵘ` and quanta `Qᵢ`: flow `i` is guaranteed the
strict service curve
`βᵢ = [Qᵢ/F·β − (Qᵢ(L−ℓᵢᵘ) + (F−Qᵢ)(Qᵢ+ℓᵢᵘ))/F]⁺` with `F = ∑ Qⱼ`
and `L = ∑ ℓⱼᵘ`. (The book derives the round-count coupling from the
deficit-counter algorithm; it is taken here as the DRR trajectory
definition.) -/
example {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {Q lmax : ι → ℝ≥0} {i : ι}
    (hSrv : IsServerN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hdrr : IsDrrServerN Q lmax S) :
    IsStrictMinimalServiceCurve (drrResidual Q lmax i β)
      (residualServer S i) :=
  isStrictMinimalServiceCurve_drrResidual_of_isDrr
    hSrv.1 hβ hdrr

/-! ## Book restatement (the basic-unit refinement)
When packet lengths and quanta are all multiples of a basic unit `ε`,
the deficit counters stay within `ℓᵢᵘ − ε`, so the round-count
coupling holds with every `ℓⱼᵘ` replaced by `ℓⱼᵘ − ε` — and the same
theorem instantiates at the sharpened residual. -/
example {ι : Type*} [Fintype ι] {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0}
    {Q lmax : ι → ℝ≥0} {ε : ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    (hdrr : IsDrr Q (fun j => lmax j - ε)
      (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    {i : ι} {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t)) :
    (Ds i) s + drrResidual Q (fun j => lmax j - ε) i β (t - s)
      ≤ (Ds i) t :=
  add_drrResidual_le_of_isDrr hc hstrict hdrr hst hbl

end DeepWiki
