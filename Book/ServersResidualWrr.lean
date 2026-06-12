import Book.ServersResidual
import Book.RealCurves

/-! # Weighted-round-robin residual service
WRR serves, per round, up to `wᵢ` packets of each flow in turn. On a
backlogged period the round count couples flow `i`'s guarantee — `wᵢ`
packets of at least `ℓᵢˡ` per complete round — with the other flows'
bound of `wⱼ` packets of at most `ℓⱼᵘ` per round, and a strict
aggregate curve yields the weight-proportional strict residual
`qᵢ/(qᵢ+Qᵢ)·[β − Qᵢ]⁺` with `qᵢ = wᵢℓᵢˡ` and `Qᵢ = ∑_{j≠i} wⱼℓⱼᵘ`
(`wrrResidual`), as well as its round-quantized refinement
`(λ₁ ∗ ν) ∘ [β − Qᵢ]⁺` from the same packet-length constants
(`wrrResidualStaircase`), of which the ratio form is the
linearization. The book's sharpest form — the pseudo-inverse
composition through cumulative packet curves — is the remaining
refinement. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **Weighted round robin**: on each backlogged period of flow `i`
there is a round count `p` granting flow `i` at least `p·wᵢ·ℓᵢˡ` (its
packets per complete round at minimal length) while every other flow
takes at most `(p+1)·wⱼ·ℓⱼᵘ`. -/
def IsWrr {ι : Type*} (w : ι → ℕ) (lmin lmax : ι → ℝ≥0)
    (A D : ι → ℝ≥0 → ℝ≥0) : Prop :=
  ∀ i : ι, ∀ s t : ℝ≥0, s ≤ t →
    IsBacklogged (A i) (D i) (Set.Ioc s t) →
    ∃ p : ℕ,
      (D i s + (p : ℝ≥0) * ((w i : ℝ≥0) * lmin i) ≤ D i t)
      ∧ ∀ j, j ≠ i →
        D j t ≤ D j s + ((p : ℝ≥0) + 1) * ((w j : ℝ≥0) * lmax j)

/-- **WRR `n`-server**: every served family obeys the round-count
coupling. -/
def IsWrrServerN {ι : Type*} (w : ι → ℕ) (lmin lmax : ι → ℝ≥0)
    (S : (ι → Curve) → (ι → Curve) → Prop) : Prop :=
  ∀ As Ds, S As Ds →
    IsWrr w lmin lmax (fun j => ⇑(As j)) (fun j => ⇑(Ds j))

/-- The WRR residual curve: flow `i`'s weight share of `β` past the
other flows' per-round price, `qᵢ/(qᵢ+Qᵢ)·[β − Qᵢ]⁺` with
`qᵢ = wᵢℓᵢˡ` and `Qᵢ = ∑_{j≠i} wⱼℓⱼᵘ`. -/
noncomputable def wrrResidual {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (lmin lmax : ι → ℝ≥0) (i : ι) (β : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun τ => ((w i : ℝ≥0) * lmin i
      / ((w i : ℝ≥0) * lmin i
        + ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j))
    * (β τ - ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j)

/-- `wrrResidual w lmin lmax i β τ` unfolds to its closed form. -/
@[simp] theorem wrrResidual_apply {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (lmin lmax : ι → ℝ≥0) (i : ι) (β : ℝ≥0 → ℝ≥0) (τ : ℝ≥0) :
    wrrResidual w lmin lmax i β τ
      = ((w i : ℝ≥0) * lmin i
          / ((w i : ℝ≥0) * lmin i
            + ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j))
        * (β τ - ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j) :=
  rfl

/-- `wrrResidual w lmin lmax i β 0 = 0` when `β 0 = 0`. -/
theorem wrrResidual_zero_eq {ι : Type*} [Fintype ι] {w : ι → ℕ}
    {lmin lmax : ι → ℝ≥0} {i : ι} {β : ℝ≥0 → ℝ≥0} (hβ0 : β 0 = 0) :
    wrrResidual w lmin lmax i β 0 = 0 := by
  rw [wrrResidual_apply, hβ0, zero_tsub, mul_zero]

/-- **WRR residual service**: under WRR with a strict aggregate `β`,
flow `i` obeys the strict service inequality for
`qᵢ/(qᵢ+Qᵢ)·[β − Qᵢ]⁺` on its backlogged periods — no arrival curves
are needed. -/
theorem add_wrrResidual_le_of_isWrr {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0} {w : ι → ℕ}
    {lmin lmax : ι → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    (hwrr : IsWrr w lmin lmax (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    {i : ι} {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t)) :
    (Ds i) s + wrrResidual w lmin lmax i β (t - s) ≤ (Ds i) t := by
  rw [wrrResidual_apply]
  obtain ⟨p, hown, hcross⟩ := hwrr i s t hst hbl
  have hstr := hstrict s t hst
    (isBacklogged_sum_of_isBacklogged (fun j _ x => hc j x)
      (Finset.mem_univ i) hbl)
  rw [← Finset.add_sum_erase Finset.univ (fun j => (Ds j) s)
      (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ (fun j => (Ds j) t)
      (Finset.mem_univ i)] at hstr
  -- the residual vanishes when `β` does not clear the per-round price
  rcases le_total (β (t - s))
      (∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j) with hd | hd
  · rw [tsub_eq_zero_of_le hd, mul_zero, add_zero]
    exact (Ds i).mono hst
  rcases eq_zero_or_pos ((w i : ℝ≥0) * lmin i
      + ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j) with hq | hq
  · -- no weighted lengths at all: junk division
    rw [hq, div_zero, zero_mul, add_zero]
    exact (Ds i).mono hst
  -- the coupled facts, in `ℝ`
  have hownR : ((Ds i) s : ℝ)
      + (p : ℝ) * (((w i : ℝ≥0) * lmin i : ℝ≥0) : ℝ)
      ≤ ((Ds i) t : ℝ) := by
    exact_mod_cast hown
  have hcrossR :
      ((∑ j ∈ Finset.univ.erase i, (Ds j) t : ℝ≥0) : ℝ)
        ≤ ((∑ j ∈ Finset.univ.erase i, (Ds j) s : ℝ≥0) : ℝ)
          + ((p : ℝ) + 1)
            * ((∑ j ∈ Finset.univ.erase i,
                (w j : ℝ≥0) * lmax j : ℝ≥0) : ℝ) := by
    have h : (∑ j ∈ Finset.univ.erase i, (Ds j) t)
        ≤ ∑ j ∈ Finset.univ.erase i,
            ((Ds j) s + ((p : ℝ≥0) + 1) * ((w j : ℝ≥0) * lmax j)) :=
      Finset.sum_le_sum fun j hj =>
        hcross j (Finset.ne_of_mem_erase hj)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    exact_mod_cast h
  have hstrR : (((Ds i) s : ℝ)
        + ((∑ j ∈ Finset.univ.erase i, (Ds j) s : ℝ≥0) : ℝ))
        + ((β (t - s) : ℝ≥0) : ℝ)
      ≤ ((Ds i) t : ℝ)
        + ((∑ j ∈ Finset.univ.erase i, (Ds j) t : ℝ≥0) : ℝ) := by
    exact_mod_cast hstr
  -- eliminate the round count
  have hkeyR : (((w i : ℝ≥0) * lmin i : ℝ≥0) : ℝ)
      * (((β (t - s) : ℝ≥0) : ℝ)
        - ((∑ j ∈ Finset.univ.erase i,
            (w j : ℝ≥0) * lmax j : ℝ≥0) : ℝ))
      ≤ ((((w i : ℝ≥0) * lmin i : ℝ≥0) : ℝ)
          + ((∑ j ∈ Finset.univ.erase i,
              (w j : ℝ≥0) * lmax j : ℝ≥0) : ℝ))
        * (((Ds i) t : ℝ) - ((Ds i) s : ℝ)) := by
    have hβbound : ((β (t - s) : ℝ≥0) : ℝ)
        ≤ (((Ds i) t : ℝ) - ((Ds i) s : ℝ))
          + ((p : ℝ) + 1)
            * ((∑ j ∈ Finset.univ.erase i,
                (w j : ℝ≥0) * lmax j : ℝ≥0) : ℝ) := by
      linarith
    have hm1 := mul_le_mul_of_nonneg_left hβbound
      ((w i : ℝ≥0) * lmin i).coe_nonneg
    have hm2 := mul_le_mul_of_nonneg_left
      (show (p : ℝ) * (((w i : ℝ≥0) * lmin i : ℝ≥0) : ℝ)
          ≤ ((Ds i) t : ℝ) - ((Ds i) s : ℝ) from by linarith)
      (∑ j ∈ Finset.univ.erase i,
        (w j : ℝ≥0) * lmax j : ℝ≥0).coe_nonneg
    ring_nf at hm1 hm2 ⊢
    linarith
  -- clear the division
  have hqR : (0 : ℝ) < (((w i : ℝ≥0) * lmin i : ℝ≥0) : ℝ)
      + ((∑ j ∈ Finset.univ.erase i,
          (w j : ℝ≥0) * lmax j : ℝ≥0) : ℝ) := by
    rw [← NNReal.coe_add]
    exact_mod_cast hq
  rw [← NNReal.coe_le_coe, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_div, NNReal.coe_add, NNReal.coe_sub hd]
  have hfinal : (((w i : ℝ≥0) * lmin i : ℝ≥0) : ℝ)
      / ((((w i : ℝ≥0) * lmin i : ℝ≥0) : ℝ)
        + ((∑ j ∈ Finset.univ.erase i,
            (w j : ℝ≥0) * lmax j : ℝ≥0) : ℝ))
      * (((β (t - s) : ℝ≥0) : ℝ)
        - ((∑ j ∈ Finset.univ.erase i,
            (w j : ℝ≥0) * lmax j : ℝ≥0) : ℝ))
      ≤ ((Ds i) t : ℝ) - ((Ds i) s : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hqR]
    ring_nf
    ring_nf at hkeyR
    linarith
  linarith

/-- Relation form: a WRR `n`-server with a strict aggregate curve
offers each flow the weight-proportional strict residual on the
residual server, without arrival-curve hypotheses. -/
theorem isStrictMinimalServiceCurve_residualServer_of_isWrr
    {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {w : ι → ℕ} {lmin lmax : ι → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hwrr : IsWrrServerN w lmin lmax S) :
    IsStrictMinimalServiceCurve (wrrResidual w lmin lmax i β)
      (residualServer S i) := by
  rintro Ai Di ⟨As, Ds, hp, rfl, rfl⟩ s t hst hbl
  exact add_wrrResidual_le_of_isWrr (fun j => hcaus As Ds hp j)
    (hβ.sum_strict hp) (hwrr As Ds hp) hst hbl

/-! ## Book restatement (WRR residual service, ratio form)
An `n`-server offering a strict service curve `β` under WRR with
weights `wⱼ` and packet lengths in `[ℓⱼˡ, ℓⱼᵘ]`: flow `i` is
guaranteed the strict service curve `qᵢ/(qᵢ+Qᵢ)·[β − Qᵢ]⁺` with
`qᵢ = wᵢℓᵢˡ` and `Qᵢ = ∑_{j≠i} wⱼℓⱼᵘ`. (The book derives the
round-count coupling from the WRR algorithm; it is taken here as the
WRR trajectory definition. The sharper forms — the pseudo-inverse
composition through cumulative packet curves, and the staircase
convolution from the same packet-length constants — are the
remaining refinements.) -/
example {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {w : ι → ℕ} {lmin lmax : ι → ℝ≥0} {i : ι}
    (hSrv : IsServerN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hwrr : IsWrrServerN w lmin lmax S) :
    IsStrictMinimalServiceCurve (wrrResidual w lmin lmax i β)
      (residualServer S i) :=
  isStrictMinimalServiceCurve_residualServer_of_isWrr
    hSrv.1 hβ hwrr

/-! ## The staircase refinement -/

/-- The WRR staircase residual curve: the round-quantized form
`(λ₁ ∗ ν) ∘ [β − Qᵢ]⁺`, where the staircase `ν` releases `qᵢ = wᵢℓᵢˡ`
per period `qᵢ + Qᵢ` with `Qᵢ = ∑_{j≠i} wⱼℓⱼᵘ` — the pseudo-inverse
of the round-count map `x ↦ x + Qᵢ(1 + ⌊x/qᵢ⌋)`. -/
noncomputable def wrrResidualStaircase {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (lmin lmax : ι → ℝ≥0) (i : ι) (β : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun τ => minConv (rate 1)
    (staircaseFun
      ((w i : ℝ≥0) * lmin i
        + ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j)
      ((w i : ℝ≥0) * lmin i) 0)
    (β τ - ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j)

/-- `wrrResidualStaircase w lmin lmax i β τ` unfolds to its
convolution form. -/
@[simp] theorem wrrResidualStaircase_apply {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (lmin lmax : ι → ℝ≥0) (i : ι) (β : ℝ≥0 → ℝ≥0)
    (τ : ℝ≥0) :
    wrrResidualStaircase w lmin lmax i β τ
      = minConv (rate 1)
          (staircaseFun
            ((w i : ℝ≥0) * lmin i
              + ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j)
            ((w i : ℝ≥0) * lmin i) 0)
          (β τ - ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j) :=
  rfl

/-- `wrrResidualStaircase w lmin lmax i β 0 = 0` when `β 0 = 0`. -/
theorem wrrResidualStaircase_zero_eq {ι : Type*} [Fintype ι]
    {w : ι → ℕ} {lmin lmax : ι → ℝ≥0} {i : ι} {β : ℝ≥0 → ℝ≥0}
    (hβ0 : β 0 = 0) :
    wrrResidualStaircase w lmin lmax i β 0 = 0 := by
  rw [wrrResidualStaircase_apply, hβ0, zero_tsub, minConv_apply_zero,
    staircaseFun_zero_eq, add_zero]
  simp [rate]

/-- The ratio form is the linearization of the staircase form:
`wrrResidual ≤ wrrResidualStaircase` pointwise. -/
theorem wrrResidual_le_wrrResidualStaircase {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (lmin lmax : ι → ℝ≥0) (i : ι) (β : ℝ≥0 → ℝ≥0)
    (τ : ℝ≥0) :
    wrrResidual w lmin lmax i β τ
      ≤ wrrResidualStaircase w lmin lmax i β τ := by
  rw [wrrResidual_apply, wrrResidualStaircase_apply]
  rcases eq_zero_or_pos ((w i : ℝ≥0) * lmin i
      + ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j) with hq | hq
  · rw [hq, div_zero, zero_mul]
    exact zero_le'
  refine le_minConv fun u v huv => ?_
  rw [← huv]
  have hqR : (0 : ℝ) < (((w i : ℝ≥0) * lmin i
      + ∑ j ∈ Finset.univ.erase i,
        (w j : ℝ≥0) * lmax j : ℝ≥0) : ℝ) := by
    exact_mod_cast hq
  rw [← NNReal.coe_le_coe]
  unfold staircaseFun rate
  push_cast
  rw [sub_zero, one_mul]
  have hratio : (((w i : ℝ≥0) * lmin i : ℝ≥0) : ℝ)
      / (((w i : ℝ≥0) * lmin i
          + ∑ j ∈ Finset.univ.erase i,
            (w j : ℝ≥0) * lmax j : ℝ≥0) : ℝ) ≤ 1 := by
    rw [div_le_one hqR]
    exact_mod_cast le_self_add
  have h1 : (((w i : ℝ≥0) * lmin i : ℝ≥0) : ℝ)
        / (((w i : ℝ≥0) * lmin i
            + ∑ j ∈ Finset.univ.erase i,
              (w j : ℝ≥0) * lmax j : ℝ≥0) : ℝ) * (u : ℝ)
      ≤ (u : ℝ) :=
    mul_le_of_le_one_left u.coe_nonneg hratio
  have h2 : (((w i : ℝ≥0) * lmin i : ℝ≥0) : ℝ)
        * ((v : ℝ)
          / (((w i : ℝ≥0) * lmin i
              + ∑ j ∈ Finset.univ.erase i,
                (w j : ℝ≥0) * lmax j : ℝ≥0) : ℝ))
      ≤ (((w i : ℝ≥0) * lmin i : ℝ≥0) : ℝ)
        * (⌈(v : ℝ)
            / (((w i : ℝ≥0) * lmin i
                + ∑ j ∈ Finset.univ.erase i,
                  (w j : ℝ≥0) * lmax j : ℝ≥0) : ℝ)⌉₊ : ℝ) :=
    mul_le_mul_of_nonneg_left (Nat.le_ceil _)
      ((w i : ℝ≥0) * lmin i).coe_nonneg
  have h2' := (div_mul_eq_mul_div (((w i : ℝ≥0) * lmin i : ℝ≥0) : ℝ)
    (((w i : ℝ≥0) * lmin i
      + ∑ j ∈ Finset.univ.erase i,
        (w j : ℝ≥0) * lmax j : ℝ≥0) : ℝ) (v : ℝ)).trans
    (mul_div_assoc _ _ _)
  push_cast at h1 h2 h2' hratio ⊢
  nlinarith [h1, h2, h2']


/-- **WRR staircase residual service**: under WRR with a strict
aggregate `β`, flow `i` obeys the strict service inequality for the
round-quantized `(λ₁ ∗ ν) ∘ [β − Qᵢ]⁺` on its backlogged periods —
witnessed by the single split at `p` complete rounds. -/
theorem add_wrrResidualStaircase_le_of_isWrr {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0} {w : ι → ℕ}
    {lmin lmax : ι → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    (hwrr : IsWrr w lmin lmax (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    {i : ι} {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t)) :
    (Ds i) s + wrrResidualStaircase w lmin lmax i β (t - s)
      ≤ (Ds i) t := by
  rw [wrrResidualStaircase_apply]
  obtain ⟨p, hown, hcross⟩ := hwrr i s t hst hbl
  -- the residual vanishes when `β` does not clear the per-round price
  rcases le_total (β (t - s))
      (∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j) with hd | hd
  · rw [tsub_eq_zero_of_le hd, minConv_apply_zero,
      staircaseFun_zero_eq, add_zero]
    simpa [rate] using (Ds i).mono hst
  -- one split bounds the convolution: `p` complete rounds to `ν`
  refine le_trans (add_le_add le_rfl (minConv_le_add _ _
    (add_tsub_cancel_of_le (tsub_le_self
      (a := β (t - s)
        - ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j)
      (b := (p : ℝ≥0) * ((w i : ℝ≥0) * lmin i
        + ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j)))))) ?_
  have hν : staircaseFun
      ((w i : ℝ≥0) * lmin i
        + ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j)
      ((w i : ℝ≥0) * lmin i) 0
      ((β (t - s) - ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j)
        - ((β (t - s)
            - ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j)
          - (p : ℝ≥0) * ((w i : ℝ≥0) * lmin i
            + ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j)))
      ≤ (w i : ℝ≥0) * lmin i * p := by
    refine staircaseFun_le ?_
    rw [zero_add]
    exact tsub_le_iff_right.mpr le_add_tsub
  refine le_trans (add_le_add le_rfl (add_le_add le_rfl hν)) ?_
  simp only [rate, one_mul]
  -- below `p` complete rounds the `λ₁` part vanishes
  rcases le_total
      (β (t - s) - ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j)
      ((p : ℝ≥0) * ((w i : ℝ≥0) * lmin i
        + ∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0) * lmax j))
      with hyT | hyT
  · rw [tsub_eq_zero_of_le hyT, zero_add,
      mul_comm ((w i : ℝ≥0) * lmin i) (p : ℝ≥0)]
    exact hown
  -- past `p` complete rounds: the strict aggregate pays the rest
  have hstr := hstrict s t hst
    (isBacklogged_sum_of_isBacklogged (fun j _ x => hc j x)
      (Finset.mem_univ i) hbl)
  rw [← Finset.add_sum_erase Finset.univ (fun j => (Ds j) s)
      (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ (fun j => (Ds j) t)
      (Finset.mem_univ i)] at hstr
  have hownR : ((Ds i) s : ℝ)
      + (p : ℝ) * (((w i : ℝ≥0) * lmin i : ℝ≥0) : ℝ)
      ≤ ((Ds i) t : ℝ) := by
    exact_mod_cast hown
  have hcrossR :
      ((∑ j ∈ Finset.univ.erase i, (Ds j) t : ℝ≥0) : ℝ)
        ≤ ((∑ j ∈ Finset.univ.erase i, (Ds j) s : ℝ≥0) : ℝ)
          + ((p : ℝ) + 1)
            * ((∑ j ∈ Finset.univ.erase i,
                (w j : ℝ≥0) * lmax j : ℝ≥0) : ℝ) := by
    have h : (∑ j ∈ Finset.univ.erase i, (Ds j) t)
        ≤ ∑ j ∈ Finset.univ.erase i,
            ((Ds j) s + ((p : ℝ≥0) + 1) * ((w j : ℝ≥0) * lmax j)) :=
      Finset.sum_le_sum fun j hj =>
        hcross j (Finset.ne_of_mem_erase hj)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    exact_mod_cast h
  have hstrR : (((Ds i) s : ℝ)
        + ((∑ j ∈ Finset.univ.erase i, (Ds j) s : ℝ≥0) : ℝ))
        + ((β (t - s) : ℝ≥0) : ℝ)
      ≤ ((Ds i) t : ℝ)
        + ((∑ j ∈ Finset.univ.erase i, (Ds j) t : ℝ≥0) : ℝ) := by
    exact_mod_cast hstr
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_sub hyT, NNReal.coe_sub hd]
  push_cast at hownR hcrossR hstrR
  linarith

/-- Relation form: a WRR `n`-server with a strict aggregate curve
offers each flow the staircase-refined strict residual on the
residual server, without arrival-curve hypotheses. -/
theorem isStrictMinimalServiceCurve_wrrResidualStaircase_of_isWrr
    {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {w : ι → ℕ} {lmin lmax : ι → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hwrr : IsWrrServerN w lmin lmax S) :
    IsStrictMinimalServiceCurve (wrrResidualStaircase w lmin lmax i β)
      (residualServer S i) := by
  rintro Ai Di ⟨As, Ds, hp, rfl, rfl⟩ s t hst hbl
  exact add_wrrResidualStaircase_le_of_isWrr (fun j => hcaus As Ds hp j)
    (hβ.sum_strict hp) (hwrr As Ds hp) hst hbl

/-! ## Book restatement (WRR residual service, staircase form)
Flow `i` is also guaranteed the sharper strict service curve
`(λ₁ ∗ ν) ∘ [β − Qᵢ]⁺`, where `ν` is the staircase of height
`qᵢ = wᵢℓᵢˡ` and period `qᵢ + Qᵢ` — the pseudo-inverse of the
round-count map `x ↦ x + Qᵢ(1 + ⌊x/qᵢ⌋)` — and the ratio form is its
linearization. (The book prints the staircase subscripts as
`ν_{qᵢ,qᵢ+Qᵢ}`; its staircase convention puts the period first, and
the curve inverting `x ↦ x + a⌊x/b⌋` has period `a + b` and height
`b`, so the subscripts are read here as height `qᵢ`, period
`qᵢ + Qᵢ`.) -/
example {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {w : ι → ℕ} {lmin lmax : ι → ℝ≥0} {i : ι}
    (hSrv : IsServerN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hwrr : IsWrrServerN w lmin lmax S) :
    IsStrictMinimalServiceCurve
        (wrrResidualStaircase w lmin lmax i β) (residualServer S i)
      ∧ ∀ τ, wrrResidual w lmin lmax i β τ
        ≤ wrrResidualStaircase w lmin lmax i β τ :=
  ⟨isStrictMinimalServiceCurve_wrrResidualStaircase_of_isWrr
      hSrv.1 hβ hwrr,
    wrrResidual_le_wrrResidualStaircase w lmin lmax i β⟩

end DeepWiki
