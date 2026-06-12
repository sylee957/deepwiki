import Book.ServersResidualWrr
import Book.PseudoInverse

/-! # Weighted-round-robin residual service through packet curves
The packet-curve form of the WRR residual: with lower and upper packet
curves `Lⱼˡ`, `Lⱼᵘ` bounding each flow's cumulative packet lengths,
the round-count coupling — own service at least `Lᵢˡ(p·wᵢ)`, every
other flow at most `Lⱼᵘ((p+1)·wⱼ)` — yields the strict residual
`f⁻¹ ∘ β`, where `f` prices a served amount by the worst admissible
round count (`wrrPacketsPrice`) and `f⁻¹` is the lower pseudo-inverse.
The linear packet curves `n ↦ n·ℓ` recover `IsWrr`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **WRR through packet curves**: on each backlogged period of flow
`i` there is a round count `p` granting flow `i` at least `Lᵢˡ(p·wᵢ)`
(its packets in `p` complete rounds, priced by the lower packet curve)
while every other flow takes at most `Lⱼᵘ((p+1)·wⱼ)`. Degenerate
periods `s = t` force `∃ p, Lᵢˡ(p·wᵢ) = 0` — satisfied by book-valid
lower curves, whose empty-window instance forces `Lᵢˡ(0) = 0`. -/
def IsWrrPackets {ι : Type*} (w : ι → ℕ) (Ll Lu : ι → ℕ → ℝ≥0)
    (A D : ι → ℝ≥0 → ℝ≥0) : Prop :=
  ∀ i : ι, ∀ s t : ℝ≥0, s ≤ t →
    IsBacklogged (A i) (D i) (Set.Ioc s t) →
    ∃ p : ℕ,
      (D i s + Ll i (p * w i) ≤ D i t)
      ∧ ∀ j, j ≠ i → D j t ≤ D j s + Lu j ((p + 1) * w j)

/-- Degenerate-interval elim: the `s = t` instance of the coupling
forces the lower packet curve to vanish at some sampled multiple. -/
theorem IsWrrPackets.exists_ll_eq_zero {ι : Type*} {w : ι → ℕ}
    {Ll Lu : ι → ℕ → ℝ≥0} {A D : ι → ℝ≥0 → ℝ≥0}
    (h : IsWrrPackets w Ll Lu A D) (i : ι) :
    ∃ p : ℕ, Ll i (p * w i) = 0 := by
  obtain ⟨p, hown, -⟩ := h i 0 0 le_rfl (by simp [IsBacklogged])
  exact ⟨p, nonpos_iff_eq_zero.mp (by simpa using hown)⟩

/-- Model witness: the zero pair satisfies the packet-curve coupling
for every lower curve with `Lᵢˡ(0) = 0`. -/
theorem isWrrPackets_zero {ι : Type*} {w : ι → ℕ}
    {Ll Lu : ι → ℕ → ℝ≥0} (hLl0 : ∀ i, Ll i 0 = 0) :
    IsWrrPackets w Ll Lu (fun _ _ => 0) (fun _ _ => 0) := by
  intro i s t hst hbl
  refine ⟨0, ?_, fun j hj => zero_le'⟩
  simp [hLl0 i]

/-- The linear packet curves `n ↦ n·ℓ` recover the constant-length
coupling: `IsWrr` transports to `IsWrrPackets`. -/
theorem IsWrr.isWrrPackets {ι : Type*} {w : ι → ℕ}
    {lmin lmax : ι → ℝ≥0} {A D : ι → ℝ≥0 → ℝ≥0}
    (h : IsWrr w lmin lmax A D) :
    IsWrrPackets w (fun j n => (n : ℝ≥0) * lmin j)
      (fun j n => (n : ℝ≥0) * lmax j) A D := by
  intro i s t hst hbl
  obtain ⟨p, hown, hcross⟩ := h i s t hst hbl
  refine ⟨p, ?_, fun j hj => ?_⟩
  · show D i s + ((p * w i : ℕ) : ℝ≥0) * lmin i ≤ D i t
    have he : ((p * w i : ℕ) : ℝ≥0) * lmin i
        = (p : ℝ≥0) * ((w i : ℝ≥0) * lmin i) := by
      push_cast
      ring
    rwa [he]
  · show D j t ≤ D j s + (((p + 1) * w j : ℕ) : ℝ≥0) * lmax j
    have he : (((p + 1) * w j : ℕ) : ℝ≥0) * lmax j
        = ((p : ℝ≥0) + 1) * ((w j : ℝ≥0) * lmax j) := by
      push_cast
      ring
    rw [he]
    exact hcross j hj

/-- **WRR packet-curve `n`-server**: every served family obeys the
packet-curve round-count coupling. -/
def IsWrrPacketsServerN {ι : Type*} (w : ι → ℕ) (Ll Lu : ι → ℕ → ℝ≥0)
    (S : (ι → Curve) → (ι → Curve) → Prop) : Prop :=
  ∀ As Ds, S As Ds →
    IsWrrPackets w Ll Lu (fun j => ⇑(As j)) (fun j => ⇑(Ds j))

/-- A constant-length WRR `n`-server is a packet-curve WRR `n`-server
for the linear packet curves. -/
theorem IsWrrServerN.isWrrPacketsServerN {ι : Type*} {w : ι → ℕ}
    {lmin lmax : ι → ℝ≥0} {S : (ι → Curve) → (ι → Curve) → Prop}
    (h : IsWrrServerN w lmin lmax S) :
    IsWrrPacketsServerN w (fun j n => (n : ℝ≥0) * lmin j)
      (fun j n => (n : ℝ≥0) * lmax j) S :=
  fun As Ds hp => (h As Ds hp).isWrrPackets

/-- The WRR packet price `f`: a served amount `x` costs `x` plus the
other flows' worst admissible per-round charge,
`⨆_{p : Lᵢˡ(p·wᵢ) ≤ x} ∑_{j≠i} Lⱼᵘ((p+1)·wⱼ)`. -/
noncomputable def wrrPacketsPrice {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (Ll Lu : ι → ℕ → ℝ≥0) (i : ι) : ℝ≥0∞ → ℝ≥0∞ :=
  fun x => x + ⨆ (p : ℕ) (_ : (Ll i (p * w i) : ℝ≥0∞) ≤ x),
    ∑ j ∈ Finset.univ.erase i, (Lu j ((p + 1) * w j) : ℝ≥0∞)

/-- `wrrPacketsPrice w Ll Lu i x` unfolds to its supremum form. -/
theorem wrrPacketsPrice_apply {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (Ll Lu : ι → ℕ → ℝ≥0) (i : ι) (x : ℝ≥0∞) :
    wrrPacketsPrice w Ll Lu i x
      = x + ⨆ (p : ℕ) (_ : (Ll i (p * w i) : ℝ≥0∞) ≤ x),
          ∑ j ∈ Finset.univ.erase i, (Lu j ((p + 1) * w j) : ℝ≥0∞) :=
  rfl

/-- The packet price is non-decreasing — a larger served amount admits
every previous round count. -/
theorem wrrPacketsPrice_mono {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (Ll Lu : ι → ℕ → ℝ≥0) (i : ι) :
    Monotone (wrrPacketsPrice w Ll Lu i) := by
  intro x y hxy
  exact add_le_add hxy
    (iSup₂_le fun p hp => le_iSup₂_of_le p (hp.trans hxy) le_rfl)

/-- Intro: any admissible round count bounds the price from below,
`x + ∑_{j≠i} Lⱼᵘ((p+1)·wⱼ) ≤ f x` once `Lᵢˡ(p·wᵢ) ≤ x`. -/
theorem add_le_wrrPacketsPrice {ι : Type*} [Fintype ι] {w : ι → ℕ}
    {Ll Lu : ι → ℕ → ℝ≥0} {i : ι} {x : ℝ≥0∞} (p : ℕ)
    (hadm : (Ll i (p * w i) : ℝ≥0∞) ≤ x) :
    x + ∑ j ∈ Finset.univ.erase i, (Lu j ((p + 1) * w j) : ℝ≥0∞)
      ≤ wrrPacketsPrice w Ll Lu i x :=
  add_le_add le_rfl (le_iSup₂_of_le p hadm le_rfl)

/-- Elim: a uniform bound on the admissible per-round charges bounds
the price, `f x ≤ x + y`. -/
theorem wrrPacketsPrice_le_add {ι : Type*} [Fintype ι] {w : ι → ℕ}
    {Ll Lu : ι → ℕ → ℝ≥0} {i : ι} {x y : ℝ≥0∞}
    (h : ∀ p : ℕ, (Ll i (p * w i) : ℝ≥0∞) ≤ x →
      ∑ j ∈ Finset.univ.erase i, (Lu j ((p + 1) * w j) : ℝ≥0∞) ≤ y) :
    wrrPacketsPrice w Ll Lu i x ≤ x + y :=
  add_le_add le_rfl (iSup₂_le h)

/-- The WRR packet-curve residual `f⁻¹ ∘ β`: the lower pseudo-inverse
of the packet price, read back into `ℝ≥0`. -/
noncomputable def wrrResidualPackets {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (Ll Lu : ι → ℕ → ℝ≥0) (i : ι) (β : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun τ =>
    (pseudoInv (wrrPacketsPrice w Ll Lu i) ((β τ : ℝ≥0) : ℝ≥0∞)).toNNReal

/-- `wrrResidualPackets w Ll Lu i β τ` unfolds to its pseudo-inverse
form. -/
@[simp] theorem wrrResidualPackets_apply {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (Ll Lu : ι → ℕ → ℝ≥0) (i : ι) (β : ℝ≥0 → ℝ≥0)
    (τ : ℝ≥0) :
    wrrResidualPackets w Ll Lu i β τ
      = (pseudoInv (wrrPacketsPrice w Ll Lu i)
          ((β τ : ℝ≥0) : ℝ≥0∞)).toNNReal :=
  rfl

/-- `wrrResidualPackets w Ll Lu i β 0 = 0` when `β 0 = 0`. -/
theorem wrrResidualPackets_zero_eq {ι : Type*} [Fintype ι]
    {w : ι → ℕ} {Ll Lu : ι → ℕ → ℝ≥0} {i : ι} {β : ℝ≥0 → ℝ≥0}
    (hβ0 : β 0 = 0) :
    wrrResidualPackets w Ll Lu i β 0 = 0 := by
  rw [wrrResidualPackets_apply, hβ0,
    show ((0 : ℝ≥0) : ℝ≥0∞) = ⊥ from rfl, pseudoInv_bot]
  rfl

/-- **WRR packet-curve residual service**: under the packet-curve
round-count coupling with a strict aggregate `β`, flow `i` obeys the
strict service inequality for `f⁻¹ ∘ β` on its backlogged periods —
the witnessed round count is admissible for the price at the served
increment, and the pseudo-inverse elim closes. -/
theorem add_wrrResidualPackets_le_of_isWrrPackets {ι : Type*}
    [Fintype ι] {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0} {w : ι → ℕ}
    {Ll Lu : ι → ℕ → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    (hwrr : IsWrrPackets w Ll Lu (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    {i : ι} {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t)) :
    (Ds i) s + wrrResidualPackets w Ll Lu i β (t - s) ≤ (Ds i) t := by
  obtain ⟨p, hown, hcross⟩ := hwrr i s t hst hbl
  have hDst : (Ds i) s ≤ (Ds i) t := (Ds i).mono hst
  rw [add_comm, ← le_tsub_iff_right hDst]
  -- the strict aggregate plus the cross bounds price the increment
  have hstr := hstrict s t hst
    (isBacklogged_sum_of_isBacklogged (fun j _ x => hc j x)
      (Finset.mem_univ i) hbl)
  rw [← Finset.add_sum_erase Finset.univ (fun j => (Ds j) s)
      (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ (fun j => (Ds j) t)
      (Finset.mem_univ i)] at hstr
  have hβbound : β (t - s) ≤ ((Ds i) t - (Ds i) s)
      + ∑ j ∈ Finset.univ.erase i, Lu j ((p + 1) * w j) := by
    have hcrossR :
        ((∑ j ∈ Finset.univ.erase i, (Ds j) t : ℝ≥0) : ℝ)
          ≤ ((∑ j ∈ Finset.univ.erase i, (Ds j) s : ℝ≥0) : ℝ)
            + ((∑ j ∈ Finset.univ.erase i,
                Lu j ((p + 1) * w j) : ℝ≥0) : ℝ) := by
      have h : (∑ j ∈ Finset.univ.erase i, (Ds j) t)
          ≤ ∑ j ∈ Finset.univ.erase i,
              ((Ds j) s + Lu j ((p + 1) * w j)) :=
        Finset.sum_le_sum fun j hj =>
          hcross j (Finset.ne_of_mem_erase hj)
      rw [Finset.sum_add_distrib] at h
      exact_mod_cast h
    have hstrR : (((Ds i) s : ℝ)
          + ((∑ j ∈ Finset.univ.erase i, (Ds j) s : ℝ≥0) : ℝ))
          + ((β (t - s) : ℝ≥0) : ℝ)
        ≤ ((Ds i) t : ℝ)
          + ((∑ j ∈ Finset.univ.erase i, (Ds j) t : ℝ≥0) : ℝ) := by
      exact_mod_cast hstr
    rw [← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hDst]
    push_cast at hcrossR hstrR
    linarith
  -- the witnessed round count is admissible at the served increment
  have hadm : (Ll i (p * w i) : ℝ≥0∞)
      ≤ (((Ds i) t - (Ds i) s : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast le_tsub_of_add_le_left hown
  have hkey : ((β (t - s) : ℝ≥0) : ℝ≥0∞)
      ≤ wrrPacketsPrice w Ll Lu i
          (((Ds i) t - (Ds i) s : ℝ≥0) : ℝ≥0∞) := by
    refine le_trans ?_ (add_le_wrrPacketsPrice p hadm)
    exact_mod_cast hβbound
  have hinv := pseudoInv_le_of_le_apply hkey
  have hread := ENNReal.toNNReal_mono ENNReal.coe_ne_top hinv
  simpa using hread

/-- Relation form: a WRR `n`-server with packet curves and a strict
aggregate curve offers each flow the packet-curve strict residual
`f⁻¹ ∘ β` on the residual server. -/
theorem isStrictMinimalServiceCurve_wrrResidualPackets_of_isWrrPackets
    {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {w : ι → ℕ} {Ll Lu : ι → ℕ → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hwrr : IsWrrPacketsServerN w Ll Lu S) :
    IsStrictMinimalServiceCurve (wrrResidualPackets w Ll Lu i β)
      (residualServer S i) := by
  rintro Ai Di ⟨As, Ds, hp, rfl, rfl⟩ s t hst hbl
  exact add_wrrResidualPackets_le_of_isWrrPackets
    (fun j => hcaus As Ds hp j) (hβ.sum_strict hp) (hwrr As Ds hp)
    hst hbl

/-! ## Book restatement (WRR residual service, packet-curve form)
An `n`-server offering a strict service curve `β` under WRR with
weights `wⱼ` and flow-`j` packets bounded by the packet curves
`Lⱼˡ ≤ · ≤ Lⱼᵘ`: flow `i` is guaranteed the strict service curve
`f⁻¹ ∘ β` — the book's most precise form. Here `f` prices a served
amount `x` as `x` plus the worst admissible per-round charge
`⨆_{p : Lᵢˡ(p·wᵢ) ≤ x} ∑_{j≠i} Lⱼᵘ((p+1)·wⱼ)`; for non-decreasing
`Lᵢˡ` and `Lⱼᵘ` (Definition 8.4's standing assumption), positive
`wᵢ`, and finite `g(x)`, the supremum is attained at the largest
admissible round count `⌊g(x)/wᵢ⌋` with `g` the upper pseudo-inverse
of `Lᵢˡ`, recovering the book's spelling
`f(x) = x + ∑_{j≠i} Lⱼᵘ(wⱼ(1 + ⌊g(x)/wᵢ⌋))`; in the corners `wᵢ = 0`
or `g(x) = ∞` the sup spelling stays well-defined where the book's
expression is not, and the theorem remains sound. `f⁻¹` is the lower
pseudo-inverse `pseudoInv`. The book's packet curves take values in
`ℝ̄min`; they are restricted here to finite `ℝ≥0` values — the
excluded `Lᵘ = ∞` instances are vacuous (zero residual). The
round-count coupling is taken as the trajectory definition
(`IsWrrPackets`); the linear packet curves recover `IsWrr`
(`IsWrr.isWrrPackets`), and the curve-level comparison with the
staircase form is deferred. -/
example {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {w : ι → ℕ} {Ll Lu : ι → ℕ → ℝ≥0} {i : ι}
    (hSrv : IsServerN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hwrr : IsWrrPacketsServerN w Ll Lu S) :
    IsStrictMinimalServiceCurve (wrrResidualPackets w Ll Lu i β)
      (residualServer S i) :=
  isStrictMinimalServiceCurve_wrrResidualPackets_of_isWrrPackets
    hSrv.1 hβ hwrr

end DeepWiki
