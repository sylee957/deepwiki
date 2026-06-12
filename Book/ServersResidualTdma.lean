import Book.ServersResidual
import Book.RealCurves

/-! # Time-division-multiple-access residual service
TDMA repeats a cycle of length `c`, within which flow `i` owns a slot
of length `sᵢ`. From the first in-period service start — at most
`Tᵢ = ℓᵢᵘ/R + c − sᵢ` after a backlogged period begins — service
alternates between the in-slot quantum `oᵢ` (served at the line rate
`R`) and the off-slot idle phase, so flow `i` is guaranteed the strict
service curve `ν_{c,oᵢ,−Tᵢ} ∗ λ_R` (`tdmaResidual`); no other flow
enters the bound. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **TDMA slot pattern**: on each backlogged period `(s, t]` of the
flow there is a first in-period service start `u ∈ [s, t]` with
`u ≤ s + T` (the latency `T` covers at most one unfinished packet plus
the off-slot remainder of a cycle) from which service follows the
cyclic alternation — `o` data per cycle `c` at rate `R`,
`(ν_{c,o,0} ∗ λ_R)(t − u)` in total. -/
def IsTdma (c o T R : ℝ≥0) (A D : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ s t : ℝ≥0, s ≤ t → IsBacklogged A D (Set.Ioc s t) →
    ∃ u, s ≤ u ∧ u ≤ t ∧ u ≤ s + T
      ∧ D u + minConv (staircaseFun c o 0) (rate R) (t - u) ≤ D t

/-- **TDMA `n`-server**: every served family obeys the slot pattern,
flow `j` with quantum `o j` and latency `T j`. -/
def IsTdmaServerN {ι : Type*} (c : ℝ≥0) (o T : ι → ℝ≥0) (R : ℝ≥0)
    (S : (ι → Curve) → (ι → Curve) → Prop) : Prop :=
  ∀ As Ds, S As Ds → ∀ i, IsTdma c (o i) (T i) R ⇑(As i) ⇑(Ds i)

/-- Model witness: the constant-rate served pair `A = D = λ_R`
satisfies `IsTdma` for every cycle, quantum, and latency — the period
start itself serves, and the split `(0, t − s)` realizes the
convolution bound. -/
theorem isTdma_rate (c o T R : ℝ≥0) :
    IsTdma c o T R (rate R) (rate R) := by
  intro s t hst _hbl
  refine ⟨s, le_rfl, hst, le_self_add, ?_⟩
  refine le_trans (add_le_add le_rfl
    (minConv_le_add _ _ (zero_add (t - s)))) ?_
  rw [staircaseFun_zero_eq, zero_add]
  show R * s + R * (t - s) ≤ R * t
  rw [← mul_add, add_tsub_cancel_of_le hst]

/-- The TDMA residual curve `ν_{c,o,−T} ∗ λ_R`: the delayed staircase
of quantum `o` per cycle `c`, smoothed at the line rate `R`. -/
noncomputable def tdmaResidual (c o T R : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  minConv (staircaseFun c o T) (rate R)

/-- `tdmaResidual c o T R τ` unfolds to its convolution form. -/
@[simp] theorem tdmaResidual_apply (c o T R τ : ℝ≥0) :
    tdmaResidual c o T R τ
      = minConv (staircaseFun c o T) (rate R) τ := rfl

/-- `tdmaResidual c o T R 0 = 0`. -/
theorem tdmaResidual_zero_eq (c o T R : ℝ≥0) :
    tdmaResidual c o T R 0 = 0 := by
  rw [tdmaResidual_apply, minConv_apply_zero, staircaseFun_zero_eq,
    zero_add]
  simp [rate]

/-- Latency shift: the delayed convolution at `τ` is below the
undelayed one at any `σ` with `τ ≤ σ + T` — each split of `σ` yields
a split of `τ` that the rigid staircase translation dominates. -/
theorem tdmaResidual_le_shift (c o T R : ℝ≥0) {τ σ : ℝ≥0}
    (h : τ ≤ σ + T) :
    tdmaResidual c o T R τ
      ≤ minConv (staircaseFun c o 0) (rate R) σ := by
  refine le_minConv fun a b hab => ?_
  have hb : τ - (a + T) ≤ b := by
    refine tsub_le_iff_left.mpr ?_
    calc τ ≤ σ + T := h
      _ = (a + T) + b := by rw [← hab]; ring
  refine le_trans (minConv_le_add _ _
    (tsub_add_cancel_of_le (tsub_le_self (a := τ) (b := a + T)))) ?_
  refine add_le_add ?_ ?_
  · calc staircaseFun c o T (τ - (τ - (a + T)))
        ≤ staircaseFun c o T (a + T) :=
          staircaseFun_mono c o T (tsub_le_iff_right.mpr le_add_tsub)
      _ = staircaseFun c o 0 a := by
          have := staircaseFun_shift c o 0 T a
          rwa [zero_add] at this
  · show R * (τ - (a + T)) ≤ R * b
    exact mul_le_mul_right hb R

/-- **TDMA residual service**: the slot pattern alone yields the
strict service inequality for `ν_{c,o,−T} ∗ λ_R` on backlogged
periods — no aggregate curve and no other flow are consumed. -/
theorem add_tdmaResidual_le_of_isTdma {c o T R : ℝ≥0}
    {A D : ℝ≥0 → ℝ≥0} (hDmono : Monotone D)
    (htdma : IsTdma c o T R A D)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged A D (Set.Ioc s t)) :
    D s + tdmaResidual c o T R (t - s) ≤ D t := by
  obtain ⟨u, hsu, _hut, husT, hserv⟩ := htdma s t hst hbl
  refine le_trans (add_le_add (hDmono hsu)
    (tdmaResidual_le_shift c o T R ?_)) hserv
  calc t - s ≤ (t - u) + (u - s) :=
      tsub_le_tsub_add_tsub (a := t) (b := u) (c := s)
    _ ≤ (t - u) + T :=
      add_le_add le_rfl (tsub_le_iff_right.mpr (by rwa [add_comm]))

/-- Relation form: a TDMA `n`-server offers each flow the strict
residual `ν_{c,oᵢ,−Tᵢ} ∗ λ_R` on the residual server. -/
theorem isStrictMinimalServiceCurve_tdmaResidual_of_isTdma
    {ι : Type*} {S : (ι → Curve) → (ι → Curve) → Prop}
    {c R : ℝ≥0} {o T : ι → ℝ≥0} {i : ι}
    (htdma : IsTdmaServerN c o T R S) :
    IsStrictMinimalServiceCurve (tdmaResidual c (o i) (T i) R)
      (residualServer S i) := by
  rintro Ai Di ⟨As, Ds, hp, rfl, rfl⟩ s t hst hbl
  exact add_tdmaResidual_le_of_isTdma (Ds i).mono (htdma As Ds hp i)
    hst hbl

/-! ## Book restatement (TDMA residual service)
An `n`-server with guaranteed rate `R` under TDMA with cycle `c`,
flow-`i` slot length `sᵢ ≥ ℓᵢᵘ/R`, and packet lengths in `[ℓᵢˡ, ℓᵢᵘ]`:
flow `i` is guaranteed the strict service curve
`βᵢᵀᴰᴹᴬ = ν_{c,oᵢ,−Tᵢ} ∗ λ_R` with latency `Tᵢ = ℓᵢᵘ/R + c − sᵢ` and
per-cycle quantum `oᵢ = ℓᵢᵘ·⌊R·sᵢ/ℓᵢᵘ⌋` when all packets have equal
length `ℓᵢˡ = ℓᵢᵘ`, and `oᵢ = ℓᵢˡ ⊔ (R·sᵢ − ℓᵢᵘ)` otherwise. The
cyclic slot-alternation facts — service `(ν_{c,oᵢ,0} ∗ λ_R)(t − u)`
from the first in-period start `u`, and `u − s ≤ Tᵢ` — are taken as
the TDMA trajectory definition (`IsTdma`); the book derives them from
the slot mechanics, with the line rate `R` consumed there. The
`ℝ≥0` truncations in the pinned constants are exact under the book's
implicit guards `0 < R` and `sᵢ ≤ c` (slots fit in the cycle). -/
example {ι : Type*} {S : (ι → Curve) → (ι → Curve) → Prop}
    {c R : ℝ≥0} {o T lmin lmax slot : ι → ℝ≥0} {i : ι}
    (_hR : 0 < R) (_hcycle : slot i ≤ c)
    (_hslot : lmax i / R ≤ slot i)
    (_ho : (lmin i = lmax i
        ∧ o i = lmax i * ⌊R * slot i / lmax i⌋₊)
      ∨ o i = lmin i ⊔ (R * slot i - lmax i))
    (hT : T i = lmax i / R + c - slot i)
    (htdma : IsTdmaServerN c o T R S) :
    IsStrictMinimalServiceCurve
      (tdmaResidual c (o i) (lmax i / R + c - slot i) R)
      (residualServer S i) :=
  hT ▸ isStrictMinimalServiceCurve_tdmaResidual_of_isTdma htdma

end DeepWiki
