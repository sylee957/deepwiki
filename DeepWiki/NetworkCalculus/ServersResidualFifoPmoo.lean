import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import DeepWiki.NetworkCalculus.ServersResidualFifo

/-! # FIFO is preserved by aggregation: the FIFO-PMOO residual
Where GPS fails to survive composition, FIFO survives *aggregation*: in a
FIFO system the two-group family `(∑_{j≠k} flow, flow k)` is again FIFO
(`isFifo_erase_pair`), because a strict aggregate clearing of the group
forces some member to clear, and FIFO then clears every flow — including
flow `k`. Feeding this to the FIFO residual theorem yields the FIFO-PMOO
residual: with flow `k` arrival-constrained by `α` and an aggregate
min-plus service curve `β`, the `m − 1` other flows together receive
`[β − α ∗ δ_θ]⁺ ∧ δ_θ` (`fifoResidual β α θ`).

The *aggregation* step is what is proved here; that the tandem itself is
FIFO and offers the aggregate `β` are taken as hypotheses (`hfifo`,
`hserv`). Both are genuine assumptions: the tandem-is-FIFO fact is a
property of the FIFO *scheduling discipline* (it does not follow from the
trajectory predicate `IsFifo` on the per-server input/output pairs alone),
and `β = ∗ₕ β⁽ʰ⁾` is the concatenation service curve — the book supplies
them separately, then reads off this residual. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Finset

/-- **FIFO survives aggregation into a flow-group**: from a FIFO family,
the two-group family pairing the aggregate of the flows other than `k`
with flow `k` is again FIFO. A strict group clearing `∑_{j≠k} Aⱼ(u) <
∑_{j≠k} Dⱼ(t)` forces some member to clear (`Finset.exists_lt_of_sum_lt`),
and FIFO then clears flow `k`; conversely flow `k` clearing clears every
member. -/
theorem isFifo_erase_pair {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve}
    (hfifo : IsFifo (fun j => ⇑(As j)) (fun j => ⇑(Ds j))) (k : ι) :
    IsFifo
      (fun i : Fin 2 => ⇑((![∑ j ∈ univ.erase k, As j, As k] : Fin 2 → Curve) i))
      (fun i : Fin 2 => ⇑((![∑ j ∈ univ.erase k, Ds j, Ds k] : Fin 2 → Curve) i)) := by
  intro i' j' t u hlt
  fin_cases i' <;> fin_cases j'
  · exact hlt.le
  · -- group cleared ⟹ some member cleared ⟹ flow `k` cleared
    have hlt' : ∑ j ∈ univ.erase k, (As j) u < ∑ j ∈ univ.erase k, (Ds j) t := by
      rw [← Curve.sum_apply, ← Curve.sum_apply]; exact hlt
    obtain ⟨j, _, hjlt⟩ := Finset.exists_lt_of_sum_lt hlt'
    exact hfifo j k t u hjlt
  · -- flow `k` cleared ⟹ every member cleared ⟹ group cleared
    show (∑ j ∈ univ.erase k, As j) u ≤ (∑ j ∈ univ.erase k, Ds j) t
    rw [Curve.sum_apply, Curve.sum_apply]
    exact Finset.sum_le_sum fun j _ => hfifo k j t u hlt
  · exact hlt.le

/-- **FIFO grouped residual**: in a FIFO system with aggregate min-plus
service curve `β` where flow `k` has arrival curve `α`, the other flows
together obey `(∑_{j≠k} Aⱼ) ∗ fifoResidual β α θ ≤ ∑_{j≠k} Dⱼ`. -/
theorem minConv_fifoResidual_le_of_isFifo_group {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0∞} {α : ℝ≥0 → ℝ≥0}
    (hfifo : IsFifo (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (hβmono : Monotone β) (hβlc : IsLeftContinuous β)
    (hserv : ∀ x, minConv (Deviation.liftENN (fun y => ∑ j, (As j) y)) β x
      ≤ ((∑ j, (Ds j) x : ℝ≥0) : ℝ≥0∞))
    {k : ι} (harr : IsMaximalArrivalBound ⇑(As k) α)
    (θ t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(∑ j ∈ univ.erase k, As j))
        (fifoResidual β (fun v => ((α v : ℝ≥0) : ℝ≥0∞)) θ) t
      ≤ (((∑ j ∈ univ.erase k, Ds j) t : ℝ≥0) : ℝ≥0∞) := by
  -- flow `0` of the two-group family is the group `∑_{j≠k}`, flow `1` is `k`
  have harr' : ∀ j : Fin 2, j ≠ 0 →
      IsMaximalArrivalBound
        ⇑((![∑ j ∈ univ.erase k, As j, As k] : Fin 2 → Curve) j)
        ((![0, α] : Fin 2 → ℝ≥0 → ℝ≥0) j) := by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    · simpa using harr
  have hserv' : ∀ x, minConv (Deviation.liftENN
        (fun y => ∑ j, ((![∑ j ∈ univ.erase k, As j, As k] : Fin 2 → Curve) j) y)) β x
      ≤ ((∑ j, ((![∑ j ∈ univ.erase k, Ds j, Ds k] : Fin 2 → Curve) j) x : ℝ≥0)
          : ℝ≥0∞) := by
    intro x
    have eA : (fun y => ∑ j : Fin 2,
          ((![∑ j ∈ univ.erase k, As j, As k] : Fin 2 → Curve) j) y)
        = (fun y => ∑ j, (As j) y) := by
      funext y
      rw [Fin.sum_univ_two]
      show (∑ j ∈ univ.erase k, As j) y + (As k) y = _
      rw [Curve.sum_apply, Finset.sum_erase_add _ _ (mem_univ k)]
    have eD : (∑ j : Fin 2,
          ((![∑ j ∈ univ.erase k, Ds j, Ds k] : Fin 2 → Curve) j) x)
        = ∑ j, (Ds j) x := by
      rw [Fin.sum_univ_two]
      show (∑ j ∈ univ.erase k, Ds j) x + (Ds k) x = _
      rw [Curve.sum_apply, Finset.sum_erase_add _ _ (mem_univ k)]
    rw [eA, eD]; exact hserv x
  have key := minConv_fifoResidual_le_of_isFifo
    (As := (![∑ j ∈ univ.erase k, As j, As k] : Fin 2 → Curve))
    (Ds := (![∑ j ∈ univ.erase k, Ds j, Ds k] : Fin 2 → Curve))
    (β := β) (α := (![0, α] : Fin 2 → ℝ≥0 → ℝ≥0))
    (isFifo_erase_pair hfifo k) hβmono hβlc hserv' (i := 0) harr' θ t
  -- the cross-traffic residual reduces to `α` (only flow `1` is in `erase 0`);
  -- the group-`0` arrival/departure are the aggregates (defeq to `key`'s `![..] 0`)
  convert key using 3
  funext v
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  -- `erase 0 = {1}` over `Fin 2`, regardless of which `DecidableEq` instance
  -- the underlying theorem baked in
  have hone : ∀ inst : DecidableEq (Fin 2),
      (∑ j ∈ @Finset.erase (Fin 2) inst univ 0,
        (![0, α] : Fin 2 → ℝ≥0 → ℝ≥0) j v) = α v := by
    intro inst
    refine Finset.sum_eq_single_of_mem (1 : Fin 2)
      (Finset.mem_erase.mpr ⟨h10, Finset.mem_univ 1⟩) ?_
    intro b _ hb1; fin_cases b <;> simp_all
  exact congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) (hone _).symm

/-! ## Book restatement (FIFO and PMOO)
Where the GPS composition fails (`not_forall_isGps_comp`), FIFO succeeds:
a tandem of FIFO servers is itself a FIFO system and, by concatenation,
offers the aggregate min-plus service curve `β = ∗ₕ β⁽ʰ⁾` — the two
hypotheses below. With flow `k` (the tagged flow) arrival-constrained by
`α`, the `m − 1` other flows together are served at the FIFO residual
`[β − α ∗ δ_θ]⁺ ∧ δ_θ`. The proof groups the others into one aggregate
flow (`isFifo_erase_pair` keeps that pairing FIFO) and applies the FIFO
residual theorem. -/
example {ι : Type*} [Fintype ι]
    {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0∞} {α : ℝ≥0 → ℝ≥0}
    (hfifo : IsFifo (fun j => ⇑(As j)) (fun j => ⇑(Ds j)))
    (hβmono : Monotone β) (hβlc : IsLeftContinuous β)
    (hserv : ∀ x, minConv (Deviation.liftENN (fun y => ∑ j, (As j) y)) β x
      ≤ ((∑ j, (Ds j) x : ℝ≥0) : ℝ≥0∞))
    {k : ι} (harr : IsMaximalArrivalBound ⇑(As k) α) (θ t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(∑ j ∈ univ.erase k, As j))
        (fifoResidual β (fun v => ((α v : ℝ≥0) : ℝ≥0∞)) θ) t
      ≤ (((∑ j ∈ univ.erase k, Ds j) t : ℝ≥0) : ℝ≥0∞) :=
  minConv_fifoResidual_le_of_isFifo_group hfifo hβmono hβlc hserv harr θ t

end DeepWiki
