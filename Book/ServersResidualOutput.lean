import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Book.ServersResidual
import Book.ArrivalCurvesOutput
import Book.ArrivalCurvesAggregate
import Book.ArrivalCurvesMaximal

/-! # Strict residual from arrival curves alone
The departure-constrained strict residual becomes usable without
departure hypotheses: the cross-traffic aggregate is itself served at
`[β − αᵢ]⁺↑` (blind multiplexing for the complement), so its output
allows the deconvolution `(∑_{j≠i} αⱼ) ⊘ [β − αᵢ]⁺↑`, whose
sub-additive closure feeds the departure-constrained theorem — the
book's corollary `βᵢ = [β − ((∑_{j≠i} αⱼ) ⊘ [β − αᵢ]⁺↑)*]⁺↑`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **Blind multiplexing for the complement**: the cross-traffic
aggregate of flow `i` is served at the residual of flow `i`'s own
constraint, `(∑_{j≠i} Aⱼ) ∗ [β − αᵢ]⁺↑ ≤ ∑_{j≠i} Dⱼ`. -/
theorem minConv_residualCurve_le_erase_sum_of_strict_aggregate
    {ι : Type*} [Fintype ι] {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    {i : ι} (harr : IsMaximalArrivalBound ⇑(As i) (α i)) (t : ℝ≥0) :
    minConv (Deviation.liftENN
        (fun x => ∑ j ∈ Finset.univ.erase i, (As j) x))
      (Deviation.liftENN (residualCurve β (α i))) t
      ≤ ((∑ j ∈ Finset.univ.erase i, (Ds j) t : ℝ≥0) : ℝ≥0∞) := by
  have hsumA : ∀ x : ℝ≥0,
      (∑ j2, ((![As i, ∑ j ∈ Finset.univ.erase i, As j]
          : Fin 2 → Curve) j2) x) = ∑ j, (As j) x := fun x => by
    rw [Fin.sum_univ_two]
    show (As i) x + (∑ j ∈ Finset.univ.erase i, As j) x = _
    rw [Curve.sum_apply]
    exact Finset.add_sum_erase Finset.univ (fun j => (As j) x)
      (Finset.mem_univ i)
  have hsumD : ∀ x : ℝ≥0,
      (∑ j2, ((![Ds i, ∑ j ∈ Finset.univ.erase i, Ds j]
          : Fin 2 → Curve) j2) x) = ∑ j, (Ds j) x := fun x => by
    rw [Fin.sum_univ_two]
    show (Ds i) x + (∑ j ∈ Finset.univ.erase i, Ds j) x = _
    rw [Curve.sum_apply]
    exact Finset.add_sum_erase Finset.univ (fun j => (Ds j) x)
      (Finset.mem_univ i)
  have h := minConv_residualCurve_le_of_strict_aggregate
    (As := ![As i, ∑ j ∈ Finset.univ.erase i, As j])
    (Ds := ![Ds i, ∑ j ∈ Finset.univ.erase i, Ds j])
    (β := β) (α := ![α i, fun _ => 0]) (i := 1)
    (by
      intro j2
      fin_cases j2
      · exact hc i
      · intro u
        show (∑ j ∈ Finset.univ.erase i, Ds j) u
          ≤ (∑ j ∈ Finset.univ.erase i, As j) u
        rw [Curve.sum_apply, Curve.sum_apply]
        exact Finset.sum_le_sum fun j _ => hc j u)
    (by
      intro s t' hst' hbl'
      rw [hsumD s, hsumD t']
      refine hstrict s t' hst' ?_
      intro u hu
      show (∑ j, (Ds j) u) < ∑ j, (As j) u
      rw [← hsumD u, ← hsumA u]
      exact hbl' u hu)
    (by
      intro j2 hj2
      fin_cases j2
      · exact harr
      · exact absurd rfl hj2)
    t
  -- the `Fin 2` erase in `h` carries the scoped classical instance, so
  -- the cross-constraint sum is evaluated by the instance-agnostic
  -- conditional `Finset.sum_erase` (its `f 1 = 0` side condition is
  -- discharged by the matrix reductions in the same simp set)
  simp only [Finset.sum_erase, Matrix.cons_val_one,
    Matrix.cons_val_zero, Fin.sum_univ_two, add_zero,
    Curve.coe_sum, Curve.sum_apply] at h
  exact h

/-- **The cross-traffic departures allow the deconvolved bound**: under
a strict aggregate with `αⱼ`-constrained arrivals, the cross-traffic
aggregate output of flow `i` allows `(∑_{j≠i} αⱼ) ⊘ [β − αᵢ]⁺↑` as a
maximal arrival bound (`ℝ≥0∞` reading). -/
theorem isMaximalArrivalBound_output_erase_sum_of_strict_aggregate
    {ι : Type*} [Fintype ι] {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    {i : ι} (harr : ∀ j, IsMaximalArrivalBound ⇑(As j) (α j)) :
    IsMaximalArrivalBound
      (Deviation.liftENN (fun x => ∑ j ∈ Finset.univ.erase i, (Ds j) x))
      (minDeconv
        (Deviation.liftENN (fun v => ∑ j ∈ Finset.univ.erase i, α j v))
        (Deviation.liftENN (residualCurve β (α i)))) := by
  -- the complement pair sits in the residual's min-plus service relation
  have hp : minimalServiceRel (liftEReal (residualCurve β (α i)))
      (∑ j ∈ Finset.univ.erase i, As j)
      (∑ j ∈ Finset.univ.erase i, Ds j) := by
    refine mem_minimalServiceRel_iff.mpr ⟨?_, ?_⟩
    · intro u
      rw [Curve.sum_apply, Curve.sum_apply]
      exact Finset.sum_le_sum fun j _ => hc j u
    · intro t
      have h := minConv_residualCurve_le_erase_sum_of_strict_aggregate
        hc hstrict (harr i) t
      rw [show Deviation.liftENN (residualCurve β (α i))
            = Deviation.toENN (liftEReal (residualCurve β (α i)))
          from (Deviation.toENN_liftEReal _).symm,
        ← Curve.coe_sum] at h
      rw [curveEReal_apply, Curve.sum_apply]
      exact (Deviation.minConv_toENN_le_coe_iff _
        (isNonneg_liftEReal _) _ t).mp h
  -- the complement arrivals are bounded by the summed constraints
  have harru : IsMaximalArrivalBound
      (Deviation.liftENN ⇑(∑ j ∈ Finset.univ.erase i, As j))
      (Deviation.liftENN
        (fun v => ∑ j ∈ Finset.univ.erase i, α j v)) := by
    rw [Curve.coe_sum]
    exact Deviation.isMaximalArrivalBound_liftENN_iff.mpr
      (isMaximalArrivalBound_sum _ fun j _ => harr j)
  have hout := isMaximalArrivalBound_output_of_isMinimalServiceCurve
    (fun A D hAD => curveEReal_le_iff.mp hAD.1)
    (isMinimalServiceCurve_minimalServiceRel _)
    (isNonneg_liftEReal _) hp harru
  rwa [Deviation.toENN_liftEReal, Curve.coe_sum] at hout

/-- **Strict residual from arrival curves alone** (the book's
corollary, pair level): with every flow `αⱼ`-constrained, any curve
`α'` dominating the sub-additive closure of the deconvolved
cross-traffic bound `((∑_{j≠i} αⱼ) ⊘ [β − αᵢ]⁺↑)*` yields the strict
residual `[β − α']⁺↑` for flow `i`. -/
theorem add_residualCurve_le_of_strict_aggregate_of_closure_le
    {ι : Type*} [Fintype ι] {As Ds : ι → Curve} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0} {α' : ℝ≥0 → ℝ≥0}
    (hc : ∀ j, Ds j ≤ As j)
    (hstrict : ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (As j) x) (fun x => ∑ j, (Ds j) x)
        (Set.Ioc s t) →
      (∑ j, (Ds j) s) + β (t - s) ≤ ∑ j, (Ds j) t)
    {i : ι} (harr : ∀ j, IsMaximalArrivalBound ⇑(As j) (α j))
    (hdom : ∀ v, subadditiveClosureENN
        (minDeconv
          (Deviation.liftENN
            (fun v => ∑ j ∈ Finset.univ.erase i, α j v))
          (Deviation.liftENN (residualCurve β (α i)))) v
      ≤ ((α' v : ℝ≥0) : ℝ≥0∞))
    {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t)) :
    (Ds i) s + residualCurve β α' (t - s) ≤ (Ds i) t := by
  refine add_residualCurve_le_of_strict_aggregate hc hstrict ?_ hst hbl
  rw [← Deviation.isMaximalArrivalBound_liftENN_iff]
  exact ((isMaximalArrivalBound_output_erase_sum_of_strict_aggregate
    hc hstrict harr).subadditiveClosureENN).mono hdom

/-- **The book's corollary, relation form**: an `n`-server with a
strict aggregate curve, restricted to pairs whose flows are all
`αⱼ`-constrained, offers flow `i` the strict residual `[β − α']⁺↑` for
any `α'` dominating the closed deconvolved bound. -/
theorem isStrictMinimalServiceCurve_residualServer_of_closure_le
    {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {β : ℝ≥0 → ℝ≥0}
    {α : ι → ℝ≥0 → ℝ≥0} {α' : ℝ≥0 → ℝ≥0} {i : ι}
    (hcaus : IsCausalN S)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    (hdom : ∀ v, subadditiveClosureENN
        (minDeconv
          (Deviation.liftENN
            (fun v => ∑ j ∈ Finset.univ.erase i, α j v))
          (Deviation.liftENN (residualCurve β (α i)))) v
      ≤ ((α' v : ℝ≥0) : ℝ≥0∞)) :
    IsStrictMinimalServiceCurve (residualCurve β α')
      (residualServer (fun A D => S A D ∧
        ∀ j, IsMaximalArrivalBound ⇑(A j) (α j)) i) := by
  rintro Ai Di ⟨As, Ds, ⟨hp, harr⟩, rfl, rfl⟩ s t hst hbl
  refine add_residualCurve_le_of_strict_aggregate_of_closure_le
    (fun j => hcaus As Ds hp j) ?_ harr hdom hst hbl
  exact hβ.sum_strict hp

/-! ## Book restatement (strict residual from arrival curves)
An `n`-server offering a strict service curve `β` whose arrival
processes all have arrival curves `αⱼ` offers flow `i` the strict
residual `βᵢ = [β − ((∑_{j≠i} αⱼ) ⊘ [β − αᵢ]⁺↑)*]⁺↑` — stated for any
`ℝ≥0`-valued `α'` dominating the (`ℝ≥0∞`-valued) closed deconvolution,
which is the bracketed curve of the book's formula whenever it is
finite. -/
example {ι : Type*} [Fintype ι]
    {S : (ι → Curve) → (ι → Curve) → Prop} {As Ds : ι → Curve}
    {β : ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0} {α' : ℝ≥0 → ℝ≥0}
    (hSrv : IsServerN S) (hp : S As Ds)
    (hβ : IsStrictMinimalServiceCurve β (aggregateServer S))
    {i : ι} (harr : ∀ j, IsMaximalArrivalCurve ⇑(As j) (α j))
    (hdom : ∀ v, subadditiveClosureENN
        (minDeconv
          (Deviation.liftENN
            (fun v => ∑ j ∈ Finset.univ.erase i, α j v))
          (Deviation.liftENN (residualCurve β (α i)))) v
      ≤ ((α' v : ℝ≥0) : ℝ≥0∞))
    {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged ⇑(As i) ⇑(Ds i) (Set.Ioc s t)) :
    (Ds i) s + residualCurve β α' (t - s) ≤ (Ds i) t :=
  add_residualCurve_le_of_strict_aggregate_of_closure_le
    (fun j => hSrv.1 As Ds hp j)
    (hβ.sum_strict hp)
    (fun j => (harr j).2) hdom hst hbl

end DeepWiki
