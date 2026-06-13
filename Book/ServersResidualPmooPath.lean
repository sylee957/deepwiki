import Book.ServersResidualPmooChain

/-! # Per-path PMOO residual (general blind-multiplexing operator)
The pay-multiplexing-only-once residual for a tandem in which each
cross-flow crosses a *contiguous sub-path* rather than the whole line.
Splitting the time `t` across the hops as `∑_{h≤n} uₕ = t`, the tagged
flow receives
`[ ∑ₕ β⁽ʰ⁾(uₕ) − ∑ᵢ αᵢ(∑_{h∈pᵢ} uₕ) ]⁺`,
the infimum over splits of the aggregate strict service less each
cross-flow's arrival charged *only over the hops on its own path*
(`pmooPathResidual`). The `ℝ≥0` truncated subtraction is the positive
part. The all-crossing case (every path the full line) collapses the
sub-path sums to the whole split and recovers `pmooResidualChain`
(`pathHops_univ_sum`). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Finset

/-- The hops on flow `i`'s contiguous sub-path `[fst i, lst i]` within the
line `0..n`. -/
def pathHops {m : ℕ} (n : ℕ) (fst lst : Fin m → ℕ) (i : Fin m) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun h => fst i ≤ h ∧ h ≤ lst i)

/-- The per-split body: the aggregate strict service `∑ₕ β⁽ʰ⁾(uₕ)` less
each cross-flow's arrival charged over the time on its own sub-path; the
`ℝ≥0` truncated subtraction is the `[·]⁺`. -/
noncomputable def pmooPathBody {m : ℕ} (n : ℕ)
    (β : ℕ → ℝ≥0 → ℝ≥0) (α : Fin m → ℝ≥0 → ℝ≥0) (fst lst : Fin m → ℕ)
    (u : ℕ → ℝ≥0) : ℝ≥0 :=
  (∑ h ∈ Finset.range (n + 1), β h (u h))
    - (∑ i, α i (∑ h ∈ pathHops n fst lst i, u h))

/-- **The per-path PMOO residual**: the infimum of `pmooPathBody` over the
time splits `∑_{h≤n} uₕ = t`. -/
noncomputable def pmooPathResidual {m : ℕ} (n : ℕ)
    (β : ℕ → ℝ≥0 → ℝ≥0) (α : Fin m → ℝ≥0 → ℝ≥0) (fst lst : Fin m → ℕ) :
    ℝ≥0 → ℝ≥0 :=
  fun t => ⨅ u : {u : ℕ → ℝ≥0 // ∑ h ∈ Finset.range (n + 1), u h = t},
    pmooPathBody n β α fst lst u.1

/-- Every prefix `t` admits the split concentrating all mass at hop `0`,
so the infimum defining `pmooPathResidual` is over a nonempty set. -/
instance pmooSplitNonempty {n : ℕ} {t : ℝ≥0} :
    Nonempty {u : ℕ → ℝ≥0 // ∑ h ∈ Finset.range (n + 1), u h = t} :=
  ⟨⟨fun h => if h = 0 then t else 0, by
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) 0 (fun _ => t)]
    simp⟩⟩

/-- `pmooPathResidual` is the infimum of the bodies over the splits. -/
theorem pmooPathResidual_apply {m : ℕ} (n : ℕ)
    (β : ℕ → ℝ≥0 → ℝ≥0) (α : Fin m → ℝ≥0 → ℝ≥0) (fst lst : Fin m → ℕ)
    (t : ℝ≥0) :
    pmooPathResidual n β α fst lst t
      = ⨅ u : {u : ℕ → ℝ≥0 // ∑ h ∈ Finset.range (n + 1), u h = t},
          pmooPathBody n β α fst lst u.1 := rfl

/-- Elim: each split's body bounds `pmooPathResidual` from below. -/
theorem pmooPathResidual_le {m : ℕ} {n : ℕ}
    {β : ℕ → ℝ≥0 → ℝ≥0} {α : Fin m → ℝ≥0 → ℝ≥0} {fst lst : Fin m → ℕ}
    {t : ℝ≥0} {u : ℕ → ℝ≥0} (hu : ∑ h ∈ Finset.range (n + 1), u h = t) :
    pmooPathResidual n β α fst lst t ≤ pmooPathBody n β α fst lst u :=
  ciInf_le_of_le (OrderBot.bddBelow _) ⟨u, hu⟩ le_rfl

/-- Intro: a lower bound on every split's body bounds `pmooPathResidual`. -/
theorem le_pmooPathResidual {m : ℕ} {n : ℕ}
    {β : ℕ → ℝ≥0 → ℝ≥0} {α : Fin m → ℝ≥0 → ℝ≥0} {fst lst : Fin m → ℕ}
    {t x : ℝ≥0}
    (h : ∀ u : ℕ → ℝ≥0, ∑ h ∈ Finset.range (n + 1), u h = t →
      x ≤ pmooPathBody n β α fst lst u) :
    x ≤ pmooPathResidual n β α fst lst t :=
  le_ciInf fun u => h u.1 u.2

/-- `pmooPathResidual … 0 = 0` when every hop curve is null at the origin:
the only split of `0` is all-zero, whose body is `0`. -/
theorem pmooPathResidual_zero_eq {m : ℕ} {n : ℕ}
    {β : ℕ → ℝ≥0 → ℝ≥0} (α : Fin m → ℝ≥0 → ℝ≥0) (fst lst : Fin m → ℕ)
    (hβ0 : ∀ h, β h 0 = 0) :
    pmooPathResidual n β α fst lst 0 = 0 := by
  refine le_antisymm ?_ zero_le'
  refine le_trans (pmooPathResidual_le (u := fun _ => 0) (by simp)) ?_
  show (∑ h ∈ Finset.range (n + 1), β h 0)
      - (∑ i, α i (∑ _h ∈ pathHops n fst lst i, (0 : ℝ≥0))) ≤ 0
  rw [Finset.sum_congr rfl (fun h _ => hβ0 h), Finset.sum_const_zero, zero_tsub]

/-- For a path ending within the line (`lst i ≤ n`) the hop set is the
integer interval `[fst i, lst i]`. -/
theorem pathHops_eq_Ico {m : ℕ} {n : ℕ} {fst lst : Fin m → ℕ} {i : Fin m}
    (hi : lst i ≤ n) :
    pathHops n fst lst i = Finset.Ico (fst i) (lst i + 1) := by
  ext h
  simp only [pathHops, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
    Nat.lt_succ_iff]
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2.trans hi, h1, h2⟩

/-- All-crossing collapse: a flow whose path is the whole line
(`fst i = 0`, `n ≤ lst i`) is charged over the entire split,
`∑_{h∈pᵢ} uₕ = ∑_{h≤n} uₕ`. -/
theorem pathHops_univ_sum {m : ℕ} {n : ℕ} {fst lst : Fin m → ℕ} {i : Fin m}
    (h0 : fst i = 0) (hn : n ≤ lst i) (u : ℕ → ℝ≥0) :
    (∑ h ∈ pathHops n fst lst i, u h) = ∑ h ∈ Finset.range (n + 1), u h := by
  apply Finset.sum_congr _ (fun _ _ => rfl)
  refine Finset.filter_true_of_mem fun h hh => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hh
  exact ⟨h0 ▸ Nat.zero_le h, hh.trans hn⟩

/-- **Layer-2 gateway**: the restricted-aggregate start-equality. At the
backlogged-period start of the `s'`-aggregate, every member `i ∈ s'` is
fully served, `Dᵢ(start) = Aᵢ(start)` — `apply_start_sum_eq` over an
arbitrary flow set rather than `univ`. -/
theorem apply_start_sum_finset_eq {ι : Type*}
    {A D : ι → ℝ≥0 → ℝ≥0} (s' : Finset ι) (hc : ∀ j x, D j x ≤ A j x)
    (hAlc : ∀ j, IsLeftContinuous (A j)) (hDlc : ∀ j, IsLeftContinuous (D j))
    (h0 : ∀ j, A j 0 = D j 0) (t : ℝ≥0) {i : ι} (hi : i ∈ s') :
    D i (start (fun x => ∑ j ∈ s', A j x) (fun x => ∑ j ∈ s', D j x) t)
      = A i (start (fun x => ∑ j ∈ s', A j x) (fun x => ∑ j ∈ s', D j x) t) := by
  set s₀ := start (fun x => ∑ j ∈ s', A j x) (fun x => ∑ j ∈ s', D j x) t
  have haggeq : (∑ j ∈ s', A j s₀) = ∑ j ∈ s', D j s₀ :=
    apply_start_eq
      (isLeftContinuous_sum _ fun j _ => hAlc j)
      (isLeftContinuous_sum _ fun j _ => hDlc j)
      (by show (∑ j ∈ s', A j 0) = ∑ j ∈ s', D j 0
          exact Finset.sum_congr rfl fun j _ => h0 j)
      (fun x => Finset.sum_le_sum fun j _ => hc j x) t
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hc j s₀)).mp haggeq.symm i hi

/-! ## The cascade witness's widths (pure facts about a monotone node family)
For a nondecreasing node sequence `s : ℕ → ℝ≥0` (the cascaded per-hop
starts, with `s (n+1) = t`), the hop widths `uₕ = s (h+1) − s h` split `t`
and telescope; the chain convolution of the gap is bounded by the sum of
the hops applied to the widths. These feed the per-path assembly with the
cascaded starts as the witness split. -/

/-- The hop widths sum to the total gap: `∑_{h≤n} (s(h+1) − sₕ) = s(n+1) − s 0`. -/
theorem sum_range_width_telescope {s : ℕ → ℝ≥0} (hs : Monotone s) (n : ℕ) :
    (∑ h ∈ Finset.range (n + 1), (s (h + 1) - s h)) = s (n + 1) - s 0 := by
  induction n with
  | zero => rw [Finset.sum_range_one]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, add_comm,
      tsub_add_tsub_cancel (hs (Nat.le_succ _)) (hs (Nat.zero_le _))]

/-- The widths over a flow's contiguous window telescope to the gap across
that window: `∑_{h∈[a,b)} (s(h+1) − sₕ) = s b − s a`. -/
theorem sum_Ico_width_telescope {s : ℕ → ℝ≥0} (hs : Monotone s) :
    ∀ {a b : ℕ}, a ≤ b →
      (∑ h ∈ Finset.Ico a b, (s (h + 1) - s h)) = s b - s a := by
  intro a b
  induction b with
  | zero => intro hab; rw [Nat.le_zero.mp hab]; simp
  | succ b ih =>
    intro hab
    rcases eq_or_lt_of_le hab with rfl | h
    · simp
    · have hab' : a ≤ b := Nat.lt_succ_iff.mp h
      rw [Finset.sum_Ico_succ_top hab', ih hab', add_comm,
        tsub_add_tsub_cancel (hs (Nat.le_succ b)) (hs hab')]

/-- **Layer 1**: the chain convolution of the total gap is bounded by the
sum of the hop curves applied to the hop widths,
`chainConv β n (s(n+1) − s 0) ≤ ∑_{h≤n} β⁽ʰ⁾(s(h+1) − sₕ)`, for any
nondecreasing node sequence `s`. The peel step splits the top width off
the convolution. -/
theorem chainConv_le_sum_widths {β : ℕ → ℝ≥0 → ℝ≥0} {s : ℕ → ℝ≥0}
    (hs : Monotone s) (n : ℕ) :
    chainConv β n (s (n + 1) - s 0)
      ≤ ∑ h ∈ Finset.range (n + 1), β h (s (h + 1) - s h) := by
  induction n with
  | zero => simp [chainConv_zero]
  | succ n ih =>
    rw [chainConv_succ]
    have hsplit : (s (n + 1) - s 0) + (s (n + 2) - s (n + 1)) = s (n + 2) - s 0 := by
      rw [add_comm]
      exact tsub_add_tsub_cancel (hs (Nat.le_succ _)) (hs (Nat.zero_le _))
    calc minConvProj (chainConv β n) (β (n + 1)) (s (n + 2) - s 0)
        ≤ chainConv β n (s (n + 1) - s 0)
            + β (n + 1) (s (n + 2) - s (n + 1)) := minConvProj_le_add hsplit
      _ ≤ (∑ h ∈ Finset.range (n + 1), β h (s (h + 1) - s h))
            + β (n + 1) (s (n + 2) - s (n + 1)) := add_le_add ih le_rfl
      _ = ∑ h ∈ Finset.range (n + 2), β h (s (h + 1) - s h) :=
          (Finset.sum_range_succ (fun h => β h (s (h + 1) - s h)) (n + 1)).symm

/-! ## The cascade node sequence and the per-hop strict step
The hop-indexed cascade `pathNode`: descending from the top `sₙ₊₁ = t`,
each node is the backlogged-period start of its hop's flow-set aggregate,
`sₕ = start_{Fl h}(sₕ₊₁)`. The widths `uₕ = sₕ₊₁ − sₕ` are the witness
split. The per-hop strict step `pathNode_strict_step` is the book's
inequality [10.2] read at the cascade: the flow-set aggregate input at
`sₕ` plus `β⁽ʰ⁾(uₕ)` is dominated by the output at `sₕ₊₁`. -/

/-- The hop-indexed cascade node: `sₕ = start_{S h}(sₕ₊₁)` for `h ≤ n`,
`sₕ = t` above the top. -/
noncomputable def pathNode {ι : Type*} [Fintype ι] (F : ℕ → ι → Curve)
    (S : ℕ → Finset ι) (n : ℕ) (t : ℝ≥0) : ℕ → ℝ≥0
  | h => if h_le : h ≤ n then
           start (fun x => ∑ j ∈ S h, (F h j) x)
             (fun x => ∑ j ∈ S h, (F (h + 1) j) x) (pathNode F S n t (h + 1))
         else t
  termination_by h => n + 1 - h
  decreasing_by omega

/-- `pathNode` descends one hop by the flow-set aggregate start (`h ≤ n`). -/
theorem pathNode_eq {ι : Type*} [Fintype ι] (F : ℕ → ι → Curve)
    (S : ℕ → Finset ι) (n : ℕ) (t : ℝ≥0) {h : ℕ} (hh : h ≤ n) :
    pathNode F S n t h
      = start (fun x => ∑ j ∈ S h, (F h j) x)
          (fun x => ∑ j ∈ S h, (F (h + 1) j) x) (pathNode F S n t (h + 1)) := by
  rw [pathNode.eq_def, dif_pos hh]

/-- Above the top hop `pathNode` is the time itself. -/
theorem pathNode_top {ι : Type*} [Fintype ι] (F : ℕ → ι → Curve)
    (S : ℕ → Finset ι) (n : ℕ) (t : ℝ≥0) {h : ℕ} (hh : ¬ h ≤ n) :
    pathNode F S n t h = t := by
  rw [pathNode.eq_def, dif_neg hh]

/-- The top node `sₙ₊₁` is `t`. -/
theorem pathNode_succ {ι : Type*} [Fintype ι] (F : ℕ → ι → Curve)
    (S : ℕ → Finset ι) (n : ℕ) (t : ℝ≥0) :
    pathNode F S n t (n + 1) = t :=
  pathNode_top F S n t (by omega)

/-- Each node sits at or before the next (the start descends). -/
theorem pathNode_le_succ {ι : Type*} [Fintype ι] (F : ℕ → ι → Curve)
    (S : ℕ → Finset ι) (n : ℕ) (t : ℝ≥0) (h : ℕ) :
    pathNode F S n t h ≤ pathNode F S n t (h + 1) := by
  by_cases hh : h ≤ n
  · rw [pathNode_eq F S n t hh]; exact start_le _ _ _
  · rw [pathNode_top F S n t hh, pathNode_top F S n t (by omega)]

/-- The cascade nodes are nondecreasing in the hop index. -/
theorem pathNode_mono {ι : Type*} [Fintype ι] (F : ℕ → ι → Curve)
    (S : ℕ → Finset ι) (n : ℕ) (t : ℝ≥0) : Monotone (pathNode F S n t) :=
  monotone_nat_of_le_succ (pathNode_le_succ F S n t)

/-- **The per-hop strict step** (book inequality [10.2] at the cascade):
the flow-set aggregate input at `sₕ` plus `β⁽ʰ⁾(uₕ)` is dominated by the
output at `sₕ₊₁`. The aggregate is backlogged on `(sₕ, sₕ₊₁]` (its own
start window) and every member is fully served at `sₕ`. -/
theorem pathNode_strict_step {ι : Type*} [Fintype ι] {F : ℕ → ι → Curve}
    {S : ℕ → Finset ι} {β : ℕ → ℝ≥0 → ℝ≥0} {n : ℕ} (t : ℝ≥0)
    (hc : ∀ h, h ≤ n → ∀ j, F (h + 1) j ≤ F h j)
    (hstrict : ∀ h, h ≤ n → ∀ s t', s ≤ t' →
      IsBacklogged (fun x => ∑ j ∈ S h, (F h j) x)
        (fun x => ∑ j ∈ S h, (F (h + 1) j) x) (Set.Ioc s t') →
      (∑ j ∈ S h, (F (h + 1) j) s) + β h (t' - s) ≤ ∑ j ∈ S h, (F (h + 1) j) t')
    {h : ℕ} (hh : h ≤ n) :
    (∑ j ∈ S h, (F h j) (pathNode F S n t h))
        + β h (pathNode F S n t (h + 1) - pathNode F S n t h)
      ≤ ∑ j ∈ S h, (F (h + 1) j) (pathNode F S n t (h + 1)) := by
  set s := pathNode F S n t h with hsdef
  set t' := pathNode F S n t (h + 1) with htdef
  have hst : s ≤ t' := pathNode_le_succ F S n t h
  have hseq : s = start (fun x => ∑ j ∈ S h, (F h j) x)
      (fun x => ∑ j ∈ S h, (F (h + 1) j) x) t' := pathNode_eq F S n t hh
  have hcS : ∀ x, (∑ j ∈ S h, (F (h + 1) j) x) ≤ ∑ j ∈ S h, (F h j) x :=
    fun x => Finset.sum_le_sum fun j _ => hc h hh j x
  have hbl : IsBacklogged (fun x => ∑ j ∈ S h, (F h j) x)
      (fun x => ∑ j ∈ S h, (F (h + 1) j) x) (Set.Ioc s t') := by
    rw [hseq]; exact isBacklogged_Ioc_start hcS t'
  have hstr := hstrict h hh s t' hst hbl
  have heq : (∑ j ∈ S h, (F (h + 1) j) s) = ∑ j ∈ S h, (F h j) s := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hseq]
    exact apply_start_sum_finset_eq (S h) (fun k x => hc h hh k x)
      (fun k => (F h k).leftCont) (fun k => (F (h + 1) k).leftCont)
      (fun k => ((F h k).zero).trans ((F (h + 1) k).zero).symm) t' hj
  rw [heq] at hstr
  exact hstr

end DeepWiki
