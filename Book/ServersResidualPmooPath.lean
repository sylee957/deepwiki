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
part. The all-crossing case (every path the full line) collapses each
cross-flow's sub-path sum to the whole split (`pathHops_univ_sum`) — the
key reduction toward the single-`α` chain residual `pmooResidualChain`.
Cumulative functions follow the repo's left-continuous convention (used for
the start-equality of the per-hop step). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Finset

/-- The hops on flow `i`'s contiguous sub-path `[fst i, lst i]` within the
line `0..n`. -/
def pathHops {ι : Type*} (n : ℕ) (fst lst : ι → ℕ) (i : ι) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun h => fst i ≤ h ∧ h ≤ lst i)

/-- The per-split body: the aggregate strict service `∑ₕ β⁽ʰ⁾(uₕ)` less
each cross-flow's arrival charged over the time on its own sub-path; the
`ℝ≥0` truncated subtraction is the `[·]⁺`. -/
noncomputable def pmooPathBody {ι : Type*} [Fintype ι] (n : ℕ)
    (β : ℕ → ℝ≥0 → ℝ≥0) (α : ι → ℝ≥0 → ℝ≥0) (fst lst : ι → ℕ)
    (u : ℕ → ℝ≥0) : ℝ≥0 :=
  (∑ h ∈ Finset.range (n + 1), β h (u h))
    - (∑ i, α i (∑ h ∈ pathHops n fst lst i, u h))

/-- **The per-path PMOO residual**: the infimum of `pmooPathBody` over the
time splits `∑_{h≤n} uₕ = t`. -/
noncomputable def pmooPathResidual {ι : Type*} [Fintype ι] (n : ℕ)
    (β : ℕ → ℝ≥0 → ℝ≥0) (α : ι → ℝ≥0 → ℝ≥0) (fst lst : ι → ℕ) :
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
theorem pmooPathResidual_apply {ι : Type*} [Fintype ι] (n : ℕ)
    (β : ℕ → ℝ≥0 → ℝ≥0) (α : ι → ℝ≥0 → ℝ≥0) (fst lst : ι → ℕ)
    (t : ℝ≥0) :
    pmooPathResidual n β α fst lst t
      = ⨅ u : {u : ℕ → ℝ≥0 // ∑ h ∈ Finset.range (n + 1), u h = t},
          pmooPathBody n β α fst lst u.1 := rfl

/-- Elim: each split's body bounds `pmooPathResidual` from below. -/
theorem pmooPathResidual_le {ι : Type*} [Fintype ι] {n : ℕ}
    {β : ℕ → ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0} {fst lst : ι → ℕ}
    {t : ℝ≥0} {u : ℕ → ℝ≥0} (hu : ∑ h ∈ Finset.range (n + 1), u h = t) :
    pmooPathResidual n β α fst lst t ≤ pmooPathBody n β α fst lst u :=
  ciInf_le_of_le (OrderBot.bddBelow _) ⟨u, hu⟩ le_rfl

/-- Intro: a lower bound on every split's body bounds `pmooPathResidual`. -/
theorem le_pmooPathResidual {ι : Type*} [Fintype ι] {n : ℕ}
    {β : ℕ → ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0} {fst lst : ι → ℕ}
    {t x : ℝ≥0}
    (h : ∀ u : ℕ → ℝ≥0, ∑ h ∈ Finset.range (n + 1), u h = t →
      x ≤ pmooPathBody n β α fst lst u) :
    x ≤ pmooPathResidual n β α fst lst t :=
  le_ciInf fun u => h u.1 u.2

/-- `pmooPathResidual … 0 = 0` when every hop curve is null at the origin:
the only split of `0` is all-zero, whose body is `0`. -/
theorem pmooPathResidual_zero_eq {ι : Type*} [Fintype ι] {n : ℕ}
    {β : ℕ → ℝ≥0 → ℝ≥0} (α : ι → ℝ≥0 → ℝ≥0) (fst lst : ι → ℕ)
    (hβ0 : ∀ h, β h 0 = 0) :
    pmooPathResidual n β α fst lst 0 = 0 := by
  refine le_antisymm ?_ zero_le'
  refine le_trans (pmooPathResidual_le (u := fun _ => 0) (by simp)) ?_
  show (∑ h ∈ Finset.range (n + 1), β h 0)
      - (∑ i, α i (∑ _h ∈ pathHops n fst lst i, (0 : ℝ≥0))) ≤ 0
  rw [Finset.sum_congr rfl (fun h _ => hβ0 h), Finset.sum_const_zero, zero_tsub]

/-- For a path ending within the line (`lst i ≤ n`) the hop set is the
integer interval `[fst i, lst i]`. -/
theorem pathHops_eq_Ico {ι : Type*} {n : ℕ} {fst lst : ι → ℕ} {i : ι}
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
theorem pathHops_univ_sum {ι : Type*} {n : ℕ} {fst lst : ι → ℕ} {i : ι}
    (h0 : fst i = 0) (hn : n ≤ lst i) (u : ℕ → ℝ≥0) :
    (∑ h ∈ pathHops n fst lst i, u h) = ∑ h ∈ Finset.range (n + 1), u h := by
  apply Finset.sum_congr _ (fun _ _ => rfl)
  refine Finset.filter_true_of_mem fun h hh => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hh
  exact ⟨h0 ▸ Nat.zero_le h, hh.trans hn⟩

/-! ## The cascade witness's widths (pure facts about a monotone node family)
For a nondecreasing node sequence `s : ℕ → ℝ≥0` (the cascaded per-hop
starts, with `s (n+1) = t`), the hop widths `uₕ = s (h+1) − s h` split `t`
and telescope — over the whole range and over each flow's contiguous
window. These feed the per-path assembly with the cascaded starts as the
witness split. -/

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

/-- **The per-hop strict step** at the cascade:
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

/-! ## The flow-set telescope (book Lemma 10.1)
Summing the per-hop steps and reorganizing the double sum
`∑ₕ ∑_{j∈Fl h}` into `∑ⱼ ∑_{h∈pᵢ}` (each flow over its own contiguous
path), every flow telescopes over its window: the service `∑ₕ β⁽ʰ⁾(uₕ)`
plus the flows' inputs at their path starts is dominated by the flows'
outputs at their path ends. -/

/-- Additive telescope over a contiguous window: shifting the summand by one
hop trades the bottom term `G a` for the top term `G (b+1)`. -/
theorem pathTelescope_shift (G : ℕ → ℝ≥0) {a b : ℕ} (hab : a ≤ b) :
    (∑ h ∈ Ico a (b + 1), G (h + 1)) + G a
      = (∑ h ∈ Ico a (b + 1), G h) + G (b + 1) := by
  have hRHS : (∑ h ∈ Ico a (b + 1), G h) + G (b + 1) = ∑ h ∈ Ico a (b + 2), G h :=
    (Finset.sum_Ico_succ_top (by omega) G).symm
  have hreindex : (∑ h ∈ Ico a (b + 1), G (h + 1)) = ∑ h ∈ Ico (a + 1) (b + 2), G h := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr (by congr 1; omega)
    intro k _; congr 1; omega
  rw [hRHS, hreindex, add_comm _ (G a),
    Finset.sum_eq_sum_Ico_succ_bot (show a < b + 2 by omega) G]

/-- **The flow-set telescope**: with flow sets
`S h = {j | fst j ≤ h ≤ lst j}` (linked by `hS`), causality `hc`, the
per-hop strict bounds `hstrict`, and contiguous in-line paths `hpath`,
the cascaded service plus the flows' inputs at their path starts is
dominated by the flows' outputs at their path ends:
`∑ₕ β⁽ʰ⁾(uₕ) + ∑ⱼ Fⱼ^{fst}(s_{fst}) ≤ ∑ⱼ Fⱼ^{lst+1}(s_{lst+1})`. -/
theorem sum_add_pathTelescope_le {ι : Type*} [Fintype ι] {F : ℕ → ι → Curve}
    {β : ℕ → ℝ≥0 → ℝ≥0} {S : ℕ → Finset ι} {fst lst : ι → ℕ} {n : ℕ} (t : ℝ≥0)
    (hS : ∀ h j, j ∈ S h ↔ (fst j ≤ h ∧ h ≤ lst j))
    (hc : ∀ h, h ≤ n → ∀ j, F (h + 1) j ≤ F h j)
    (hstrict : ∀ h, h ≤ n → ∀ s t', s ≤ t' →
      IsBacklogged (fun x => ∑ j ∈ S h, (F h j) x)
        (fun x => ∑ j ∈ S h, (F (h + 1) j) x) (Set.Ioc s t') →
      (∑ j ∈ S h, (F (h + 1) j) s) + β h (t' - s) ≤ ∑ j ∈ S h, (F (h + 1) j) t')
    (hpath : ∀ j, fst j ≤ lst j ∧ lst j ≤ n) :
    (∑ h ∈ range (n + 1), β h (pathNode F S n t (h + 1) - pathNode F S n t h))
      + ∑ j, (F (fst j) j) (pathNode F S n t (fst j))
    ≤ ∑ j, (F (lst j + 1) j) (pathNode F S n t (lst j + 1)) := by
  set node := pathNode F S n t with hnode
  set P := ∑ j, ∑ h ∈ pathHops n fst lst j, (F h j) (node h) with hP
  set Q := ∑ j, ∑ h ∈ pathHops n fst lst j, (F (h + 1) j) (node (h + 1)) with hQ
  have hequiv : ∀ (h : ℕ) (j : ι),
      h ∈ range (n + 1) ∧ j ∈ S h ↔ h ∈ pathHops n fst lst j ∧ j ∈ (univ : Finset ι) := by
    intro h j
    simp only [Finset.mem_range, Finset.mem_univ, and_true, pathHops, Finset.mem_filter,
      hS h j]
  have step1 : P + (∑ h ∈ range (n + 1), β h (node (h + 1) - node h)) ≤ Q := by
    have hsum : (∑ h ∈ range (n + 1), (∑ j ∈ S h, (F h j) (node h)))
                 + ∑ h ∈ range (n + 1), β h (node (h + 1) - node h)
               ≤ ∑ h ∈ range (n + 1), ∑ j ∈ S h, (F (h + 1) j) (node (h + 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro h hh
      exact pathNode_strict_step t hc hstrict (Nat.lt_succ_iff.mp (Finset.mem_range.mp hh))
    rwa [Finset.sum_comm' hequiv (f := fun h j => (F h j) (node h)),
      Finset.sum_comm' hequiv (f := fun h j => (F (h + 1) j) (node (h + 1)))] at hsum
  have telsum : Q + ∑ j, (F (fst j) j) (node (fst j))
              = P + ∑ j, (F (lst j + 1) j) (node (lst j + 1)) := by
    rw [hP, hQ, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [pathHops_eq_Ico (hpath j).2]
    exact pathTelescope_shift (fun h => (F h j) (node h)) (hpath j).1
  have key : P + ((∑ h ∈ range (n + 1), β h (node (h + 1) - node h))
              + ∑ j, (F (fst j) j) (node (fst j)))
            ≤ P + ∑ j, (F (lst j + 1) j) (node (lst j + 1)) :=
    calc P + ((∑ h ∈ range (n + 1), β h (node (h + 1) - node h))
              + ∑ j, (F (fst j) j) (node (fst j)))
        = (P + ∑ h ∈ range (n + 1), β h (node (h + 1) - node h))
            + ∑ j, (F (fst j) j) (node (fst j)) := by ring
      _ ≤ Q + ∑ j, (F (fst j) j) (node (fst j)) := add_le_add step1 le_rfl
      _ = P + ∑ j, (F (lst j + 1) j) (node (lst j + 1)) := telsum
  exact le_of_add_le_add_left key

/-! ## Assembly: the general per-path PMOO service curve (book Theorem 10.1)
The telescope bounds the tagged flow's service by the cascaded
`∑ₕ β⁽ʰ⁾(uₕ)` less each cross-flow's arrival over its own sub-path; the
operator is the infimum over splits, reached at the cascade widths. -/

/-- Causality chained over a flow's contiguous path: `Fⱼ^{b+1}(x) ≤ Fⱼ^a(x)`
for `a ≤ b ≤ n` (output after the path at most input before it). -/
theorem causality_fold {ι : Type*} {F : ℕ → ι → Curve} {n : ℕ}
    (hc : ∀ h, h ≤ n → ∀ j, F (h + 1) j ≤ F h j) (j : ι) (x : ℝ≥0) :
    ∀ {a b : ℕ}, a ≤ b → b ≤ n → (F (b + 1) j) x ≤ (F a j) x := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => intro hbn; exact hc a hbn j x
  | succ b hab ih => intro hbn; exact le_trans (hc (b + 1) hbn j x) (ih (by omega))

/-- **The tagged-flow floor**: a flow crossing every hop is at most as far
along at the cascade bottom (input) as at the top (output),
`F⁰_tg(s₀) ≤ Fⁿ⁺¹_tg(t)` — full service at each cascade start plus
monotonicity. -/
theorem pathNode_floor {ι : Type*} [Fintype ι] {F : ℕ → ι → Curve} {S : ℕ → Finset ι}
    {fst lst : ι → ℕ} {n : ℕ} (t : ℝ≥0) {tg : ι}
    (hS : ∀ h j, j ∈ S h ↔ (fst j ≤ h ∧ h ≤ lst j))
    (hc : ∀ h, h ≤ n → ∀ j, F (h + 1) j ≤ F h j)
    (htgfst : fst tg = 0) (htglst : lst tg = n) :
    (F 0 tg) (pathNode F S n t 0) ≤ (F (n + 1) tg) (pathNode F S n t (n + 1)) := by
  set node := pathNode F S n t with hnode
  have htgmem : ∀ h, h ≤ n → tg ∈ S h := fun h hh =>
    (hS h tg).mpr ⟨htgfst ▸ Nat.zero_le h, htglst ▸ hh⟩
  have hstep : ∀ h, h ≤ n → (F h tg) (node h) ≤ (F (h + 1) tg) (node (h + 1)) := by
    intro h hh
    have heq : (F (h + 1) tg) (node h) = (F h tg) (node h) := by
      rw [hnode, pathNode_eq F S n t hh]
      exact apply_start_sum_finset_eq (S h) (fun k x => hc h hh k x)
        (fun k => (F h k).leftCont) (fun k => (F (h + 1) k).leftCont)
        (fun k => ((F h k).zero).trans ((F (h + 1) k).zero).symm) _ (htgmem h hh)
    calc (F h tg) (node h) = (F (h + 1) tg) (node h) := heq.symm
      _ ≤ (F (h + 1) tg) (node (h + 1)) := (F (h + 1) tg).mono (pathNode_le_succ F S n t h)
  have hfold : ∀ k, k ≤ n + 1 → (F 0 tg) (node 0) ≤ (F k tg) (node k) := by
    intro k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih => intro hk; exact le_trans (ih (by omega)) (hstep k (by omega))
  exact hfold (n + 1) le_rfl

/-- **The per-path PMOO residual is a service curve for the tagged flow**
(strict aggregates, blind multiplexing): in a tandem
where each cross-flow `j ≠ tg` is `αⱼ`-constrained on its contiguous
sub-path `[fst j, lst j]` and the tagged flow crosses every hop, flow `tg`
obeys the strict service inequality for `pmooPathResidual` from the
cascade bottom. Charging the tagged flow itself is suppressed (`α tg = 0`);
each cross-flow pays once over its own path. -/
theorem add_pmooPathResidual_le_of_strict_path {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ℕ → ι → Curve}
    {β : ℕ → ℝ≥0 → ℝ≥0} {S : ℕ → Finset ι} {α : ι → ℝ≥0 → ℝ≥0}
    {fst lst : ι → ℕ} {n : ℕ} (t : ℝ≥0) {tg : ι}
    (hS : ∀ h j, j ∈ S h ↔ (fst j ≤ h ∧ h ≤ lst j))
    (hc : ∀ h, h ≤ n → ∀ j, F (h + 1) j ≤ F h j)
    (hstrict : ∀ h, h ≤ n → ∀ s t', s ≤ t' →
      IsBacklogged (fun x => ∑ j ∈ S h, (F h j) x) (fun x => ∑ j ∈ S h, (F (h + 1) j) x)
        (Set.Ioc s t') →
      (∑ j ∈ S h, (F (h + 1) j) s) + β h (t' - s) ≤ ∑ j ∈ S h, (F (h + 1) j) t')
    (hpath : ∀ j, fst j ≤ lst j ∧ lst j ≤ n)
    (harr : ∀ j, j ≠ tg → IsMaximalArrivalBound (F (fst j) j) (α j))
    (htgfst : fst tg = 0) (htglst : lst tg = n) (hαtg : α tg = 0) :
    (F 0 tg) (pathNode F S n t 0)
        + pmooPathResidual n β α fst lst (t - pathNode F S n t 0)
      ≤ (F (n + 1) tg) t := by
  set node := pathNode F S n t with hnode
  have hmono := pathNode_mono F S n t
  have hsumu : ∑ h ∈ range (n + 1), (node (h + 1) - node h) = t - node 0 := by
    have h := sum_range_width_telescope hmono n
    rwa [pathNode_succ F S n t] at h
  have hwin : ∀ i, (∑ h ∈ pathHops n fst lst i, (node (h + 1) - node h))
      = node (lst i + 1) - node (fst i) := fun i => by
    rw [pathHops_eq_Ico (hpath i).2]
    exact sum_Ico_width_telescope hmono (le_trans (hpath i).1 (Nat.le_succ _))
  have htel := sum_add_pathTelescope_le (β := β) t hS hc hstrict hpath
  have hcross : ∀ j ∈ univ.erase tg,
      (F (lst j + 1) j) (node (lst j + 1))
        ≤ (F (fst j) j) (node (fst j)) + α j (node (lst j + 1) - node (fst j)) := by
    intro j hj
    have hjtg : j ≠ tg := Finset.ne_of_mem_erase hj
    have harr' := (isMaximalArrivalBound_iff_increment _ _).mp (harr j hjtg)
      (node (fst j)) (node (lst j + 1) - node (fst j))
    rw [add_tsub_cancel_of_le (hmono (le_trans (hpath j).1 (Nat.le_succ _)))] at harr'
    exact le_trans (causality_fold hc j _ (hpath j).1 (hpath j).2) harr'
  refine le_trans (add_le_add le_rfl
    (pmooPathResidual_le (β := β) (α := α) (fst := fst) (lst := lst) hsumu)) ?_
  have hbody : pmooPathBody n β α fst lst (fun h => node (h + 1) - node h)
      = (∑ h ∈ range (n + 1), β h (node (h + 1) - node h))
        - (∑ i, α i (node (lst i + 1) - node (fst i))) := by
    rw [pmooPathBody]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hwin i]
  rw [hbody]
  set B := ∑ h ∈ range (n + 1), β h (node (h + 1) - node h) with hB
  set X := ∑ i, α i (node (lst i + 1) - node (fst i)) with hX
  have hnt : node (n + 1) = t := pathNode_succ F S n t
  have hclub : B + (F 0 tg) (node 0) ≤ (F (n + 1) tg) t + X := by
    rw [← Finset.add_sum_erase univ (fun j => (F (fst j) j) (node (fst j))) (mem_univ tg),
        ← Finset.add_sum_erase univ (fun j => (F (lst j + 1) j) (node (lst j + 1)))
          (mem_univ tg), htgfst, htglst, hnt] at htel
    have hXsplit : X = ∑ j ∈ univ.erase tg, α j (node (lst j + 1) - node (fst j)) := by
      rw [hX, ← Finset.add_sum_erase univ (fun j => α j (node (lst j + 1) - node (fst j)))
        (mem_univ tg), hαtg]
      simp
    have hcrosssum : (∑ j ∈ univ.erase tg, (F (lst j + 1) j) (node (lst j + 1)))
        ≤ (∑ j ∈ univ.erase tg, (F (fst j) j) (node (fst j)))
          + ∑ j ∈ univ.erase tg, α j (node (lst j + 1) - node (fst j)) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum hcross
    rw [hXsplit, ← NNReal.coe_le_coe]
    have h1 := NNReal.coe_le_coe.mpr htel
    have h2 := NNReal.coe_le_coe.mpr hcrosssum
    push_cast at h1 h2 ⊢
    linarith
  have hfloor : (F 0 tg) (node 0) ≤ (F (n + 1) tg) t := by
    have h := pathNode_floor (F := F) (S := S) t hS hc htgfst htglst
    rwa [pathNode_succ F S n t] at h
  rcases le_total X B with hXB | hBX
  · rw [← NNReal.coe_le_coe]
    have hc' := NNReal.coe_le_coe.mpr hclub
    push_cast [NNReal.coe_sub hXB] at hc' ⊢
    linarith
  · rw [tsub_eq_zero_of_le hBX, add_zero]; exact hfloor

/-- **Min-plus service-curve form**: the tagged flow is
served at the per-path PMOO residual, `Aᵗᵍ ∗ pmooPathResidual ≤ Dᵗᵍ` —
the convolution splits at the cascade bottom. -/
theorem minConv_pmooPathResidual_le_of_strict_path {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ℕ → ι → Curve}
    {β : ℕ → ℝ≥0 → ℝ≥0} {S : ℕ → Finset ι} {α : ι → ℝ≥0 → ℝ≥0}
    {fst lst : ι → ℕ} {n : ℕ} (t : ℝ≥0) {tg : ι}
    (hS : ∀ h j, j ∈ S h ↔ (fst j ≤ h ∧ h ≤ lst j))
    (hc : ∀ h, h ≤ n → ∀ j, F (h + 1) j ≤ F h j)
    (hstrict : ∀ h, h ≤ n → ∀ s t', s ≤ t' →
      IsBacklogged (fun x => ∑ j ∈ S h, (F h j) x) (fun x => ∑ j ∈ S h, (F (h + 1) j) x)
        (Set.Ioc s t') →
      (∑ j ∈ S h, (F (h + 1) j) s) + β h (t' - s) ≤ ∑ j ∈ S h, (F (h + 1) j) t')
    (hpath : ∀ j, fst j ≤ lst j ∧ lst j ≤ n)
    (harr : ∀ j, j ≠ tg → IsMaximalArrivalBound (F (fst j) j) (α j))
    (htgfst : fst tg = 0) (htglst : lst tg = n) (hαtg : α tg = 0) :
    minConv (Deviation.liftENN ⇑(F 0 tg))
        (Deviation.liftENN (pmooPathResidual n β α fst lst)) t
      ≤ ((F (n + 1) tg) t : ℝ≥0∞) := by
  have hkey := add_pmooPathResidual_le_of_strict_path t hS hc hstrict hpath harr
    htgfst htglst hαtg
  have hnode0t : pathNode F S n t 0 ≤ t :=
    le_trans (pathNode_mono F S n t (Nat.zero_le (n + 1))) (le_of_eq (pathNode_succ F S n t))
  refine le_trans (minConv_le_add _ _ (add_tsub_cancel_of_le hnode0t)) ?_
  exact_mod_cast hkey

/-- **Theorem 10.1, relation/server form**: a tandem of `n+1` per-hop servers `Srv h`, each
offering a strict service curve `β h` on its *present-flow* `Fl(h)`-aggregate (the flows `j` with
`fst j ≤ h ≤ lst j`), with each cross-flow `j ≠ tg` constrained by `αⱼ` at its entry input
`G_{fst j}`: the residual server of the tagged flow (which crosses every hop) offers the per-path
PMOO residual `pmooPathResidual` as a min-plus service curve. The per-path analogue of the chain's
full-aggregate `isMinimalServiceCurve_pmooResidualChain_of_strict_chain` — the strictness here is
on each hop's `Fl(h)`-restricted aggregate (`aggregateServerOn`). -/
theorem isMinimalServiceCurve_pmooPathResidual_of_strict_path {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    {Srv : ℕ → (ι → Curve) → (ι → Curve) → Prop}
    {β : ℕ → ℝ≥0 → ℝ≥0} {α : ι → ℝ≥0 → ℝ≥0} {fst lst : ι → ℕ} {n : ℕ} {tg : ι}
    (hpath : ∀ j, fst j ≤ lst j ∧ lst j ≤ n)
    (hcaus : ∀ h, h ≤ n → IsCausalN (Srv h))
    (hβ : ∀ h, h ≤ n → IsStrictMinimalServiceCurve (β h)
      (aggregateServerOn (Srv h) (Finset.univ.filter (fun j => fst j ≤ h ∧ h ≤ lst j))))
    (htgfst : fst tg = 0) (htglst : lst tg = n) (hαtg : α tg = 0) :
    IsMinimalServiceCurve
      (liftEReal (pmooPathResidual n β α fst lst))
      (residualServer (fun A D =>
        ∃ G : ℕ → ι → Curve, G 0 = A ∧ G (n + 1) = D
          ∧ (∀ h, h ≤ n → Srv h (G h) (G (h + 1)))
          ∧ ∀ j, j ≠ tg → IsMaximalArrivalBound ⇑(G (fst j) j) (α j)) tg) := by
  rintro Ai Di ⟨As, Ds, ⟨G, hG0, hGn, hhops, harr⟩, rfl, rfl⟩ t
  subst hG0
  subst hGn
  have hS : ∀ h j,
      j ∈ Finset.univ.filter (fun j => fst j ≤ h ∧ h ≤ lst j) ↔ (fst j ≤ h ∧ h ≤ lst j) :=
    fun h j => by simp [Finset.mem_filter]
  have h := minConv_pmooPathResidual_le_of_strict_path
    (F := G) (β := β) (S := fun h => Finset.univ.filter (fun j => fst j ≤ h ∧ h ≤ lst j))
    (α := α) (fst := fst) (lst := lst) (n := n) t hS
    (fun h hh j => hcaus h hh (G h) (G (h + 1)) (hhops h hh) j)
    (fun h hh => (hβ h hh).sum_strict_on (hhops h hh))
    hpath harr htgfst htglst hαtg
  rw [show Deviation.liftENN (pmooPathResidual n β α fst lst)
      = Deviation.toENN (liftEReal (pmooPathResidual n β α fst lst))
    from (Deviation.toENN_liftEReal _).symm] at h
  rw [curveEReal_apply]
  exact (Deviation.minConv_toENN_le_coe_iff (G 0 tg) (isNonneg_liftEReal _)
    ((G (n + 1) tg) t) t).mp h

/-! ## Book restatement (Theorem 10.1, per-path PMOO)
A tandem of `n + 1` servers each offering a strict service curve `β⁽ʰ⁾`,
under blind multiplexing, where the tagged flow crosses every server and
each cross-flow `j` is `αⱼ`-constrained over the contiguous sub-path
`[fst j, lst j]` it crosses: the tagged flow is served at the min-plus
residual `pmooPathResidual`, the infimum over time splits of
`∑ₕ β⁽ʰ⁾(uₕ) − ∑ⱼ αⱼ(∑_{h∈pⱼ} uₕ)` — each cross-flow's burst paid once,
over its own path. The all-crossing case (`pathHops_univ_sum`) reduces the
sub-path sums to the whole split, the bridge toward `pmooResidualChain`. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ℕ → ι → Curve}
    {β : ℕ → ℝ≥0 → ℝ≥0} {S : ℕ → Finset ι} {α : ι → ℝ≥0 → ℝ≥0}
    {fst lst : ι → ℕ} {n : ℕ} (t : ℝ≥0) {tg : ι}
    (hS : ∀ h j, j ∈ S h ↔ (fst j ≤ h ∧ h ≤ lst j))
    (hc : ∀ h, h ≤ n → ∀ j, F (h + 1) j ≤ F h j)
    (hstrict : ∀ h, h ≤ n → ∀ s t', s ≤ t' →
      IsBacklogged (fun x => ∑ j ∈ S h, (F h j) x) (fun x => ∑ j ∈ S h, (F (h + 1) j) x)
        (Set.Ioc s t') →
      (∑ j ∈ S h, (F (h + 1) j) s) + β h (t' - s) ≤ ∑ j ∈ S h, (F (h + 1) j) t')
    (hpath : ∀ j, fst j ≤ lst j ∧ lst j ≤ n)
    (harr : ∀ j, j ≠ tg → IsMaximalArrivalCurve ⇑(F (fst j) j) (α j))
    (htgfst : fst tg = 0) (htglst : lst tg = n) (hαtg : α tg = 0) :
    minConv (Deviation.liftENN ⇑(F 0 tg))
        (Deviation.liftENN (pmooPathResidual n β α fst lst)) t
      ≤ ((F (n + 1) tg) t : ℝ≥0∞) :=
  minConv_pmooPathResidual_le_of_strict_path t hS hc hstrict hpath
    (fun j hj => (harr j hj).2) htgfst htglst hαtg

end DeepWiki
