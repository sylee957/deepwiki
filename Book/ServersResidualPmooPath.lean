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

end DeepWiki
