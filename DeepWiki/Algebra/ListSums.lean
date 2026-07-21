import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-! # List sum identities

Small algebraic identities for finite sums over lists.
-/

namespace DeepWiki

/-- Summing a map over a `filterMap` is summing the option-elimination over the source. -/
theorem sum_map_filterMap {α β M : Type*} [AddCommMonoid M]
    (f : α → Option β) (g : β → M) :
    ∀ l : List α, ((l.filterMap f).map g).sum
      = (l.map fun a => ((f a).map g).getD 0).sum := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
      rcases hfa : f a with _ | b
      · rw [List.filterMap_cons_none hfa, List.map_cons, List.sum_cons, hfa]
        simpa using ih
      · rw [List.filterMap_cons_some hfa, List.map_cons, List.sum_cons, List.map_cons,
          List.sum_cons, hfa]
        simp only [Option.map_some, Option.getD_some]
        rw [ih]

/-- Summing a map over `zipIdx` is an index-range sum over the entries. -/
theorem sum_map_zipIdx {α M : Type*} [AddCommMonoid M] (h : α × ℕ → M) (d₀ : α) :
    ∀ (l : List α) (n : ℕ), ((l.zipIdx n).map h).sum
      = ∑ j ∈ Finset.range l.length, h (l.getD j d₀, n + j) := by
  intro l
  induction l with
  | nil => intro n; simp
  | cons a t ih =>
      intro n
      rw [List.zipIdx_cons, List.map_cons, List.sum_cons, List.length_cons,
        Finset.sum_range_succ', ih (n + 1)]
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show n + 1 + j = n + (j + 1) from by omega]

/-- `Σ (g x / c) = (Σ g x) / c` over a list. -/
theorem list_sum_map_div {β K : Type*} [Field K] (L : List β) (g : β → K) (c : K) :
    (L.map (fun x => g x / c)).sum = (L.map g).sum / c := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, add_div]

/-- `Σ (c - g x) = n • c - Σ g x` over a list. -/
theorem list_sum_map_const_sub {β M : Type*} [AddCommGroup M] (L : List β) (c : M) (g : β → M) :
    (L.map (fun x => c - g x)).sum = L.length • c - (L.map g).sum := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, List.length_cons,
      succ_nsmul]
    abel

end DeepWiki
