import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-! # List sum identities

Small algebraic identities for finite sums over lists.
-/

namespace DeepWiki

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
