import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # List product divisibility

Coprimality and divisibility lemmas for finite products over lists.
-/

namespace DeepWiki

/-- If `x` is coprime to every list entry, then `x` is coprime to the list product. -/
theorem isRelPrime_list_prod_right {α : Type*} [CommMonoidWithZero α] [GCDMonoid α]
    (x : α) (L : List α) (h : ∀ a ∈ L, IsRelPrime x a) : IsRelPrime x L.prod := by
  induction L with
  | nil => simpa using isRelPrime_one_right
  | cons hd tl ih =>
    rw [List.prod_cons]
    exact (h hd (List.mem_cons_self ..)).mul_right (ih fun a ha => h a (List.mem_cons_of_mem _ ha))

/-- Pairwise-coprime list factors that each divide `z` have product dividing `z`. -/
theorem list_prod_dvd_of_pairwise {α : Type*} [CommMonoidWithZero α] [GCDMonoid α]
    (L : List α) (z : α) (hpw : L.Pairwise IsRelPrime) (hd : ∀ a ∈ L, a ∣ z) : L.prod ∣ z := by
  induction L with
  | nil => simp
  | cons hd' tl ih =>
    rw [List.prod_cons, List.pairwise_cons] at *
    exact IsRelPrime.mul_dvd (isRelPrime_list_prod_right hd' tl fun i hi => hpw.1 i hi)
      (hd hd' (List.mem_cons_self ..)) (ih hpw.2 fun a ha => hd a (List.mem_cons_of_mem _ ha))

end DeepWiki
