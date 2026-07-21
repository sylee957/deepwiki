import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-! # List product divisibility

Coprimality and divisibility lemmas for finite products over lists.
-/

namespace DeepWiki

/-- Two entries at distinct positions divide the list product. -/
theorem getElem_mul_getElem_dvd_prod {M : Type*} [CommMonoid M] :
    ∀ (l : List M) (j k : ℕ), ∀ (hj : j < l.length) (hk : k < l.length), j ≠ k →
      l[j] * l[k] ∣ l.prod := by
  intro l
  induction l with
  | nil => intro j k hj; simp at hj
  | cons a t ih =>
      intro j k hj hk hne
      rcases j with _ | j <;> rcases k with _ | k
      · omega
      · simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.prod_cons]
        exact mul_dvd_mul_left a (List.dvd_prod (List.getElem_mem _))
      · simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.prod_cons]
        rw [mul_comm]
        exact mul_dvd_mul_left a (List.dvd_prod (List.getElem_mem _))
      · simp only [List.getElem_cons_succ, List.prod_cons]
        exact Dvd.dvd.mul_left
          (ih j k (by simpa using hj) (by simpa using hk) (by omega)) a

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
