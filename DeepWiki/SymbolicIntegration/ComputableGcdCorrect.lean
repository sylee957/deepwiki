import DeepWiki.SymbolicIntegration.ComputableFieldGcd
import DeepWiki.SymbolicIntegration.SubresultantCorrectness

/-! # `filter_prod_mul` — a finite-product combinatorial lemma

The generic helper `filter_prod_mul` (over any `[CommMonoid M]`): pulling one indexed factor out of
a `zipIdx`-filtered product recovers the full product. Consumed by the generic gcd-content theory. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-- Pulling one indexed factor out of a `zipIdx`-filtered finite product: filtering out the index-`i`
entry of `ds` and re-multiplying that entry's image recovers the full product of `ds.map f`. -/
theorem filter_prod_mul {α M : Type*} [CommMonoid M] (f : α → M) (def0 : α) :
    ∀ (ds : List α) (k i : ℕ), k ≤ i → i < k + ds.length →
      (((ds.zipIdx k).filter (fun de => decide (de.2 ≠ i))).map (fun de => f de.1)).prod
        * f (ds.getD (i - k) def0) = (ds.map f).prod := by
  intro ds
  induction ds with
  | nil => intro k i _ hlt; simp at hlt; omega
  | cons d tl ih =>
    intro k i hk hlt
    rw [List.zipIdx_cons, List.filter_cons]
    rcases Nat.eq_or_lt_of_le hk with hik | hik
    · subst hik
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
      have hkeep : ((tl.zipIdx (k+1)).filter (fun de => decide (de.2 ≠ k))).map (fun de => f de.1)
          = (tl.zipIdx (k+1)).map (fun de => f de.1) := by
        congr 1
        rw [List.filter_eq_self.mpr]
        intro de hde
        have hge := List.le_snd_of_mem_zipIdx hde
        simp only [decide_eq_true_eq, ne_eq]; omega
      rw [hkeep]
      calc ((tl.zipIdx (k+1)).map (fun de => f de.1)).prod * f ((d :: tl).getD (k - k) def0)
          = (tl.map f).prod * f d := by
            congr 1
            · calc ((tl.zipIdx (k+1)).map (fun de => f de.1)).prod
                  = (((tl.zipIdx (k+1)).map Prod.fst).map f).prod := by rw [List.map_map]; rfl
                _ = (tl.map f).prod := by simp
            · simp
        _ = (List.map f (d :: tl)).prod := by rw [List.map_cons, List.prod_cons, mul_comm]
    · have hne : (k ≠ i) := Nat.ne_of_lt hik
      simp only [hne, ne_eq, not_false_eq_true, decide_true, if_true]
      rw [List.map_cons, List.prod_cons]
      have hsub : i - k = (i - (k+1)) + 1 := by omega
      rw [hsub, List.getD_cons_succ]
      have hih := ih (k+1) i (by omega) (by simp at hlt ⊢; omega)
      rw [List.map_cons, List.prod_cons, ← hih, mul_assoc]

end DeepWiki.SymbolicIntegration
