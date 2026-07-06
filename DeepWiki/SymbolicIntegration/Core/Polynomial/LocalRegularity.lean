import DeepWiki.SymbolicIntegration.Core.Polynomial.LocalPrincipalParts

/-! # Regularity of rational functions at a point

A rational function is regular at `α` when it has a polynomial quotient
presentation whose denominator does not vanish at `α`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- A rational function is regular at `α` if it is `N/M` with `M(α) ≠ 0`. -/
def RegularAt (α : K) (f : RatFunc K) : Prop :=
  ∃ (N M : K[X]), M.eval α ≠ 0 ∧ f = algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) M

/-- `0` is regular at `α`. -/
theorem RegularAt.zero (α : K) : RegularAt α (0 : RatFunc K) :=
  ⟨0, 1, by simp, by simp⟩

/-- `RegularAt` is closed under addition. -/
theorem RegularAt.add {α : K} {f g : RatFunc K} (hf : RegularAt α f) (hg : RegularAt α g) :
    RegularAt α (f + g) := by
  obtain ⟨N₁, M₁, hM₁, rfl⟩ := hf
  obtain ⟨N₂, M₂, hM₂, rfl⟩ := hg
  have hM₁0 : algebraMap K[X] (RatFunc K) M₁ ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (fun h => hM₁ (by rw [h, Polynomial.eval_zero]))
  have hM₂0 : algebraMap K[X] (RatFunc K) M₂ ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (fun h => hM₂ (by rw [h, Polynomial.eval_zero]))
  refine ⟨N₁ * M₂ + M₁ * N₂, M₁ * M₂, by rw [Polynomial.eval_mul]; exact mul_ne_zero hM₁ hM₂, ?_⟩
  rw [div_add_div _ _ hM₁0 hM₂0, map_add, map_mul, map_mul, map_mul]

/-- `RegularAt` is closed under finite sums. -/
theorem RegularAt.sum {α : K} {ι : Type*} {s : Finset ι} {f : ι → RatFunc K}
    (hf : ∀ i ∈ s, RegularAt α (f i)) : RegularAt α (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RegularAt.zero α
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- A principal part at `β` is regular at every distinct point `α`. -/
theorem RegularAt.localPrincipalPart {α β : K} (hαβ : α ≠ β) (A M : K[X]) (i : ℕ) :
    RegularAt α (localPrincipalPart A M β i) := by
  refine ⟨localApprox A M β i, (Polynomial.X - Polynomial.C β) ^ i, ?_, ?_⟩
  · rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact pow_ne_zero _ (sub_ne_zero.mpr hαβ)
  · rw [localPrincipalPart_eq_div, map_pow]

/-- Unpack `RegularAt α f` as a concrete quotient with denominator nonzero at `α`. -/
theorem RegularAt.exists_div {α : K} {f : RatFunc K} (hf : RegularAt α f) :
    ∃ (N Md : K[X]), Md.eval α ≠ 0
      ∧ f = algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) Md := hf

end DeepWiki.SymbolicIntegration
