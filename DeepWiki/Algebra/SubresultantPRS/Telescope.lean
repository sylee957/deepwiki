import DeepWiki.Algebra.SubresultantSpec
import DeepWiki.Algebra.PseudoDivision

/-! # Subresultant PRS telescopes

Stepwise and telescoped similarity theorems for subresultants along a PRS. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R]

/-- Raising the second polynomial's formal degree from `k` to `n` scales the subresultant by a nonzero
constant, so `subresultant B Rem m n j` is `IsSimilar` to `subresultant B Rem m k j`. -/
theorem isSimilar_subresultant_padding [IsDomain R] (B Rem : R[X]) (m k j : ℕ)
    (hjk : j < k) (hjm : j ≤ m) (hB : B.natDegree ≤ m) (hRem : Rem.natDegree ≤ k)
    (hlc : B.coeff m ≠ 0) {n : ℕ} (hn : k ≤ n) :
    IsSimilar (subresultant B Rem m n j) (subresultant B Rem m k j) := by
  rw [subresultant_padding B Rem m k j hjk hjm hB hRem n hn]
  exact ⟨1, (B.coeff m) ^ (n - k), one_ne_zero, pow_ne_zero _ hlc,
    by rw [map_one, one_mul, map_pow]⟩

/-- Per-step similarity: across one PRS division step `α·A = β·C + B·Q`, the subresultants `Sⱼ(A,B)`
and `Sⱼ(B,C)` are `IsSimilar` for `j < deg C`. -/
theorem subresultant_prs_similar [IsDomain R] (A B C_poly Q : R[X]) (α β : R) (a b c j : ℕ)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hlcB : B.coeff b ≠ 0) (hjc : j < c) (hcb : c < b)
    (hcpoly : C_poly.natDegree = c) (hB : B.natDegree ≤ b) (hQ : Q.natDegree + b ≤ a)
    (hrel : C α * A = C β * C_poly + B * Q) :
    IsSimilar (subresultant A B a b j) (subresultant B C_poly b c j) := by
  refine ⟨α ^ (b - j), (-1 : R) ^ ((a - j) * (b - j)) * (B.coeff b) ^ (a - c) * β ^ (b - j),
    pow_ne_zero _ hα,
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hlcB)) (pow_ne_zero _ hβ),
    ?_⟩
  rw [subresultant_prs_step A B C_poly Q α β a b c j hβ hjc hcb hcpoly hB hQ hrel,
    map_mul, map_mul, map_pow, map_pow, map_pow, map_neg, map_one]
  ring

/-- Telescoped similarity: for a PRS `F` with steps `α l·F l = β l·F (l+2) + F (l+1)·Q l`, the
subresultant `Sⱼ(F₀,F₁)` is `IsSimilar` to `Sⱼ(Fₘ,F_{m+1})` for every `m`. -/
theorem subresultant_prs_telescope [IsDomain R] (F : ℕ → R[X]) (α β : ℕ → R) (Q : ℕ → R[X])
    (j : ℕ) (m : ℕ)
    (hα : ∀ l < m, α l ≠ 0) (hβ : ∀ l < m, β l ≠ 0)
    (hlc : ∀ l < m, (F (l + 1)).coeff (F (l + 1)).natDegree ≠ 0)
    (hcb : ∀ l < m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, j < (F (l + 2)).natDegree)
    (hQ : ∀ l < m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l < m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l) :
    IsSimilar (subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree j)
      (subresultant (F m) (F (m + 1)) (F m).natDegree (F (m + 1)).natDegree j) := by
  induction m with
  | zero => exact IsSimilar.refl _
  | succ n ih =>
    refine (ih (fun l hl => hα l (by omega)) (fun l hl => hβ l (by omega))
      (fun l hl => hlc l (by omega)) (fun l hl => hcb l (by omega)) (fun l hl => hj l (by omega))
      (fun l hl => hQ l (by omega)) (fun l hl => hrel l (by omega))).trans ?_
    exact subresultant_prs_similar (F n) (F (n + 1)) (F (n + 2)) (Q n) (α n) (β n)
      (F n).natDegree (F (n + 1)).natDegree (F (n + 2)).natDegree j
      (hα n (by omega)) (hβ n (by omega)) (hlc n (by omega)) (hj n (by omega)) (hcb n (by omega))
      rfl le_rfl (hQ n (by omega)) (hrel n (by omega))

/-- Explicit product form of the telescope: `Sⱼ(F₀,F₁)·∏ αₗ^(n_{l+1}-j)` equals `Sⱼ(Fₘ,F_{m+1})`
times the explicit sign/leading-coefficient/`β` product over `l < m`. -/
theorem subresultant_prs_telescope_explicit [IsDomain R] (F : ℕ → R[X]) (α β : ℕ → R) (Q : ℕ → R[X])
    (j : ℕ) (m : ℕ)
    (hβ : ∀ l < m, β l ≠ 0)
    (hcb : ∀ l < m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, j < (F (l + 2)).natDegree)
    (hQ : ∀ l < m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l < m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l) :
    subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree j
        * ∏ l ∈ Finset.range m, C (α l ^ ((F (l + 1)).natDegree - j))
      = subresultant (F m) (F (m + 1)) (F m).natDegree (F (m + 1)).natDegree j
        * ∏ l ∈ Finset.range m, ((-1 : R[X]) ^ (((F l).natDegree - j) * ((F (l + 1)).natDegree - j))
            * C ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ ((F l).natDegree - (F (l + 2)).natDegree)
            * C (β l ^ ((F (l + 1)).natDegree - j))) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ← mul_assoc,
      ih (fun l hl => hβ l (by omega)) (fun l hl => hcb l (by omega)) (fun l hl => hj l (by omega))
        (fun l hl => hQ l (by omega)) (fun l hl => hrel l (by omega))]
    have h21 := subresultant_prs_step (F n) (F (n + 1)) (F (n + 2)) (Q n) (α n) (β n)
      (F n).natDegree (F (n + 1)).natDegree (F (n + 2)).natDegree j (hβ n (by omega))
      (hj n (by omega)) (hcb n (by omega)) rfl le_rfl (hQ n (by omega)) (hrel n (by omega))
    linear_combination (∏ l ∈ Finset.range n,
      ((-1 : R[X]) ^ (((F l).natDegree - j) * ((F (l + 1)).natDegree - j))
        * C ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ ((F l).natDegree - (F (l + 2)).natDegree)
        * C (β l ^ ((F (l + 1)).natDegree - j)))) * h21

/-- Vanishing branch: if the endpoint subresultant `Sⱼ(Fₘ,F_{m+1}) = 0`, then `Sⱼ(F₀,F₁) = 0`. -/
theorem subresultant_prs_vanish [IsDomain R] (F : ℕ → R[X]) (α β : ℕ → R) (Q : ℕ → R[X])
    (j : ℕ) (m : ℕ)
    (hα : ∀ l < m, α l ≠ 0) (hβ : ∀ l < m, β l ≠ 0)
    (hcb : ∀ l < m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, j < (F (l + 2)).natDegree)
    (hQ : ∀ l < m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l < m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l)
    (hend : subresultant (F m) (F (m + 1)) (F m).natDegree (F (m + 1)).natDegree j = 0) :
    subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree j = 0 := by
  have h30 := subresultant_prs_telescope_explicit F α β Q j m hβ hcb hj hQ hrel
  rw [hend, zero_mul] at h30
  have hprod : (∏ l ∈ Finset.range m, C (α l ^ ((F (l + 1)).natDegree - j))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro l hl
    rw [Ne, C_eq_zero]
    exact pow_ne_zero _ (hα l (Finset.mem_range.mp hl))
  exact (mul_eq_zero.mp h30).resolve_right hprod

end DeepWiki.SymbolicIntegration
