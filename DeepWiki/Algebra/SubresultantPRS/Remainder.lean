import DeepWiki.Algebra.SubresultantPRS.Telescope

/-! # Subresultant PRS endpoint remainders

Endpoint similarity, gcd, and fraction-ring consequences for subresultant PRS elements. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R]

/-- At the regular index `j = deg C`, `S_{deg C}(A,B)` is `IsSimilar` to the remainder `C` itself. -/
theorem subresultant_prs_similar_remainder [IsDomain R] (A B C_poly Q : R[X]) (α β : R) (a b c : ℕ)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hlcB : B.coeff b ≠ 0) (hC : C_poly ≠ 0) (hcb : c < b)
    (hcpoly : C_poly.natDegree = c) (hB : B.natDegree ≤ b) (hQ : Q.natDegree + b ≤ a)
    (hrel : C α * A = C β * C_poly + B * Q) :
    IsSimilar (subresultant A B a b c) C_poly := by
  have hlcBC : (C β * C_poly).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (mul_ne_zero (by rwa [Ne, C_eq_zero]) hC)
  refine ⟨α ^ (b - c),
    (-1 : R) ^ ((a - c) * (b - c)) * (B.coeff b) ^ (a - c)
      * (C β * C_poly).leadingCoeff ^ (b - c - 1) * β,
    pow_ne_zero _ hα,
    mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hlcB))
      (pow_ne_zero _ hlcBC)) hβ, ?_⟩
  rw [subresultant_prs_step_deg A B C_poly Q α β a b c hβ hcb hcpoly hB hQ hrel]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

/-- At the regular index `j = deg B − 1`, `S_{deg B-1}(A,B)` is `IsSimilar` to the remainder `C`. -/
theorem subresultant_prs_similar_remainder_top [IsDomain R] (A B C_poly Q : R[X]) (α β : R)
    (a b c : ℕ) (hα : α ≠ 0) (hβ : β ≠ 0) (hlcB : B.coeff b ≠ 0) (hcb : c < b)
    (hcpoly : C_poly.natDegree = c) (hB : B.natDegree ≤ b) (hQ : Q.natDegree + b ≤ a)
    (hrel : C α * A = C β * C_poly + B * Q) :
    IsSimilar (subresultant A B a b (b - 1)) C_poly := by
  refine ⟨α, (-1 : R) ^ (a - b + 1) * (B.coeff b) ^ (a - b + 1) * β, hα,
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hlcB)) hβ, ?_⟩
  rw [subresultant_prs_step_top A B C_poly Q α β a b c hβ hcb hcpoly hB hQ hrel]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

/-- At the regular index `j = deg F_{m+2}`, the subresultant `Sⱼ(F₀,F₁)` is `IsSimilar` to the PRS
element `F_{m+2}`. -/
theorem subresultant_prs_similar_elt [IsDomain R] (F : ℕ → R[X]) (α β : ℕ → R) (Q : ℕ → R[X]) (m : ℕ)
    (hα : ∀ l ≤ m, α l ≠ 0) (hβ : ∀ l ≤ m, β l ≠ 0)
    (hlc : ∀ l ≤ m, (F (l + 1)).coeff (F (l + 1)).natDegree ≠ 0)
    (hcb : ∀ l ≤ m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, (F (m + 2)).natDegree < (F (l + 2)).natDegree)
    (hQ : ∀ l ≤ m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l ≤ m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l)
    (hC : F (m + 2) ≠ 0) :
    IsSimilar (subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree (F (m + 2)).natDegree)
      (F (m + 2)) :=
  (subresultant_prs_telescope F α β Q (F (m + 2)).natDegree m
      (fun l hl => hα l (by omega)) (fun l hl => hβ l (by omega)) (fun l hl => hlc l (by omega))
      (fun l hl => hcb l (by omega)) hj (fun l hl => hQ l (by omega))
      (fun l hl => hrel l (by omega))).trans
    (subresultant_prs_similar_remainder (F m) (F (m + 1)) (F (m + 2)) (Q m) (α m) (β m)
      (F m).natDegree (F (m + 1)).natDegree (F (m + 2)).natDegree (hα m le_rfl) (hβ m le_rfl)
      (hlc m le_rfl) hC (hcb m le_rfl) rfl le_rfl (hQ m le_rfl) (hrel m le_rfl))

/-- Subresultant–gcd link: if a terminating PRS has `F_{m+2}` similar to `gcd(F₀,F₁)`, then the
subresultant of `F₀,F₁` at degree `deg F_{m+2}` is `IsSimilar` to `gcd(F₀,F₁)`. -/
theorem subresultant_isSimilar_gcd [IsDomain R] [GCDMonoid R[X]] (F : ℕ → R[X]) (α β : ℕ → R)
    (Q : ℕ → R[X]) (m : ℕ) (hα : ∀ l ≤ m, α l ≠ 0) (hβ : ∀ l ≤ m, β l ≠ 0)
    (hlc : ∀ l ≤ m, (F (l + 1)).coeff (F (l + 1)).natDegree ≠ 0)
    (hcb : ∀ l ≤ m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, (F (m + 2)).natDegree < (F (l + 2)).natDegree)
    (hQ : ∀ l ≤ m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l ≤ m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l)
    (hC : F (m + 2) ≠ 0) (hgcd : IsSimilar (F (m + 2)) (gcd (F 0) (F 1))) :
    IsSimilar (subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree (F (m + 2)).natDegree)
      (gcd (F 0) (F 1)) :=
  (subresultant_prs_similar_elt F α β Q m hα hβ hlc hcb hj hQ hrel hC).trans hgcd

/-- Exact rational form over `Frac(D)`: at `j = deg F_{m+2}`, `Sⱼ(F₀,F₁) = η · F_{m+2}` in `Frac(D)[x]`
for some nonzero `η`. -/
theorem subresultant_prs_eq_fractionRing {D : Type*} [CommRing D] [IsDomain D]
    (F : ℕ → D[X]) (α β : ℕ → D) (Q : ℕ → D[X]) (m : ℕ)
    (hα : ∀ l ≤ m, α l ≠ 0) (hβ : ∀ l ≤ m, β l ≠ 0)
    (hlc : ∀ l ≤ m, (F (l + 1)).coeff (F (l + 1)).natDegree ≠ 0)
    (hcb : ∀ l ≤ m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, (F (m + 2)).natDegree < (F (l + 2)).natDegree)
    (hQ : ∀ l ≤ m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l ≤ m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l)
    (hC : F (m + 2) ≠ 0) :
    ∃ η : FractionRing D, η ≠ 0 ∧
      (subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree (F (m + 2)).natDegree).map
          (algebraMap D (FractionRing D))
        = C η * (F (m + 2)).map (algebraMap D (FractionRing D)) :=
  (subresultant_prs_similar_elt F α β Q m hα hβ hlc hcb hj hQ hrel hC).exists_fractionRing

/-- At the other regular index `j = deg F_{m+1} − 1`, `Sⱼ(F₀,F₁)` is `IsSimilar` to the PRS element
`F_{m+2}`. -/
theorem subresultant_prs_similar_elt_top [IsDomain R] (F : ℕ → R[X]) (α β : ℕ → R) (Q : ℕ → R[X])
    (m : ℕ) (hα : ∀ l ≤ m, α l ≠ 0) (hβ : ∀ l ≤ m, β l ≠ 0)
    (hlc : ∀ l ≤ m, (F (l + 1)).coeff (F (l + 1)).natDegree ≠ 0)
    (hcb : ∀ l ≤ m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, (F (m + 1)).natDegree - 1 < (F (l + 2)).natDegree)
    (hQ : ∀ l ≤ m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l ≤ m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l) :
    IsSimilar (subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree ((F (m + 1)).natDegree - 1))
      (F (m + 2)) :=
  (subresultant_prs_telescope F α β Q ((F (m + 1)).natDegree - 1) m
      (fun l hl => hα l (by omega)) (fun l hl => hβ l (by omega)) (fun l hl => hlc l (by omega))
      (fun l hl => hcb l (by omega)) hj (fun l hl => hQ l (by omega))
      (fun l hl => hrel l (by omega))).trans
    (subresultant_prs_similar_remainder_top (F m) (F (m + 1)) (F (m + 2)) (Q m) (α m) (β m)
      (F m).natDegree (F (m + 1)).natDegree (F (m + 2)).natDegree (hα m le_rfl) (hβ m le_rfl)
      (hlc m le_rfl) (hcb m le_rfl) rfl le_rfl (hQ m le_rfl) (hrel m le_rfl))

end DeepWiki.SymbolicIntegration
