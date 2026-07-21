import DeepWiki.Algebra.SubresultantPRS.Remainder

/-! # Subresultant PRS closed forms

Normal and defective closed forms for the subresultant PRS theorem. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R]

/-- Base step (`η = 1`): for the pseudo-division `lc(B)^(δ+1)·A = B·Q + (-1)^(δ+1)·Rem`, the subresultant
equals the remainder exactly, `S_{deg B-1}(A,B) = Rem`. -/
theorem subresultant_eq_pseudoRem [IsDomain R] (A B Rem Q : R[X]) (a b c : ℕ)
    (hlcB : B.coeff b ≠ 0) (hcb : c < b) (hcpoly : Rem.natDegree = c) (hB : B.natDegree ≤ b)
    (hQ : Q.natDegree + b ≤ a)
    (hrel : C ((B.coeff b) ^ (a - b + 1)) * A
      = C ((-1 : R) ^ (a - b + 1)) * Rem + B * Q) :
    subresultant A B a b (b - 1) = Rem := by
  have hstep := subresultant_prs_step_top A B Rem Q ((B.coeff b) ^ (a - b + 1)) ((-1 : R) ^ (a - b + 1))
    a b c (pow_ne_zero _ (by norm_num)) hcb hcpoly hB hQ hrel
  rw [map_pow] at hstep
  have hsq : (-1 : R[X]) ^ (a - b + 1) * (-1) ^ (a - b + 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have key : (C (B.coeff b)) ^ (a - b + 1) * subresultant A B a b (b - 1)
      = (C (B.coeff b)) ^ (a - b + 1) * Rem := by
    rw [hstep]
    simp only [map_pow, map_neg, map_one]
    rw [show (-1 : R[X]) ^ (a - b + 1) * ((C (B.coeff b)) ^ (a - b + 1)
        * ((-1) ^ (a - b + 1) * Rem))
      = ((-1 : R[X]) ^ (a - b + 1) * (-1) ^ (a - b + 1)) * ((C (B.coeff b)) ^ (a - b + 1) * Rem)
      from by ring, hsq, one_mul]
  exact mul_left_cancel₀ (pow_ne_zero _ (by rw [Ne, C_eq_zero]; exact hlcB)) key

/-- Explicit closed form at the η-index `j = deg F_{m+1} − 1`:
`Sⱼ(F₀,F₁)·(αₘ-product) = (sign·lc·βₘ·F_{m+2})·(telescope product)`. -/
theorem subresultant_prs_closed_top [IsDomain R] (F : ℕ → R[X]) (α β : ℕ → R) (Q : ℕ → R[X]) (m : ℕ)
    (hβ : ∀ l ≤ m, β l ≠ 0)
    (hcb : ∀ l ≤ m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, (F (m + 1)).natDegree - 1 < (F (l + 2)).natDegree)
    (hQ : ∀ l ≤ m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l ≤ m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l) :
    subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree ((F (m + 1)).natDegree - 1)
        * (C (α m)
          * ∏ l ∈ Finset.range m, C (α l ^ ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1))))
      = ((-1 : R[X]) ^ ((F m).natDegree - (F (m + 1)).natDegree + 1)
          * (C ((F (m + 1)).coeff (F (m + 1)).natDegree ^ ((F m).natDegree - (F (m + 1)).natDegree + 1))
             * (C (β m) * F (m + 2))))
        * ∏ l ∈ Finset.range m,
            ((-1 : R[X]) ^ (((F l).natDegree - ((F (m + 1)).natDegree - 1))
                  * ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1)))
              * C ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ ((F l).natDegree - (F (l + 2)).natDegree)
              * C (β l ^ ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1)))) := by
  have htel := subresultant_prs_telescope_explicit F α β Q ((F (m + 1)).natDegree - 1) m
    (fun l hl => hβ l (by omega)) (fun l hl => hcb l (by omega)) hj
    (fun l hl => hQ l (by omega)) (fun l hl => hrel l (by omega))
  have htop := subresultant_prs_step_top (F m) (F (m + 1)) (F (m + 2)) (Q m) (α m) (β m)
    (F m).natDegree (F (m + 1)).natDegree (F (m + 2)).natDegree (hβ m le_rfl) (hcb m le_rfl) rfl
    le_rfl (hQ m le_rfl) (hrel m le_rfl)
  set αprod := ∏ l ∈ Finset.range m, C (α l ^ ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1)))
    with hαdef
  set Prhs := ∏ l ∈ Finset.range m,
      ((-1 : R[X]) ^ (((F l).natDegree - ((F (m + 1)).natDegree - 1))
            * ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1)))
        * C ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ ((F l).natDegree - (F (l + 2)).natDegree)
        * C (β l ^ ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1)))) with hPdef
  linear_combination C (α m) * htel + Prhs * htop

section NormalCollapse

variable {M : Type*} [CommRing M]

open Finset in
/-- Leading-coefficient product collapse (normal case, `δ=1`): the `∏ c(l+1)^(2(n+1-l+1))` product equals
`c(n+1)²·∏ c(l+1)²` times the reindexed `β`-product, forcing `η = 1`. -/
theorem lc_prod_collapse_normal (c : ℕ → M) (n : ℕ) :
    ∏ l ∈ range (n + 1), (c (l + 1)) ^ (2 * (n + 1 - l + 1))
      = (c (n + 1)) ^ 2 * (∏ l ∈ range (n + 1), (c (l + 1)) ^ 2)
        * ∏ l ∈ range (n + 1), (if l = 0 then (1 : M) else (c l) ^ 2) ^ (n + 1 - l + 1) := by
  rw [prod_range_succ (f := fun l => (c (l + 1)) ^ (2 * (n + 1 - l + 1))),
    prod_range_succ (f := fun l => (c (l + 1)) ^ 2), prod_range_succ']
  simp only [Nat.succ_ne_zero, if_false, if_true, one_pow, mul_one]
  rw [show 2 * (n + 1 - n + 1) = 4 from by omega]
  have hcomb : (∏ x ∈ range n, (c (x + 1)) ^ 2)
        * (∏ x ∈ range n, ((c (x + 1)) ^ 2) ^ (n + 1 - (x + 1) + 1))
      = ∏ x ∈ range n, (c (x + 1)) ^ (2 * (n + 1 - x + 1)) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl (fun x hx => ?_)
    rw [← pow_mul, ← pow_add]
    rw [mem_range] at hx
    congr 1
    omega
  rw [← hcomb]
  ring

end NormalCollapse

open Finset in
/-- Normal case (`η = 1`): for a strictly-degree-decreasing-by-one PRS with `αₗ = (lc F_{l+1})²`,
`βₗ = (lc Fₗ)²`, the subresultant equals the PRS element, `S_{deg F_{m+1}-1}(F₀,F₁) = F_{m+2}`. -/
theorem subresultant_prs_normal_eq [IsDomain R] (F : ℕ → R[X]) (Q : ℕ → R[X]) (m d : ℕ)
    (hm : 1 ≤ m) (hd : m + 2 ≤ d)
    (hdeg : ∀ l ≤ m + 2, (F l).natDegree = d - l)
    (hlc : ∀ l ≤ m + 1, (F l).coeff (F l).natDegree ≠ 0)
    (hQ : ∀ l ≤ m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l ≤ m,
      C (((F (l + 1)).coeff (F (l + 1)).natDegree) ^ 2) * F l
        = C (if l = 0 then (1 : R) else ((F l).coeff (F l).natDegree) ^ 2) * F (l + 2)
          + F (l + 1) * Q l) :
    subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree ((F (m + 1)).natDegree - 1)
      = F (m + 2) := by
  set α : ℕ → R := fun l => ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ 2 with hα
  set β : ℕ → R := fun l => if l = 0 then (1 : R) else ((F l).coeff (F l).natDegree) ^ 2 with hβ
  have hcb : ∀ l ≤ m, (F (l + 2)).natDegree < (F (l + 1)).natDegree := by
    intro l hl; rw [hdeg (l + 2) (by omega), hdeg (l + 1) (by omega)]; omega
  have hj' : ∀ l < m, (F (m + 1)).natDegree - 1 < (F (l + 2)).natDegree := by
    intro l hl; rw [hdeg (m + 1) (by omega), hdeg (l + 2) (by omega)]; omega
  have hβne : ∀ l ≤ m, β l ≠ 0 := by
    intro l hl; simp only [hβ]; split
    · exact one_ne_zero
    · exact pow_ne_zero _ (hlc l (by omega))
  have hclosed := subresultant_prs_closed_top F α β Q m hβne hcb hj' hQ hrel
  -- degree facts (range m membership ⇒ l < m)
  have hE : ∀ l ∈ range m, (F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1) = m - l + 1 := by
    intro l hl; rw [mem_range] at hl; rw [hdeg (l + 1) (by omega), hdeg (m + 1) (by omega)]; omega
  have hG : ∀ l ∈ range m, (F l).natDegree - (F (l + 2)).natDegree = 2 := by
    intro l hl; rw [mem_range] at hl; rw [hdeg l (by omega), hdeg (l + 2) (by omega)]; omega
  have hSgn : ∀ l ∈ range m,
      (-1 : R[X]) ^ (((F l).natDegree - ((F (m + 1)).natDegree - 1))
        * ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1))) = 1 := by
    intro l hl
    refine Even.neg_one_pow ?_
    rw [mem_range] at hl
    rw [hdeg l (by omega), hdeg (l + 1) (by omega), hdeg (m + 1) (by omega)]
    rw [show d - l - (d - (m + 1) - 1) = (m - l + 1) + 1 from by omega,
      show d - (l + 1) - (d - (m + 1) - 1) = m - l + 1 from by omega, mul_comm]
    exact Nat.even_mul_succ_self _
  have hend : (F m).natDegree - (F (m + 1)).natDegree + 1 = 2 := by
    rw [hdeg m (by omega), hdeg (m + 1) (by omega)]; omega
  have hL : C (α m) * ∏ l ∈ range m, C (α l ^ ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1)))
      = C (((F (m + 1)).coeff (F (m + 1)).natDegree) ^ 2
          * ∏ l ∈ range m, ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ (2 * (m - l + 1))) := by
    rw [map_mul, map_prod]
    simp only [hα]
    congr 1
    refine prod_congr rfl (fun l hl => ?_)
    rw [hE l hl, ← pow_mul]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  set SL : R := ((F (k + 1 + 1)).coeff (F (k + 1 + 1)).natDegree) ^ 2
      * ∏ l ∈ range (k + 1), ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ (2 * (k + 1 - l + 1))
    with hSLdef
  have hScal : ((F (k + 1 + 1)).coeff (F (k + 1 + 1)).natDegree) ^ 2
        * (β (k + 1) * ∏ l ∈ range (k + 1),
            (((F (l + 1)).coeff (F (l + 1)).natDegree) ^ 2 * β l ^ (k + 1 - l + 1)))
      = SL := by
    rw [hSLdef]
    have hcol := lc_prod_collapse_normal (fun l => (F l).coeff (F l).natDegree) k
    rw [hcol, prod_mul_distrib]
    simp only [hβ]
    rw [if_neg (Nat.succ_ne_zero k)]
    ring
  rw [hL] at hclosed
  have hSLne : C SL ≠ 0 := by
    rw [Ne, C_eq_zero, hSLdef]
    refine mul_ne_zero (pow_ne_zero _ (hlc (k + 1 + 1) (by omega))) ?_
    rw [Finset.prod_ne_zero_iff]
    intro l hl
    exact pow_ne_zero _ (hlc (l + 1) (by rw [mem_range] at hl; omega))
  have hprodR : (∏ l ∈ range (k + 1),
        ((-1 : R[X]) ^ (((F l).natDegree - ((F (k + 1 + 1)).natDegree - 1))
              * ((F (l + 1)).natDegree - ((F (k + 1 + 1)).natDegree - 1)))
          * C ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ ((F l).natDegree - (F (l + 2)).natDegree)
          * C (β l ^ ((F (l + 1)).natDegree - ((F (k + 1 + 1)).natDegree - 1)))))
      = ∏ l ∈ range (k + 1),
          ((C ((F (l + 1)).coeff (F (l + 1)).natDegree)) ^ 2 * C (β l ^ (k + 1 - l + 1))) := by
    refine prod_congr rfl (fun l hl => ?_)
    rw [hSgn l hl, hG l hl, hE l hl, one_mul]
  rw [hend, neg_one_sq, one_mul, hprodR] at hclosed
  have hBprod : (∏ l ∈ range (k + 1),
        ((C ((F (l + 1)).coeff (F (l + 1)).natDegree)) ^ 2 * C (β l ^ (k + 1 - l + 1))))
      = C (∏ l ∈ range (k + 1),
          (((F (l + 1)).coeff (F (l + 1)).natDegree) ^ 2 * β l ^ (k + 1 - l + 1))) := by
    rw [map_prod]
    refine prod_congr rfl (fun l hl => ?_)
    simp only [map_mul, map_pow]
  rw [hBprod] at hclosed
  rw [show (C (((F (k + 1 + 1)).coeff (F (k + 1 + 1)).natDegree) ^ 2)
        * (C (β (k + 1)) * F (k + 1 + 2)))
        * C (∏ l ∈ range (k + 1),
            (((F (l + 1)).coeff (F (l + 1)).natDegree) ^ 2 * β l ^ (k + 1 - l + 1)))
      = F (k + 1 + 2) * (C (((F (k + 1 + 1)).coeff (F (k + 1 + 1)).natDegree) ^ 2)
        * (C (β (k + 1)) * C (∏ l ∈ range (k + 1),
            (((F (l + 1)).coeff (F (l + 1)).natDegree) ^ 2 * β l ^ (k + 1 - l + 1)))))
      from by ring, ← map_mul, ← map_mul, hScal] at hclosed
  exact mul_right_cancel₀ hSLne hclosed

section DefectiveCollapse

open Finset

variable {M : Type*} [CommMonoid M]

/-- Index shift: `∏_{range m} c(l+1)^(f l)` reindexes to `∏_{Ico 1 (m+1)} c k^(f (k-1))`. -/
theorem shift_prod (c : ℕ → M) (f : ℕ → ℕ) (m : ℕ) :
    ∏ l ∈ range m, (c (l + 1)) ^ (f l) = ∏ k ∈ Ico 1 (m + 1), (c k) ^ (f (k - 1)) := by
  rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  refine prod_congr rfl (fun l _ => ?_)
  rw [show (1 : ℕ) + l - 1 = l from by omega, Nat.add_comm 1 l]

/-- `β`-endpoint fold: with `E m = 1`, the endpoint `c m^(δ_{m-1}+1)` absorbs into the `β`-product,
giving `∏_{Ico 1 (m+1)} c k^((δ_{k-1}+1)·E k)`. -/
theorem beta_fold (c : ℕ → M) (δ E : ℕ → ℕ) (m : ℕ) (hm : 1 ≤ m) (hEm : E m = 1) :
    (c m) ^ (δ (m - 1) + 1)
        * ∏ l ∈ range m, (if l = 0 then (1 : M) else (c l) ^ (δ (l - 1) + 1)) ^ (E l)
      = ∏ k ∈ Ico 1 (m + 1), (c k) ^ ((δ (k - 1) + 1) * E k) := by
  rw [Finset.prod_Ico_succ_top hm, hEm, mul_one, mul_comm]
  congr 1
  rw [Finset.range_eq_Ico, ← Finset.prod_Ico_consecutive _ (Nat.zero_le 1) hm]
  rw [show ∏ l ∈ Ico 0 1, (if l = 0 then (1 : M) else (c l) ^ (δ (l - 1) + 1)) ^ (E l) = 1 from by
        rw [← Finset.range_eq_Ico, Finset.prod_range_one]; simp, one_mul]
  refine prod_congr rfl (fun l hl => ?_)
  rw [Finset.mem_Ico] at hl
  rw [if_neg (by omega), ← pow_mul]

/-- General-`δ` leading-coefficient collapse (defective case): with `E k = E(k+1)+δ(k+1)`, `1 ≤ δ k`, and
`E m = 1`, the `α`-product equals the `(βₘ·lc·β)`-product times the coefficient `∏ c(l+1)^(δ l·(δ(l+1)-1))`. -/
theorem lc_collapse_defective (c : ℕ → M) (δ E : ℕ → ℕ) (m : ℕ) (hm : 1 ≤ m)
    (hE : ∀ k, k < m → E k = E (k + 1) + δ (k + 1)) (hδ : ∀ k, 0 < k → k ≤ m → 1 ≤ δ k)
    (hEm : E m = 1) :
    ∏ l ∈ range m, (c (l + 1)) ^ ((δ l + 1) * E l)
      = (c m) ^ (δ (m - 1) + 1)
        * (∏ l ∈ range m, ((c (l + 1)) ^ (δ l + δ (l + 1))
            * (if l = 0 then (1 : M) else (c l) ^ (δ (l - 1) + 1)) ^ (E l)))
        * ∏ l ∈ range m, (c (l + 1)) ^ (δ l * (δ (l + 1) - 1)) := by
  rw [Finset.prod_mul_distrib]
  have hR :
      (c m) ^ (δ (m - 1) + 1)
        * ((∏ l ∈ range m, (c (l + 1)) ^ (δ l + δ (l + 1)))
            * ∏ l ∈ range m, (if l = 0 then (1 : M) else (c l) ^ (δ (l - 1) + 1)) ^ (E l))
        * ∏ l ∈ range m, (c (l + 1)) ^ (δ l * (δ (l + 1) - 1))
      = ((c m) ^ (δ (m - 1) + 1)
            * ∏ l ∈ range m, (if l = 0 then (1 : M) else (c l) ^ (δ (l - 1) + 1)) ^ (E l))
          * (∏ l ∈ range m, (c (l + 1)) ^ (δ l + δ (l + 1)))
          * ∏ l ∈ range m, (c (l + 1)) ^ (δ l * (δ (l + 1) - 1)) := by ac_rfl
  rw [hR, beta_fold c δ E m hm hEm, shift_prod c (fun l => δ l + δ (l + 1)) m,
    shift_prod c (fun l => δ l * (δ (l + 1) - 1)) m, shift_prod c (fun l => (δ l + 1) * E l) m,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine prod_congr rfl (fun k hk => ?_)
  rw [Finset.mem_Ico] at hk
  rw [← pow_add, ← pow_add]
  congr 1
  simp only [show (k - 1) + 1 = k from by omega]
  have hEk : E (k - 1) = E k + δ k := by
    have h := hE (k - 1) (by omega); rwa [show k - 1 + 1 = k from by omega] at h
  have hb := hδ k (by omega) (by omega)
  rw [hEk]
  rcases hd : δ k with _ | p
  · omega
  · simp; ring

end DefectiveCollapse

section SubresPRSCoeff

variable {K : Type*} [Field K]

/-- The subresultant-PRS coefficient `γ`: `γ₀ = 1`, `γ₁ = -1`, `γᵢ₊₁ = (-rᵢ)^δᵢ · γᵢ^(1-δᵢ)`. -/
noncomputable def subresPRS_gamma (r : ℕ → K) (δ : ℕ → ℕ) : ℕ → K
  | 0 => 1
  | 1 => -1
  | (i + 2) => (-(r (i + 1))) ^ (δ (i + 1))
      * (subresPRS_gamma r δ (i + 1)) ^ ((1 : ℤ) - (δ (i + 1) : ℤ))

/-- The subresultant-PRS coefficient `β`: `β₁ = (-1)^(δ₁+1)`, `βᵢ₊₁ = -rᵢ · γᵢ₊₁^(δᵢ+1)`. -/
noncomputable def subresPRS_beta (r : ℕ → K) (δ : ℕ → ℕ) : ℕ → K
  | 0 => 1
  | 1 => (-1) ^ (δ 1 + 1)
  | (i + 2) => -(r (i + 1)) * (subresPRS_gamma r δ (i + 2)) ^ (δ (i + 1) + 1)

/-- The coefficients `γᵢ` are nonzero for `i ≥ 1`, provided every `rᵢ` is nonzero. -/
theorem subresPRS_gamma_ne_zero (r : ℕ → K) (δ : ℕ → ℕ) (hr : ∀ i, r i ≠ 0) :
    ∀ i, 1 ≤ i → subresPRS_gamma r δ i ≠ 0 := by
  intro i
  induction i with
  | zero => omega
  | succ n ih =>
    intro _
    match n, ih with
    | 0, _ => simp [subresPRS_gamma]
    | (k + 1), ih =>
      rw [subresPRS_gamma]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr (hr (k + 1))))
        (zpow_ne_zero _ (ih (by omega)))

end SubresPRSCoeff

/-- Defective (gap) vanishing: `Sⱼ(F₀,F₁) = 0` at every index strictly inside the last degree gap,
`deg F_{m+2} < j < deg F_{m+1} − 1`. -/
theorem subresultant_prs_gap_zero [IsDomain R] (F : ℕ → R[X]) (α β : ℕ → R) (Q : ℕ → R[X]) (m j : ℕ)
    (hα : ∀ l ≤ m, α l ≠ 0) (hβ : ∀ l ≤ m, β l ≠ 0)
    (hcb : ∀ l ≤ m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, j < (F (l + 2)).natDegree)
    (hQ : ∀ l ≤ m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l ≤ m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l)
    (hlo : (F (m + 2)).natDegree < j) (hhi : j < (F (m + 1)).natDegree - 1) :
    subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree j = 0 := by
  apply subresultant_prs_vanish F α β Q j m (fun l hl => hα l (by omega))
    (fun l hl => hβ l (by omega)) (fun l hl => hcb l (by omega)) hj
    (fun l hl => hQ l (by omega)) (fun l hl => hrel l (by omega))
  exact subresultant_prs_step_gap (F m) (F (m + 1)) (F (m + 2)) (Q m) (α m) (β m)
    (F m).natDegree (F (m + 1)).natDegree (F (m + 2)).natDegree j (hα m le_rfl) (hβ m le_rfl)
    hlo hhi rfl le_rfl (hQ m le_rfl) (hrel m le_rfl)

open Finset in
/-- Defective (general-gap) closed form: for a degree-decreasing reduced PRS with
`αₗ = (lc F_{l+1})^(δₗ+1)`, `βₗ = (lc Fₗ)^(δ_{l-1}+1)`, the denominator-cleared identity
`(∏ (lc F_{l+1})^(δₗ(δ_{l+1}-1)))·S_{deg F_{m+1}-1}(F₀,F₁) = SIGN·F_{m+2}` holds. -/
theorem subresultant_prs_defective_eq [IsDomain R] (F : ℕ → R[X]) (Q : ℕ → R[X]) (m : ℕ)
    (hm : 1 ≤ m) (hdec : ∀ l ≤ m + 1, (F (l + 1)).natDegree < (F l).natDegree)
    (hm1 : 1 ≤ (F (m + 1)).natDegree)
    (hlc : ∀ l ≤ m + 1, (F l).coeff (F l).natDegree ≠ 0)
    (hQ : ∀ l ≤ m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l ≤ m,
      C (((F (l + 1)).coeff (F (l + 1)).natDegree)
          ^ ((F l).natDegree - (F (l + 1)).natDegree + 1)) * F l
        = C (if l = 0 then (1 : R)
              else ((F l).coeff (F l).natDegree) ^ ((F (l - 1)).natDegree - (F l).natDegree + 1))
          * F (l + 2) + F (l + 1) * Q l) :
    C (∏ l ∈ range m, ((F (l + 1)).coeff (F (l + 1)).natDegree)
          ^ (((F l).natDegree - (F (l + 1)).natDegree)
              * ((F (l + 1)).natDegree - (F (l + 2)).natDegree - 1)))
        * subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree ((F (m + 1)).natDegree - 1)
      = ((-1 : R[X]) ^ ((F m).natDegree - (F (m + 1)).natDegree + 1)
          * ∏ l ∈ range m, (-1 : R[X]) ^ (((F l).natDegree - ((F (m + 1)).natDegree - 1))
              * ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1))))
        * F (m + 2) := by
  set c : ℕ → R := fun l => (F l).coeff (F l).natDegree with hc
  set δ : ℕ → ℕ := fun l => (F l).natDegree - (F (l + 1)).natDegree with hδdef
  set E : ℕ → ℕ := fun l => (F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1) with hEdef
  set α : ℕ → R := fun l => ((F (l + 1)).coeff (F (l + 1)).natDegree)
      ^ ((F l).natDegree - (F (l + 1)).natDegree + 1) with hαdef
  set β : ℕ → R := fun l => if l = 0 then (1 : R)
      else ((F l).coeff (F l).natDegree) ^ ((F (l - 1)).natDegree - (F l).natDegree + 1) with hβdef
  have hmono : ∀ a b, a ≤ b → b ≤ m + 1 → (F b).natDegree ≤ (F a).natDegree := by
    have key : ∀ e a, a + e ≤ m + 1 → (F (a + e)).natDegree ≤ (F a).natDegree := by
      intro e; induction e with
      | zero => intro a _; simp
      | succ f ih => intro a ha
                     have h1 := hdec (a + f) (by omega); have h2 := ih a (by omega)
                     rw [show a + (f + 1) = a + f + 1 from by ring]; omega
    intro a b hab hb
    have := key (b - a) a (by omega); rwa [show a + (b - a) = b from by omega] at this
  have hcb : ∀ l ≤ m, (F (l + 2)).natDegree < (F (l + 1)).natDegree := fun l hl => hdec (l + 1) (by omega)
  have hβne : ∀ l ≤ m, β l ≠ 0 := by
    intro l hl; simp only [hβdef]; split
    · exact one_ne_zero
    · exact pow_ne_zero _ (hlc l (by omega))
  have hclosed := subresultant_prs_closed_top F α β Q m hβne hcb
    (fun l hl => by have := hmono (l + 2) (m + 1) (by omega) (by omega); omega) hQ hrel
  have hcol := lc_collapse_defective c δ E m hm
    (fun k hk => by simp only [hEdef, hδdef]
                    have h1 := hdec (k + 1) (by omega)
                    have h2 := hmono (k + 1 + 1) (m + 1) (by omega) (by omega)
                    have h3 := hmono (k + 1) (m + 1) (by omega) (by omega); omega)
    (fun k hk0 hkm => by simp only [hδdef]; have := hdec k (by omega); omega)
    (by simp only [hEdef]; omega)
  have hL : C (α m) * ∏ l ∈ range m, C (α l ^ E l)
      = C (α m * (((F m).coeff (F m).natDegree) ^ ((F (m - 1)).natDegree - (F m).natDegree + 1)
            * ∏ l ∈ range m, ((c (l + 1)) ^ (δ l + δ (l + 1))
                * (if l = 0 then (1 : R)
                    else ((F l).coeff (F l).natDegree) ^ ((F (l - 1)).natDegree - (F l).natDegree + 1))
                  ^ (E l))))
        * C (∏ l ∈ range m, (c (l + 1)) ^ (δ l * (δ (l + 1) - 1))) := by
    rw [← map_prod, ← map_mul, ← map_mul]; congr 1
    have hconv : ∏ l ∈ range m, α l ^ E l = ∏ l ∈ range m, (c (l + 1)) ^ ((δ l + 1) * E l) := by
      refine prod_congr rfl (fun l _ => ?_); simp only [hαdef, hc, hδdef]; rw [← pow_mul]
    have hbr : (∏ l ∈ range m, ((c (l + 1)) ^ (δ l + δ (l + 1))
            * (if l = 0 then (1 : R) else (c l) ^ (δ (l - 1) + 1)) ^ (E l)))
        = ∏ l ∈ range m, ((c (l + 1)) ^ (δ l + δ (l + 1))
            * (if l = 0 then (1 : R)
                else ((F l).coeff (F l).natDegree) ^ ((F (l - 1)).natDegree - (F l).natDegree + 1)) ^ (E l)) := by
      refine prod_congr rfl (fun l hl => ?_); rw [mem_range] at hl
      rcases Nat.eq_zero_or_pos l with h0 | h0
      · simp [h0]
      · rw [if_neg (by omega), if_neg (by omega)]
        simp only [hc, hδdef]; rw [show l - 1 + 1 = l from by omega]
    rw [hconv, hcol, hbr,
      show (c m) ^ (δ (m - 1) + 1)
          = ((F m).coeff (F m).natDegree) ^ ((F (m - 1)).natDegree - (F m).natDegree + 1) from by
        simp only [hc, hδdef]; rw [show m - 1 + 1 = m from by omega]]
    ac_rfl
  have hGl : ∏ l ∈ range m, ((c (l + 1)) ^ ((F l).natDegree - (F (l + 2)).natDegree) * β l ^ (E l))
      = ∏ l ∈ range m, ((c (l + 1)) ^ (δ l + δ (l + 1)) * β l ^ (E l)) := by
    refine prod_congr rfl (fun l hl => ?_); rw [mem_range] at hl
    rw [show (F l).natDegree - (F (l + 2)).natDegree = δ l + δ (l + 1) from by
      have e1 : (F (l + 1)).natDegree < (F l).natDegree := hdec l (by omega)
      have e2 : (F (l + 2)).natDegree < (F (l + 1)).natDegree := hdec (l + 1) (by omega)
      simp only [hδdef, show l + 1 + 1 = l + 2 from rfl]; omega]
  have hsigns : (∏ l ∈ range m,
        ((-1 : R[X]) ^ (((F l).natDegree - ((F (m + 1)).natDegree - 1))
              * ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1)))
          * C ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ ((F l).natDegree - (F (l + 2)).natDegree)
          * C (β l ^ ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1)))))
      = (∏ l ∈ range m, (-1 : R[X]) ^ (((F l).natDegree - ((F (m + 1)).natDegree - 1))
              * ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1))))
        * C (∏ l ∈ range m, ((c (l + 1)) ^ ((F l).natDegree - (F (l + 2)).natDegree)
              * β l ^ ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1)))) := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine prod_congr rfl (fun l _ => ?_)
    simp only [map_mul, map_pow, hc]
    ring
  rw [hL, hsigns, hGl] at hclosed
  set LCR : R := α m * (((F m).coeff (F m).natDegree) ^ ((F (m - 1)).natDegree - (F m).natDegree + 1)
      * ∏ l ∈ range m, ((c (l + 1)) ^ (δ l + δ (l + 1))
          * (if l = 0 then (1 : R)
              else ((F l).coeff (F l).natDegree) ^ ((F (l - 1)).natDegree - (F l).natDegree + 1)) ^ (E l)))
    with hLCR
  have hLCne : C LCR ≠ 0 := by
    rw [Ne, C_eq_zero, hLCR]
    simp only [hαdef]
    refine mul_ne_zero (pow_ne_zero _ (hlc (m + 1) (by omega)))
      (mul_ne_zero (pow_ne_zero _ (hlc m (by omega))) ?_)
    rw [Finset.prod_ne_zero_iff]
    intro l hl; rw [mem_range] at hl
    refine mul_ne_zero (pow_ne_zero _ (hlc (l + 1) (by omega))) (pow_ne_zero _ ?_)
    split
    · exact one_ne_zero
    · exact pow_ne_zero _ (hlc l (by omega))
  have hgoal : C (∏ l ∈ range m, (c (l + 1)) ^ (δ l * (δ (l + 1) - 1)))
        * subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree ((F (m + 1)).natDegree - 1)
      = ((-1 : R[X]) ^ ((F m).natDegree - (F (m + 1)).natDegree + 1)
          * ∏ l ∈ range m, (-1 : R[X]) ^ (((F l).natDegree - ((F (m + 1)).natDegree - 1))
              * ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1))))
        * F (m + 2) := by
    refine mul_left_cancel₀ hLCne ?_
    rw [show C LCR * (C (∏ l ∈ range m, (c (l + 1)) ^ (δ l * (δ (l + 1) - 1)))
            * subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree ((F (m + 1)).natDegree - 1))
          = subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree ((F (m + 1)).natDegree - 1)
              * (C LCR * C (∏ l ∈ range m, (c (l + 1)) ^ (δ l * (δ (l + 1) - 1)))) from by ring,
        hclosed, hLCR]
    simp only [hαdef, hβdef]
    rw [if_neg (show m ≠ 0 by omega)]
    simp only [map_mul, map_pow, map_prod, hc]
    ring
  exact hgoal

end DeepWiki.SymbolicIntegration
