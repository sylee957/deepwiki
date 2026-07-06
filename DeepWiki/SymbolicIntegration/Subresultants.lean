import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-! # Subresultants
The `j`-th subresultant `Sⱼ(A,B)` as a sum of `(m+n−2j)`-square Sylvester submatrix
determinants against `xⁱ`; the `0`-th subresultant is the resultant. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R]

open Matrix Finset in
/-- Closed-form Laplace expansion of a `4×4` determinant. -/
theorem det_fin_four (M : Matrix (Fin 4) (Fin 4) R) :
    M.det =
      M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) - M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
                + M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1))
      - M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) - M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
                + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0))
      + M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) - M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
                + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))
      - M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1) - M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)
                + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  simp only [det_succ_row_zero, submatrix_apply, Fin.succ_zero_eq_one, submatrix_submatrix,
    det_unique, Fin.default_eq_zero, Function.comp_apply, Fin.succ_one_eq_two, Fin.sum_univ_succ,
    Fin.val_zero, Fin.zero_succAbove, univ_unique, Fin.val_succ, Fin.val_eq_zero,
    Fin.succ_succAbove_zero, sum_singleton, Fin.succ_succAbove_one,
    show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl,
    show (Fin.succAbove (1 : Fin 4) 2 : Fin 4) = 3 from rfl,
    show (Fin.succAbove (2 : Fin 4) 2 : Fin 4) = 3 from rfl,
    show (Fin.succAbove (3 : Fin 4) 2 : Fin 4) = 2 from rfl]
  ring

/-- Sylvester matrix of `A` (degree `n`) and `B` (degree `m`): `m` shifted `A`-rows then `n` shifted `B`-rows. -/
def bSylvester (A B : R[X]) (n m : ℕ) : Matrix (Fin (m + n)) (Fin (m + n)) R :=
  .of fun i l =>
    if (i : ℕ) < m then
      (if (i : ℕ) ≤ (l : ℕ) ∧ (l : ℕ) ≤ (i : ℕ) + n then A.coeff (n + i - l) else 0)
    else
      (if (i : ℕ) - m ≤ (l : ℕ) ∧ (l : ℕ) ≤ (i : ℕ) then B.coeff ((i : ℕ) - l) else 0)

/-- Row selector for `ⱼSᵢ`: keep `A`-rows `0..m−j−1` then `B`-rows `m..m+n−j−1` (delete the last
`j` rows of each block). -/
def subRow (n m j : ℕ) : Fin (m + n - 2 * j) → Fin (m + n) :=
  fun t => ⟨if (t : ℕ) < m - j then (t : ℕ) else (t : ℕ) + j, by have := t.isLt; split <;> omega⟩

/-- Column selector for `ⱼSᵢ`: keep the first `m+n−2j−1` columns plus column `m+n−i−j−1`. -/
def subCol (n m j i : ℕ) : Fin (m + n - 2 * j) → Fin (m + n) :=
  fun s => ⟨if (s : ℕ) < m + n - 2 * j - 1 then (s : ℕ) else m + n - i - j - 1,
    by have := s.isLt; split <;> omega⟩

/-- The `j`-th subresultant `Sⱼ(A,B) = ∑_{i=0}^{j} det(ⱼSᵢ)·xⁱ` of Sylvester submatrices. -/
noncomputable def subresultant (A B : R[X]) (n m j : ℕ) : R[X] :=
  ∑ i ∈ Finset.range (j + 1),
    C ((bSylvester A B n m).submatrix (subRow n m j) (subCol n m j i)).det * X ^ i

/-- For `j = 0` the row/column selectors are the identity. -/
theorem subRow_zero (n m : ℕ) : subRow n m 0 = id := by
  funext t; apply Fin.ext; simp only [subRow, Nat.sub_zero, Nat.add_zero, ite_self, id_eq]

theorem subCol_zero (n m : ℕ) : subCol n m 0 0 = id := by
  funext s; apply Fin.ext
  have := s.isLt
  simp only [subCol, Nat.mul_zero, Nat.sub_zero, id_eq]
  split
  · rfl
  · omega

/-- `S₀(A,B) = C (det (Sylvester A B))`: the `0`-th subresultant is the resultant. -/
theorem subresultant_zero (A B : R[X]) (n m : ℕ) :
    subresultant A B n m 0 = C (bSylvester A B n m).det := by
  rw [subresultant, Finset.sum_range_one, subRow_zero, subCol_zero, Matrix.submatrix_id_id,
    pow_zero, mul_one]

/-- `Sⱼ(σA, σB) = σ(Sⱼ(A,B))`: the subresultant commutes with a coefficient ring homomorphism `σ` at fixed formal degrees. -/
theorem subresultant_map {S : Type*} [CommRing S] (σ : R →+* S) (A B : R[X]) (n m j : ℕ) :
    subresultant (A.map σ) (B.map σ) n m j = (subresultant A B n m j).map σ := by
  have hbS : bSylvester (A.map σ) (B.map σ) n m = (bSylvester A B n m).map σ := by
    ext i l
    simp only [bSylvester, Matrix.map_apply, Matrix.of_apply, coeff_map]
    split <;> split <;> simp [map_zero]
  rw [subresultant, subresultant, Polynomial.map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hbS, Matrix.submatrix_map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

open Matrix Finset in
/-- Scaling law: `Sⱼ(a·A, b·B) = a^(m−j)·b^(n−j)·Sⱼ(A,B)`. -/
theorem subresultant_C_mul (a b : R) (A B : R[X]) (n m j : ℕ) (hjm : j ≤ m) (hjn : j ≤ n) :
    subresultant (C a * A) (C b * B) n m j
      = C (a ^ (m - j) * b ^ (n - j)) * subresultant A B n m j := by
  rw [subresultant, subresultant, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hentry : ∀ p q, bSylvester (C a * A) (C b * B) n m p q
      = (if (p : ℕ) < m then a else b) * bSylvester A B n m p q := by
    intro p q; simp only [bSylvester, Matrix.of_apply, coeff_C_mul]; split <;> (split <;> ring)
  have hsub : ((bSylvester (C a * A) (C b * B) n m).submatrix (subRow n m j) (subCol n m j i))
      = Matrix.diagonal (fun t => if (subRow n m j t : ℕ) < m then a else b)
        * ((bSylvester A B n m).submatrix (subRow n m j) (subCol n m j i)) := by
    ext t s; simp only [Matrix.submatrix_apply, Matrix.diagonal_mul, hentry]
  rw [hsub, Matrix.det_mul, Matrix.det_diagonal]
  have hprod : (∏ t : Fin (m + n - 2 * j), if (subRow n m j t : ℕ) < m then a else b)
      = a ^ (m - j) * b ^ (n - j) := by
    have hcond : ∀ t : Fin (m + n - 2 * j), ((subRow n m j t : ℕ) < m ↔ (t : ℕ) < m - j) := by
      intro t; have := t.isLt; simp only [subRow]; split <;> omega
    rw [Finset.prod_congr rfl (fun t _ => if_congr (hcond t) rfl rfl), Finset.prod_ite,
      Finset.prod_const, Finset.prod_const]
    have hcardA : (Finset.univ.filter (fun t : Fin (m + n - 2 * j) => (t : ℕ) < m - j)).card
        = m - j := by
      conv_rhs => rw [← Finset.card_range (m - j)]
      apply Finset.card_bij (fun (t : Fin (m + n - 2 * j)) _ => (t : ℕ))
      · intro t ht; rw [Finset.mem_filter] at ht; exact Finset.mem_range.mpr ht.2
      · intro t₁ _ t₂ _ he; exact Fin.val_injective he
      · intro x hx; exact ⟨⟨x, by have := Finset.mem_range.mp hx; omega⟩,
          by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, Finset.mem_range.mp hx⟩, rfl⟩
    have hcardB : (Finset.univ.filter (fun t : Fin (m + n - 2 * j) => ¬(t : ℕ) < m - j)).card
        = n - j := by
      rw [Finset.filter_not, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Fintype.card_fin, hcardA]; omega
    rw [hcardA, hcardB]
  rw [hprod, map_mul]; ring

/-- `Sⱼ(C c · A, B) = c^(m−j) · Sⱼ(A, B)` (`j ≤ m`, `j ≤ n`): subresultant scaled in the first argument. -/
theorem subresultant_C_mul_left (c : R) (A B : R[X]) (n m j : ℕ)
    (hjm : j ≤ m) (hjn : j ≤ n) :
    subresultant (C c * A) B n m j = C (c ^ (m - j)) * subresultant A B n m j := by
  have h := subresultant_C_mul c 1 A B n m j hjm hjn
  rw [map_one, one_mul, one_pow, mul_one] at h
  rw [h]

/-- Determinant is additive over a `Finset`-sum in a single column. -/
theorem det_updateCol_sum' {N : Type*} [DecidableEq N] [Fintype N] (M : Matrix N N R) (c : N)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → N → R) :
    (M.updateCol c (∑ i ∈ s, g i)).det = ∑ i ∈ s, (M.updateCol c (g i)).det := by
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]
             exact Matrix.det_eq_zero_of_column_eq_zero c (fun i => by simp)
  | insert a s ha ih => rw [Finset.sum_insert ha, Matrix.det_updateCol_add, ih, Finset.sum_insert ha]

/-- `Sⱼ(A,B)` equals the determinant of the `C`-lifted submatrix with its last column replaced by the polynomial `∑ᵢ Xⁱ·(column i)`. -/
theorem subresultant_eq_det_polyCol (A B : R[X]) (n m j : ℕ) (hlt : 2 * j < m + n) :
    subresultant A B n m j
      = (Matrix.updateCol
          (fun (t s : Fin (m + n - 2 * j)) => C (bSylvester A B n m (subRow n m j t) (subCol n m j 0 s)))
          ⟨m + n - 2 * j - 1, by omega⟩
          (∑ i ∈ Finset.range (j + 1), fun (t : Fin (m + n - 2 * j)) =>
            (X : R[X]) ^ i • C (bSylvester A B n m (subRow n m j t)
              (subCol n m j i ⟨m + n - 2 * j - 1, by omega⟩)))).det := by
  rw [subresultant, det_updateCol_sum']
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (fun (t : Fin (m + n - 2 * j)) => (X : R[X]) ^ i
        • C (bSylvester A B n m (subRow n m j t) (subCol n m j i ⟨m + n - 2 * j - 1, by omega⟩)))
      = (X : R[X]) ^ i • (fun (t : Fin (m + n - 2 * j)) =>
        C (bSylvester A B n m (subRow n m j t) (subCol n m j i ⟨m + n - 2 * j - 1, by omega⟩)))
      from rfl, Matrix.det_updateCol_smul]
  have hcol : (Matrix.updateCol
      (fun (t s : Fin (m + n - 2 * j)) => C (bSylvester A B n m (subRow n m j t) (subCol n m j 0 s)))
      ⟨m + n - 2 * j - 1, by omega⟩
      (fun t => C (bSylvester A B n m (subRow n m j t) (subCol n m j i ⟨m + n - 2 * j - 1, by omega⟩))))
      = ((bSylvester A B n m).submatrix (subRow n m j) (subCol n m j i)).map C := by
    ext t s
    by_cases hs : s = ⟨m + n - 2 * j - 1, by omega⟩
    · subst hs; simp [Matrix.submatrix_apply]
    · rw [Matrix.updateCol_apply, if_neg hs]
      simp only [Matrix.submatrix_apply, Matrix.map_apply]
      have hne : (s : ℕ) ≠ m + n - 2 * j - 1 := fun h => hs (Fin.ext h)
      have hsv : (s : ℕ) < m + n - 2 * j - 1 := by have := s.isLt; omega
      have hsub : subCol n m j 0 s = subCol n m j i s := by
        apply Fin.ext; simp only [subCol]; rw [if_pos hsv, if_pos hsv]
      rw [hsub]
  rw [hcol, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact mul_comm _ _

/-- Determinant is unchanged by adding a `Finset`-sum of scalar multiples of other rows to a row. -/
theorem det_updateRow_add_sum_smul_self {N : Type*} [DecidableEq N] [Fintype N] (M : Matrix N N R)
    (i : N) {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → R) (f : ι → N)
    (hf : ∀ k ∈ s, f k ≠ i) :
    (M.updateRow i (M i + ∑ k ∈ s, c k • M (f k))).det = M.det := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hfa : f a ≠ i := hf a (Finset.mem_insert_self a s)
    have hsub : ∀ k ∈ s, f k ≠ i := fun k hk => hf k (Finset.mem_insert_of_mem hk)
    set M' := M.updateRow i (M i + ∑ k ∈ s, c k • M (f k)) with hM'
    have hMi' : M' i = M i + ∑ k ∈ s, c k • M (f k) := by rw [hM']; exact Matrix.updateRow_self
    have hMfa' : M' (f a) = M (f a) := by rw [hM']; exact Matrix.updateRow_ne hfa
    have h1 := Matrix.det_updateRow_add_smul_self M' hfa.symm (c a)
    rw [hMi', hMfa'] at h1
    rw [Finset.sum_insert ha]
    rw [show M i + (c a • M (f a) + ∑ k ∈ s, c k • M (f k))
        = (M i + ∑ k ∈ s, c k • M (f k)) + c a • M (f a) by abel]
    rw [show M.updateRow i ((M i + ∑ k ∈ s, c k • M (f k)) + c a • M (f a))
        = M'.updateRow i ((M i + ∑ k ∈ s, c k • M (f k)) + c a • M (f a)) by
      rw [hM', Matrix.updateRow_idem]]
    rw [h1, hM', ih hsub]

/-- `Sⱼ(A + a·Xᵈ·B, B) = Sⱼ(A,B)`: subresultant invariance under adding a monomial multiple of `B` to `A`. -/
theorem subresultant_add_monomial_mul (A B : R[X]) (a : R) (n m j d : ℕ)
    (hjn : j < n) (hB : B.natDegree ≤ m) (hd : m + d ≤ n) :
    subresultant (A + C a * (X ^ d * B)) B n m j = subresultant A B n m j := by
  rw [subresultant, subresultant]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  set P : Matrix (Fin (m + n - 2 * j)) (Fin (m + n - 2 * j)) R :=
    Matrix.of (fun t t' => if (t : ℕ) < m - j ∧ (t' : ℕ) = n - j + (t : ℕ) - d then 1 else 0) with hP
  have hTtri : (1 + a • P : Matrix _ _ R).BlockTriangular id := by
    intro u v huv
    simp only [Matrix.add_apply, Matrix.smul_apply, hP, Matrix.of_apply, id] at huv ⊢
    rw [Matrix.one_apply_ne (fun h => absurd (h ▸ huv) (lt_irrefl _)),
      if_neg (by rintro ⟨_, h⟩; omega), smul_zero, add_zero]
  have hTdet : (1 + a • P : Matrix _ _ R).det = 1 := by
    rw [Matrix.det_of_upperTriangular hTtri]
    refine Finset.prod_eq_one (fun t _ => ?_)
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, hP, Matrix.of_apply]
    rw [if_neg (by rintro ⟨_, h⟩; omega), smul_zero, add_zero]
  set M := (bSylvester A B n m).submatrix (subRow n m j) (subCol n m j i) with hM
  have hprod : (bSylvester (A + C a * (X ^ d * B)) B n m).submatrix (subRow n m j) (subCol n m j i)
      = (1 + a • P) * M := by
    ext t s
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul]
    set l := (subCol n m j i s : ℕ) with hl
    by_cases ht : (t : ℕ) < m - j
    · have hb1 : n - j + (t : ℕ) - d < m + n - 2 * j := by have := t.isLt; omega
      have hPMt : (P * M) t s = M ⟨n - j + (t : ℕ) - d, hb1⟩ s := by
        rw [hP, Matrix.mul_apply, Finset.sum_eq_single ⟨n - j + (t : ℕ) - d, hb1⟩]
        · simp only [Matrix.of_apply, ht, true_and, if_true, one_mul]
        · intro b _ hb
          simp only [Matrix.of_apply]; rw [if_neg (fun hc => hb (Fin.ext hc.2)), zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hPMt, hM, Matrix.submatrix_apply, Matrix.submatrix_apply, Matrix.submatrix_apply]
      have hsr : (subRow n m j t : Fin (m + n)) = ⟨(t : ℕ), by have := t.isLt; omega⟩ := by
        apply Fin.ext; simp only [subRow]; rw [if_pos ht]
      have hsr2 : (subRow n m j ⟨n - j + (t : ℕ) - d, hb1⟩ : Fin (m + n))
          = ⟨n + (t : ℕ) - d, by have := t.isLt; omega⟩ := by
        apply Fin.ext; simp only [subRow, Fin.val_mk]
        rw [if_neg (show ¬ (n - j + (t : ℕ) - d < m - j) by omega)]; omega
      rw [hsr, hsr2]
      simp only [bSylvester, Matrix.of_apply, coeff_add, coeff_C_mul, coeff_X_pow_mul', ← hl,
        if_pos (show (t : ℕ) < m by omega), if_neg (show ¬ n + (t : ℕ) - d < m by omega)]
      by_cases hc : (t : ℕ) ≤ l ∧ l ≤ (t : ℕ) + n
      · simp only [if_pos hc]
        by_cases hd2 : d ≤ n + (t : ℕ) - l
        · by_cases hc2a : n + (t : ℕ) - d - m ≤ l
          · rw [if_pos hd2, if_pos (show n + (t : ℕ) - d - m ≤ l ∧ l ≤ n + (t : ℕ) - d by omega),
              Nat.sub_right_comm (n + (t : ℕ)) l d]
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
              (show B.natDegree < n + (t : ℕ) - l - d by omega),
              if_neg (show ¬ (n + (t : ℕ) - d - m ≤ l ∧ l ≤ n + (t : ℕ) - d) by omega)]
            simp only [if_pos hd2, mul_zero]
        · rw [if_neg hd2, if_neg (show ¬ (n + (t : ℕ) - d - m ≤ l ∧ l ≤ n + (t : ℕ) - d) by omega)]
      · simp only [if_neg hc,
          if_neg (show ¬ (n + (t : ℕ) - d - m ≤ l ∧ l ≤ n + (t : ℕ) - d) by omega),
          mul_zero, add_zero]
    · have hPMt : (P * M) t s = 0 := by
        rw [hP, Matrix.mul_apply]; refine Finset.sum_eq_zero (fun b _ => ?_)
        simp only [Matrix.of_apply]; rw [if_neg (fun hc => ht hc.1), zero_mul]
      rw [hPMt, mul_zero, add_zero, hM, Matrix.submatrix_apply, Matrix.submatrix_apply]
      have hsr : (subRow n m j t : Fin (m + n)) = ⟨(t : ℕ) + j, by have := t.isLt; omega⟩ := by
        apply Fin.ext; simp only [subRow]; rw [if_neg ht]
      rw [hsr]
      simp only [bSylvester, Matrix.of_apply, ← hl, if_neg (show ¬ (t : ℕ) + j < m by omega)]
  rw [hprod, Matrix.det_mul, hTdet, one_mul]

/-- `Sⱼ(A + c·B, B) = Sⱼ(A,B)`: invariance under adding a constant multiple of `B` to `A`. -/
theorem subresultant_add_const_mul (A B : R[X]) (c : R) (n m j : ℕ)
    (hmn : m ≤ n) (hjn : j < n) (hB : B.natDegree ≤ m) :
    subresultant (A + C c * B) B n m j = subresultant A B n m j := by
  simpa using subresultant_add_monomial_mul A B c n m j 0 hjn hB (by omega)

/-- `Sⱼ(A + B·p, B) = Sⱼ(A,B)`: invariance under adding any polynomial multiple of `B` to `A`. -/
theorem subresultant_add_mul (A B p : R[X]) (n m j : ℕ)
    (hjn : j < n) (hB : B.natDegree ≤ m) (hp : p.natDegree + m ≤ n) :
    subresultant (A + B * p) B n m j = subresultant A B n m j := by
  have key : ∀ N, (∀ e ∈ Finset.range N, m + e ≤ n) → ∀ A' : R[X],
      subresultant (A' + ∑ e ∈ Finset.range N, C (p.coeff e) * (X ^ e * B)) B n m j
        = subresultant A' B n m j := by
    intro N
    induction N with
    | zero => intro _ A'; simp
    | succ N ih =>
      intro hN A'
      rw [Finset.sum_range_succ, ← add_assoc,
        subresultant_add_monomial_mul _ B (p.coeff N) n m j N hjn hB
          (hN N (Finset.self_mem_range_succ N))]
      exact ih (fun e he => hN e (Finset.mem_range.mpr
        (Nat.lt_succ_of_lt (Finset.mem_range.mp he)))) A'
  have hsum : B * p = ∑ e ∈ Finset.range (p.natDegree + 1), C (p.coeff e) * (X ^ e * B) := by
    conv_lhs => rw [p.as_sum_range_C_mul_X_pow, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  rw [hsum]
  exact key (p.natDegree + 1) (fun e he => by have := Finset.mem_range.mp he; omega) A

/-- `bSylvester B A m n` is `bSylvester A B n m` reindexed by the block permutation swapping the `A`- and `B`-rows. -/
theorem bSylvester_swap (A B : R[X]) (n m : ℕ) :
    bSylvester B A m n = (bSylvester A B n m).submatrix
      (fun i : Fin (n + m) => (⟨if (i : ℕ) < n then m + (i : ℕ) else (i : ℕ) - n,
        by have := i.isLt; split <;> omega⟩ : Fin (m + n)))
      (finCongr (Nat.add_comm n m)) := by
  refine Matrix.ext fun i l => ?_
  simp only [bSylvester, Matrix.submatrix_apply, Matrix.of_apply, finCongr_apply, Fin.val_cast]
  by_cases hi : (i : ℕ) < n
  · simp only [if_pos hi, if_neg (show ¬ m + (i : ℕ) < m by omega),
      show m + (i : ℕ) - m = (i : ℕ) from by omega, Nat.add_comm (i : ℕ) m]
  · simp only [if_neg hi, if_pos (show (i : ℕ) - n < m by have := i.isLt; omega),
      show n + ((i : ℕ) - n) - (l : ℕ) = (i : ℕ) - (l : ℕ) from by omega,
      show (i : ℕ) - n + n = (i : ℕ) from by omega]

/-- `((finRotate (N+1))^q r : ℕ) = (r + q) % (N+1)`: the `q`-th power of `finRotate` adds `q` mod `N+1`. -/
theorem finRotate_pow_val (N q : ℕ) (r : Fin (N + 1)) :
    (((finRotate (N + 1)) ^ q) r : ℕ) = (r.val + q) % (N + 1) := by
  have hstep : ∀ x : Fin (N + 1), (finRotate (N + 1) x : ℕ) = (x.val + 1) % (N + 1) := by
    intro x
    rw [coe_finRotate]
    split_ifs with h
    · subst h; simp [Fin.val_last]
    · rw [Nat.mod_eq_of_lt (by have := Fin.val_lt_last h; omega)]
  induction q with
  | zero => simp [Nat.mod_eq_of_lt r.isLt]
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, hstep, ih, Nat.mod_add_mod]; congr 1

open Matrix Equiv in
/-- `finRotate_pow_val` for any positive modulus `K` (reduces to the `N+1` form). -/
theorem finRotate_pow_val_pos (K q : ℕ) (hK : 0 < K) (r : Fin K) :
    ((finRotate K ^ q) r : ℕ) = (r.val + q) % K := by
  obtain ⟨N, rfl⟩ : ∃ N, K = N + 1 := ⟨K - 1, by omega⟩
  exact finRotate_pow_val N q r

open Matrix Equiv in
/-- `det ⱼSᵢ(B,A) = (-1)^((m-j)(n-j)) · det ⱼSᵢ(A,B)`: sign of the per-minor row swap. -/
theorem bSylvester_submatrix_det_swap (A B : R[X]) (n m j i : ℕ) (hjm : j ≤ m) (hjn : j < n) :
    ((bSylvester B A m n).submatrix (subRow m n j) (subCol m n j i)).det
      = (-1 : R) ^ ((m - j) * (n - j)) *
        ((bSylvester A B n m).submatrix (subRow n m j) (subCol n m j i)).det := by
  set ρ : Equiv.Perm (Fin (n + m - 2 * j)) :=
    { toFun := fun s => ⟨if (s : ℕ) < n - j then (s : ℕ) + (m - j) else (s : ℕ) - (n - j),
        by have := s.isLt; split <;> omega⟩
      invFun := fun r => ⟨if (r : ℕ) < m - j then (r : ℕ) + (n - j) else (r : ℕ) - (m - j),
        by have := r.isLt; split <;> omega⟩
      left_inv := fun s => by apply Fin.ext; have := s.isLt; dsimp only; split_ifs <;> omega
      right_inv := fun r => by apply Fin.ext; have := r.isLt; dsimp only; split_ifs <;> omega }
    with hρ
  set c : Fin (n + m - 2 * j) ≃ Fin (m + n - 2 * j) := finCongr (by omega) with hc
  have hentry : (bSylvester B A m n).submatrix (subRow m n j) (subCol m n j i)
      = (((bSylvester A B n m).submatrix (subRow n m j) (subCol n m j i)).submatrix c c).submatrix
          ρ id := by
    rw [bSylvester_swap]
    refine Matrix.ext fun s s' => ?_
    simp only [Matrix.submatrix_apply, id_eq]
    congr 1
    · apply Fin.ext
      simp only [hρ, hc, Equiv.coe_fn_mk, finCongr_apply, Fin.val_cast, subRow]
      have := s.isLt; split_ifs <;> omega
    · apply Fin.ext
      simp only [hc, finCongr_apply, Fin.val_cast, subCol]
      have := s'.isLt; split_ifs <;> omega
  rw [hentry, Matrix.det_permute, Matrix.det_submatrix_equiv_self]
  have hsign : (Equiv.Perm.sign ρ : R) = (-1 : R) ^ ((m - j) * (n - j)) := by
    have heq : ρ = finRotate (n + m - 2 * j) ^ (m - j) := by
      apply Equiv.ext; intro s; apply Fin.ext
      rw [finRotate_pow_val_pos _ _ (by omega), hρ]
      simp only [Equiv.coe_fn_mk]
      have := s.isLt
      split_ifs with h
      · rw [Nat.mod_eq_of_lt (by omega)]
      · rw [show (s : ℕ) + (m - j) = ((s : ℕ) - (n - j)) + (n + m - 2 * j) from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [heq, map_pow, sign_finRotate]
    push_cast
    rw [← pow_mul, show n + m - 2 * j - 1 = (m - j) + (n - j) - 1 from by omega]
    obtain ⟨p, rfl⟩ : ∃ p, m = j + p := ⟨m - j, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, n = j + q := ⟨n - j, by omega⟩
    simp only [Nat.add_sub_cancel_left]
    have key : (p + q - 1) * p = p * q + p * (p - 1) := by
      cases p with
      | zero => simp
      | succ k =>
        rw [show k + 1 + q - 1 = k + q from by omega, show k + 1 - 1 = k from by omega]; ring
    have heven : Even (p * (p - 1)) := by
      cases p with
      | zero => simp
      | succ k => rw [Nat.succ_sub_one, mul_comm]; exact Nat.even_mul_succ_self k
    rw [key, pow_add, heven.neg_one_pow, mul_one, mul_comm p q]
  rw [hsign]

/-- `Sⱼ(A,B) = (-1)^((m-j)(n-j)) · Sⱼ(B,A)`: swapping the polynomials multiplies the subresultant by a sign. -/
theorem subresultant_swap (A B : R[X]) (n m j : ℕ) (hjm : j ≤ m) (hjn : j < n) :
    subresultant A B n m j = (-1 : R[X]) ^ ((m - j) * (n - j)) * subresultant B A m n j := by
  rw [subresultant, subresultant, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [bSylvester_submatrix_det_swap A B n m j i hjm hjn, map_mul, map_pow, map_neg, map_one,
    ← mul_assoc, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]

/-- `Sⱼ(A,B) = (-1)^((m-j)(n-j)) · Sⱼ(B,Rem)` for a division step `A = Rem + B·Q`. -/
theorem subresultant_rem (A B Q Rem : R[X]) (n m j : ℕ) (hjm : j ≤ m) (hjn : j < n)
    (hB : B.natDegree ≤ m) (hQ : Q.natDegree + m ≤ n) (hA : A = Rem + B * Q) :
    subresultant A B n m j = (-1 : R[X]) ^ ((m - j) * (n - j)) * subresultant B Rem m n j := by
  rw [hA, subresultant_add_mul Rem B Q n m j hjn hB hQ, subresultant_swap Rem B n m j hjm hjn]

/-- Deleting the first row and column of the `ⱼSᵢ` submatrix at formal degree `d+1` gives the `ⱼSᵢ` submatrix at degree `d`. -/
private theorem subresultant_pad_entry (B Rem : R[X]) (m d j i : ℕ) (hjd : j < d) (hjm : j ≤ m)
    (hij : i ≤ j) (hRem : Rem.natDegree ≤ d) (s s' : Fin (d + m - 2 * j)) :
    (bSylvester B Rem m (d + 1)) (subRow m (d + 1) j ⟨(s : ℕ) + 1, by have := s.isLt; omega⟩)
        (subCol m (d + 1) j i ⟨(s' : ℕ) + 1, by have := s'.isLt; omega⟩)
      = (bSylvester B Rem m d) (subRow m d j s) (subCol m d j i s') := by
  have hs := s.isLt; have hs' := s'.isLt
  simp only [bSylvester, subRow, subCol, Matrix.of_apply]
  by_cases hsB : (s : ℕ) + 1 < (d + 1) - j <;>
    by_cases hcol : (s' : ℕ) + 1 < (d + 1) + m - 2 * j - 1 <;>
    [ (rw [if_pos hsB, if_pos (show (s : ℕ) < d - j by omega), if_pos hcol,
          if_pos (show (s' : ℕ) < d + m - 2 * j - 1 by omega),
          if_pos (show (s : ℕ) + 1 < d + 1 by omega), if_pos (show (s : ℕ) < d by omega)]) ;
      (rw [if_pos hsB, if_pos (show (s : ℕ) < d - j by omega), if_neg hcol,
          if_neg (show ¬ (s' : ℕ) < d + m - 2 * j - 1 by omega),
          if_pos (show (s : ℕ) + 1 < d + 1 by omega), if_pos (show (s : ℕ) < d by omega)]) ;
      (rw [if_neg hsB, if_neg (show ¬ (s : ℕ) < d - j by omega), if_pos hcol,
          if_pos (show (s' : ℕ) < d + m - 2 * j - 1 by omega),
          if_neg (show ¬ (s : ℕ) + 1 + j < d + 1 by omega),
          if_neg (show ¬ (s : ℕ) + j < d by omega)]) ;
      (rw [if_neg hsB, if_neg (show ¬ (s : ℕ) < d - j by omega), if_neg hcol,
          if_neg (show ¬ (s' : ℕ) < d + m - 2 * j - 1 by omega),
          if_neg (show ¬ (s : ℕ) + 1 + j < d + 1 by omega),
          if_neg (show ¬ (s : ℕ) + j < d by omega)]) ] <;>
    (split_ifs <;>
      first | rfl | rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)] | (congr 1; omega))

/-- Column `0` of the `ⱼSᵢ` submatrix at formal degree `d+1` has its only nonzero entry `B.coeff m` at row `0`. -/
private theorem subresultant_pad_col0 (B Rem : R[X]) (m d j i : ℕ) (hjd : j < d) (hjm : j ≤ m)
    (_hB : B.natDegree ≤ m) (hRem : Rem.natDegree ≤ d) (s c0 : Fin (d + 1 + m - 2 * j))
    (hc0 : (c0 : ℕ) = 0) :
    ((bSylvester B Rem m (d + 1)).submatrix (subRow m (d + 1) j) (subCol m (d + 1) j i)) s c0
      = if (s : ℕ) = 0 then B.coeff m else 0 := by
  have hs := s.isLt
  simp only [Matrix.submatrix_apply, subCol, subRow, bSylvester, Matrix.of_apply]
  rw [hc0, if_pos (show (0 : ℕ) < d + 1 + m - 2 * j - 1 by omega)]
  by_cases hs0 : (s : ℕ) = 0
  · rw [hs0]
    simp only [if_pos (show (0 : ℕ) < (d + 1) - j by omega), if_pos (show (0 : ℕ) < d + 1 by omega),
      if_pos (show (0 : ℕ) ≤ 0 ∧ (0 : ℕ) ≤ 0 + m by omega)]
    simp
  · rw [if_neg hs0]
    split_ifs <;> first | rfl | rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- `Sⱼ(B,Rem; m,d+1) = C (B.coeff m) · Sⱼ(B,Rem; m,d)`: raising `Rem`'s formal degree by one scales by `lc B`. -/
theorem subresultant_pad_step (B Rem : R[X]) (m d j : ℕ) (hjd : j < d) (hjm : j ≤ m)
    (hB : B.natDegree ≤ m) (hRem : Rem.natDegree ≤ d) :
    subresultant B Rem m (d + 1) j = C (B.coeff m) * subresultant B Rem m d j := by
  rw [subresultant, subresultant, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hij : i ≤ j := by rw [Finset.mem_range] at hi; omega
  have hdet : ((bSylvester B Rem m (d + 1)).submatrix (subRow m (d + 1) j)
        (subCol m (d + 1) j i)).det
      = B.coeff m * ((bSylvester B Rem m d).submatrix (subRow m d j) (subCol m d j i)).det := by
    set e : Fin ((d + m - 2 * j) + 1) ≃ Fin (d + 1 + m - 2 * j) := finCongr (by omega) with he
    rw [← Matrix.det_submatrix_equiv_self e, Matrix.det_succ_column_zero,
      Finset.sum_eq_single (0 : Fin ((d + m - 2 * j) + 1))]
    · rw [Matrix.submatrix_apply,
        subresultant_pad_col0 B Rem m d j i hjd hjm hB hRem (e 0) (e 0) (by simp [he])]
      simp only [Fin.val_zero, pow_zero, one_mul]
      rw [show ((e 0 : Fin _) : ℕ) = 0 by simp [he], if_pos rfl]
      congr 1
      congr 1
      apply Matrix.ext
      intro s s'
      rw [Matrix.submatrix_apply, Matrix.submatrix_apply, Matrix.submatrix_apply]
      have hrow : e ((0 : Fin ((d + m - 2 * j) + 1)).succAbove s)
          = (⟨(s : ℕ) + 1, by have := s.isLt; omega⟩ : Fin (d + 1 + m - 2 * j)) := by
        apply Fin.ext; simp [he]
      have hcol : e (Fin.succ s')
          = (⟨(s' : ℕ) + 1, by have := s'.isLt; omega⟩ : Fin (d + 1 + m - 2 * j)) := by
        apply Fin.ext; simp [he]
      rw [hrow, hcol, subresultant_pad_entry B Rem m d j i hjd hjm hij hRem s s',
        Matrix.submatrix_apply]
    · intro p _ hp
      have hpne : ((e p : Fin (d + 1 + m - 2 * j)) : ℕ) ≠ 0 := by
        simp only [he, finCongr_apply, Fin.val_cast]
        exact fun h => hp (Fin.ext h)
      rw [Matrix.submatrix_apply,
        subresultant_pad_col0 B Rem m d j i hjd hjm hB hRem (e p) (e 0) (by simp [he]), if_neg hpne]
      ring
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hdet, map_mul]; ring

/-- `Sⱼ(B,Rem; m,n) = C (B.coeff m)^(n−k) · Sⱼ(B,Rem; m,k)`: padding `Rem`'s formal degree from `k` to `n`. -/
theorem subresultant_padding (B Rem : R[X]) (m k j : ℕ) (hjk : j < k) (hjm : j ≤ m)
    (hB : B.natDegree ≤ m) (hRem : Rem.natDegree ≤ k) :
    ∀ n, k ≤ n →
      subresultant B Rem m n j = (C (B.coeff m)) ^ (n - k) * subresultant B Rem m k j := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [subresultant_pad_step B Rem m n j (by omega) hjm hB (by omega), ih, ← mul_assoc,
      ← pow_succ', show n - k + 1 = n + 1 - k from by omega]

/-- `Sⱼ(A,B) = (-1)^((m-j)(n-j)) · C (B.coeff m)^(n−k) · Sⱼ(B,Rem)` at `k = Rem.natDegree`, for `A = Rem + B·Q` and `j < k`. -/
theorem subresultant_rem_lt (A B Q Rem : R[X]) (n m j : ℕ) (hjm : j ≤ m)
    (hjk : j < Rem.natDegree) (hkn : Rem.natDegree ≤ n) (hB : B.natDegree ≤ m)
    (hQ : Q.natDegree + m ≤ n) (hA : A = Rem + B * Q) :
    subresultant A B n m j
      = (-1 : R[X]) ^ ((m - j) * (n - j)) *
        ((C (B.coeff m)) ^ (n - Rem.natDegree) * subresultant B Rem m Rem.natDegree j) := by
  rw [subresultant_rem A B Q Rem n m j hjm (by omega) hB hQ hA,
    subresultant_padding B Rem m Rem.natDegree j hjk hjm hB le_rfl n hkn]

/-- Per-minor value at `j = γ-1`: `det ⱼSᵢ = (B.coeff γ)^(φ-γ+1) · Rem.coeff i`. -/
private theorem subresultant_deg_sub_one_entry (B Rem : R[X]) (γ φ i : ℕ) (hγ : 1 ≤ γ)
    (hγφ : γ ≤ φ) (hRem : Rem.natDegree < γ) (hi : i < γ) :
    ((bSylvester B Rem γ φ).submatrix (subRow γ φ (γ - 1)) (subCol γ φ (γ - 1) i)).det
      = (B.coeff γ) ^ (φ - γ + 1) * Rem.coeff i := by
  set e : Fin ((φ - γ + 1) + 1) ≃ Fin (φ + γ - 2 * (γ - 1)) := finCongr (by omega) with he
  rw [← Matrix.det_submatrix_equiv_self e, Matrix.det_of_upperTriangular]
  · rw [Fin.prod_univ_castSucc]
    congr 1
    · rw [Finset.prod_congr rfl (fun t _ => ?_), Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      have htv : ((e (Fin.castSucc t) : Fin _) : ℕ) = (t : ℕ) := by simp [he]
      have hti := t.isLt
      have hrow : (subRow γ φ (γ - 1) (e (Fin.castSucc t)) : ℕ) = (t : ℕ) := by
        simp only [subRow, htv]; rw [if_pos (show (t : ℕ) < φ - (γ - 1) by omega)]
      have hcol : (subCol γ φ (γ - 1) i (e (Fin.castSucc t)) : ℕ) = (t : ℕ) := by
        simp only [subCol, htv]; rw [if_pos (show (t : ℕ) < φ + γ - 2 * (γ - 1) - 1 by omega)]
      rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
      simp only [bSylvester, Matrix.of_apply, hrow, hcol]
      rw [if_pos (show (t : ℕ) < φ by omega), if_pos ⟨le_rfl, by omega⟩]
      congr 1; omega
    · have hlv : ((e (Fin.last (φ - γ + 1)) : Fin _) : ℕ) = φ - γ + 1 := by simp [he]
      have hrow : (subRow γ φ (γ - 1) (e (Fin.last (φ - γ + 1))) : ℕ) = φ := by
        simp only [subRow, hlv]
        rw [if_neg (show ¬ (φ - γ + 1 < φ - (γ - 1)) by omega)]; omega
      have hcol : (subCol γ φ (γ - 1) i (e (Fin.last (φ - γ + 1))) : ℕ) = φ - i := by
        simp only [subCol, hlv]
        rw [if_neg (show ¬ (φ - γ + 1 < φ + γ - 2 * (γ - 1) - 1) by omega)]; omega
      rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
      simp only [bSylvester, Matrix.of_apply, hrow, hcol]
      rw [if_neg (show ¬ (φ < φ) by omega), if_pos ⟨by omega, by omega⟩]
      congr 1; omega
  · intro t s hts
    have hsv : ((e s : Fin _) : ℕ) = (s : ℕ) := by simp [he]
    have htv : ((e t : Fin _) : ℕ) = (t : ℕ) := by simp [he]
    have hstn : (s : ℕ) < (t : ℕ) := by simpa using hts
    have htle := t.isLt
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
    have hcolv : (subCol γ φ (γ - 1) i (e s) : ℕ)
        = if (s : ℕ) < φ + γ - 2 * (γ - 1) - 1 then (s : ℕ) else φ + γ - i - (γ - 1) - 1 := by
      simp only [subCol, hsv]
    have hrowv : (subRow γ φ (γ - 1) (e t) : ℕ)
        = if (t : ℕ) < φ - (γ - 1) then (t : ℕ) else (t : ℕ) + (γ - 1) := by
      simp only [subRow, htv]
    simp only [bSylvester, Matrix.of_apply, hcolv, hrowv]
    by_cases htB : (t : ℕ) < φ - (γ - 1)
    · rw [if_pos htB, if_pos (show (s : ℕ) < φ + γ - 2 * (γ - 1) - 1 by omega),
        if_pos (show (t : ℕ) < φ by omega), if_neg (by omega)]
    · rw [if_neg htB, if_neg (show ¬ ((t : ℕ) + (γ - 1) < φ) by omega)]
      by_cases hsB : (s : ℕ) < φ + γ - 2 * (γ - 1) - 1
      · rw [if_pos hsB, if_pos ⟨by omega, by omega⟩, coeff_eq_zero_of_natDegree_lt (by omega)]
      · rw [if_neg hsB, if_neg (by omega)]

/-- `S_{γ-1}(B,Rem; γ,φ) = C ((B.coeff γ)^(φ-γ+1)) · Rem` for `deg Rem < γ ≤ φ`. -/
theorem subresultant_deg_sub_one (B Rem : R[X]) (γ φ : ℕ) (hγ : 1 ≤ γ) (hγφ : γ ≤ φ)
    (hRem : Rem.natDegree < γ) :
    subresultant B Rem γ φ (γ - 1) = C ((B.coeff γ) ^ (φ - γ + 1)) * Rem := by
  rw [subresultant, show (γ - 1) + 1 = γ from by omega]
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [subresultant_deg_sub_one_entry B Rem γ φ i hγ hγφ hRem (Finset.mem_range.mp hi), map_mul,
      mul_assoc]), ← Finset.mul_sum]
  congr 1
  simp only [C_mul_X_pow_eq_monomial]
  exact (Rem.as_sum_range' γ (by omega)).symm

/-- `S_{γ-1}(A,B) = (-1)^(φ-γ+1) · C ((B.coeff γ)^(φ-γ+1)) · Rem` for `A = Rem + B·Q`, `deg Rem < γ ≤ φ`. -/
theorem subresultant_rem_eq_15 (A B Q Rem : R[X]) (γ φ : ℕ) (hγ : 1 ≤ γ) (hγφ : γ ≤ φ)
    (hB : B.natDegree ≤ γ) (hRem : Rem.natDegree < γ) (hQ : Q.natDegree + γ ≤ φ)
    (hA : A = Rem + B * Q) :
    subresultant A B φ γ (γ - 1)
      = (-1 : R[X]) ^ (φ - γ + 1) * (C ((B.coeff γ) ^ (φ - γ + 1)) * Rem) := by
  rw [subresultant_rem A B Q Rem φ γ (γ - 1) (by omega) (by omega) hB hQ hA,
    subresultant_deg_sub_one B Rem γ φ hγ hγφ hRem,
    show (γ - (γ - 1)) * (φ - (γ - 1)) = φ - γ + 1 from by
      rw [show γ - (γ - 1) = 1 from by omega, one_mul]; omega]

/-- For `j ≥ deg Rem` the `ⱼSᵢ` submatrix of `bSylvester B Rem γ φ` is upper-triangular (entries below the diagonal vanish). -/
private theorem subresultant_deg_ge_upperTri (B Rem : R[X]) (γ φ j i : ℕ) (hj1 : Rem.natDegree ≤ j)
    (hj2 : j < γ) (hγφ : γ ≤ φ)
    (e : Fin ((φ + γ - 2 * j - 1) + 1) ≃ Fin (φ + γ - 2 * j)) (he : e = finCongr (by omega))
    (t s : Fin ((φ + γ - 2 * j - 1) + 1)) (hts : s < t) :
    ((bSylvester B Rem γ φ).submatrix (subRow γ φ j) (subCol γ φ j i)).submatrix e e t s = 0 := by
  have hsv : ((e s : Fin _) : ℕ) = (s : ℕ) := by simp [he]
  have htv : ((e t : Fin _) : ℕ) = (t : ℕ) := by simp [he]
  have hstn : (s : ℕ) < (t : ℕ) := by simpa using hts
  have htle := t.isLt
  rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
  have hcolv : (subCol γ φ j i (e s) : ℕ)
      = if (s : ℕ) < φ + γ - 2 * j - 1 then (s : ℕ) else φ + γ - i - j - 1 := by
    simp only [subCol, hsv]
  have hrowv : (subRow γ φ j (e t) : ℕ)
      = if (t : ℕ) < φ - j then (t : ℕ) else (t : ℕ) + j := by
    simp only [subRow, htv]
  simp only [bSylvester, Matrix.of_apply, hcolv, hrowv]
  by_cases htB : (t : ℕ) < φ - j
  · rw [if_pos htB, if_pos (show (s : ℕ) < φ + γ - 2 * j - 1 by omega),
      if_pos (show (t : ℕ) < φ by omega), if_neg (by omega)]
  · rw [if_neg htB, if_neg (show ¬ ((t : ℕ) + j < φ) by omega),
      if_pos (show (s : ℕ) < φ + γ - 2 * j - 1 by omega)]
    split
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
    · rfl

/-- `Sⱼ(B,Rem; γ,φ) = 0` for `deg Rem < j < γ - 1`. -/
theorem subresultant_deg_mid (B Rem : R[X]) (γ φ j : ℕ) (hj1 : Rem.natDegree < j) (hj2 : j < γ - 1)
    (hγφ : γ ≤ φ) :
    subresultant B Rem γ φ j = 0 := by
  rw [subresultant]
  apply Finset.sum_eq_zero
  intro i hi
  have hij : i ≤ j := by rw [Finset.mem_range] at hi; omega
  set e : Fin ((φ + γ - 2 * j - 1) + 1) ≃ Fin (φ + γ - 2 * j) := finCongr (by omega) with he
  rw [show ((bSylvester B Rem γ φ).submatrix (subRow γ φ j) (subCol γ φ j i)).det = 0 from ?_,
    map_zero, zero_mul]
  rw [← Matrix.det_submatrix_equiv_self e,
    Matrix.det_of_upperTriangular (fun t s hts =>
      subresultant_deg_ge_upperTri B Rem γ φ j i (by omega) (by omega) hγφ e he t s hts)]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨φ - j, by omega⟩ : Fin ((φ + γ - 2 * j - 1) + 1)))
  have hv : ((e (⟨φ - j, by omega⟩ : Fin ((φ + γ - 2 * j - 1) + 1)) : Fin _) : ℕ) = φ - j := by
    simp [he]
  rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
  have hrow : (subRow γ φ j (e ⟨φ - j, by omega⟩) : ℕ) = φ := by
    simp only [subRow, hv]; rw [if_neg (show ¬ (φ - j < φ - j) by omega)]; omega
  have hcol : (subCol γ φ j i (e ⟨φ - j, by omega⟩) : ℕ) = φ - j := by
    simp only [subCol, hv]; rw [if_pos (show φ - j < φ + γ - 2 * j - 1 by omega)]
  simp only [bSylvester, Matrix.of_apply, hrow, hcol]
  rw [if_neg (show ¬ (φ < φ) by omega), if_pos ⟨by omega, by omega⟩]
  exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- `Sⱼ(A,B) = 0` for `A = Rem + B·Q` with `deg Rem < j < γ - 1`. -/
theorem subresultant_rem_eq_14 (A B Q Rem : R[X]) (γ φ j : ℕ) (hj1 : Rem.natDegree < j)
    (hj2 : j < γ - 1) (hγφ : γ ≤ φ) (hB : B.natDegree ≤ γ) (hQ : Q.natDegree + γ ≤ φ)
    (hA : A = Rem + B * Q) :
    subresultant A B φ γ j = 0 := by
  rw [subresultant_rem A B Q Rem φ γ j (by omega) (by omega) hB hQ hA,
    subresultant_deg_mid B Rem γ φ j hj1 hj2 hγφ, mul_zero]

/-- `#{t : Fin M | t.val < k} = k` for `k ≤ M`. -/
private theorem card_filter_lt (M k : ℕ) (h : k ≤ M) :
    (Finset.univ.filter (fun t : Fin M => (t : ℕ) < k)).card = k := by
  conv_rhs => rw [← Finset.card_range k]
  apply Finset.card_bij (fun (t : Fin M) _ => (t : ℕ))
  · intro t ht; rw [Finset.mem_filter] at ht; exact Finset.mem_range.mpr ht.2
  · intro a _ b _ hab; exact Fin.ext hab
  · intro b hb; rw [Finset.mem_range] at hb
    exact ⟨⟨b, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩

/-- Per-minor value for `deg Rem ≤ j < γ`: `det ⱼSᵢ = (B.coeff γ)^(φ-j) · (Rem.coeff j)^(γ-j-1) · Rem.coeff i`. -/
private theorem subresultant_deg_ge_entry (B Rem : R[X]) (γ φ j i : ℕ) (hj1 : Rem.natDegree ≤ j)
    (hj2 : j < γ) (hγφ : γ ≤ φ) (hi : i ≤ j) :
    ((bSylvester B Rem γ φ).submatrix (subRow γ φ j) (subCol γ φ j i)).det
      = (B.coeff γ) ^ (φ - j) * ((Rem.coeff j) ^ (γ - j - 1) * Rem.coeff i) := by
  set e : Fin ((φ + γ - 2 * j - 1) + 1) ≃ Fin (φ + γ - 2 * j) := finCongr (by omega) with he
  rw [← Matrix.det_submatrix_equiv_self e,
    Matrix.det_of_upperTriangular (fun t s hts =>
      subresultant_deg_ge_upperTri B Rem γ φ j i hj1 hj2 hγφ e he t s hts),
    Fin.prod_univ_castSucc]
  have hlast : (((bSylvester B Rem γ φ).submatrix (subRow γ φ j) (subCol γ φ j i)).submatrix e e)
      (Fin.last _) (Fin.last _) = Rem.coeff i := by
    have hlv : ((e (Fin.last (φ + γ - 2 * j - 1)) : Fin _) : ℕ) = φ + γ - 2 * j - 1 := by simp [he]
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
    have hrow : (subRow γ φ j (e (Fin.last (φ + γ - 2 * j - 1))) : ℕ) = φ + γ - j - 1 := by
      simp only [subRow, hlv]; rw [if_neg (show ¬ (φ + γ - 2 * j - 1 < φ - j) by omega)]; omega
    have hcol : (subCol γ φ j i (e (Fin.last (φ + γ - 2 * j - 1))) : ℕ) = φ + γ - i - j - 1 := by
      simp only [subCol, hlv]; rw [if_neg (show ¬ (φ + γ - 2 * j - 1 < φ + γ - 2 * j - 1) by omega)]
    simp only [bSylvester, Matrix.of_apply, hrow, hcol]
    rw [if_neg (show ¬ (φ + γ - j - 1 < φ) by omega), if_pos ⟨by omega, by omega⟩]
    congr 1; omega
  have hmid : ∀ t : Fin (φ + γ - 2 * j - 1),
      (((bSylvester B Rem γ φ).submatrix (subRow γ φ j) (subCol γ φ j i)).submatrix e e)
        (Fin.castSucc t) (Fin.castSucc t)
      = if (t : ℕ) < φ - j then B.coeff γ else Rem.coeff j := by
    intro t
    have htv : ((e (Fin.castSucc t) : Fin _) : ℕ) = (t : ℕ) := by simp [he]
    have hti := t.isLt
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
    have hcol : (subCol γ φ j i (e (Fin.castSucc t)) : ℕ) = (t : ℕ) := by
      simp only [subCol, htv]; rw [if_pos (show (t : ℕ) < φ + γ - 2 * j - 1 by omega)]
    by_cases htB : (t : ℕ) < φ - j
    · have hrow : (subRow γ φ j (e (Fin.castSucc t)) : ℕ) = (t : ℕ) := by
        simp only [subRow, htv]; rw [if_pos (show (t : ℕ) < φ - j by omega)]
      simp only [bSylvester, Matrix.of_apply, hrow, hcol]
      rw [if_pos (show (t : ℕ) < φ by omega), if_pos ⟨le_rfl, by omega⟩, if_pos htB]
      congr 1; omega
    · have hrow : (subRow γ φ j (e (Fin.castSucc t)) : ℕ) = (t : ℕ) + j := by
        simp only [subRow, htv]; rw [if_neg (show ¬ ((t : ℕ) < φ - j) by omega)]
      simp only [bSylvester, Matrix.of_apply, hrow, hcol]
      rw [if_neg (show ¬ ((t : ℕ) + j < φ) by omega), if_pos ⟨by omega, by omega⟩, if_neg htB]
      congr 1; omega
  rw [hlast, Finset.prod_congr rfl (fun t _ => hmid t), Finset.prod_ite, Finset.prod_const,
    Finset.prod_const, card_filter_lt _ _ (by omega)]
  have hcn : (Finset.univ.filter (fun t : Fin (φ + γ - 2 * j - 1) => ¬ (t : ℕ) < φ - j)).card
      = γ - j - 1 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (φ + γ - 2 * j - 1)))) (p := fun t => (t : ℕ) < φ - j)
    rw [card_filter_lt _ _ (by omega), Finset.card_univ, Fintype.card_fin] at h; omega
  rw [hcn]; ring

/-- `Sⱼ(B,Rem; γ,φ) = C ((B.coeff γ)^(φ-j) · (Rem.coeff j)^(γ-j-1)) · Rem` for `deg Rem ≤ j < γ`. -/
theorem subresultant_deg_ge (B Rem : R[X]) (γ φ j : ℕ) (hj1 : Rem.natDegree ≤ j) (hj2 : j < γ)
    (hγφ : γ ≤ φ) :
    subresultant B Rem γ φ j = C ((B.coeff γ) ^ (φ - j) * (Rem.coeff j) ^ (γ - j - 1)) * Rem := by
  rw [subresultant]
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [subresultant_deg_ge_entry B Rem γ φ j i hj1 hj2 hγφ (by rw [Finset.mem_range] at hi; omega),
      show (B.coeff γ) ^ (φ - j) * ((Rem.coeff j) ^ (γ - j - 1) * Rem.coeff i)
        = ((B.coeff γ) ^ (φ - j) * (Rem.coeff j) ^ (γ - j - 1)) * Rem.coeff i from by ring,
      map_mul, mul_assoc]), ← Finset.mul_sum]
  congr 1
  simp only [C_mul_X_pow_eq_monomial]
  exact (Rem.as_sum_range' (j + 1) (by omega)).symm

/-- For `j ≥ deg B`, `m ≤ n` the `ⱼSᵢ` submatrix of `bSylvester A B n m` is upper-triangular (normal orientation). -/
private theorem subresultant_deg_ge_normal_upperTri (A B : R[X]) (n m j i : ℕ)
    (hj1 : B.natDegree ≤ j) (hj2 : j < n) (hmn : m ≤ n) (hjm : j ≤ m)
    (e : Fin ((m + n - 2 * j - 1) + 1) ≃ Fin (m + n - 2 * j)) (he : e = finCongr (by omega))
    (t s : Fin ((m + n - 2 * j - 1) + 1)) (hts : s < t) :
    ((bSylvester A B n m).submatrix (subRow n m j) (subCol n m j i)).submatrix e e t s = 0 := by
  have hsv : ((e s : Fin _) : ℕ) = (s : ℕ) := by simp [he]
  have htv : ((e t : Fin _) : ℕ) = (t : ℕ) := by simp [he]
  have hstn : (s : ℕ) < (t : ℕ) := by simpa using hts
  have htle := t.isLt
  rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
  have hcolv : (subCol n m j i (e s) : ℕ)
      = if (s : ℕ) < m + n - 2 * j - 1 then (s : ℕ) else m + n - i - j - 1 := by
    simp only [subCol, hsv]
  have hrowv : (subRow n m j (e t) : ℕ)
      = if (t : ℕ) < m - j then (t : ℕ) else (t : ℕ) + j := by
    simp only [subRow, htv]
  simp only [bSylvester, Matrix.of_apply, hcolv, hrowv]
  by_cases htB : (t : ℕ) < m - j
  · rw [if_pos htB, if_pos (show (s : ℕ) < m + n - 2 * j - 1 by omega),
      if_pos (show (t : ℕ) < m by omega), if_neg (by omega)]
  · rw [if_neg htB, if_neg (show ¬ ((t : ℕ) + j < m) by omega),
      if_pos (show (s : ℕ) < m + n - 2 * j - 1 by omega)]
    split
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
    · rfl

/-- Per-minor value (normal orientation) for `deg B ≤ j ≤ m ≤ n`, `j < n`: `det ⱼSᵢ = (A.coeff n)^(m-j) · (B.coeff j)^(n-j-1) · B.coeff i`. -/
private theorem subresultant_deg_ge_normal_entry (A B : R[X]) (n m j i : ℕ)
    (hj1 : B.natDegree ≤ j) (hj2 : j < n) (hmn : m ≤ n) (hjm : j ≤ m) (hi : i ≤ j) :
    ((bSylvester A B n m).submatrix (subRow n m j) (subCol n m j i)).det
      = (A.coeff n) ^ (m - j) * ((B.coeff j) ^ (n - j - 1) * B.coeff i) := by
  set e : Fin ((m + n - 2 * j - 1) + 1) ≃ Fin (m + n - 2 * j) := finCongr (by omega) with he
  rw [← Matrix.det_submatrix_equiv_self e,
    Matrix.det_of_upperTriangular (fun t s hts =>
      subresultant_deg_ge_normal_upperTri A B n m j i hj1 hj2 hmn hjm e he t s hts),
    Fin.prod_univ_castSucc]
  have hlast : (((bSylvester A B n m).submatrix (subRow n m j) (subCol n m j i)).submatrix e e)
      (Fin.last _) (Fin.last _) = B.coeff i := by
    have hlv : ((e (Fin.last (m + n - 2 * j - 1)) : Fin _) : ℕ) = m + n - 2 * j - 1 := by simp [he]
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
    have hrow : (subRow n m j (e (Fin.last (m + n - 2 * j - 1))) : ℕ) = m + n - j - 1 := by
      simp only [subRow, hlv]; rw [if_neg (show ¬ (m + n - 2 * j - 1 < m - j) by omega)]; omega
    have hcol : (subCol n m j i (e (Fin.last (m + n - 2 * j - 1))) : ℕ) = m + n - i - j - 1 := by
      simp only [subCol, hlv]; rw [if_neg (show ¬ (m + n - 2 * j - 1 < m + n - 2 * j - 1) by omega)]
    simp only [bSylvester, Matrix.of_apply, hrow, hcol]
    rw [if_neg (show ¬ (m + n - j - 1 < m) by omega), if_pos ⟨by omega, by omega⟩]
    congr 1; omega
  have hmid : ∀ t : Fin (m + n - 2 * j - 1),
      (((bSylvester A B n m).submatrix (subRow n m j) (subCol n m j i)).submatrix e e)
        (Fin.castSucc t) (Fin.castSucc t)
      = if (t : ℕ) < m - j then A.coeff n else B.coeff j := by
    intro t
    have htv : ((e (Fin.castSucc t) : Fin _) : ℕ) = (t : ℕ) := by simp [he]
    have hti := t.isLt
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
    have hcol : (subCol n m j i (e (Fin.castSucc t)) : ℕ) = (t : ℕ) := by
      simp only [subCol, htv]; rw [if_pos (show (t : ℕ) < m + n - 2 * j - 1 by omega)]
    by_cases htA : (t : ℕ) < m - j
    · have hrow : (subRow n m j (e (Fin.castSucc t)) : ℕ) = (t : ℕ) := by
        simp only [subRow, htv]; rw [if_pos (show (t : ℕ) < m - j by omega)]
      simp only [bSylvester, Matrix.of_apply, hrow, hcol]
      rw [if_pos (show (t : ℕ) < m by omega), if_pos ⟨le_rfl, by omega⟩, if_pos htA]
      congr 1; omega
    · have hrow : (subRow n m j (e (Fin.castSucc t)) : ℕ) = (t : ℕ) + j := by
        simp only [subRow, htv]; rw [if_neg (show ¬ ((t : ℕ) < m - j) by omega)]
      simp only [bSylvester, Matrix.of_apply, hrow, hcol]
      rw [if_neg (show ¬ ((t : ℕ) + j < m) by omega), if_pos ⟨by omega, by omega⟩, if_neg htA]
      congr 1; omega
  rw [hlast, Finset.prod_congr rfl (fun t _ => hmid t), Finset.prod_ite, Finset.prod_const,
    Finset.prod_const, card_filter_lt _ _ (by omega)]
  have hcn : (Finset.univ.filter (fun t : Fin (m + n - 2 * j - 1) => ¬ (t : ℕ) < m - j)).card
      = n - j - 1 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (m + n - 2 * j - 1)))) (p := fun t => (t : ℕ) < m - j)
    rw [card_filter_lt _ _ (by omega), Finset.card_univ, Fintype.card_fin] at h; omega
  rw [hcn]; ring

/-- `Sⱼ(A,B; n,m) = C ((A.coeff n)^(m-j) · (B.coeff j)^(n-j-1)) · B` (normal orientation) for `deg B ≤ j ≤ m ≤ n`, `j < n`. -/
theorem subresultant_deg_ge_normal (A B : R[X]) (n m j : ℕ) (hj1 : B.natDegree ≤ j) (hj2 : j < n)
    (hmn : m ≤ n) (hjm : j ≤ m) :
    subresultant A B n m j = C ((A.coeff n) ^ (m - j) * (B.coeff j) ^ (n - j - 1)) * B := by
  rw [subresultant]
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [subresultant_deg_ge_normal_entry A B n m j i hj1 hj2 hmn hjm
        (by rw [Finset.mem_range] at hi; omega),
      show (A.coeff n) ^ (m - j) * ((B.coeff j) ^ (n - j - 1) * B.coeff i)
        = ((A.coeff n) ^ (m - j) * (B.coeff j) ^ (n - j - 1)) * B.coeff i from by ring,
      map_mul, mul_assoc]), ← Finset.mul_sum]
  congr 1
  simp only [C_mul_X_pow_eq_monomial]
  exact (B.as_sum_range' (j + 1) (by omega)).symm

-- The normal-orientation degenerate formula: `Sⱼ(A,B; n,m) = C(...)·B` for `deg B ≤ j ≤ m ≤ n`, `j < n`.
example (A B : R[X]) (n m j : ℕ) (hj1 : B.natDegree ≤ j) (hj2 : j < n) (hmn : m ≤ n) (hjm : j ≤ m) :
    subresultant A B n m j = C ((A.coeff n) ^ (m - j) * (B.coeff j) ^ (n - j - 1)) * B :=
  subresultant_deg_ge_normal A B n m j hj1 hj2 hmn hjm

/-- `S_η(A,B) = (-1)^((φ-η)(γ-η)) · C ((B.coeff γ)^(φ-η) · (lc Rem)^(γ-η-1)) · Rem` at `η = deg Rem`, for `A = Rem + B·Q`. -/
theorem subresultant_rem_eq_13 (A B Q Rem : R[X]) (γ φ : ℕ) (hη : Rem.natDegree < γ) (hγφ : γ ≤ φ)
    (hB : B.natDegree ≤ γ) (hQ : Q.natDegree + γ ≤ φ) (hA : A = Rem + B * Q) :
    subresultant A B φ γ Rem.natDegree
      = (-1 : R[X]) ^ ((φ - Rem.natDegree) * (γ - Rem.natDegree))
        * (C ((B.coeff γ) ^ (φ - Rem.natDegree)
            * Rem.leadingCoeff ^ (γ - Rem.natDegree - 1)) * Rem) := by
  rw [subresultant_rem A B Q Rem φ γ Rem.natDegree (by omega) (by omega) hB hQ hA,
    subresultant_deg_ge B Rem γ φ Rem.natDegree le_rfl hη hγφ,
    Nat.mul_comm (γ - Rem.natDegree) (φ - Rem.natDegree)]
  rfl

/-- PRS step for `α·A = β·C + B·Q`, `0 ≤ j < c`: `α^(b-j)·Sⱼ(A,B) = (-1)^((a-j)(b-j))·(lc B)^(a-c)·β^(b-j)·Sⱼ(B,C)`. -/
theorem subresultant_prs_step [IsDomain R] (A B C_poly Q : R[X]) (α β : R) (a b c j : ℕ)
    (hβ : β ≠ 0) (hjc : j < c) (hcb : c < b) (hcpoly : C_poly.natDegree = c)
    (hB : B.natDegree ≤ b) (hQ : Q.natDegree + b ≤ a)
    (hrel : C α * A = C β * C_poly + B * Q) :
    C (α ^ (b - j)) * subresultant A B a b j
      = (-1 : R[X]) ^ ((a - j) * (b - j))
        * ((C (B.coeff b)) ^ (a - c) * (C (β ^ (b - j)) * subresultant B C_poly b c j)) := by
  have hRn : (C β * C_poly).natDegree = c := by rw [natDegree_C_mul hβ, hcpoly]
  have hL : subresultant (C α * A) B a b j = C (α ^ (b - j)) * subresultant A B a b j := by
    conv_lhs => rw [show B = C (1 : R) * B from by rw [map_one, one_mul]]
    rw [subresultant_C_mul α 1 A B a b j (by omega) (by omega), one_pow, mul_one]
  have hR : subresultant B (C β * C_poly) b c j
      = C (β ^ (b - j)) * subresultant B C_poly b c j := by
    conv_lhs => rw [show B = C (1 : R) * B from by rw [map_one, one_mul]]
    rw [subresultant_C_mul 1 β B C_poly b c j (by omega) (by omega), one_pow, one_mul]
  rw [← hL, subresultant_rem_lt (C α * A) B Q (C β * C_poly) a b j (by omega) (by rw [hRn]; omega)
      (by rw [hRn]; omega) hB hQ hrel, hRn, hR, mul_comm (b - j) (a - j)]

/-- `Sⱼ(α·A, B) = C (α^(b-j)) · Sⱼ(A,B)`: unscale the first argument. -/
private theorem prs_unscale (A B : R[X]) (α : R) (a b j : ℕ) (hjb : j ≤ b) (hja : j ≤ a) :
    subresultant (C α * A) B a b j = C (α ^ (b - j)) * subresultant A B a b j := by
  conv_lhs => rw [show B = C (1 : R) * B from by rw [map_one, one_mul]]
  rw [subresultant_C_mul α 1 A B a b j hjb hja, one_pow, mul_one]

/-- PRS step at `j = b - 1`: `α·S_{b-1}(A,B) = (-1)^(a-b+1) · C ((lc B)^(a-b+1)) · β·C`. -/
theorem subresultant_prs_step_top [IsDomain R] (A B C_poly Q : R[X]) (α β : R) (a b c : ℕ)
    (hβ : β ≠ 0) (hcb : c < b) (hcpoly : C_poly.natDegree = c)
    (hB : B.natDegree ≤ b) (hQ : Q.natDegree + b ≤ a) (hrel : C α * A = C β * C_poly + B * Q) :
    C α * subresultant A B a b (b - 1)
      = (-1 : R[X]) ^ (a - b + 1) * (C ((B.coeff b) ^ (a - b + 1)) * (C β * C_poly)) := by
  have hRn : (C β * C_poly).natDegree = c := by rw [natDegree_C_mul hβ, hcpoly]
  have hL := prs_unscale A B α a b (b - 1) (by omega) (by omega)
  rw [show b - (b - 1) = 1 from by omega, pow_one] at hL
  rw [← hL, subresultant_rem_eq_15 (C α * A) B Q (C β * C_poly) b a (by omega) (by omega) hB
      (by rw [hRn]; omega) hQ hrel]

/-- Vanishing PRS step: `Sⱼ(A,B) = 0` for `c < j < b - 1`. -/
theorem subresultant_prs_step_gap [IsDomain R] (A B C_poly Q : R[X]) (α β : R) (a b c j : ℕ)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hcj : c < j) (hjb : j < b - 1)
    (hcpoly : C_poly.natDegree = c) (hB : B.natDegree ≤ b) (hQ : Q.natDegree + b ≤ a)
    (hrel : C α * A = C β * C_poly + B * Q) :
    subresultant A B a b j = 0 := by
  have hRn : (C β * C_poly).natDegree = c := by rw [natDegree_C_mul hβ, hcpoly]
  have hL := prs_unscale A B α a b j (by omega) (by omega)
  have h0 : subresultant (C α * A) B a b j = 0 :=
    subresultant_rem_eq_14 (C α * A) B Q (C β * C_poly) b a j (by rw [hRn]; omega) (by omega)
      (by omega) hB hQ hrel
  rw [hL] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h (by rw [C_eq_zero]; exact pow_ne_zero _ hα)
  · exact h

/-- PRS step at `j = c`: `α^(b-c)·S_c(A,B) = (-1)^((a-c)(b-c))·(lc B)^(a-c)·(lc βC)^(b-c-1)·βC`. -/
theorem subresultant_prs_step_deg [IsDomain R] (A B C_poly Q : R[X]) (α β : R) (a b c : ℕ)
    (hβ : β ≠ 0) (hcb : c < b) (hcpoly : C_poly.natDegree = c)
    (hB : B.natDegree ≤ b) (hQ : Q.natDegree + b ≤ a) (hrel : C α * A = C β * C_poly + B * Q) :
    C (α ^ (b - c)) * subresultant A B a b c
      = (-1 : R[X]) ^ ((a - c) * (b - c))
        * (C ((B.coeff b) ^ (a - c) * (C β * C_poly).leadingCoeff ^ (b - c - 1)) * (C β * C_poly)) := by
  have hRn : (C β * C_poly).natDegree = c := by rw [natDegree_C_mul hβ, hcpoly]
  have hL := prs_unscale A B α a b c (by omega) (by omega)
  have key := subresultant_rem_eq_13 (C α * A) B Q (C β * C_poly) b a (by rw [hRn]; omega) (by omega)
    hB hQ hrel
  rw [hRn] at key
  rw [← hL, key]

/-- `σ(Sⱼ(A,B)) = C (σ(lc A))^(deg B − deg σB) · Sⱼ(σA, σB)` when `σ` preserves `deg A` but may lower `deg B`. -/
theorem subresultant_map_lt {S : Type*} [CommRing S] (σ : R →+* S) (A B : R[X]) (j : ℕ)
    (hA : (A.map σ).natDegree = A.natDegree) (hj1 : j < (B.map σ).natDegree)
    (hj2 : j ≤ A.natDegree) :
    (subresultant A B A.natDegree B.natDegree j).map σ
      = (C (σ A.leadingCoeff)) ^ (B.natDegree - (B.map σ).natDegree)
        * subresultant (A.map σ) (B.map σ) (A.map σ).natDegree (B.map σ).natDegree j := by
  rw [hA, ← subresultant_map σ A B A.natDegree B.natDegree j,
    subresultant_padding (A.map σ) (B.map σ) A.natDegree (B.map σ).natDegree j hj1 hj2
      natDegree_map_le (le_refl _) B.natDegree natDegree_map_le]
  congr 3
  rw [coeff_map]
  rfl

end DeepWiki.SymbolicIntegration
