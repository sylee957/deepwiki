import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-! # Subresultants (Bronstein §1.4, Definition 1.4.2)
The `j`-th subresultant `Sⱼ(A,B)` of `A` (degree `n`) and `B` (degree `m`) is built from the
Sylvester matrix by deleting the last `j` rows of each of the `A`- and `B`-blocks and summing the
determinants of the `(m+n−2j)`-square submatrices `ⱼSᵢ` (one per `0 ≤ i ≤ j`) against `xⁱ`. We use
Bronstein's row layout (`m` shifted rows of `A`, then `n` shifted rows of `B`) so the deletion
recipe applies verbatim. The `0`-th subresultant is the resultant (`subresultant_zero`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R]

open Matrix Finset in
/-- Closed-form `4×4` determinant (the `Matrix.det_fin_four` Mathlib lacks): Laplace expansion
along row `0`, each `3×3` minor expanded along its row `0`. Lets a concrete symbolic `4×4`
determinant be computed by `rw [det_fin_four]` + entry reduction + `ring`, avoiding the recursive
`det_succ` blow-up. -/
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

/-- **Sylvester matrix** (§1.4, Bronstein layout): `m` shifted rows of `A` (degree `n`) followed by
`n` shifted rows of `B` (degree `m`), size `(m+n)×(m+n)`. Row `i < m` is `A` shifted by `i`; row
`m ≤ i` is `B` shifted by `i − m`. -/
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

/-- **Definition 1.4.2**: the `j`-th *subresultant* `Sⱼ(A,B) = ∑_{i=0}^{j} det(ⱼSᵢ)·xⁱ ∈ R[x]`,
where `ⱼSᵢ` is the `(m+n−2j)`-square submatrix of the Sylvester matrix selected by `subRow`/`subCol`. -/
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

/-- **The `0`-th subresultant is the resultant** (§1.4): `S₀(A,B) = det(Sylvester(A,B))` (as a
constant polynomial), since the `j = 0` submatrix is the full Sylvester matrix. -/
theorem subresultant_zero (A B : R[X]) (n m : ℕ) :
    subresultant A B n m 0 = C (bSylvester A B n m).det := by
  rw [subresultant, Finset.sum_range_one, subRow_zero, subCol_zero, Matrix.submatrix_id_id,
    pow_zero, mul_one]

/-- **Theorem 1.4.3** (§1.4, degree-preserving case): the subresultant commutes with a coefficient
ring homomorphism `σ`, `Sⱼ(σ̄A, σ̄B) = σ̄(Sⱼ(A,B))`. This is Bronstein's "Note in particular" form —
valid whenever `σ` preserves the degree parameters `n, m` (e.g. `A` or `B` monic). The general case
carries a `σ(lc A)^(deg B − deg σ̄B)` factor when `σ` lowers a degree. -/
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
/-- **Subresultant scaling law** (Geddes–Czapor–Labahn §7.3, used in the proof of the Fundamental
PRS Theorem): scaling the arguments by constants scales the subresultant,
`Sⱼ(a·A, b·B) = a^(m−j)·b^(n−j)·Sⱼ(A,B)`. Each `ⱼSᵢ` keeps `m−j` rows of `A` and `n−j` rows of `B`,
so its determinant scales by `a^(m−j) b^(n−j)` (a uniform factor across `i`). -/
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

/-- Determinant is additive over a `Finset`-sum in a single column. -/
theorem det_updateCol_sum' {N : Type*} [DecidableEq N] [Fintype N] (M : Matrix N N R) (c : N)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → N → R) :
    (M.updateCol c (∑ i ∈ s, g i)).det = ∑ i ∈ s, (M.updateCol c (g i)).det := by
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]
             exact Matrix.det_eq_zero_of_column_eq_zero c (fun i => by simp)
  | insert a s ha ih => rw [Finset.sum_insert ha, Matrix.det_updateCol_add, ih, Finset.sum_insert ha]

/-- **Subresultant as a single polynomial-column determinant** (Geddes–Czapor–Labahn §7.3, eq 7.12;
the form in which the Fundamental-PRS-Theorem row reduction is clean). Since all `ⱼSᵢ` share their
first `m+n−2j−1` columns and differ only in the last (`subCol` index `m+n−i−j−1`),
`Sⱼ(A,B) = ∑ᵢ C(det ⱼSᵢ)·Xⁱ` equals the determinant of the matrix whose last column is the
polynomial `∑ᵢ Xⁱ·(that column)` — derived entirely from this library's own `bSylvester`/`subCol`,
via determinant multilinearity in the last column (`det_updateCol_sum'` + `det_updateCol_smul`) and
`RingHom.map_det` for the `C`-lift. -/
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

/-- Determinant is unchanged when a `Finset`-sum of (scalar multiples of) *other* rows is added to a
row — the iterated transvection that drives the Fundamental-PRS-Theorem row reduction (subtracting
`Q`-multiples of the `B`-rows from the `A`-rows). -/
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

/-- **Subresultant invariance under `A ↦ A + a·Xᵈ·B`** (Geddes §7.3, the single-monomial step of
Lemma 7.1's row reduction): every subresultant `Sⱼ(A,B)` is unchanged by adding `a·Xᵈ·B` to `A`
(requires `j < n`, `B.natDegree ≤ m`, `m + d ≤ n`). Proof: per submatrix,
`ⱼSᵢ(A + a·Xᵈ·B) = (1 + a•P)·ⱼSᵢ(A)`, where `P` sends each A-row to its B-row source shifted by `d`;
`1 + a•P` is unipotent upper-triangular (`det = 1`), and the product is the coefficient identity
`(a·Xᵈ·B).coeff(ν) = a·B.coeff(ν−d)` (the windows agree because `B.coeff` vanishes outside its degree
range). -/
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

/-- **Subresultant invariance under `A ↦ A + c·B`** (the constant `d = 0` case of
`subresultant_add_monomial_mul`): adding a constant multiple of `B` to `A` leaves every `Sⱼ(A,B)`
fixed (`m ≤ n`, `j < n`, `B.natDegree ≤ m`). -/
theorem subresultant_add_const_mul (A B : R[X]) (c : R) (n m j : ℕ)
    (hmn : m ≤ n) (hjn : j < n) (hB : B.natDegree ≤ m) :
    subresultant (A + C c * B) B n m j = subresultant A B n m j := by
  simpa using subresultant_add_monomial_mul A B c n m j 0 hjn hB (by omega)

/-- **Subresultant invariance under `A ↦ A + B·p`** (Geddes §7.3, the full row-reduction half of
Lemma 7.1): for any polynomial `p` with `p.natDegree + m ≤ n`, every subresultant is unchanged by
adding `B·p` to `A` (`j < n`, `B.natDegree ≤ m`). Proof: write `p = ∑ₑ p_e·Xᵉ` and fold the monomial
invariance `subresultant_add_monomial_mul` over the terms. With `p = −Q` (where `A = Q·B + R`) this
yields `Sⱼ(A,B) = Sⱼ(rem(A,B),B)`. -/
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

/-- **Sylvester-matrix swap symmetry** (foundation for the swap half of Geddes §7.3 Lemma 7.1):
swapping the two polynomials reindexes the Sylvester matrix by the block permutation that exchanges
the `m` `A`-rows with the `n` `B`-rows — `bSylvester B A m n` is `bSylvester A B n m` with rows sent
by `φ` (`i ↦ m+i` on the `B`-rows `i < n`, `i ↦ i−n` on the `A`-rows) and columns by the
value-preserving cast. -/
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

/-- The `q`-th power of `finRotate (N+1)` is "add `q` modulo `N+1`": `(finRotate (N+1))^q r` has
underlying value `(r + q) mod (N+1)`. (Mathlib has `finRotate_succ_apply`/`coe_finRotate` but no
closed form for the power; this supplies it, used to identify a block-swap permutation as a power of
`finRotate` and read off its sign.) -/
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
/-- **Determinant swap for the subresultant submatrices** (the per-`ⱼSᵢ` heart of the swap half of
Geddes §7.3 Lemma 7.1): `det ⱼSᵢ(B,A) = (-1)^((m-j)(n-j)) · det ⱼSᵢ(A,B)` (`j ≤ m`, `j < n`). The two
submatrices share rows and columns (`bSylvester_swap`) up to the block permutation `ρ` exchanging the
`(m-j)` kept `A`-rows with the `(n-j)` kept `B`-rows; `ρ` is `(finRotate (n+m-2j))^(m-j)`, so its sign
is `(-1)^((m-j)(n-j))` (`det_permute` + `det_submatrix_equiv_self`). -/
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

/-- **Subresultant swap-with-sign** (Geddes §7.3, the swap half of Lemma 7.1): swapping the two
polynomials multiplies every subresultant by `(-1)^((m-j)(n-j))` —
`Sⱼ(A,B) = (-1)^((m-j)(n-j)) · Sⱼ(B,A)` (`j ≤ m`, `j < n`). Each `ⱼSᵢ` determinant picks up the sign
(`bSylvester_submatrix_det_swap`); since the sign is a square root of unity the factor cancels through
the `C`-coefficients and the sum. -/
theorem subresultant_swap (A B : R[X]) (n m j : ℕ) (hjm : j ≤ m) (hjn : j < n) :
    subresultant A B n m j = (-1 : R[X]) ^ ((m - j) * (n - j)) * subresultant B A m n j := by
  rw [subresultant, subresultant, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [bSylvester_submatrix_det_swap A B n m j i hjm hjn, map_mul, map_pow, map_neg, map_one,
    ← mul_assoc, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]

/-- **Euclidean-step subresultant relation** (Geddes §7.3 Lemma 7.1, the engine of the Fundamental
PRS Theorem): for a division step `A = R + B·Q` (so `R = A − B·Q` is the remainder), every
subresultant of `(A,B)` equals — up to the swap sign — the corresponding subresultant of `(B,R)`:
`Sⱼ(A,B) = (-1)^((m-j)(n-j)) · Sⱼ(B,R)` (`j ≤ m`, `j < n`, `B.natDegree ≤ m`, `Q.natDegree + m ≤ n`).
Combines the row-reduction invariance `subresultant_add_mul` (kill `B·Q`) with `subresultant_swap`. -/
theorem subresultant_rem (A B Q Rem : R[X]) (n m j : ℕ) (hjm : j ≤ m) (hjn : j < n)
    (hB : B.natDegree ≤ m) (hQ : Q.natDegree + m ≤ n) (hA : A = Rem + B * Q) :
    subresultant A B n m j = (-1 : R[X]) ^ ((m - j) * (n - j)) * subresultant B Rem m n j := by
  rw [hA, subresultant_add_mul Rem B Q n m j hjn hB hQ, subresultant_swap Rem B n m j hjm hjn]

end DeepWiki.SymbolicIntegration
