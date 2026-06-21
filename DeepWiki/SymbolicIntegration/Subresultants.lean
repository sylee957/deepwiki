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

/-- Helper for the degree-padding step: when the second polynomial `Rem` has formal degree `d+1`
but true degree `≤ d`, the minor obtained by deleting the first row and column of the `ⱼSᵢ`
submatrix of `bSylvester B Rem m (d+1)` is exactly the corresponding `ⱼSᵢ` submatrix of
`bSylvester B Rem m d` (the column index shifts by one). -/
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

/-- Helper for the degree-padding step: column `0` of the `ⱼSᵢ` submatrix of `bSylvester B Rem m
(d+1)` (with `Rem.natDegree ≤ d`) has the single nonzero entry `B.coeff m` at row `0`. -/
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

/-- **Degree-padding, one step** (Geddes §7.3, the leading-coefficient bookkeeping of Lemma 7.1):
increasing the formal degree of the second polynomial `Rem` from `d` to `d+1` (when its true degree
is `≤ d`) multiplies every subresultant by the leading coefficient `B.coeff m` of the first —
`Sⱼ(B, Rem; m, d+1) = (lc B) · Sⱼ(B, Rem; m, d)` (`j < d`, `j ≤ m`, `B.natDegree ≤ m`,
`Rem.natDegree ≤ d`). Proof: cofactor-expand each `ⱼSᵢ` along its first column, which is `B.coeff m`
times a unit vector (`subresultant_pad_col0`), and identify the minor (`subresultant_pad_entry`). -/
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

/-- **Degree padding** (Geddes §7.3, Lemma 7.1's leading-coefficient correction): a subresultant
computed with the second polynomial `Rem` at formal degree `n` equals `(lc B)^(n−k)` times the one
at `Rem`'s true degree `k`, where `lc B = B.coeff m` — `Sⱼ(B,Rem; m,n) = (B.coeff m)^(n−k) ·
Sⱼ(B,Rem; m,k)` (`j < k`, `j ≤ m`, `B.natDegree ≤ m`, `Rem.natDegree ≤ k ≤ n`). Iterates
`subresultant_pad_step`. -/
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

/-- **Euclidean-step subresultant relation with degree correction** (Geddes §7.3 Lemma 7.1, the
case `0 ≤ j < deg(rem)` of the Fundamental PRS Theorem): for a division step `A = Rem + B·Q`, every
subresultant of `(A,B)` reduces to a genuine subresultant of `(B,Rem)` at `Rem`'s true degree, with
the swap sign and the leading-coefficient power — `Sⱼ(A,B) = (-1)^((m-j)(n-j)) · (lc B)^(n−k) ·
Sⱼ(B,Rem)` where `k = Rem.natDegree` (`j ≤ m`, `j < k ≤ n`, `B.natDegree ≤ m`, `Q.natDegree+m ≤ n`).
Combines `subresultant_rem` and `subresultant_padding`. -/
theorem subresultant_rem_lt (A B Q Rem : R[X]) (n m j : ℕ) (hjm : j ≤ m)
    (hjk : j < Rem.natDegree) (hkn : Rem.natDegree ≤ n) (hB : B.natDegree ≤ m)
    (hQ : Q.natDegree + m ≤ n) (hA : A = Rem + B * Q) :
    subresultant A B n m j
      = (-1 : R[X]) ^ ((m - j) * (n - j)) *
        ((C (B.coeff m)) ^ (n - Rem.natDegree) * subresultant B Rem m Rem.natDegree j) := by
  rw [subresultant_rem A B Q Rem n m j hjm (by omega) hB hQ hA,
    subresultant_padding B Rem m Rem.natDegree j hjk hjm hB le_rfl n hkn]

/-- Per-minor evaluation for the degenerate index `j = γ-1` (Brown–Traub Lemma 1, eq 15):
the `ⱼSᵢ` submatrix of `bSylvester B Rem γ φ` is upper-triangular — its single `Rem`-row is
`[0,…,0, Rem.coeff i]` (since `Rem.coeff(φ-c)=0` on the kept columns, as `φ-c ≥ γ > deg Rem`) and the
`B`-block is upper-triangular with `lc B = B.coeff γ` on the diagonal — so `det = (lc B)^(φ-γ+1)·Rem.coeff i`. -/
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

/-- **Subresultant at index `γ-1`** (Geddes §7.3 / Brown–Traub eq 15): for `deg Rem < γ ≤ φ`,
`Sⱼ(B,Rem; γ,φ) = (lc B)^(φ-γ+1)·Rem` at `j = γ-1` — summing the per-minor determinants
(`subresultant_deg_sub_one_entry`) reassembles `Rem` via `as_sum_range'` (`deg Rem < γ`). -/
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

/-- **Fundamental PRS Theorem, degenerate case `j = deg G − 1`** (Brown–Traub Lemma 1, eq 15): for a
division step `A = Rem + B·Q` with `deg Rem < deg B = γ ≤ deg A = φ`,
`S_{γ-1}(A,B) = (-1)^(φ-γ+1)·(lc B)^(φ-γ+1)·Rem` — the `(γ-1)`-th subresultant is the remainder up to
sign and a power of `lc B`. Composes `subresultant_rem` (swap-with-sign) with `subresultant_deg_sub_one`. -/
theorem subresultant_rem_eq_15 (A B Q Rem : R[X]) (γ φ : ℕ) (hγ : 1 ≤ γ) (hγφ : γ ≤ φ)
    (hB : B.natDegree ≤ γ) (hRem : Rem.natDegree < γ) (hQ : Q.natDegree + γ ≤ φ)
    (hA : A = Rem + B * Q) :
    subresultant A B φ γ (γ - 1)
      = (-1 : R[X]) ^ (φ - γ + 1) * (C ((B.coeff γ) ^ (φ - γ + 1)) * Rem) := by
  rw [subresultant_rem A B Q Rem φ γ (γ - 1) (by omega) (by omega) hB hQ hA,
    subresultant_deg_sub_one B Rem γ φ hγ hγφ hRem,
    show (γ - (γ - 1)) * (φ - (γ - 1)) = φ - γ + 1 from by
      rw [show γ - (γ - 1) = 1 from by omega, one_mul]; omega]

/-- For `j ≥ deg Rem` the `ⱼSᵢ` submatrix of `bSylvester B Rem γ φ` is upper-triangular: the `B`-block
has `lc B`-diagonal with zeros below, and every `Rem`-row entry strictly below the diagonal is
`Rem.coeff` of a degree `> j ≥ deg Rem`, hence `0`. Shared core of the degenerate cases (eqs 13–15). -/
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

/-- **Fundamental PRS Theorem, vanishing case `deg Rem < j < deg G − 1`** (Brown–Traub Lemma 1, eq 14):
`Sⱼ(B,Rem; γ,φ) = 0`. The `ⱼSᵢ` submatrix is upper-triangular (`subresultant_deg_ge_upperTri`) and a
middle `Rem`-row contributes the diagonal entry `Rem.coeff j = 0` (as `j > deg Rem`), so the determinant
vanishes. -/
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

/-- **Fundamental PRS Theorem, vanishing case** (Brown–Traub Lemma 1, eq 14): for a division step
`A = Rem + B·Q` with `deg Rem < j < deg B − 1`, `Sⱼ(A,B) = 0`. Composes `subresultant_rem` with
`subresultant_deg_mid`. -/
theorem subresultant_rem_eq_14 (A B Q Rem : R[X]) (γ φ j : ℕ) (hj1 : Rem.natDegree < j)
    (hj2 : j < γ - 1) (hγφ : γ ≤ φ) (hB : B.natDegree ≤ γ) (hQ : Q.natDegree + γ ≤ φ)
    (hA : A = Rem + B * Q) :
    subresultant A B φ γ j = 0 := by
  rw [subresultant_rem A B Q Rem φ γ j (by omega) (by omega) hB hQ hA,
    subresultant_deg_mid B Rem γ φ j hj1 hj2 hγφ, mul_zero]

/-- `#{t : Fin M | t.val < k} = k` for `k ≤ M` (the first `k` elements of `Fin M`). -/
private theorem card_filter_lt (M k : ℕ) (h : k ≤ M) :
    (Finset.univ.filter (fun t : Fin M => (t : ℕ) < k)).card = k := by
  conv_rhs => rw [← Finset.card_range k]
  apply Finset.card_bij (fun (t : Fin M) _ => (t : ℕ))
  · intro t ht; rw [Finset.mem_filter] at ht; exact Finset.mem_range.mpr ht.2
  · intro a _ b _ hab; exact Fin.ext hab
  · intro b hb; rw [Finset.mem_range] at hb
    exact ⟨⟨b, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩

/-- Per-minor evaluation for `deg Rem ≤ j < γ` (the general degenerate index, Brown–Traub eq 19): the
upper-triangular `ⱼSᵢ` det is the product of its diagonal — `φ-j` copies of `lc B`, `γ-j-1` copies of
`Rem.coeff j`, and one `Rem.coeff i` — so `det = (lc B)^(φ-j)·(Rem.coeff j)^(γ-j-1)·Rem.coeff i`. -/
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

/-- **Subresultant for `deg Rem ≤ j < γ`** (Geddes §7.3 / Brown–Traub eq 19, the unified degenerate
formula): `Sⱼ(B,Rem; γ,φ) = (lc B)^(φ-j)·(Rem.coeff j)^(γ-j-1)·Rem`. Summing the per-minor determinants
(`subresultant_deg_ge_entry`) reassembles `Rem` (`as_sum_range'`, `deg Rem ≤ j`). Specializes to eq 15
(`j=γ-1`, exponent `0`), eq 14 (`j>deg Rem` ⇒ `Rem.coeff j = 0`), and eq 13 (`j=deg Rem`). -/
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

/-- **Fundamental PRS Theorem, case `j = deg H`** (Brown–Traub Lemma 1, eq 13): for a division step
`A = Rem + B·Q` with `deg Rem < deg B = γ ≤ deg A = φ`,
`S_η(A,B) = (-1)^((φ-η)(γ-η))·(lc B)^(φ-η)·(lc Rem)^(γ-η-1)·Rem` at `η = deg Rem`. Composes
`subresultant_rem` with `subresultant_deg_ge`. -/
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

/-- **Theorem 1.4.3** (§1.4, general scaling case): when a coefficient homomorphism `σ` preserves the
degree of `A` (`deg σ̄A = deg A`) but may lower that of `B`, the subresultant specializes up to a
power of `σ(lc A)` — `σ̄(Sⱼ(A,B)) = σ(lc A)^(deg B − deg σ̄B) · Sⱼ(σ̄A, σ̄B)` for `0 ≤ j < deg σ̄B`,
`j ≤ deg A`. Composes `subresultant_map` (σ commutes at the original formal degrees) with
`subresultant_padding` (relating `σ̄B`'s formal degree `deg B` to its true degree `deg σ̄B`, the extra
rows cofactor-expanding to `lc σ̄A = σ(lc A)`). The degree-preserving case is `subresultant_map`. -/
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
