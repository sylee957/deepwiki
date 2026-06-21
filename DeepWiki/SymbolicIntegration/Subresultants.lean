import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Basic
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

end DeepWiki.SymbolicIntegration
