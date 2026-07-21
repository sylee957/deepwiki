import DeepWiki.Algebra.SubresultantSpec
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable

/-! # Residues of rational functions
The residue of `A/D` at a simple root `α` of `D` is `A(α)/D'(α)`; the residue-`a` roots of `D` are the
common roots of `D` and `A − a·D'`, and over an algebraically closed field the residues are the zeros of
the Rothstein–Trager resultant `res_x(D, A − t·D')`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {F : Type*} [Field F]

/-- If `D = (X − α)·E`, then `D'(α) = E(α)`. -/
theorem eval_derivative_X_sub_C_mul (E : F[X]) (α : F) :
    (derivative ((X - C α) * E)).eval α = E.eval α := by
  rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]

/-- Residue at a simple root: `A(α)/D'(α) = A(α)/E(α)` for `D = (X − α)·E`. -/
theorem residue_eq_eval_div_eval_derivative (A E : F[X]) (α : F) :
    A.eval α / (derivative ((X - C α) * E)).eval α = A.eval α / E.eval α := by
  rw [eval_derivative_X_sub_C_mul]

/-- If `A = c·E + (X−α)·B` with `E(α) ≠ 0` and `D = (X−α)·E`, the partial-fraction coefficient is the
residue `c = A(α)/D'(α)`. -/
theorem residue_of_partialFraction (A E B : F[X]) (c α : F) (hE : E.eval α ≠ 0)
    (hpf : A = C c * E + (X - C α) * B) :
    c = A.eval α / (derivative ((X - C α) * E)).eval α := by
  rw [eval_derivative_X_sub_C_mul, hpf]
  simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul, add_zero]
  rw [mul_div_assoc, div_self hE, mul_one]

/-- With `D'(α) ≠ 0`, the residue `A(α)/D'(α) = a` iff `α` is a root of `A − a·D'`. -/
theorem residue_eq_iff_isRoot_sub (A D : F[X]) (a α : F) (hα : (derivative D).eval α ≠ 0) :
    A.eval α / (derivative D).eval α = a ↔ (A - C a * derivative D).IsRoot α := by
  rw [IsRoot.def, div_eq_iff hα, eval_sub, eval_mul, eval_C, sub_eq_zero]

open scoped Classical in
/-- The roots of `gcd(D, A − a·D')` are exactly the roots `α` of `D` with residue `A(α)/D'(α) = a`. -/
theorem isRoot_gcd_iff_residue (A D : F[X]) (a α : F) (hα : (derivative D).eval α ≠ 0) :
    (gcd D (A - C a * derivative D)).IsRoot α
      ↔ (D.IsRoot α ∧ A.eval α / (derivative D).eval α = a) := by
  rw [← dvd_iff_isRoot, dvd_gcd_iff, dvd_iff_isRoot, dvd_iff_isRoot,
    residue_eq_iff_isRoot_sub A D a α hα]

open scoped Classical in
/-- For split squarefree `D = Lagrange.nodal s id`, `gcd(D, A − a·D') = ∏_{α∈s, res(α)=a}(X−α)`. -/
theorem gcd_nodal_eq_prod_residue (s : Finset F) (A : F[X]) (a : F) :
    gcd (Lagrange.nodal s id) (A - C a * derivative (Lagrange.nodal s id))
      = ∏ α ∈ s.filter
          (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id)) = a), (X - C α) := by
  set D := Lagrange.nodal s id with hD
  set res : F → F := fun α => A.eval α / eval α (derivative D) with hres
  set E := A - C a * derivative D with hE
  have hDprod : D = ∏ α ∈ s, (X - C α) := by simp [hD, Lagrange.nodal_eq, id]
  have hDsep : D.Separable := by
    rw [hDprod]; exact separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ h => h
  have hD0 : D ≠ 0 := hD ▸ Lagrange.nodal_ne_zero
  have hDroots : D.roots = s.val := by rw [hDprod, roots_prod_X_sub_C]
  have hd : ∀ {α : F}, D.IsRoot α → (derivative D).eval α ≠ 0 := by
    intro α hα
    have := hDsep.eval₂_derivative_ne_zero (RingHom.id F)
      (by simpa [eval₂_eq_eval_map, Polynomial.map_id] using hα)
    simpa [eval₂_eq_eval_map, Polynomial.map_id] using this
  have hgsep : (gcd D E).Separable := hDsep.of_dvd (gcd_dvd_left _ _)
  have hg0 : gcd D E ≠ 0 := fun h =>
    hD0 (zero_dvd_iff.mp (h ▸ gcd_dvd_left D E))
  have hgmonic : (gcd D E).Monic := normalize_gcd D E ▸ monic_normalize hg0
  have hDsplits : D.Splits := by
    rw [hDprod]; exact Splits.prod fun α _ => Splits.X_sub_C _
  have hgsplits : (gcd D E).Splits := hDsplits.of_dvd hD0 (gcd_dvd_left D E)
  have hroots : (gcd D E).roots = (s.filter (fun α => res α = a)).val := by
    refine Multiset.Nodup.ext (nodup_roots hgsep) (s.filter (fun α => res α = a)).nodup |>.mpr
      fun α => ?_
    rw [mem_roots hg0, Finset.mem_val, Finset.mem_filter]
    constructor
    · intro hα
      have hDα : D.IsRoot α := (dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr hα).trans (gcd_dvd_left D E)))
      obtain ⟨_, hres'⟩ := (isRoot_gcd_iff_residue A D a α (hd hDα)).mp hα
      have hαs : α ∈ s := by
        have : α ∈ s.val := hDroots ▸ (mem_roots hD0).mpr hDα
        exact this
      exact ⟨hαs, hres'⟩
    · rintro ⟨hαs, hres'⟩
      have hDα : D.IsRoot α := (mem_roots hD0).mp (hDroots ▸ hαs)
      exact (isRoot_gcd_iff_residue A D a α (hd hDα)).mpr ⟨hDα, hres'⟩
  rw [hgsplits.eq_prod_roots_of_monic hgmonic, hroots, Finset.prod_eq_multiset_prod]

/-- Over an algebraically closed field with separable `D`, the resultant `res_x(D, A − a·D') = 0` iff `a`
is a residue `A(α)/D'(α)` at some root `α` of `D`. -/
theorem residue_iff_resultant_eq_zero [IsAlgClosed F]
    (A D : F[X]) (hD : D.Separable) (a : F) :
    D.resultant (A - C a * derivative D) = 0 ↔
      ∃ α, D.IsRoot α ∧ A.eval α / (derivative D).eval α = a := by
  have hD0 : D ≠ 0 := hD.ne_zero
  have hev : ∀ (p : F[X]) (x : F), aeval x p = p.eval x := fun p x => by
    simp [aeval_def, eval₂_eq_eval_map, Polynomial.map_id]
  have hd : ∀ {α : F}, D.eval α = 0 → (derivative D).eval α ≠ 0 := by
    intro α hα
    have := hD.eval₂_derivative_ne_zero (RingHom.id F)
      (by simpa [eval₂_eq_eval_map, Polynomial.map_id] using hα)
    simpa [eval₂_eq_eval_map, Polynomial.map_id] using this
  rw [resultant_eq_zero_iff, and_iff_right (Or.inl hD0),
    Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := F) (K := F)]
  simp only [not_forall, hev, ne_eq, not_or, not_not, eval_sub, eval_mul, eval_C, IsRoot.def]
  refine exists_congr fun α => and_congr_right fun hDα => ?_
  rw [div_eq_iff (hd hDα), sub_eq_zero]

end DeepWiki.SymbolicIntegration
