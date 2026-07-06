import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms
import DeepWiki.SymbolicIntegration.LazardRiobooTragerCorrectness
import DeepWiki.SymbolicIntegration.MonomialExtensions
import DeepWiki.SymbolicIntegration.RiobooCoprimalityLrt
import Mathlib.LinearAlgebra.Lagrange

/-! # General-derivation Rothstein–Trager / Lazard–Rioboo–Trager

The abstract RT/LRT theory (`rtResultant`, `lrtSubresultant`, …) is stated with the plain polynomial
`derivative D`. This file generalizes the *residue-object* layer to an **arbitrary** `B : K[X]` in place
of `derivative D` — the setting needed for a general derivation, where `B = D_tower(D)` (`= implicitDeriv`).
The residue resultant becomes `resultant_x(D, A − z·B)`; residues are `c = A(β)/B(β)` at roots `β` of `D`.

Per the `derivative`-dependence map (see `docs/generalize-lrt-derivation.md`): the resultant/subresultant
*defs and evaluation lemmas* treat `derivative D` **opaquely**, so they generalize verbatim. The residue↔root
theory (next phase) replaces the single essential fact `D.Separable → D'(β) ≠ 0` with a **normality**
hypothesis `IsCoprime D B` (equivalently `B(β) ≠ 0` at roots), keeping `Squarefree D`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- **General-derivation Rothstein–Trager resultant.** `resultant_x(D, A − z·B)` as a polynomial in `z`,
for an arbitrary `B` (the derivation image). Specializes to `rtResultant A D` at `B = derivative D`. -/
noncomputable def rtResultantGen (A D B : K[X]) : K[X] :=
  Polynomial.resultant (D.map (C : K →+* K[X]))
    (A.map (C : K →+* K[X]) - C Polynomial.X * B.map (C : K →+* K[X]))
    D.natDegree (D.natDegree - 1)

/-- `rtResultantGen A D (derivative D) = rtResultant A D`: the plain-derivative case. -/
@[simp] theorem rtResultantGen_derivative (A D : K[X]) :
    rtResultantGen A D (derivative D) = rtResultant A D := rfl

/-- Evaluating `rtResultantGen A D B` at `a` gives `resultant_x(D, A − C a·B)`. -/
theorem rtResultantGen_eval (A D B : K[X]) (a : K) :
    (rtResultantGen A D B).eval a
      = Polynomial.resultant D (A - C a * B) D.natDegree (D.natDegree - 1) := by
  have hcomp : (Polynomial.evalRingHom a).comp (C : K →+* K[X]) = RingHom.id K := by ext k; simp
  show Polynomial.evalRingHom a (rtResultantGen A D B) = _
  rw [rtResultantGen, ← Polynomial.resultant_map_map]
  congr 1
  · rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C, hcomp,
      Polynomial.map_id]
    simp

/-- **General-derivation LRT subresultant.** The `j`-th subresultant of `D` and `A − z·B` over `K[z]`.
Specializes to `lrtSubresultant A D j` at `B = derivative D`. -/
noncomputable def lrtSubresultantGen (A D B : K[X]) (j : ℕ) : (K[X])[X] :=
  subresultant (D.map (C : K →+* K[X]))
    (A.map (C : K →+* K[X]) - C Polynomial.X * B.map (C : K →+* K[X]))
    D.natDegree (D.natDegree - 1) j

/-- `lrtSubresultantGen A D (derivative D) j = lrtSubresultant A D j`. -/
@[simp] theorem lrtSubresultantGen_derivative (A D : K[X]) (j : ℕ) :
    lrtSubresultantGen A D (derivative D) j = lrtSubresultant A D j := rfl

/-- Specializing `lrtSubresultantGen A D B j` at `z = a` gives the parameter subresultant over `K`. -/
theorem lrtSubresultantGen_eval (A D B : K[X]) (a : K) (j : ℕ) :
    (lrtSubresultantGen A D B j).map (Polynomial.evalRingHom a)
      = subresultant D (A - C a * B) D.natDegree (D.natDegree - 1) j := by
  have hcomp : (Polynomial.evalRingHom a).comp (C : K →+* K[X]) = RingHom.id K := by ext k; simp
  rw [lrtSubresultantGen, ← subresultant_map]
  congr 1
  · rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C, hcomp,
      Polynomial.map_id]
    simp

/-! ## The residue↔root theory for a general derivation `B`

The single essential `derivative`-fact — `D.Separable → D'(α) ≠ 0` at roots of `D` — is replaced by a
**normality** hypothesis `hB : ∀ α ∈ D.roots, B.eval α ≠ 0` (equivalently `IsCoprime D B`). `D` stays
`Separable`/`Squarefree` for the "divisor of `D` is squarefree ⟹ nodup roots" steps. -/

/-- With `B(α) ≠ 0`, the residue `A(α)/B(α) = a` iff `α` is a root of `A − a·B`. -/
theorem residue_eq_iff_isRoot_sub_gen (A B : K[X]) (a α : K) (hα : B.eval α ≠ 0) :
    A.eval α / B.eval α = a ↔ (A - C a * B).IsRoot α := by
  rw [IsRoot.def, div_eq_iff hα, eval_sub, eval_mul, eval_C, sub_eq_zero]

open scoped Classical in
/-- The roots of `gcd(D, A − a·B)` are exactly the roots `α` of `D` with residue `A(α)/B(α) = a`. -/
theorem isRoot_gcd_iff_residue_gen (A D B : K[X]) (a α : K) (hα : B.eval α ≠ 0) :
    (gcd D (A - C a * B)).IsRoot α ↔ (D.IsRoot α ∧ A.eval α / B.eval α = a) := by
  rw [← dvd_iff_isRoot, dvd_gcd_iff, dvd_iff_isRoot, dvd_iff_isRoot,
    residue_eq_iff_isRoot_sub_gen A B a α hα]

/-- At a root `α` with `B(α) ≠ 0`, `C(A α) − X·C(B α) = −C(B α)·(X − C(A α/B α))`. -/
theorem linearFactor_eq_residue_gen (A B : K[X]) (α : K) (hα : B.eval α ≠ 0) :
    C (A.eval α) - Polynomial.X * C (B.eval α)
      = -C (B.eval α) * (Polynomial.X - C (A.eval α / B.eval α)) := by
  have hC : C (B.eval α) * C (A.eval α / B.eval α) = C (A.eval α) := by
    rw [← C_mul, mul_div_cancel₀ _ hα]
  linear_combination -hC

open scoped Classical in
/-- Root-product form: `rtResultantGen A D B = lc(D)^{deg D−1} · ∏_{α : D(α)=0}(C(A α) − X·C(B α))`. -/
theorem rtResultantGen_eq_prod_roots [IsAlgClosed K] (A D B : K[X])
    (hA : A.natDegree < D.natDegree) (hB_deg : B.natDegree ≤ D.natDegree - 1) :
    rtResultantGen A D B
      = C (D.leadingCoeff) ^ (D.natDegree - 1) *
        (D.roots.map (fun α => C (A.eval α) - Polynomial.X * C (B.eval α))).prod := by
  have hCinj : Function.Injective (C : K →+* K[X]) := C_injective
  have hndeg : (D.map (C : K →+* K[X])).natDegree = D.natDegree :=
    natDegree_map_eq_of_injective hCinj D
  have hg : (A.map (C : K →+* K[X])
      - C Polynomial.X * B.map (C : K →+* K[X])).natDegree ≤ D.natDegree - 1 := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_map_eq_of_injective hCinj]; omega
    · refine (natDegree_C_mul_le _ _).trans ?_
      rw [natDegree_map_eq_of_injective hCinj]; exact hB_deg
  have hsplit : (D.map (C : K →+* K[X])).Splits := (IsAlgClosed.splits D).map (C : K →+* K[X])
  rw [rtResultantGen]
  nth_rewrite 1 [← hndeg]
  rw [Polynomial.resultant_eq_prod_eval (D.map (C : K →+* K[X]))
        (A.map (C : K →+* K[X]) - C Polynomial.X * B.map (C : K →+* K[X]))
        (D.natDegree - 1) hg hsplit,
      leadingCoeff_map_of_injective hCinj,
      (IsAlgClosed.splits D).roots_map (C : K →+* K[X]), Multiset.map_map]
  refine congrArg (C (D.leadingCoeff) ^ (D.natDegree - 1) * ·)
    (congrArg Multiset.prod (Multiset.map_congr rfl (fun α _ => ?_)))
  simp only [Function.comp_apply, eval_sub, eval_mul, eval_C, eval_map,
    show A.eval₂ (C : K →+* K[X]) (C α) = C (A.eval α) from eval₂_hom (C : K →+* K[X]) α,
    show B.eval₂ (C : K →+* K[X]) (C α) = C (B.eval α) from eval₂_hom (C : K →+* K[X]) α]

open scoped Classical in
/-- The roots of `rtResultantGen A D B` (with multiplicity) are the residues `A(α)/B(α)` over the roots
`α` of `D`, under normality `hB : B(α) ≠ 0` and `deg A < deg D`, `deg B ≤ deg D − 1`. -/
theorem roots_rtResultantGen [IsAlgClosed K] (A D B : K[X]) (hD0 : D ≠ 0)
    (hB : ∀ α ∈ D.roots, B.eval α ≠ 0) (hA : A.natDegree < D.natDegree)
    (hB_deg : B.natDegree ≤ D.natDegree - 1) :
    (rtResultantGen A D B).roots = D.roots.map (fun α => A.eval α / B.eval α) := by
  set s : K := D.leadingCoeff ^ (D.natDegree - 1) *
    (D.roots.map (fun α => -B.eval α)).prod with hs
  have hs0 : s ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hD0))
      (Multiset.prod_ne_zero (by simpa using fun α hα => hB α hα))
  have hRC : rtResultantGen A D B
      = C s * (D.roots.map (fun α => Polynomial.X - C (A.eval α / B.eval α))).prod := by
    rw [rtResultantGen_eq_prod_roots A D B hA hB_deg,
      Multiset.map_congr rfl (fun α hα => linearFactor_eq_residue_gen A B α (hB α hα)),
      Multiset.prod_map_mul, hs, map_mul, map_pow,
      map_multiset_prod (C : K →+* K[X]), Multiset.map_map]
    simp only [Function.comp_apply, map_neg]
    ring
  have hmap : (D.roots.map (fun α => Polynomial.X - C (A.eval α / B.eval α)))
      = (D.roots.map (fun α => A.eval α / B.eval α)).map (fun a => Polynomial.X - C a) :=
    (Multiset.map_map (fun a => Polynomial.X - C a) (fun α => A.eval α / B.eval α) D.roots).symm
  rw [hRC, roots_C_mul _ hs0, hmap, roots_multiset_prod_X_sub_C]

open scoped Classical in
/-- **`rtResultantGen A D B ≠ 0`** under normality (`hB`). From the root-product form: the leading scalar
`lc(D)^{deg D−1}` is nonzero and each factor `C(A α) − X·C(B α) = −C(B α)·(X − C residue)` is nonzero. -/
theorem rtResultantGen_ne_zero [IsAlgClosed K] (A D B : K[X]) (hD0 : D ≠ 0)
    (hB : ∀ α ∈ D.roots, B.eval α ≠ 0) (hA : A.natDegree < D.natDegree)
    (hB_deg : B.natDegree ≤ D.natDegree - 1) :
    rtResultantGen A D B ≠ 0 := by
  rw [rtResultantGen_eq_prod_roots A D B hA hB_deg]
  refine mul_ne_zero (pow_ne_zero _ ?_) (Multiset.prod_ne_zero ?_)
  · rw [Ne, C_eq_zero]; exact leadingCoeff_ne_zero.mpr hD0
  · rw [Multiset.mem_map]
    rintro ⟨α, hα, hfα⟩
    rw [linearFactor_eq_residue_gen A B α (hB α hα)] at hfα
    exact mul_ne_zero (neg_ne_zero.mpr (C_ne_zero.mpr (hB α hα)))
      (Polynomial.X_sub_C_ne_zero _) hfα

open scoped Classical in
/-- `deg gcd(D, A − a·B) = #{roots α of D with residue A(α)/B(α) = a}`, under `Squarefree`/`Separable D`
and normality `hB`. -/
theorem natDegree_gcd_eq_count_residue_gen [IsAlgClosed K] (A D B : K[X]) (hD : D.Separable)
    (hB : ∀ α ∈ D.roots, B.eval α ≠ 0) (a : K) :
    (gcd D (A - C a * B)).natDegree = (D.roots.map (fun α => A.eval α / B.eval α)).count a := by
  have hD0 : D ≠ 0 := hD.ne_zero
  have hgsep : (gcd D (A - C a * B)).Separable := hD.of_dvd (gcd_dvd_left _ _)
  have hg0 : gcd D (A - C a * B) ≠ 0 := fun h =>
    hD0 (zero_dvd_iff.mp (h ▸ gcd_dvd_left D (A - C a * B)))
  have hroots : (gcd D (A - C a * B)).roots
      = D.roots.filter (fun α => A.eval α / B.eval α = a) := by
    refine (Multiset.Nodup.ext (nodup_roots hgsep) ((nodup_roots hD).filter _)).mpr fun α => ?_
    rw [mem_roots hg0, Multiset.mem_filter, mem_roots hD0]
    constructor
    · intro hα
      have hDα : D.IsRoot α :=
        (dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr hα).trans (gcd_dvd_left D _)))
      exact (isRoot_gcd_iff_residue_gen A D B a α (hB α ((mem_roots hD0).mpr hDα))).mp hα
    · rintro ⟨hDα, hres⟩
      exact (isRoot_gcd_iff_residue_gen A D B a α (hB α ((mem_roots hD0).mpr hDα))).mpr ⟨hDα, hres⟩
  have hcount : (D.roots.map (fun α => A.eval α / B.eval α)).count a
      = (D.roots.filter (fun α => A.eval α / B.eval α = a)).card := by
    rw [Multiset.count_map,
      Multiset.filter_congr (q := fun α => A.eval α / B.eval α = a) (fun α _ => eq_comm)]
  rw [(IsAlgClosed.splits (gcd D (A - C a * B))).natDegree_eq_card_roots, hroots, hcount]

open scoped Classical in
/-- **The general-derivation Rothstein–Trager residue-multiplicity theorem.**
`rootMultiplicity a (rtResultantGen A D B) = deg gcd(D, A − a·B)`, under `Separable D`, normality `hB`,
`deg A < deg D`, `deg B ≤ deg D − 1`. Generalizes `rootMultiplicity_rtResultant_eq_natDegree_gcd` from
`derivative D` to an arbitrary `B`. -/
theorem rootMultiplicity_rtResultantGen_eq_natDegree_gcd [IsAlgClosed K] (A D B : K[X])
    (hD : D.Separable) (hB : ∀ α ∈ D.roots, B.eval α ≠ 0) (hA : A.natDegree < D.natDegree)
    (hB_deg : B.natDegree ≤ D.natDegree - 1) (a : K) :
    (rtResultantGen A D B).rootMultiplicity a = (gcd D (A - C a * B)).natDegree := by
  rw [← count_roots, roots_rtResultantGen A D B hD.ne_zero hB hA hB_deg,
    ← natDegree_gcd_eq_count_residue_gen A D B hD hB a]

/-! ## The LRT subresultant-similarity theorem for a general derivation `B`

Bronstein Thm 2.5.1(ii) generalized: the LRT subresultant at the residue multiplicity index, specialized
`z ↦ a`, is similar to `gcd(D, A − a·B)`. The subresultant/PRS engine is already `derivative`-agnostic;
`derivative D` enters only via `E := A − a·B` (opaque) and the degree bound `deg B ≤ deg D − 1`. -/

/-- Multi-step (`k ≥ 2`) LRT subresultant similarity for a general `B`. -/
theorem isSimilar_lrtSubresultant_eval_gcd_gen {K : Type*} [Field K] [GCDMonoid K[X]]
    (A D B : K[X]) (a : K) (hD : D ≠ 0) (hA : A.natDegree < D.natDegree)
    (hB_deg : B.natDegree ≤ D.natDegree - 1)
    {k : ℕ} (hk2 : 2 ≤ k) (hk0 : euclideanPRS D (A - C a * B) (k + 1) = 0)
    (hknz : ∀ j, 1 ≤ j → j ≤ k → euclideanPRS D (A - C a * B) j ≠ 0) :
    IsSimilar
      ((lrtSubresultantGen A D B (euclideanPRS D (A - C a * B) k).natDegree).map
        (Polynomial.evalRingHom a))
      (gcd D (A - C a * B)) := by
  rw [lrtSubresultantGen_eval]
  set E := A - C a * B with hE
  have hElt : E.natDegree ≤ D.natDegree - 1 :=
    (natDegree_sub_le _ _).trans (max_le (by omega) ((natDegree_C_mul_le _ _).trans hB_deg))
  have hjE : (euclideanPRS D E k).natDegree < E.natDegree := by
    have h := euclideanPRS_natDegree_strictAnti D E hknz 1 k (le_refl 1) (by omega) (le_refl k)
    rwa [euclideanPRS_one] at h
  have hengine := subresultant_euclideanPRS_isSimilar_gcd D E hD
    (le_trans hElt (Nat.sub_le _ _)) hk2 hk0 hknz
  exact (isSimilar_subresultant_padding D E D.natDegree E.natDegree
    (euclideanPRS D E k).natDegree hjE
    (le_trans (le_of_lt hjE) (le_trans hElt (Nat.sub_le _ _))) le_rfl le_rfl
    (leadingCoeff_ne_zero.mpr hD) hElt).trans hengine

/-- Top-index (`k = 1`, `E ∣ D`) LRT subresultant similarity for a general `B`. -/
theorem isSimilar_lrtSubresultant_eval_gcd_top_gen {K : Type*} [Field K] [GCDMonoid K[X]]
    (A D B : K[X]) (a : K) (hD : D ≠ 0) (hA : A.natDegree < D.natDegree)
    (hB_deg : B.natDegree ≤ D.natDegree - 1) (hE : A - C a * B ≠ 0)
    (h0 : euclideanPRS D (A - C a * B) 2 = 0) :
    IsSimilar
      ((lrtSubresultantGen A D B (A - C a * B).natDegree).map (Polynomial.evalRingHom a))
      (gcd D (A - C a * B)) := by
  rw [lrtSubresultantGen_eval]
  set E := A - C a * B with hEdef
  have hElt : E.natDegree ≤ D.natDegree - 1 :=
    (natDegree_sub_le _ _).trans (max_le (by omega) ((natDegree_C_mul_le _ _).trans hB_deg))
  have hsim : IsSimilar (subresultant D E D.natDegree (D.natDegree - 1) E.natDegree) E := by
    rw [subresultant_deg_ge_normal D E D.natDegree (D.natDegree - 1) E.natDegree le_rfl
      (by omega) (Nat.sub_le _ _) hElt]
    exact ⟨1, (D.coeff D.natDegree) ^ (D.natDegree - 1 - E.natDegree)
        * E.coeff E.natDegree ^ (D.natDegree - E.natDegree - 1), one_ne_zero,
      mul_ne_zero (pow_ne_zero _ (by rw [← leadingCoeff]; exact leadingCoeff_ne_zero.mpr hD))
        (pow_ne_zero _ (by rw [← leadingCoeff]; exact leadingCoeff_ne_zero.mpr hE)),
      by rw [map_one, one_mul]⟩
  exact hsim.trans (isSimilar_gcd_right_of_euclideanPRS_two_eq_zero D E hE h0).symm

open scoped Classical in
/-- LRT subresultant similarity at the residue multiplicity index (part-(ii) regime `i < deg D`) for a
general `B` under normality `hB`. -/
theorem lazardRiobooTrager_isSimilar_gcd_gen {K : Type*} [Field K] [IsAlgClosed K]
    (A D B : K[X]) (hD : D.Separable) (hB : ∀ α ∈ D.roots, B.eval α ≠ 0)
    (hA : A.natDegree < D.natDegree) (hB_deg : B.natDegree ≤ D.natDegree - 1) (a : K)
    (hi : (rtResultantGen A D B).rootMultiplicity a < D.natDegree) :
    IsSimilar
      ((lrtSubresultantGen A D B ((rtResultantGen A D B).rootMultiplicity a)).map
        (Polynomial.evalRingHom a))
      (gcd D (A - C a * B)) := by
  set E := A - C a * B with hE
  have hDne : D ≠ 0 := fun h => by simp [h] at hA
  have hmul : (rtResultantGen A D B).rootMultiplicity a = (gcd D E).natDegree :=
    rootMultiplicity_rtResultantGen_eq_natDegree_gcd A D B hD hB hA hB_deg a
  have hEne : E ≠ 0 := by
    intro h
    rw [h, (IsSimilar.of_associated
      (gcd_zero_right D ▸ normalize_associated D)).natDegree_eq] at hmul
    rw [hmul] at hi; exact absurd hi (lt_irrefl _)
  obtain ⟨k, hk1, hk0, hknz⟩ := exists_last_euclideanPRS_nonzero D E hEne
  have hsim : IsSimilar (euclideanPRS D E k) (gcd D E) :=
    (isPRS_euclideanPRS D E).isSimilar_gcd hk0 (fun j hj1 hjk => hknz j hj1 hjk)
  have hdeg : (euclideanPRS D E k).natDegree = (gcd D E).natDegree := hsim.natDegree_eq
  rcases Nat.lt_or_ge k 2 with hk | hk2
  · have hk1' : k = 1 := by omega
    subst hk1'
    rw [euclideanPRS_one] at hdeg
    have h0 : euclideanPRS D E 2 = 0 := hk0
    rw [hmul, ← hdeg]
    exact isSimilar_lrtSubresultant_eval_gcd_top_gen A D B a hDne hA hB_deg hEne h0
  · rw [hmul, ← hdeg]
    exact isSimilar_lrtSubresultant_eval_gcd_gen A D B a hDne hA hB_deg hk2 hk0 hknz

open scoped Classical in
/-- **The general-derivation LRT algorithm-output correctness (unified, no excluded case).** For any `a`,
the LRT output curve `Sᵢ` at multiplicity `i = rootMultiplicity a (rtResultantGen A D B)` — namely `D` if
`i = deg D`, else `lrtSubresultantGen A D B i` — specialized `z ↦ a`, is similar to `gcd(D, A − a·B)`.
Generalizes `lazardRiobooTrager_output_isSimilar_gcd` from `derivative D` to an arbitrary `B` under
normality `hB` (`B(α) ≠ 0` at roots of `D`). -/
theorem lazardRiobooTrager_output_isSimilar_gcd_gen {K : Type*} [Field K] [IsAlgClosed K]
    (A D B : K[X]) (hD : D.Separable) (hB : ∀ α ∈ D.roots, B.eval α ≠ 0)
    (hA : A.natDegree < D.natDegree) (hB_deg : B.natDegree ≤ D.natDegree - 1) (a : K) :
    IsSimilar
      ((if (rtResultantGen A D B).rootMultiplicity a = D.natDegree then D.map (C : K →+* K[X])
        else lrtSubresultantGen A D B ((rtResultantGen A D B).rootMultiplicity a)).map
        (Polynomial.evalRingHom a))
      (gcd D (A - C a * B)) := by
  have hDne : D ≠ 0 := fun h => by simp [h] at hA
  set E := A - C a * B with hE
  have hmul : (rtResultantGen A D B).rootMultiplicity a = (gcd D E).natDegree :=
    rootMultiplicity_rtResultantGen_eq_natDegree_gcd A D B hD hB hA hB_deg a
  have hile : (rtResultantGen A D B).rootMultiplicity a ≤ D.natDegree :=
    hmul.le.trans (natDegree_le_of_dvd (gcd_dvd_left D E) hDne)
  by_cases hcase : (rtResultantGen A D B).rootMultiplicity a = D.natDegree
  · rw [if_pos hcase]
    have hmapid : (D.map (C : K →+* K[X])).map (Polynomial.evalRingHom a) = D := by
      rw [Polynomial.map_map,
        show (Polynomial.evalRingHom a).comp (C : K →+* K[X]) = RingHom.id K from by ext k; simp,
        Polynomial.map_id]
    rw [hmapid]
    exact (isSimilar_gcd_left_of_natDegree_eq hDne (hmul.symm.trans hcase)).symm
  · rw [if_neg hcase]
    exact lazardRiobooTrager_isSimilar_gcd_gen A D B hD hB hA hB_deg a (lt_of_le_of_ne hile hcase)

/-! ## `z`-degree bound (over a general field, needed for the interpolation certification)

`rtResultantGen A D B` has `z`-degree `≤ deg D`, generalizing `natDegree_rtResultant_le` (stated over `ℚ`)
to any field `K` and arbitrary `B`. Needed to certify `cResidueResultantTowerGWf` (an interpolant of the
resultant samples) via interpolation uniqueness. -/

/-- Column-degree bound for a matrix determinant (general field). -/
theorem natDegree_det_le_sum_col_gen {ι : Type*} [DecidableEq ι] [Fintype ι]
    (M : Matrix ι ι K[X]) (b : ι → ℕ) (hb : ∀ i j, (M i j).natDegree ≤ b j) :
    (M.det).natDegree ≤ ∑ j, b j := by
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, ?_⟩
  intro σ _
  rw [Function.comp_apply]
  refine (natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  exact Finset.sum_le_sum (fun i _ => hb (σ i) i)

/-- Each `z`-coefficient of `A.map C − C z · B.map C` has `natDegree ≤ 1` (linear in `z`). -/
theorem natDegree_coeff_rtResultantGen_g_le (A B : K[X]) (k : ℕ) :
    ((A.map (C : K →+* K[X]) - C Polynomial.X * B.map (C : K →+* K[X])).coeff k).natDegree ≤ 1 := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C_mul, Polynomial.coeff_map]
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [Polynomial.natDegree_C]; exact Nat.zero_le 1
  · refine (Polynomial.natDegree_mul_le (p := (Polynomial.X : K[X]))
      (q := Polynomial.C (B.coeff k))).trans ?_
    rw [Polynomial.natDegree_X, Polynomial.natDegree_C]

/-- `rtResultantGen A D B` has `z`-degree `≤ deg D`. -/
theorem natDegree_rtResultantGen_le (A D B : K[X]) :
    (rtResultantGen A D B).natDegree ≤ D.natDegree := by
  rw [rtResultantGen, resultant]
  refine le_trans (natDegree_det_le_sum_col_gen _
    (fun j => j.addCases (fun _ => 1) (fun _ => 0)) ?_) ?_
  · intro i j
    rw [Polynomial.sylvester, Matrix.of_apply]
    refine j.addCases (fun j₁ => ?_) (fun j₁ => ?_)
    · simp only [Fin.addCases_left]
      split_ifs with h
      · exact natDegree_coeff_rtResultantGen_g_le A B _
      · simp
    · simp only [Fin.addCases_right]
      split_ifs with h
      · rw [Polynomial.coeff_map, Polynomial.natDegree_C]
      · simp
  · rw [Fin.sum_univ_add]; simp

/-- For a **monic** `p` and a constant `v` (`deg v = 0`), the general derivation image has the tight
degree bound `deg(implicitDeriv v p) ≤ deg p − 1` — the plain-derivative bound. The leading term of
`mapCoeffs p` vanishes (`D(leadingCoeff) = D(1) = 0`) and `v·p'` has degree `≤ deg p − 1`. This is the
tower-side degree fact certifying the formal degree `deg D − 1` of `rtResultantGen` for the **primitive**
reduced case (`Dt` constant, `Dstar` monic). -/
theorem natDegree_implicitDeriv_le_of_monic {F : Type*} [Field F] [Differential F] (v p : F[X])
    (hp : p.Monic) (hv : v.natDegree = 0) :
    (Differential.implicitDeriv v p).natDegree ≤ p.natDegree - 1 := by
  have happly : Differential.implicitDeriv v p = Differential.mapCoeffs p + v * derivative p := by
    simp [Differential.implicitDeriv, derivative']
  have hmc : (Differential.mapCoeffs p).natDegree ≤ p.natDegree - 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro N hN
    rw [Differential.coeff_mapCoeffs]
    rcases eq_or_lt_of_le (show p.natDegree ≤ N by omega) with heq | hlt
    · rw [← heq, ← Polynomial.leadingCoeff, hp.leadingCoeff]; simp
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]; simp
  have hvd : (v * derivative p).natDegree ≤ p.natDegree - 1 := by
    refine natDegree_mul_le.trans ?_
    rw [hv, zero_add]; exact natDegree_derivative_le p
  rw [happly]
  exact (natDegree_add_le _ _).trans (max_le hmc hvd)

open scoped Differential in
/-- **Exact degree drop for a genuine primitive monomial.** For monic `p` (`deg p ≥ 1`), constant `v`
(`deg v = 0`, `η = v.coeff 0`) with `η` **not a derivative** (`∀ γ, γ′ ≠ η`), `implicitDeriv v p` has degree
*exactly* `deg p − 1`. The sub-leading coefficient is `(cₙ₋₁)′ + n·η`; were it `0`, then `η = D(−cₙ₋₁/n)` would
be a derivative — contradiction. This is the `hm` frontier condition, derived from the monomial property. -/
theorem natDegree_implicitDeriv_eq_of_monic_of_not_range {F : Type*} [Field F] [Differential F] [CharZero F]
    (v p : F[X]) (hp : p.Monic) (hv : v.natDegree = 0) (hn : 1 ≤ p.natDegree)
    (hrange : ∀ (γ : F), γ′ ≠ v.coeff 0) :
    (Differential.implicitDeriv v p).natDegree = p.natDegree - 1 := by
  have hle := natDegree_implicitDeriv_le_of_monic v p hp hv
  have happly : Differential.implicitDeriv v p = Differential.mapCoeffs p + v * derivative p := by
    simp [Differential.implicitDeriv, derivative']
  have hn0 : (p.natDegree : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcoeff : (Differential.implicitDeriv v p).coeff (p.natDegree - 1)
      = (p.coeff (p.natDegree - 1))′ + v.coeff 0 * (p.natDegree : F) := by
    rw [happly, Polynomial.coeff_add, Differential.coeff_mapCoeffs]
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hv]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_derivative,
      show p.natDegree - 1 + 1 = p.natDegree from by omega, hp.coeff_natDegree, one_mul,
      show ((p.natDegree - 1 : ℕ) : F) + 1 = (p.natDegree : F) from by
        rw [Nat.cast_sub hn, Nat.cast_one]; ring]
  refine le_antisymm hle (Polynomial.le_natDegree_of_ne_zero ?_)
  rw [hcoeff]
  intro h0
  refine hrange (- (p.coeff (p.natDegree - 1)) / (p.natDegree : F)) ?_
  have hleib : ((p.natDegree : F) * (- (p.coeff (p.natDegree - 1)) / (p.natDegree : F)))′
      = (p.natDegree : F) * ((- (p.coeff (p.natDegree - 1)) / (p.natDegree : F))′) := by
    rw [Derivation.leibniz]
    simp [Derivation.map_natCast Differential.deriv]
  have hkey : (p.natDegree : F) * ((- (p.coeff (p.natDegree - 1)) / (p.natDegree : F))′)
      = (p.natDegree : F) * v.coeff 0 := by
    rw [← hleib, mul_div_cancel₀ _ hn0, map_neg]
    linear_combination -h0
  exact mul_left_cancel₀ hn0 hkey

open scoped Classical in
/-- **`z`-degree bound on the bivariate subresultant coefficient.** Each `t`-coefficient of
`lrtSubresultantGen A D B j` (a polynomial in the residue variable `z`) has degree `≤ deg D + (deg D − 1)`,
hence `< N = deg D + (deg D − 1) + 1` — the node count of `cSubresultantParam`. This is what makes the
engine's interpolation-in-`z` recover the true subresultant coefficient exactly (G4c). Proved by
`natDegree_det_le_sum_col_gen`: every Sylvester entry is a coefficient of `D.map C` (`z`-constant) or of
`A.map C − z·B.map C` (`z`-linear), so each is `z`-degree `≤ 1`, and the submatrix has `≤ deg D + (deg D − 1)`
columns. -/
theorem natDegree_coeff_lrtSubresultantGen_le (A D B : K[X]) (j k : ℕ) :
    ((lrtSubresultantGen A D B j).coeff k).natDegree ≤ D.natDegree + (D.natDegree - 1) := by
  have hentry : ∀ (i l : Fin ((D.natDegree - 1) + D.natDegree)),
      (bSylvester (D.map (C : K →+* K[X]))
        (A.map (C : K →+* K[X]) - C Polynomial.X * B.map (C : K →+* K[X]))
        D.natDegree (D.natDegree - 1) i l).natDegree ≤ 1 := by
    intro i l
    rw [bSylvester, Matrix.of_apply]
    split_ifs
    · rw [Polynomial.coeff_map, Polynomial.natDegree_C]; omega
    · simp
    · exact natDegree_coeff_rtResultantGen_g_le A B _
    · simp
  by_cases hk : k < j + 1
  · have hcoeff : (lrtSubresultantGen A D B j).coeff k
        = ((bSylvester (D.map (C : K →+* K[X]))
            (A.map (C : K →+* K[X]) - C Polynomial.X * B.map (C : K →+* K[X]))
            D.natDegree (D.natDegree - 1)).submatrix
            (subRow D.natDegree (D.natDegree - 1) j)
            (subCol D.natDegree (D.natDegree - 1) j k)).det := by
      rw [lrtSubresultantGen, subresultant, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_range, hk, if_true]
    rw [hcoeff]
    refine (natDegree_det_le_sum_col_gen _ (fun _ => 1) (fun i l => ?_)).trans ?_
    · rw [Matrix.submatrix_apply]; exact hentry _ _
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      omega
  · rw [show (lrtSubresultantGen A D B j).coeff k = 0 from ?_, Polynomial.natDegree_zero]
    · omega
    · rw [lrtSubresultantGen, subresultant, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_range, hk, if_false]

/-! ## Base change of `lrtSubresultantGen` (for the computable→abstract connection over `E`) -/

/-- `rtResultantGen` commutes with an injective base change `φ : K →+* L`:
`(rtResultantGen A D B).map φ = rtResultantGen (A.map φ) (D.map φ) (B.map φ)`. Base-changes the residue
resultant to a splitting field `L`, so `roots_rtResultantGen` (roots = residues) applies there. -/
theorem rtResultantGen_map {L : Type*} [Field L] (φ : K →+* L) (A D B : K[X])
    (hφ : Function.Injective φ) :
    (rtResultantGen A D B).map φ = rtResultantGen (A.map φ) (D.map φ) (B.map φ) := by
  have hcomm : (Polynomial.mapRingHom φ).comp (C : K →+* K[X]) = (C : L →+* L[X]).comp φ := by
    ext a; simp
  have hmapC : ∀ p : K[X], (p.map (C : K →+* K[X])).map (Polynomial.mapRingHom φ)
      = (p.map φ).map (C : L →+* L[X]) := fun p => by
    rw [Polynomial.map_map, hcomm, ← Polynomial.map_map]
  have hdeg : (D.map φ).natDegree = D.natDegree := natDegree_map_eq_of_injective hφ D
  rw [rtResultantGen, rtResultantGen]
  rw [show ((Polynomial.resultant (D.map (C : K →+* K[X]))
        (A.map (C : K →+* K[X]) - C Polynomial.X * B.map (C : K →+* K[X]))
        D.natDegree (D.natDegree - 1)).map φ)
      = Polynomial.mapRingHom φ (Polynomial.resultant (D.map (C : K →+* K[X]))
        (A.map (C : K →+* K[X]) - C Polynomial.X * B.map (C : K →+* K[X]))
        D.natDegree (D.natDegree - 1)) from rfl,
    ← Polynomial.resultant_map_map, hdeg, hmapC D]
  congr 2
  rw [Polynomial.map_sub, Polynomial.map_mul, hmapC A, hmapC B]
  simp

/-- `lrtSubresultantGen` commutes with an injective base change `φ : K →+* L`:
`(lrtSubresultantGen A D B j).map (mapRingHom φ) = lrtSubresultantGen (A.map φ) (D.map φ) (B.map φ) j`. -/
theorem lrtSubresultantGen_map {L : Type*} [Field L] (φ : K →+* L) (A D B : K[X]) (j : ℕ)
    (hφ : Function.Injective φ) :
    (lrtSubresultantGen A D B j).map (Polynomial.mapRingHom φ)
      = lrtSubresultantGen (A.map φ) (D.map φ) (B.map φ) j := by
  have hcomm : (Polynomial.mapRingHom φ).comp (C : K →+* K[X]) = (C : L →+* L[X]).comp φ := by
    ext a; simp
  have hmapC : ∀ p : K[X], (p.map (C : K →+* K[X])).map (Polynomial.mapRingHom φ)
      = (p.map φ).map (C : L →+* L[X]) := by
    intro p; rw [Polynomial.map_map, hcomm, ← Polynomial.map_map]
  have hdeg : (D.map φ).natDegree = D.natDegree := natDegree_map_eq_of_injective hφ D
  rw [lrtSubresultantGen, lrtSubresultantGen, ← subresultant_map, hdeg, hmapC D]
  congr 2
  rw [Polynomial.map_sub, Polynomial.map_mul, hmapC A, hmapC B]
  simp

/-- **`lrtSubresultantGen` base-changed and specialized at `z = c` is the residue subresultant over `L`.**
`(lrtSubresultantGen A D B j).map (eval₂RingHom φ c) = subresultant (D.map φ) (A.map φ − C c·B.map φ) …`.
This is exactly `evalLrtArg`'s raw value once the computable `Sᵢ` coefficients are read as `lrtSubresultantGen`
coefficients (G4c). -/
theorem lrtSubresultantGen_map_eval₂ {L : Type*} [Field L] (φ : K →+* L) (A D B : K[X]) (c : L) (j : ℕ)
    (hφ : Function.Injective φ) :
    (lrtSubresultantGen A D B j).map (Polynomial.eval₂RingHom φ c)
      = subresultant (D.map φ) (A.map φ - Polynomial.C c * B.map φ) D.natDegree (D.natDegree - 1) j := by
  have heq : (Polynomial.eval₂RingHom φ c : K[X] →+* L)
      = (Polynomial.evalRingHom c).comp (Polynomial.mapRingHom φ) := by
    ext p
    · simp
    · simp
  have hdeg : (D.map φ).natDegree = D.natDegree := natDegree_map_eq_of_injective hφ D
  rw [heq, ← Polynomial.map_map, lrtSubresultantGen_map φ A D B j hφ,
    lrtSubresultantGen_eval (A.map φ) (D.map φ) (B.map φ) c j, hdeg]

open scoped Classical in
/-- **`gcd(nodal s, A − a·B) = ∏_{res β=a}(X−β)`** for a general `B` (the general-derivation form of
`gcd_nodal_eq_prod_residue`), under normality `hB : B(β) ≠ 0` on `s`. The residue gcd is the product of the
residue-`a` linear factors. -/
theorem gcd_nodal_eq_prod_residue_gen (s : Finset K) (A B : K[X]) (a : K)
    (hB : ∀ α ∈ s, B.eval α ≠ 0) :
    gcd (Lagrange.nodal s id) (A - C a * B)
      = ∏ α ∈ s.filter (fun α => A.eval α / B.eval α = a), (X - C α) := by
  set D := Lagrange.nodal s id with hD
  set res : K → K := fun α => A.eval α / B.eval α with hres
  set E := A - C a * B with hE
  have hDprod : D = ∏ α ∈ s, (X - C α) := by simp [hD, Lagrange.nodal_eq, id]
  have hDsep : D.Separable := by
    rw [hDprod]; exact separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ h => h
  have hDmonic : D.Monic := hD ▸ Lagrange.nodal_monic
  have hD0 : D ≠ 0 := hD ▸ Lagrange.nodal_ne_zero
  have hDroots : D.roots = s.val := by rw [hDprod, roots_prod_X_sub_C]
  have hBroot : ∀ {α : K}, D.IsRoot α → B.eval α ≠ 0 := fun {α} hα =>
    hB α (by have : α ∈ s.val := hDroots ▸ (mem_roots hD0).mpr hα; exact this)
  have hgsep : (gcd D E).Separable := hDsep.of_dvd (gcd_dvd_left _ _)
  have hg0 : gcd D E ≠ 0 := fun h => hD0 (zero_dvd_iff.mp (h ▸ gcd_dvd_left D E))
  have hgmonic : (gcd D E).Monic := normalize_gcd D E ▸ monic_normalize hg0
  have hDsplits : D.Splits := by rw [hDprod]; exact Splits.prod fun α _ => Splits.X_sub_C _
  have hgsplits : (gcd D E).Splits := hDsplits.of_dvd hD0 (gcd_dvd_left D E)
  have hroots : (gcd D E).roots = (s.filter (fun α => res α = a)).val := by
    refine (Multiset.Nodup.ext (nodup_roots hgsep) (s.filter (fun α => res α = a)).nodup).mpr
      fun α => ?_
    rw [mem_roots hg0, Finset.mem_val, Finset.mem_filter]
    constructor
    · intro hα
      have hDα : D.IsRoot α := dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr hα).trans (gcd_dvd_left D E))
      obtain ⟨_, hres'⟩ := (isRoot_gcd_iff_residue_gen A D B a α (hBroot hDα)).mp hα
      exact ⟨(by have : α ∈ s.val := hDroots ▸ (mem_roots hD0).mpr hDα; exact this), hres'⟩
    · rintro ⟨hαs, hres'⟩
      have hDα : D.IsRoot α := (mem_roots hD0).mp (hDroots ▸ hαs)
      exact (isRoot_gcd_iff_residue_gen A D B a α (hBroot hDα)).mpr ⟨hDα, hres'⟩
  rw [hgsplits.eq_prod_roots_of_monic hgmonic, hroots, Finset.prod_eq_multiset_prod]

open scoped Classical in
/-- **The residue subresultant is similar to the residue-pole product** (over an alg-closed `E`). Combining
G3 (`lazardRiobooTrager_output_isSimilar_gcd_gen`, `~ gcd`), `lrtSubresultantGen_eval` (the specialized
subresultant), and G2 (`gcd_nodal_eq_prod_residue_gen`, `gcd = ∏`): for `D = nodal s`, the subresultant of
`(D, A − c·B)` at index `i = rootMultiplicity c` (`< deg D`) is similar to `∏_{res β = c}(X−β)`. This is the
`hsim` input to `evalLrtArg_cSubresultantParam_eq_prod`. -/
theorem isSimilar_subresultant_prod {E : Type*} [Field E] [IsAlgClosed E] (A B : E[X]) (s : Finset E)
    (c : E) (hB : ∀ β ∈ s, B.eval β ≠ 0)
    (hA : A.natDegree < (Lagrange.nodal s id).natDegree)
    (hB_deg : B.natDegree ≤ (Lagrange.nodal s id).natDegree - 1)
    (hi : (rtResultantGen A (Lagrange.nodal s id) B).rootMultiplicity c
        < (Lagrange.nodal s id).natDegree) :
    IsSimilar (subresultant (Lagrange.nodal s id) (A - C c * B) (Lagrange.nodal s id).natDegree
        ((Lagrange.nodal s id).natDegree - 1)
        ((rtResultantGen A (Lagrange.nodal s id) B).rootMultiplicity c))
      (∏ α ∈ s.filter (fun α => A.eval α / B.eval α = c), (X - C α)) := by
  set D := Lagrange.nodal s id with hD
  have hDprod : D = ∏ α ∈ s, (X - C α) := by simp [hD, Lagrange.nodal_eq, id]
  have hDsep : D.Separable := by
    rw [hDprod]; exact separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ h => h
  have hBroots : ∀ α ∈ D.roots, B.eval α ≠ 0 := by
    intro α hα
    have hr : D.roots = s.val := by rw [hDprod, roots_prod_X_sub_C]
    exact hB α (Finset.mem_val.mp (hr ▸ hα))
  have hg3 := lazardRiobooTrager_output_isSimilar_gcd_gen A D B hDsep hBroots hA hB_deg c
  rw [if_neg (ne_of_lt hi), lrtSubresultantGen_eval] at hg3
  rw [← gcd_nodal_eq_prod_residue_gen s A B c hB]
  exact hg3

/-! ## Monic normalization (the log argument is the monic gcd, up to association) -/

/-- **Monic normalization kills a scalar factor.** If `p = C k · q` with `k ≠ 0` and `q` monic, then
`p · C(p.leadingCoeff)⁻¹ = q`. -/
theorem monicNormalize_of_eq_C_mul_monic {p q : K[X]} (k : K) (hk : k ≠ 0)
    (hq : q.Monic) (h : p = C k * q) :
    p * C p.leadingCoeff⁻¹ = q := by
  have hlc : (C k * q).leadingCoeff = k := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hq.leadingCoeff, mul_one]
  rw [h, hlc, mul_right_comm, ← C_mul, mul_inv_cancel₀ hk, C_1, one_mul]

/-- **Monic normalization is an association-class invariant** (over a field). For `p ~ q` (associated) with
`q` monic, `p · C(p.leadingCoeff)⁻¹ = q`. So a subresultant `~ gcd` monic-normalizes to the monic gcd. -/
theorem monicNormalize_of_associated_monic {p q : K[X]} (hq : q.Monic) (h : Associated p q) :
    p * C p.leadingCoeff⁻¹ = q := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨k, hk, hkC⟩ : ∃ k : K, k ≠ 0 ∧ (u : K[X]) = C k := by
    obtain ⟨k, hk⟩ := Polynomial.isUnit_iff.mp u.isUnit
    exact ⟨k, fun h => by simp [h] at hk, hk.2.symm⟩
  refine monicNormalize_of_eq_C_mul_monic k⁻¹ (inv_ne_zero hk) hq ?_
  rw [← hu, hkC, mul_comm (C k⁻¹) (p * C k), mul_assoc, ← C_mul, mul_inv_cancel₀ hk, C_1, mul_one]

/-- **The monic log argument is the residue-pole product.** If the (specialized) subresultant `S` is
similar to `∏_{β}(t−β)`, its monic normalization equals `∏_{β}(t−β)` exactly. This is the P3 endpoint: with
`S = lrtSubresultantGen … .map (evalRingHom c)` (`~ gcd` by G3) and `gcd = ∏_{res β = c}(t−β)` (by G2), the
monic log argument is the residue-`c` linear-factor product. -/
theorem monicNormalize_eq_of_isSimilar_prod {S : K[X]} (poles : Multiset K)
    (hsim : IsSimilar S (poles.map (fun β => X - C β)).prod) :
    S * C S.leadingCoeff⁻¹ = (poles.map (fun β => X - C β)).prod :=
  monicNormalize_of_associated_monic
    (monic_multiset_prod_of_monic _ _ (fun β _ => monic_X_sub_C β)) (IsSimilar.associated hsim)

end DeepWiki.SymbolicIntegration
