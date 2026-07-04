import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms
import DeepWiki.SymbolicIntegration.LazardRiobooTragerCorrectness

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

end DeepWiki.SymbolicIntegration
