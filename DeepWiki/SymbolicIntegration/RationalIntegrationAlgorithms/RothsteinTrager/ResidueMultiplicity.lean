import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.RtResultant
import DeepWiki.SymbolicIntegration.Residues

/-! # Residue multiplicity
The multiplicity of a residue `a` as a root of the Rothstein–Trager resultant `R(t) = res_x(D, A − t·D')`
equals `deg gcd(D, A − a·D')`, over an algebraically closed field for separable `D`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {F : Type*} [Field F]

open scoped Classical in
/-- `deg gcd(D, A − a·D')` equals the count of roots `α` of `D` with residue `A(α)/D'(α) = a`. -/
theorem natDegree_gcd_eq_count_residue [IsAlgClosed F] (A D : F[X]) (hD : D.Separable) (a : F) :
    (gcd D (A - C a * derivative D)).natDegree
      = (D.roots.map (fun α => A.eval α / (derivative D).eval α)).count a := by
  have hD0 : D ≠ 0 := hD.ne_zero
  -- `D'(α) ≠ 0` at every root of `D`, from separability.
  have hd : ∀ {α : F}, D.IsRoot α → (derivative D).eval α ≠ 0 := by
    intro α hα
    have := hD.eval₂_derivative_ne_zero (RingHom.id F)
      (by simpa [eval₂_eq_eval_map, Polynomial.map_id] using hα)
    simpa [eval₂_eq_eval_map, Polynomial.map_id] using this
  have hgsep : (gcd D (A - C a * derivative D)).Separable := hD.of_dvd (gcd_dvd_left _ _)
  have hg0 : gcd D (A - C a * derivative D) ≠ 0 := fun h =>
    hD0 (zero_dvd_iff.mp (h ▸ gcd_dvd_left D (A - C a * derivative D)))
  -- The roots of the gcd are exactly the residue-`a` roots of `D`.
  have hroots : (gcd D (A - C a * derivative D)).roots
      = D.roots.filter (fun α => A.eval α / (derivative D).eval α = a) := by
    refine (Multiset.Nodup.ext (nodup_roots hgsep) ((nodup_roots hD).filter _)).mpr fun α => ?_
    rw [mem_roots hg0, Multiset.mem_filter, mem_roots hD0]
    constructor
    · intro hα
      -- a root of the gcd is a root of `D` (gcd ∣ D), so `D'(α) ≠ 0`
      have hDα : D.IsRoot α :=
        (dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr hα).trans (gcd_dvd_left D _)))
      exact (isRoot_gcd_iff_residue A D a α (hd hDα)).mp hα
    · rintro ⟨hDα, hres⟩
      exact (isRoot_gcd_iff_residue A D a α (hd hDα)).mpr ⟨hDα, hres⟩
  have hcount : (D.roots.map (fun α => A.eval α / (derivative D).eval α)).count a
      = (D.roots.filter (fun α => A.eval α / (derivative D).eval α = a)).card := by
    rw [Multiset.count_map,
      Multiset.filter_congr (q := fun α => A.eval α / (derivative D).eval α = a)
        (fun α _ => eq_comm)]
  rw [(IsAlgClosed.splits (gcd D (A - C a * derivative D))).natDegree_eq_card_roots, hroots,
    hcount]

open scoped Classical in
-- `deg gcd(D, A − a·D')` equals the number of `D`-roots with residue `a`.
/-- Root-product form over `K[t]`: `R(t) = lc(D)^{deg D − 1} · ∏_{α : D(α)=0} (C(A α) − X·C(D' α))`,
for `deg A < deg D` over an algebraically closed field. -/
theorem rtResultant_eq_prod_roots [IsAlgClosed F] (A D : F[X]) (hA : A.natDegree < D.natDegree) :
    rtResultant A D
      = C (D.leadingCoeff) ^ (D.natDegree - 1) *
        (D.roots.map (fun α =>
          C (A.eval α) - Polynomial.X * C ((derivative D).eval α))).prod := by
  have hCinj : Function.Injective (C : F →+* F[X]) := C_injective
  have hndeg : (D.map (C : F →+* F[X])).natDegree = D.natDegree :=
    natDegree_map_eq_of_injective hCinj D
  -- formal degree bound `deg(A − t·D') ≤ deg D − 1`
  have hg : (A.map (C : F →+* F[X])
      - C Polynomial.X * (derivative D).map (C : F →+* F[X])).natDegree ≤ D.natDegree - 1 := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_map_eq_of_injective hCinj]; omega
    · refine (natDegree_C_mul_le _ _).trans ?_
      rw [natDegree_map_eq_of_injective hCinj]
      exact natDegree_derivative_le D
  -- `D.map C` splits over `K[t]`
  have hsplit : (D.map (C : F →+* F[X])).Splits := (IsAlgClosed.splits D).map (C : F →+* F[X])
  rw [rtResultant]
  nth_rewrite 1 [← hndeg]
  rw [Polynomial.resultant_eq_prod_eval (D.map (C : F →+* F[X]))
        (A.map (C : F →+* F[X]) - C Polynomial.X * (derivative D).map (C : F →+* F[X]))
        (D.natDegree - 1) hg hsplit,
      leadingCoeff_map_of_injective hCinj,
      (IsAlgClosed.splits D).roots_map (C : F →+* F[X]), Multiset.map_map]
  refine congrArg (C (D.leadingCoeff) ^ (D.natDegree - 1) * ·)
    (congrArg Multiset.prod (Multiset.map_congr rfl (fun α _ => ?_)))
  -- read `g(C α) = C(A(α)) − X·C(D'(α))`
  simp only [Function.comp_apply, eval_sub, eval_mul, eval_C, eval_map,
    show A.eval₂ (C : F →+* F[X]) (C α) = C (A.eval α) from eval₂_hom (C : F →+* F[X]) α,
    show (derivative D).eval₂ (C : F →+* F[X]) (C α) = C ((derivative D).eval α)
      from eval₂_hom (C : F →+* F[X]) α]

-- The un-evaluated root-product form of `R(t)` over `K[t]`.
/-- At a root `α` with `D'(α) ≠ 0`, `C(A α) − X·C(D' α) = −C(D' α)·(X − C(A α/D' α))`. -/
theorem linearFactor_eq_residue (A D : F[X]) (α : F) (hα : (derivative D).eval α ≠ 0) :
    C (A.eval α) - Polynomial.X * C ((derivative D).eval α)
      = -C ((derivative D).eval α) * (Polynomial.X - C (A.eval α / (derivative D).eval α)) := by
  have hC : C ((derivative D).eval α) * C (A.eval α / (derivative D).eval α) = C (A.eval α) := by
    rw [← C_mul, mul_div_cancel₀ _ hα]
  linear_combination -hC

open scoped Classical in
/-- The roots of `rtResultant A D` (with multiplicity) are the residues `A(α)/D'(α)` over the roots `α`
of `D`, for separable `D` and `deg A < deg D` over an algebraically closed field. -/
theorem roots_rtResultant [IsAlgClosed F] (A D : F[X]) (hD : D.Separable)
    (hA : A.natDegree < D.natDegree) :
    (rtResultant A D).roots = D.roots.map (fun α => A.eval α / (derivative D).eval α) := by
  have hd : ∀ α ∈ D.roots, (derivative D).eval α ≠ 0 := by
    intro α hα
    have hr : D.IsRoot α := (mem_roots hD.ne_zero).mp hα
    have := hD.eval₂_derivative_ne_zero (RingHom.id F)
      (by simpa [eval₂_eq_eval_map, Polynomial.map_id] using hr)
    simpa [eval₂_eq_eval_map, Polynomial.map_id] using this
  -- the nonzero constant scalar pulled out of the product
  set s : F := D.leadingCoeff ^ (D.natDegree - 1) *
    (D.roots.map (fun α => -(derivative D).eval α)).prod with hs
  have hs0 : s ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hD.ne_zero)) ?_
    exact Multiset.prod_ne_zero (by simpa using fun α hα => hd α hα)
  -- `R = C s · ∏_α (t − C(residue α))`
  have hRC : rtResultant A D
      = C s * (D.roots.map (fun α => Polynomial.X - C (A.eval α / (derivative D).eval α))).prod := by
    rw [rtResultant_eq_prod_roots A D hA,
      Multiset.map_congr rfl (fun α hα => linearFactor_eq_residue A D α (hd α hα)),
      Multiset.prod_map_mul, hs, map_mul, map_pow,
      map_multiset_prod (C : F →+* F[X]), Multiset.map_map]
    simp only [Function.comp_apply, map_neg]
    ring
  have hmap : (D.roots.map (fun α => Polynomial.X - C (A.eval α / (derivative D).eval α)))
      = (D.roots.map (fun α => A.eval α / (derivative D).eval α)).map (fun a => Polynomial.X - C a) :=
    (Multiset.map_map (fun a => Polynomial.X - C a)
      (fun α => A.eval α / (derivative D).eval α) D.roots).symm
  rw [hRC, roots_C_mul _ hs0, hmap, roots_multiset_prod_X_sub_C]

open scoped Classical in
-- The roots of `R(t)` (with multiplicity) are the residues over the roots of `D`.
open scoped Classical in
/-- `rootMultiplicity a (rtResultant A D) = deg gcd(D, A − a·D')`, for separable `D` and `deg A < deg D`
over an algebraically closed field. -/
theorem rootMultiplicity_rtResultant_eq_natDegree_gcd [IsAlgClosed F] (A D : F[X]) (hD : D.Separable)
    (hA : A.natDegree < D.natDegree) (a : F) :
    (rtResultant A D).rootMultiplicity a = (gcd D (A - C a * derivative D)).natDegree := by
  rw [← count_roots, roots_rtResultant A D hD hA, ← natDegree_gcd_eq_count_residue A D hD a]

open scoped Classical in
-- `rootMultiplicity a R = deg gcd(D, A − a·D')`: the residue multiplicity is the gcd degree.
open scoped Classical in
/-- The distinct roots of `rtResultant A D` are the distinct residues `{A(α)/D'(α) : D(α) = 0}`, for
separable `D` and `deg A < deg D` over an algebraically closed field. -/
theorem rtResultant_roots_toFinset [IsAlgClosed F] (A D : F[X]) (hD : D.Separable)
    (hA : A.natDegree < D.natDegree) :
    (rtResultant A D).roots.toFinset
      = D.roots.toFinset.image (fun α => A.eval α / (derivative D).eval α) := by
  rw [roots_rtResultant A D hD hA, Multiset.toFinset_map]

open scoped Classical in
/-- The monic squarefree product `∏(X − a)` over the distinct roots `a` of `rtResultant A D` divides it. -/
theorem czichowskiR1_dvd_rtResultant [IsAlgClosed F] (A D : F[X]) :
    ((rtResultant A D).roots.toFinset.prod (fun a => Polynomial.X - C a)) ∣ rtResultant A D :=
  (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map (Multiset.dedup_le _))).trans
    (prod_multiset_X_sub_C_dvd _)

open scoped Classical in
/-- The residue multiplicity is at most `deg D` (it is the degree of a divisor of `D`). -/
theorem rootMultiplicity_rtResultant_le [IsAlgClosed F] (A D : F[X]) (hD : D.Separable)
    (hA : A.natDegree < D.natDegree) (a : F) :
    (rtResultant A D).rootMultiplicity a ≤ D.natDegree := by
  rw [rootMultiplicity_rtResultant_eq_natDegree_gcd A D hD hA a]
  exact Polynomial.natDegree_le_of_dvd (gcd_dvd_left _ _) (fun h => by simp [h] at hA)

/-- The Rothstein–Trager resultant of a separable denominator is nonzero: each root-product
factor carries `−D′(α)·t` with `D′(α) ≠ 0` by separability. -/
theorem rtResultant_ne_zero [IsAlgClosed F] (A D : F[X]) (hD : D.Separable)
    (hA : A.natDegree < D.natDegree) : rtResultant A D ≠ 0 := by
  have hD0 : D ≠ 0 := fun h => by simp [h] at hA
  rw [rtResultant_eq_prod_roots A D hA]
  refine mul_ne_zero (pow_ne_zero _ (by
    rw [Ne, C_eq_zero]
    exact leadingCoeff_ne_zero.mpr hD0)) ?_
  refine Multiset.prod_ne_zero ?_
  rw [Multiset.mem_map]
  rintro ⟨α, hα, hfac⟩
  have hDα : D.eval α = 0 := by
    have := (mem_roots hD0).mp hα
    exact this
  have hD'α : (derivative D).eval α = 0 := by
    have h1 := congrArg (fun q => Polynomial.coeff q 1) hfac
    simp only [coeff_sub, coeff_C, coeff_zero, mul_comm Polynomial.X, coeff_C_mul,
      coeff_X_one, mul_one, if_neg one_ne_zero, zero_sub, neg_eq_zero] at h1
    exact h1
  obtain ⟨u, v, huv⟩ := hD
  have := congrArg (Polynomial.eval α) huv
  simp [hDα, hD'α] at this

end DeepWiki.SymbolicIntegration
