import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms
import DeepWiki.SymbolicIntegration.Residues

/-! # Residue multiplicity (Bronstein Theorem 2.5.1, the multiplicity bridge)
The Rothstein–Trager resultant `R(t) = res_x(D, A − t·D')` has, as a polynomial in `t`, each residue
`a` of `A/D` as a root; its *multiplicity* there equals the number of roots `α` of `D` whose residue
`A(α)/D'(α)` is `a`, which in turn equals `deg gcd(D, A − a·D')` (the degree of the Rothstein–Trager
`Gₐ`). This file proves that bridge over an algebraically closed field for separable `D`:
`deg gcd(D, A − a·D') = #{α : D(α) = 0, A(α)/D'(α) = a} = rootMultiplicity a R`. It identifies the
LRT subresultant index `i = deg_x R_m` with `rootMultiplicity a R`, discharging the degree hypotheses
of `isSimilar_lrtSubresultant_eval_gcd`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {F : Type*} [Field F]

open scoped Classical in
/-- **Residue count, gcd-degree form** (Bronstein Thm 2.5.1, the degree side): over an algebraically
closed field with separable `D`, the roots of `Gₐ = gcd(D, A − a·D')` are exactly the roots `α` of `D`
with residue `A(α)/D'(α) = a`. Both multisets are nodup (separable), so they coincide; taking cardinality
gives `deg gcd(D, A − a·D') = #{α ∈ D.roots : A(α)/D'(α) = a}` as a `Multiset.count` of the residue map. -/
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
example [IsAlgClosed F] (A D : F[X]) (hD : D.Separable) (a : F) :
    (gcd D (A - C a * derivative D)).natDegree
      = (D.roots.map (fun α => A.eval α / (derivative D).eval α)).count a :=
  natDegree_gcd_eq_count_residue A D hD a

end DeepWiki.SymbolicIntegration
