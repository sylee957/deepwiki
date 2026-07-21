import DeepWiki.SymbolicIntegration.RationalIntegrationGcdLogForm
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.ResidueMultiplicity

/-! # The non-monic Rothstein–Trager log-form

The switchable gcd log-form (`ratFunc_eq_sum_residue_of_isSimilar_gcd`) is stated over the
monic split denominator `Lagrange.nodal s id`. This file wraps it for an arbitrary
separable denominator over an algebraically closed field: `D = C (lc D) · nodal(roots D)`,
the residues and the residue gcds are invariant under the leading-coefficient scaling, and
the sum ranges over the residues — equivalently the roots of the Rothstein–Trager
resultant. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open scoped Classical in
/-- The residue image of the roots is the root set of the Rothstein–Trager resultant. -/
theorem image_residue_eq_roots_rtResultant [IsAlgClosed K] (A D : K[X]) (hD : D.Separable)
    (hA : A.natDegree < D.natDegree) :
    D.roots.toFinset.image (fun α => A.eval α / (derivative D).eval α)
      = (rtResultant A D).roots.toFinset := by
  rw [roots_rtResultant A D hD hA, Multiset.toFinset_map]

open scoped Classical in
/-- **The non-monic switchable log-form**: for separable `D` over an algebraically closed
field and `deg A < deg D`, `A/D = ∑_a a · logDeriv (g a)` over the residues, for any family
`g` similar to the residue gcds `rtLogGcd A D a`. -/
theorem ratFunc_eq_sum_rtLogGcd [IsAlgClosed K] (A D : K[X]) (hD : D.Separable)
    (hA : A.natDegree < D.natDegree) (g : K → K[X])
    (hg : ∀ a, IsSimilar (g a) (rtLogGcd A D a)) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D
      = ∑ a ∈ D.roots.toFinset.image (fun α => A.eval α / (derivative D).eval α),
          algebraMap K[X] (RatFunc K) (C a)
            * Differential.logDeriv (algebraMap K[X] (RatFunc K) (g a)) := by
  have hD0 : D ≠ 0 := fun h => by simp [h] at hA
  set lc : K := D.leadingCoeff with hlcdef
  have hlc : lc ≠ 0 := leadingCoeff_ne_zero.mpr hD0
  have hnodup : D.roots.Nodup := nodup_roots hD
  set s : Finset K := D.roots.toFinset with hs
  have hsval : s.val = D.roots := by
    rw [hs, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  have hcard : s.card = D.natDegree := by
    show Multiset.card s.val = D.natDegree
    rw [hsval]
    exact splits_iff_card_roots.mp (IsAlgClosed.splits D)
  have hnodal : D = C lc * Lagrange.nodal s id := by
    conv_lhs => rw [Splits.eq_prod_roots (IsAlgClosed.splits D)]
    congr 1
    rw [Lagrange.nodal]
    show (D.roots.map fun a => X - C a).prod = (s.val.map fun i => X - C (id i)).prod
    rw [hsval]
    rfl
  have hD' : derivative D = C lc * derivative (Lagrange.nodal s id) := by
    conv_lhs => rw [hnodal]
    rw [derivative_C_mul]
  set A' : K[X] := C lc⁻¹ * A with hA'
  have hCC : (C lc : K[X]) * (C lc⁻¹ * A) = A := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hlc, map_one, one_mul]
  have hE : ∀ a : K, A - C a * derivative D
      = C lc * (A' - C a * derivative (Lagrange.nodal s id)) := by
    intro a
    rw [hA', mul_sub, hCC, hD']
    ring
  have hgcdE : ∀ a : K,
      gcd (Lagrange.nodal s id) (A' - C a * derivative (Lagrange.nodal s id))
        = rtLogGcd A D a := by
    intro a
    rw [rtLogGcd, hE a]
    conv_rhs => rw [hnodal]
    rw [gcd_mul_left, normalize_eq_one.mpr (isUnit_C.mpr hlc.isUnit), one_mul]
  have hg' : ∀ a, IsSimilar (g a)
      (gcd (Lagrange.nodal s id) (A' - C a * derivative (Lagrange.nodal s id))) := by
    intro a
    rw [hgcdE a]
    exact hg a
  have hA'deg : A'.degree < s.card := by
    rw [hcard]
    rcases eq_or_ne A' 0 with h0 | h0
    · rw [h0, degree_zero]
      exact WithBot.bot_lt_coe _
    · rw [degree_eq_natDegree h0]
      exact_mod_cast lt_of_le_of_lt (natDegree_C_mul_le _ _) hA
  have hmain := ratFunc_eq_sum_residue_of_isSimilar_gcd s A' hA'deg g hg'
  have hu : algebraMap K[X] (RatFunc K) (C lc) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective K), C_eq_zero]
    exact hlc
  have hLHS : algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D
      = algebraMap K[X] (RatFunc K) A'
          / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) := by
    conv_lhs => rw [hnodal, ← hCC, ← hA']
    rw [show algebraMap K[X] (RatFunc K) (C lc * A')
        = algebraMap K[X] (RatFunc K) (C lc) * algebraMap K[X] (RatFunc K) A' from
        map_mul _ _ _,
      show algebraMap K[X] (RatFunc K) (C lc * Lagrange.nodal s id)
        = algebraMap K[X] (RatFunc K) (C lc)
            * algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) from map_mul _ _ _,
      mul_div_mul_left _ _ hu]
  have hres : ∀ α ∈ s, A'.eval α / eval α (derivative (Lagrange.nodal s id))
      = A.eval α / (derivative D).eval α := by
    intro α _
    rw [hA', hD']
    simp only [eval_mul, eval_C]
    rw [div_mul_eq_div_div, div_eq_mul_inv (A.eval α), mul_comm (A.eval α)]
  rw [hLHS, hmain]
  congr 1
  exact Finset.image_congr fun α hα => hres α hα

end DeepWiki.SymbolicIntegration
