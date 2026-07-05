import DeepWiki.SymbolicIntegration.Computable.LrtSoundness
import DeepWiki.SymbolicIntegration.Computable.DifferentialAlgebraicClosure

/-! # Discharging the residue-resultant nonvanishing `hR0` from normality `hE`

`LrtReducedGenuineData` used to carry the Rothstein–Trager resultant nonvanishing
`res_t(Dstar, hNum − z·D Dstar) ≠ 0` (`hR0`) as a **separate** field. Bronstein's residue criterion
(Thm 5.6.1, §4.4) *derives* it from the genuine normality `hE` (`η ≠ β′` at the poles), which the book
carries anyway. This file makes that derivation: over the concrete `E = AlgebraicClosure K`
(`K = CFieldSpec.K α`, derivation from `DifferentialAlgebraicClosure`), normality gives `D(Dstar)(β) ≠ 0` at
every root, so `rtResultantGen_ne_zero` shows the base-changed resultant — hence the `K`-level one, by
injectivity of `algebraMap` — is nonzero. `hR0` is therefore **no longer a field**; the assembled reduced
soundness `isIntegralResultLrtG_cIntegrateReducedLrtG_of_genuine` supplies it here. -/

namespace DeepWiki.SymbolicIntegration

open Polynomial Compute CPolyG QFunNZG Classical
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]

/-- **`hR0` is derivable from `hE` (specialized at the algebraic closure).** Given the primitive-case data
(`hDt0`, `hAD`) and normality `hnorm` at the poles over `E = AlgebraicClosure K`, the residue resultant
`cResidueResultantTowerGWf` is nonzero. The `hB` (`implicitDeriv` nonvanishing) is derived from `hnorm` exactly
as in `isIntegralResultLrtG_cIntegrateReducedLrtG_of_setup`; `hB_deg` is automatic from monic `Dstar` +
`hDt0`; then `toPolyG_cResidueResultantTowerGWf_map` + `rtResultantGen_ne_zero` + `map` injectivity close it. -/
theorem residueResultant_ne_zero_of_hnormAlgClosure [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0)
    (hpp : (toPolyG d).primPart ≠ 0) (hDt0 : (toPolyG Dt).natDegree = 0)
    (hAD : (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).natDegree
        < (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2).natDegree)
    (hnorm : ∀ β ∈ ((toPolyG (cHermiteReduceTowerGWf Dt a d).2.2).map
              (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α)))).roots.toFinset,
        ((toPolyG Dt).map (algebraMap (CFieldSpec.K α)
            (AlgebraicClosure (CFieldSpec.K α)))).eval β ≠ β′) :
    toPolyG (cResidueResultantTowerGWf Dt (cHermiteReduceTowerGWf Dt a d).2.1
        (cHermiteReduceTowerGWf Dt a d).2.2) ≠ 0 := by
  set hNum := (cHermiteReduceTowerGWf Dt a d).2.1 with hNumdef
  set Dstar := (cHermiteReduceTowerGWf Dt a d).2.2 with hDstardef
  set φ := algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α)) with hφdef
  have hDmonic : (toPolyG Dstar).Monic := toPolyG_cHermiteReduceTowerGWf_Dstar_monic hgcd Dt a d hd0
  have hDsep : (toPolyG Dstar).Separable :=
    PerfectField.separable_iff_squarefree.mpr
      (toPolyG_cHermiteReduceTowerGWf_Dstar_squarefree hgcd Dt a d hd0 hpp)
  have hDmonicE : ((toPolyG Dstar).map φ).Monic := hDmonic.map φ
  have hDsepE : ((toPolyG Dstar).map φ).Separable := (Polynomial.separable_map φ).mpr hDsep
  have hB : ∀ β ∈ ((toPolyG Dstar).map φ).roots,
      (Differential.implicitDeriv ((toPolyG Dt).map φ) ((toPolyG Dstar).map φ)).eval β ≠ 0 := by
    intro β hβ
    have hcop : IsCoprime ((toPolyG Dstar).map φ)
        (Differential.implicitDeriv ((toPolyG Dt).map φ) ((toPolyG Dstar).map φ)) := by
      rw [monic_separable_eq_nodal _ hDmonicE hDsepE, Lagrange.nodal]
      exact (isCoprime_prod_X_sub_C_implicitDeriv_iff _ _).mpr (by simpa using hnorm)
    exact isCoprime_X_sub_C_iff.mp (hcop.of_isCoprime_of_dvd_left
      (dvd_iff_isRoot.mpr (Polynomial.isRoot_of_mem_roots hβ)))
  have hAnd : ((toPolyG hNum).map φ).natDegree < ((toPolyG Dstar).map φ).natDegree := by
    rw [Polynomial.natDegree_map, Polynomial.natDegree_map]; exact hAD
  have hB_deg : (Differential.implicitDeriv ((toPolyG Dt).map φ) ((toPolyG Dstar).map φ)).natDegree
      ≤ ((toPolyG Dstar).map φ).natDegree - 1 :=
    natDegree_implicitDeriv_le_of_monic ((toPolyG Dt).map φ) ((toPolyG Dstar).map φ) hDmonicE
      (by rw [Polynomial.natDegree_map]; exact hDt0)
  have hmap_ne : (toPolyG (cResidueResultantTowerGWf Dt hNum Dstar)).map φ ≠ 0 := by
    rw [toPolyG_cResidueResultantTowerGWf_map Dt hNum Dstar hDmonic hDt0 hAD]
    exact rtResultantGen_ne_zero _ _ _ hDmonicE.ne_zero hB hAnd hB_deg
  exact fun h => hmap_ne (by rw [h, Polynomial.map_zero])

/-- **`hR0` from the pole-normality `def`.** Instantiates `LrtPoleNormalityData` at `E = AlgebraicClosure K`
(a `def`-hypothesis instantiation, so the `CFieldSpec.K α` universe unifies — the same mechanism as
`isIntegralResultLrtG_algebraicClosure`) and feeds `residueResultant_ne_zero_of_hnormAlgClosure`. This is what
lets `hR0` be *dropped* as a field of `LrtReducedGenuineData`. -/
theorem hR0_of_normalityData [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hDt0 : (toPolyG Dt).natDegree = 0)
    (hAD : (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).natDegree
        < (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2).natDegree)
    (h : LrtPoleNormalityData Dt a d) :
    toPolyG (cResidueResultantTowerGWf Dt (cHermiteReduceTowerGWf Dt a d).2.1
        (cHermiteReduceTowerGWf Dt a d).2.2) ≠ 0 :=
  residueResultant_ne_zero_of_hnormAlgClosure hgcd Dt a d hd0 hpp hDt0 hAD
    (h (AlgebraicClosure (CFieldSpec.K α)))

set_option maxHeartbeats 800000 in
/-- **The assembled LRT reduced soundness from the bundled genuine data.** Moved here from `LrtSoundness`
because it now *derives* `hR0` (via `hR0_of_normalityData`, which needs the algebraic closure) rather than
reading it off a structure field. Given only `d ≠ 0` and the genuine `LrtReducedGenuineData` (now `hR0`-free),
the root-free primitive reduced integrator `cIntegrateReducedLrtG` is sound. -/
theorem isIntegralResultLrtG_cIntegrateReducedLrtG_of_genuine [CharZero (CFieldSpec.K α)]
    [Algebra ℚ (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α)
    (hd0 : toPolyG d ≠ 0) (hgen : LrtReducedGenuineData Dt a d) :
    IsIntegralResultLrtG Dt a d (cIntegrateReducedLrtG Dt a d) :=
  isIntegralResultLrtG_cIntegrateReducedLrtG_of_setup hgcd Dt a d hd0
    (Polynomial.primPart_ne_zero _) hgen.hcopgcd hgen.hDt0 hgen.hAD
    (hR0_of_normalityData hgcd Dt a d hd0 (Polynomial.primPart_ne_zero _) hgen.hDt0 hgen.hAD hgen.hE)
    (Polynomial.primPart_ne_zero _) hgen.hm hgen.hE

end DeepWiki.SymbolicIntegration
