import DeepWiki.SymbolicIntegration.Engine.LrtSoundness
import DeepWiki.SymbolicIntegration.DifferentialAlgebra.AlgebraicClosure
import DeepWiki.SymbolicIntegration.Engine.FuelFreeDiophantine
import DeepWiki.SymbolicIntegration.Engine.RefinesPoly
import DeepWiki.SymbolicIntegration.Engine.LrtResidueResultantDischarge.GenuineMonomial

/-! # Residue-resultant nonvanishing from pole normality

Derives nonvanishing of the tower residue resultant from genuine pole normality. Over
`E = AlgebraicClosure K`, normality gives nonvanishing of the implicit derivative at each pole, so
`rtResultantGen_ne_zero` proves the base-changed resultant nonzero; injectivity of `algebraMap` then returns
the `K`-level result used by the reduced LRT integrator soundness theorem. -/

namespace DeepWiki.SymbolicIntegration

open Polynomial DensePoly CFrac Classical
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]

/-- **`hR0` is derivable from `hE` (specialized at the algebraic closure).** Given the primitive-case data
(`hDt0`, `hAD`) and normality `hnorm` at the poles over `E = AlgebraicClosure K`, the residue resultant
`cResidueResultantTower` is nonzero. The `hB` (`implicitDeriv` nonvanishing) is derived from `hnorm` exactly
as in `isIntegralResultLrtG_cIntegrateReducedLrtG_of_setup`; `hB_deg` is automatic from monic `Dstar` +
`hDt0`; then `toPolyG_cResidueResultantTowerG_map` + `rtResultantGen_ne_zero` + `map` injectivity close it. -/
theorem residueResultant_ne_zero_of_hnormAlgClosure [CharZero (CFieldSpec.K α)]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hpp : (toPoly d).primPart ≠ 0) (hDt0 : (toPoly Dt).natDegree = 0)
    (hAD : (toPoly (cHermiteReduceTower Dt a d).2.1).natDegree
        < (toPoly (cHermiteReduceTower Dt a d).2.2).natDegree)
    (hnorm : ∀ β ∈ ((toPoly (cHermiteReduceTower Dt a d).2.2).map
              (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α)))).roots.toFinset,
        ((toPoly Dt).map (algebraMap (CFieldSpec.K α)
            (AlgebraicClosure (CFieldSpec.K α)))).eval β ≠ β′) :
    toPoly (cResidueResultantTower Dt (cHermiteReduceTower Dt a d).2.1
        (cHermiteReduceTower Dt a d).2.2) ≠ 0 := by
  set hNum := (cHermiteReduceTower Dt a d).2.1 with hNumdef
  set Dstar := (cHermiteReduceTower Dt a d).2.2 with hDstardef
  set φ := algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α)) with hφdef
  have hDmonic : (toPoly Dstar).Monic := toPolyG_cHermiteReduceTowerG_Dstar_monic hgcd Dt a d hd0
  have hDsep : (toPoly Dstar).Separable :=
    PerfectField.separable_iff_squarefree.mpr
      (toPolyG_cHermiteReduceTowerG_Dstar_squarefree hgcd Dt a d hd0 hpp)
  have hDmonicE : ((toPoly Dstar).map φ).Monic := hDmonic.map φ
  have hDsepE : ((toPoly Dstar).map φ).Separable := (Polynomial.separable_map φ).mpr hDsep
  have hB : ∀ β ∈ ((toPoly Dstar).map φ).roots,
      (Differential.implicitDeriv ((toPoly Dt).map φ) ((toPoly Dstar).map φ)).eval β ≠ 0 := by
    intro β hβ
    have hcop : IsCoprime ((toPoly Dstar).map φ)
        (Differential.implicitDeriv ((toPoly Dt).map φ) ((toPoly Dstar).map φ)) := by
      rw [monic_separable_eq_nodal _ hDmonicE hDsepE, Lagrange.nodal]
      exact (isCoprime_prod_X_sub_C_implicitDeriv_iff _ _).mpr (by simpa using hnorm)
    exact isCoprime_X_sub_C_iff.mp (hcop.of_isCoprime_of_dvd_left
      (dvd_iff_isRoot.mpr (Polynomial.isRoot_of_mem_roots hβ)))
  have hAnd : ((toPoly hNum).map φ).natDegree < ((toPoly Dstar).map φ).natDegree := by
    rw [Polynomial.natDegree_map, Polynomial.natDegree_map]; exact hAD
  have hB_deg : (Differential.implicitDeriv ((toPoly Dt).map φ) ((toPoly Dstar).map φ)).natDegree
      ≤ ((toPoly Dstar).map φ).natDegree - 1 :=
    natDegree_implicitDeriv_le_of_monic ((toPoly Dt).map φ) ((toPoly Dstar).map φ) hDmonicE
      (by rw [Polynomial.natDegree_map]; exact hDt0)
  have hmap_ne : (toPoly (cResidueResultantTower Dt hNum Dstar)).map φ ≠ 0 := by
    rw [toPolyG_cResidueResultantTowerG_map Dt hNum Dstar hDmonic hDt0 hAD]
    exact rtResultantGen_ne_zero _ _ _ hDmonicE.ne_zero hB hAnd hB_deg
  exact fun h => hmap_ne (by rw [h, Polynomial.map_zero])

/-- **`hR0` from the pole-normality `def`.** Instantiates `LrtPoleNormalityData` at `E = AlgebraicClosure K`
(a `def`-hypothesis instantiation, so the `CFieldSpec.K α` universe unifies — the same mechanism as
`isIntegralResultLrtG_algebraicClosure`) and feeds `residueResultant_ne_zero_of_hnormAlgClosure`. This is what
lets `hR0` be *dropped* as a field of `LrtReducedGenuineData`. -/
theorem hR0_of_normalityData [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hDt0 : (toPoly Dt).natDegree = 0)
    (hAD : (toPoly (cHermiteReduceTower Dt a d).2.1).natDegree
        < (toPoly (cHermiteReduceTower Dt a d).2.2).natDegree)
    (h : LrtPoleNormalityData Dt a d) :
    toPoly (cResidueResultantTower Dt (cHermiteReduceTower Dt a d).2.1
        (cHermiteReduceTower Dt a d).2.2) ≠ 0 :=
  residueResultant_ne_zero_of_hnormAlgClosure hgcd Dt a d hd0 hpp hDt0 hAD
    (h (AlgebraicClosure (CFieldSpec.K α)))

set_option maxHeartbeats 800000 in
/-- **The reduced integrator is sound in the no-poles / trivial-normal-part case** (`deg Dstar = 0`). With a
constant squarefree denominator there are no residues, the log part is empty, and the leftover numerator
vanishes by properness, leaving the pure Hermite identity. -/
theorem isIntegralResultLrtG_cIntegrateReducedLrtG_of_noPoles [CharZero (CFieldSpec.K α)]
    [Algebra ℚ (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α)
    (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0) (hDtdeg : (toPoly Dt).natDegree ≤ 1)
    (haProper : (toPoly a).degree < (toPoly d).degree) (hgen : GenuinePrimitiveMonomialLrt Dt)
    (hDstar0 : (toPoly (cHermiteReduceTower Dt a d).2.2).natDegree = 0) :
    IsIntegralResultLrt Dt a d (cIntegrateReducedLrt Dt a d) := by
  have hcopgcd := hcopgcd_of_genuineMonomial hgcd Dt d hd0 hpp hgen
  have hADdeg := hAD_degree_of_genuineMonomial hgcd Dt a d hd0 hpp hDtdeg haProper hgen
  have hNum0 : toPoly (cHermiteReduceTower Dt a d).2.1 = 0 := by
    by_contra h; have := Polynomial.natDegree_lt_natDegree h hADdeg; omega
  have hDstarcdeg : cdeg (cHermiteReduceTower Dt a d).2.2 = 0 := by
    rw [cdegG_eq_natDegree]; exact hDstar0
  intro E _ _ _ _ _ _
  rw [cIntegrateReducedLrt]
  simp only [cLrtLogArgG_eq_nil_of_cdegG_zero Dt _ _ hDstarcdeg, logResidueSumLrtG_nil, add_zero]
  have hh := hherm_lrt_E (E := E) hgcd Dt a d hd0 hpp hcopgcd
  rw [hNum0, show amGExt (0 : (CFieldSpec.K α)[X]) = (0 : RatFunc E) from by simp [amGExt],
    zero_div, add_zero] at hh
  exact hh

set_option maxHeartbeats 800000 in
/-- **The assembled LRT reduced soundness from the genuine monomial property alone.** Given `d ≠ 0`, the
decidable scope guard `hDt0`, the input properness `haProper` (`deg a < deg d`), and the single genuine datum
`LrtReducedGenuineData` (now just `hE`), the root-free primitive reduced integrator `cIntegrateReducedLrt` is
sound. Case-splits on `deg Dstar`: **no poles** (`deg Dstar = 0`) is the trivially-sound no-poles branch
(`…_of_noPoles`); otherwise the Hermite properness `hAD` is *derived* in `.natDegree` form from the `.degree`
discharge (`hAD_degree_of_genuineMonomial` + `natDegree_lt_natDegree`, `deg Dstar ≥ 1`) and fed to `…_of_setup`
alongside the derived `hR0`/`hm`/`hnorm`/`hcopgcd`. Every side condition flows from `hE`. -/
theorem isIntegralResultLrtG_cIntegrateReducedLrtG_of_genuine [CharZero (CFieldSpec.K α)]
    [Algebra ℚ (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α)
    (hd0 : toPoly d ≠ 0) (hDt0 : (toPoly Dt).natDegree = 0)
    (haProper : (toPoly a).degree < (toPoly d).degree) (hgen : LrtReducedGenuineData Dt a d) :
    IsIntegralResultLrt Dt a d (cIntegrateReducedLrt Dt a d) := by
  have hDtdeg : (toPoly Dt).natDegree ≤ 1 := hDt0 ▸ Nat.zero_le 1
  by_cases hDstar0 : (toPoly (cHermiteReduceTower Dt a d).2.2).natDegree = 0
  · -- no poles: `deg Dstar = 0` ⟹ trivially sound (the `.natDegree hAD = 0<0` gap)
    exact isIntegralResultLrtG_cIntegrateReducedLrtG_of_noPoles hgcd Dt a d hd0
      (Polynomial.primPart_ne_zero _) hDtdeg haProper hgen.hE hDstar0
  · -- `deg Dstar ≥ 1`: derive `.natDegree hAD` from the `.degree` discharge, then the residue path
    have hADdeg := hAD_degree_of_genuineMonomial hgcd Dt a d hd0 (Polynomial.primPart_ne_zero _)
      hDtdeg haProper hgen.hE
    have hAD : (toPoly (cHermiteReduceTower Dt a d).2.1).natDegree
        < (toPoly (cHermiteReduceTower Dt a d).2.2).natDegree := by
      by_cases hh : toPoly (cHermiteReduceTower Dt a d).2.1 = 0
      · rw [hh, Polynomial.natDegree_zero]; omega
      · exact Polynomial.natDegree_lt_natDegree hh hADdeg
    have hnorm : LrtPoleNormalityData Dt a d := lrtPoleNormalityData_of_genuineMonomial hgen.hE
    exact isIntegralResultLrtG_cIntegrateReducedLrtG_of_setup hgcd Dt a d hd0
      (Polynomial.primPart_ne_zero _)
      (hcopgcd_of_genuineMonomial hgcd Dt d hd0 (Polynomial.primPart_ne_zero _) hgen.hE)
      hDt0 hAD ⟨hR0_of_normalityData hgcd Dt a d hd0 (Polynomial.primPart_ne_zero _) hDt0 hAD hnorm,
        Polynomial.primPart_ne_zero _⟩
      (hm_of_genuineMonomial hgcd Dt a d hd0 hgen.hE hDt0) hnorm

end DeepWiki.SymbolicIntegration
